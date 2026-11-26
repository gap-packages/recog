#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This file's authors include Alice Niemeyer.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##  This file contains an implementation of the naming algorithms
##  (non-constructive recognition algorithms) for classical groups in their
##  natural representation by  Niemeyer and Praeger.
##
##  Details of the algorithms implemented here are in the following publications.
##
##  [NP98] Alice C. Niemeyer and  Cheryl E. Praeger
##      "A Recognition Algorithm for Classical Groups over Finite Fields",
##      Proc. London Math. Soc (3) 77, 1998, 117-169.
##
##  [NP97] Alice C. Niemeyer and  Cheryl E. Praeger
##      "Implementing a Recognition Algorithm for Classical Groups"
##      "Groups and Computation II", Amer. Math. Soc. DIMACS Series 28, 1997.
##
##  [NP99] Alice C. Niemeyer and  Cheryl E. Praeger
##      "A Recognition Algorithm for Non-Generic Classical Groups over
##       Finite Fields",  J. Austral. Math. Soc. (Series A)67 , 223-253, 1999.
##
##  [NP92] Peter M. Neumann and Cheryl E. Praeger
##      "A Recognition Algorithm for Special Linear Groups",
##      Proc. London Math. Soc. (3) 65, 1992, 555-603.
##
##  [Kle87] Peter B. Kleidman
##      "The maximal subgroups of the finite 8-dimensional orthogonal groups
##       POmega+(8,q) and of their automorphism groups",
##      J. Algebra 110, 1987, 173-242.
##
##  This implementation uses some algorithms described elsewhere:
##
##  [CLG97a] Frank Celler and C.R. Leedham-Green
##      "Calculating the order of an invertible matrix",
##      "Groups and Computation II", Amer. Math. Soc. DIMACS Series 28, 1997.
##
##  [CLG97b] Frank Celler and C.R. Leedham-Green
##      "A non-constructive recognition algorithm for the special linear
##      and other classical groups"
##      "Groups and Computation II", Amer. Math. Soc. DIMACS Series 28, 1997.
##
##    In this implementation we use the irreducibility test of the algorithm
##    described in [CL97b], which can often avoid an application  of the Meataxe
##    algorithm.
##
##   An overview on applications of ppd-elements, see
##
##  [Pra99] Cheryl E. Praeger,
##      "Primitive prime divisor elements in finite classical groups",
##       Proc. of Groups St. Andrews in Bath 1997, Cambridge University
##      Press, 1999.
##
##
##
#############################################################################

BindGlobal( "ClassicalMethDb", [] );
BindGlobal( "ClassicalMethDbForDegree2", [] );

BindGlobal( "FindHomMethodsClassical", rec() );

#
###
# Test whether <n> (assumed integer) is a power of 2
IsPowerOfTwo := n -> IsInt(n) and n > 1 and 2 ^ Log2Int(n) = n;

# Use the current random element g to rule out that the group preserves,
# up to scalars, a bilinear form (maybeDual) or a sesquilinear form
# (maybeFrobenius). If g preserves a form up to the scalar lambda, then g^-1
# is similar to lambda^-1 * g, respectively to lambda^-1 * g^sigma for the
# field automorphism sigma of order 2. So for the coefficients c_i of the
# characteristic polynomial of g
#
#     c_0 * c_(d-i) = lambda^i * c_i     (with c_(d-i)^sigma for sesquilinear)
#
#     trace(g) = lambda * trace(g^-1)    (with trace(g)^sigma for sesquilinear)
#
# Nonzero traces determine lambda, and the identities are checked with it.
# Otherwise the identities only determine lambda^i0, where i0 is the gcd of
# q-1 and the exponents i with c_i (and hence c_(d-i)) nonzero, and
# consistency with that is checked instead.
RECOG.RuleOutFormsByCharPoly := function(recognise)
    local d, q, c, I, a, tM, tMi, qq, l, consistent;

    d := recognise.d;
    q := recognise.q;
    c := CoefficientsOfUnivariatePolynomial(recognise.cpol);
    I := Filtered([0 .. d], i -> not IsZero(c[i+1]));
    tM := Trace(recognise.g);
    tMi := Trace(recognise.g^-1);

    # traces vanish together; nonzero coefficients occur in pairs i, d-i
    if IsZero(tM) <> IsZero(tMi) or Reversed(d - I) <> I then
        recognise.maybeDual := false;
        recognise.maybeFrobenius := false;
        return;
    fi;

    # Test whether l[k] = lambda^I[k] for all k, where tr = lambda * tri
    # determines lambda if nonzero
    consistent := function(l, tr, tri)
        local Iq, t, i0, lambda;

        if IsZero(tr) then
            # lambda^(q-1) = 1, so q-1 may join the gcd without a factor in l
            Iq := Concatenation(I, [q - 1]);
            t := GcdRepresentation(Iq);
            i0 := Iq * t;
            lambda := Product([1 .. Length(I)], k -> l[k]^t[k]); # = lambda^i0
        else
            i0 := 1;  # lambda is known exactly, not just lambda^i0
            lambda := tr / tri;
        fi;
        return ForAll([1 .. Length(I)], k -> l[k] = lambda^(I[k] / i0));
    end;

    a := c[1];

    if recognise.maybeDual then
        l := List(I, i -> a * c[d-i+1] / c[i+1]);
        if not consistent(l, tM, tMi) then
            recognise.maybeDual := false;
        fi;
    fi;

    if recognise.maybeFrobenius then
        qq := recognise.p^(recognise.a / 2);
        l := List(I, i -> a * c[d-i+1]^qq / c[i+1]);
        if not consistent(l, tM^qq, tMi) then
            recognise.maybeFrobenius := false;
        fi;
    fi;
end;


# Check if m > 5 and the order of a basic lppd(d,q;e) element

HasLBGgt5 := function( m, p, a, e )

    local pm, i,  ppds;

    if m <= 5 then
        return false;
    fi;

    # Find the basic ppds of p^(ae)-1
    pm := PrimitivePrimeDivisors(a*e, p);
    # find the ppds in m
    ppds := GcdInt(pm.ppds, m);

    # There are no ppds
    if ppds = 1 then
        return false;
    fi;

    ## Every ppd is at least e+1, so a prime other than e+1 dividing
    ## ppds is large; e+1 itself is large only if its square divides <m>
    while ppds mod (e+1) = 0 do
        ppds := ppds / (e+1);
    od;
    if ppds = 1 then
        return IsPrimeInt(e+1) and m mod (e+1)^2 = 0;
    fi;

    return true;
end;


# "Inverse" to KroneckerProduct on 2x2 matrices -- does not handle inputs with
# a zero block in the top left (but the code calling this deals with this by
# simply looking at another random element)
BindGlobal("KroneckerFactors", function(g)
    local a, b, c, d, A, Ainv, B, C, D, I;

    A := g{[1,2]}{[1,2]};
    if IsZero(Determinant(A)) then
        return false;
    fi;
    Ainv := A^-1;
    B := g{[1,2]}{[3,4]};
    C := g{[3,4]}{[1,2]};
    D := g{[3,4]}{[3,4]};
    B := B * Ainv; b := B[1,1];
    C := C * Ainv; c := C[1,1];
    D := D * Ainv; d := D[1,1];

    I := A^0;
    if B <> I*b or C <> I*c or D <> I*d then
        return false;
    fi;

    return [ [[I[1,1], b], [c, d]], A ];
end);


######################################################################
##
#F  FindBase (field, phi) . . . . . . . . . . . find appropriate basis
##
##  The following function returns a matrix B such that B phi B^T has
##  the form ( 0, 0, 0, -1), ( 0, 0, 1, 0 ) (0, 1, 0, 0), (-1, 0, 0, 0)
##
FindBase := function( field, phi )

     local form, mat1, mat2, mat;

     form := BilinearFormByMatrix(
          [[ 0,0,0,-1],[ 0,0,1,0],[0,1,0,0],[-1,0,0,0]]*One(field), field);
     mat1 := BaseChangeToCanonical(phi);
     mat2 := BaseChangeToCanonical(form);
     mat := LeftQuotient(mat2, mat1);
     return mat;

end;

FindBaseC2 := function( field, qf )

     local form2, mat, mat2;

     form2 := QuadraticFormByMatrix(
             [[0,0,0,-1],[0,0,1,0],[0,0,0,0],[0,0,0,0]]*One(field), field);
     mat := BaseChangeToCanonical(qf);
     mat2 := BaseChangeToCanonical(form2);
     mat := mat2 / mat;
     return mat;

end;

# Helper function which tries to compute the order of a matrix group G
# treated as a projective group. The result may be too small, but it
# will divide the actual order.
RECOG.EstimateProjOrder := function(G)
  local S, base, gens, size, i, o;
  S := StabilizerChain(G,rec( Projective := true ));

  # genss enumerates each basic orbit under the generators of its own layer
  # only, so Size(S) need not divide the order. Enumerate the i-th orbit
  # under all strong generators fixing the first i-1 base points instead;
  # the product of these orbit lengths divides the order of G.
  base := BaseStabilizerChain(S);
  gens := GeneratorsOfGroup(G);
  size := 1;
  for i in [1 .. Length(base.points)] do
    o := Orb(gens, base.points[i], base.ops[i]);
    Enumerate(o);
    size := size * Length(o);

    gens := Filtered(StrongGenerators(S), g -> ForAll([1 .. i],
                j -> base.ops[j](base.points[j], g) = base.points[j]));
    if IsEmpty(gens) then
      break;
    fi;
  od;
  return size;
end;

# Return true if there is a nonzero w in the fourth exterior power of the
# natural module such that w * g = c(g)^2 * w for all g in <gens>, where
# g * F * g^T = c(g) * F. The Cayley 4-form spans such a line for the
# normaliser of Spin(7,q) in its spin representation.
RECOG.FixesFourFormLine := function(gens, F)
    local d, field, one, outer, pairs, quads, P2, L, a, b, S, T, J, sgn,
          i, j, B, g, c, ext2, ext4, X;

    d := Length(F);
    field := DefaultFieldOfMatrix(F);
    one := One(field);
    outer := {u, v} -> Concatenation(List(u, x -> x * v));
    pairs := Combinations([1 .. d], 2);
    quads := Combinations([1 .. d], 4);

    # P2 maps u ⊗ v to u ∧ v
    P2 := NullMat(d^2, Length(pairs), field);
    for a in [1 .. Length(pairs)] do
        P2[(pairs[a][1] - 1) * d + pairs[a][2], a] := one;
        P2[(pairs[a][2] - 1) * d + pairs[a][1], a] := -one;
    od;
    P2 := ImmutableMatrix(field, P2);

    # L maps x ⊗ y in Λ²V ⊗ Λ²V to x ∧ y in Λ⁴V
    L := NullMat(Length(pairs)^2, Length(quads), field);
    for a in [1 .. Length(pairs)] do
        for b in [1 .. Length(pairs)] do
            S := pairs[a];
            T := pairs[b];
            if not IsEmpty(Intersection(S, T)) then
                continue;
            fi;
            J := Union(S, T);
            sgn := SignPerm(PermList(List(Concatenation(S, T),
                                          x -> Position(J, x))));
            L[(a - 1) * Length(pairs) + b, Position(quads, J)] := sgn * one;
        od;
    od;
    L := ImmutableMatrix(field, L);

    # B spans the common eigenspace of the generators seen so far
    i := PositionProperty(F, row -> not IsZero(row));
    j := PositionNonZero(F[i]);
    B := IdentityMat(Length(quads), field);
    for g in gens do
        c := (g * F * TransposedMat(g))[i, j] / F[i, j];
        ext2 := List(pairs, p -> outer(g[p[1]], g[p[2]])) * P2;
        ext4 := List(quads, Q -> outer(ext2[Position(pairs, Q{[1, 2]})],
                                       ext2[Position(pairs, Q{[3, 4]})])) * L;
        X := NullspaceMat(B * ext4 - c^2 * B);
        if IsEmpty(X) then
            return false;
        fi;
        B := X * B;
    od;
    return true;
end;

# The naming algorithm for classical groups is divided into two
# parts: A version that applies to classical groups for sufficiently
# large parameters, called generic parameters, as described in [NP98, Def.3.2],
# and a part that applies to smaller cases of classical groups, where
# the exsistence of sufficiently informative ppd elements is not guaranteed.
# The naming algorithm for these cases  is decribed in [NP99] and implemented
# in the functions whose name starts with NonGeneric below. This function tests
# whether the parameters are generic or not.
#
BindRecogMethod("FindHomMethodsClassical", "IsGenericParameters",
"tests whether group has generic parameters",
function(recognise)
    local fact, d, q, hint;

    hint := recognise.hint;

    d := recognise.d;
    q := recognise.q;

    if hint = "unknown" then
        return NeverApplicable;

    elif hint = "linear" and d <= 2 then
        recognise.isGeneric := false;
        return NeverApplicable;

    elif hint = "linear" and d = 3 then
        #q = 2^s-1
        if IsPowerOfTwo( q+1 ) then
            recognise.isGeneric := false;
        fi;
        return NeverApplicable;

    elif hint = "symplectic" and
      (d < 6 or (d mod 2 <> 0) or
       [d,q] in [[6,2],[6,3],[8,2]]) then
        recognise.isGeneric := false;
        return NeverApplicable;

    elif hint = "unitary" and
      (d < 5 or d = 6 or [d,q] = [5,4]) then
        recognise.isGeneric := false;
        return NeverApplicable;

    elif hint = "orthogonalplus" and
      (d mod 2 <> 0 or d < 10
       or (d = 10 and q = 2)) then
        recognise.isGeneric := false;
        return NeverApplicable;

    elif hint = "orthogonalminus" and
      (d mod 2 <> 0 or d < 6
       or [d,q] in [[6,2],[6,3],[8,2]]) then
        recognise.isGeneric := false;
        return NeverApplicable;

    elif hint = "orthogonalcircle" then
        if d < 7 or [d,q] = [7,3] then
            recognise.isGeneric := false;
            return NeverApplicable;
        fi;
        if d mod 2 = 0 then
            recognise.isGeneric := false;
            return NeverApplicable;
        fi;
        if q mod 2 = 0 then
            #TODO: INFORECOG1 ... not irreducible
            #TODO: INFORECOG2 ... d odd --> q odd
            recognise.isReducible := true;
            recognise.isGeneric := false;
            return NeverApplicable;
        fi;
    fi;

    return NeverApplicable;
end);


#
# In the case of generic parameters we need to have found at least
# two ppd elements, one large and one basic. If we have not yet
# found them, we return TemporaryFailure and have to inspect
# more random elements.
BindRecogMethod("FindHomMethodsClassical", "IsGeneric",
"tests whether group is generic",
function(recognise)
    if recognise.isGeneric = false then
        return NeverApplicable;
    fi;

    if Length(recognise.E) < 2 or
       Length(recognise.LE) = 0 or
       Length(recognise.BE) = 0 then
        return TemporaryFailure;
    fi;

    recognise.isGeneric := true;
    return NeverApplicable;
end);



#  Once we have verified that  the  group has generic  parameters we need to
#  rule  out  the  extension  field case, that is we have to show the group
#  cannot be embedded into GL(d/b,q^b).b. To rule this out, we need to find a
#  b-witness for each of the pi(d) distinct prime divisors b of d, or
#  in some cases a pair of witnesses, as discussed in Section 3.3  of
#  [NP98].   The function RuledOutExtField() tests whether we can
#  deduce that the group does not preserve an extension field structure.

BindRecogMethod("FindHomMethodsClassical", "RuledOutExtField",
"tests whether extension field case is ruled out",
function(recognise)
    local differmodfour, d, q, E, b, bx, hint;

    hint := recognise.hint;
    d := recognise.d;
    q := recognise.q;
    E := recognise.E;

    differmodfour := function(E)
        local e;
        for e in E do
            if E[1] mod 4 <> e mod 4 then
                return true;
            fi;
        od;
        return false;
    end;

    b := recognise.currentgcd;

    if hint = "unknown" then
        if Length(recognise.ClassicalForms) > 0 then
            # A trivial form only tells us that we are in the linear case.
            # For generic linear groups, use that to avoid ruling out Singer
            # normalizers too early. Test it before IsSymplecticForm, which
            # also holds for the zero form.
            if First(recognise.ClassicalForms, IsTrivialForm) <> fail then
                hint := "linear";
            elif First(recognise.ClassicalForms, IsHermitianForm) <> fail then
                hint := "unitary";
            elif First(recognise.ClassicalForms, IsSymplecticForm) <> fail then
                hint := "symplectic";
            elif First(recognise.ClassicalForms, IsHyperbolicForm) <> fail then
                hint := "orthogonalplus";
            elif First(recognise.ClassicalForms, IsEllipticForm) <> fail then
                hint := "orthogonalminus";
            elif First(recognise.ClassicalForms, IsParabolicForm) <> fail then
                hint := "orthogonalcircle";
            fi;
        fi;
    fi;

    if hint = "unknown" and b < 2 then
        return TemporaryFailure;
    fi;

    if hint in ["linear","unitary","orthogonalcircle"] then
        bx := 1;
    else
        bx := 2;
    fi;


    if b < bx then
        if recognise.hint <> "unknown" then
           recognise.hintIsWrong := true;
           # clean up and never come back
           return Success;
        fi;
        recognise.isNotExt := true;
        return NeverApplicable;
    fi;
    if b > bx then
        return TemporaryFailure;
    fi;

    if hint = "linear" then
        if d = 3 and not 2 in recognise.LE then
            # The 3-witnesses of [NP98, Section 7] are lppd(3,q;2)-elements,
            # which SL(3,q) lacks for q = 3*2^s-1. Every element of
            # GammaL(1,q^3) has order dividing q^3-1 or 3(q-1), so an element
            # of any other order is a witness as well.
            if not recognise.needOrders then
                recognise.needOrders := true;
                return TemporaryFailure;
            fi;
            if ForAny(recognise.orders,
                      o -> (q^3-1) mod o <> 0 and 3*(q-1) mod o <> 0) then
                recognise.isNotExt := true;
                return NeverApplicable;
            fi;
            return TemporaryFailure;
        fi;
        if d >= 3 then
            # For generic linear groups, E is built from random elements.
            # Seeing only part of the expected extension-field pattern is not
            # enough to rule that case out yet; we only reject when the data is
            # actually incompatible with a Singer normalizer, and otherwise wait
            # until we have seen the full [d-1,d] pattern.
            if not IsPrime(d)
               or not IsSubset([d-1,d], E)
               or d-1 in recognise.LE then
                recognise.isNotExt := true;
                return NeverApplicable;
            fi;
            if E <> [d-1,d] then
                return TemporaryFailure;
            fi;
        fi;

    elif hint = "unitary" then
        recognise.isNotExt := true;
        return NeverApplicable;

    # Below, only a witness decides: without one, the random elements seen
    # so far do not show that G lies in an extension field group.
    elif hint = "symplectic" then
        if d mod 4 = 2 and q mod 2 = 1 then
             if ForAny(E, x -> x mod 4 = 0) then
                 recognise.isNotExt := true;
             fi;
        elif d mod 4 = 0 and q mod 2 = 0 then
             if ForAny(E, x -> x mod 4 = 2) then
                 recognise.isNotExt := true;
             fi;
        elif d mod 4 = 0 and q mod 2 = 1 then
             if Length(E) < 2 then
                 return TemporaryFailure;
             fi;
             if differmodfour(E) then
                 recognise.isNotExt := true;
             fi;
        elif d mod 4 = 2 and q mod 2 = 0 then
            if Length(E) > 0 then
                recognise.isNotExt := true;
            fi;
        else
           Info( InfoRecog_ClassicalNaming, 2, "d cannot be odd in hint Sp");
           recognise.hintIsWrong := true;
           # clean up and never come back
           return Success;
        fi;

    elif hint = "orthogonalplus" then
        if d mod 4 = 2 then
            if ForAny(E, x -> x mod 4 = 0) then
                recognise.isNotExt := true;
            fi;
        elif d mod 4 = 0 then
            # With only one observed ppd exponent there is no mod 4
            # discrepancy yet, so we cannot conclude that the extension-field
            # case is still possible.
            if Length(E) < 2 then
                return TemporaryFailure;
            fi;
            if differmodfour(E) then
                recognise.isNotExt := true;
            fi;
        else
           Info( InfoRecog_ClassicalNaming, 2, "d cannot be odd in hint O+");
           recognise.hintIsWrong := true;
           # clean up and never come back
           return Success;
        fi;


    elif hint = "orthogonalminus" then
        if d mod 4 = 0 then
            if ForAny(E, x -> x mod 4 = 2) then
                recognise.isNotExt := true;
            fi;
        elif d mod 4 = 2 then
            if Length(E) < 2 then
                return TemporaryFailure;
            fi;
            if differmodfour(E) then
                recognise.isNotExt := true;
            fi;
        else
           Info( InfoRecog_ClassicalNaming, 2, "d cannot be odd in hint O-");
           recognise.hintIsWrong := true;
           # clean up and never come back
           return Success;
        fi;

    elif hint = "orthogonalcircle" then
        recognise.isNotExt := true;
        return NeverApplicable;
    fi;

    if recognise.isNotExt = true then
        return NeverApplicable;
    else
        return TemporaryFailure;
    fi;
end);


#   Methods to rule  out  the   nearly  simple groups
#
#  We assume that we have already tested that the group acts irreducibly
#  on the  underlying  vector space and has a ppd(d,q;e_1)-element and a
#  ppd(d,q;e_2)-element for d/2 < e_1 < e_2 <= d of which at least one is
#  large and one is basic. The nearly simple groups that can have such
#  ppd elements are listed in Tables 13 and 14 in [NP98]. These could
#  arise as the commutator  subgroup  of the given group. In these
#  tables also elements are listed that occur in a classical group but
#  not in these nearly simple groups. If we find such elements, these
#  groups are thereby ruled out.
#
BindRecogMethod("FindHomMethodsClassical", "IsNotAlternating",
"tests whether alternating groups are ruled out",
function(recognise)
    local V, P, i, g ,q, o;

    q := recognise.q;

#   if recognise.hint <> "unknown" and recognise.hint <> "linear" then
#       Info( InfoRecog_ClassicalNaming, 2, "G' not an AlternatingGroup;");
#       recognise.isNotAlternating := true;
#       return NeverApplicable;
#   fi;

    if Length(recognise.ClassicalForms) > 0 and
        First(recognise.ClassicalForms,IsTrivialForm)=fail then
       recognise.isNotAlternating := true;
       return NeverApplicable;
    fi;

    if recognise.d <> 4 or q <> recognise.p or (3 <= q and q < 23) then
       Info( InfoRecog_ClassicalNaming, 2, "G is not an alternating group" );
       recognise.isNotAlternating := true;
       return NeverApplicable;
    fi;

    if q = 2 then
       if Size(recognise.grp) <> 2520 then  # 2520 = 3*4*5*6*7 = |A7|
           Info( InfoRecog_ClassicalNaming, 2, "G is not an alternating group" );
           recognise.isNotAlternating := true;
           return NeverApplicable;
       else
           Info( InfoRecog_ClassicalNaming, 2, "G' might be A7;");
           AddSet(recognise.possibleNearlySimple,"A7");
           return Success;
       fi;
    fi;

    if q >= 23 then
       if 4 in recognise.LE then
           Info( InfoRecog_ClassicalNaming, 2, "G' not alternating;");
           recognise.isNotAlternating := true;
           return NeverApplicable;
       fi;

       if recognise.n > 15 then
           AddSet (recognise.possibleNearlySimple, "2.A7");
           Info( InfoRecog_ClassicalNaming, 2, "G' might be 2.A7;");
           return TemporaryFailure;
       fi;
   fi;

   return TemporaryFailure;

end);



BindRecogMethod("FindHomMethodsClassical", "IsNotMathieu",
"tests whether Mathieu groups are ruled out",
function(recognise)
   local i, fn, g, d, q, E, ord;

   d := recognise.d;
   q := recognise.q;
   E := recognise.E;
   g := recognise.g;

#   if recognise.hint <> "unknown" and recognise.hint <> "linear" then
#       Info( InfoRecog_ClassicalNaming, 2, "G' not a Mathieu Group;");
#       recognise.isNotMathieu := true;
#       return NeverApplicable;
#   fi;

    if Length(recognise.ClassicalForms) > 0 and
        First(recognise.ClassicalForms,IsTrivialForm)=fail then
       recognise.isNotMathieu := true;
       return NeverApplicable;
    fi;

   if not [d, q] in [ [5, 3], [6,3], [11, 2] ] then
       Info( InfoRecog_ClassicalNaming, 2, "G' is not a Mathieu group;");
       recognise.isNotMathieu := true;
       return NeverApplicable;
   fi;

   if d = 5 or d = 6 then
       ord := Order(g);
       if (ord mod 121=0 or (d=5 and ord=13) or (d=6 and ord=7)) then
          Info( InfoRecog_ClassicalNaming, 2, "G' is not a Mathieu group.;");
          recognise.isNotMathieu := true;
          return NeverApplicable;
       fi;
   else
       if ForAny([6,7,8,9], m -> m in E) then
          Info( InfoRecog_ClassicalNaming, 2, "G' is not a Mathieu group;");
           recognise.isNotMathieu := true;
           return NeverApplicable;
       fi;
   fi;


# TODO Check how big n should be
    # if G' might be a Mathieu group, add the Atlas name to
    # recognise.possibleNearlySimple
    if d = 5 then
        if recognise.n > 15 then
            AddSet(recognise.possibleNearlySimple, "M11" );
            Info( InfoRecog_ClassicalNaming, 2, "G' might be M11;");
            return TemporaryFailure;
        fi;
    elif d = 6 then
        if recognise.n > 15 then
            AddSet(recognise.possibleNearlySimple, "2.M12" );
            Info( InfoRecog_ClassicalNaming, 2, "G' might be 2.M12;");
            return TemporaryFailure;
        fi;
    else
        if recognise.n > 15 then
            AddSet(recognise.possibleNearlySimple, "M23" );
            AddSet(recognise.possibleNearlySimple, "M24" );
            Info( InfoRecog_ClassicalNaming, 2, "G' might be M23 or M24;");
            return TemporaryFailure;
        fi;
    fi;

   return TemporaryFailure;

end);


# This method is meant to rule out the situation PSL(2,r) <= G <= Z x PGL(2,r)
# for some central factor Z, i.e. G' is PSL(2,r).
#
# For more information, see Section 8.4 in [NP98].
BindRecogMethod("FindHomMethodsClassical", "IsNotPSL",
"tests whether PSL groups are ruled out",
function(recognise)
   local i, E, LE, d, p, q, str, fn, ord, r;

    E := recognise.E;
    LE := recognise.LE;
    d := recognise.d;
    q := recognise.q;
    p := recognise.p;

#    if recognise.hint <> "unknown" and recognise.hint <> "linear" then
#        Info( InfoRecog_ClassicalNaming, 2, "G' not PSL(2,r);");
#        recognise.isNotPSL := true;
#        return NeverApplicable;
#    fi;

    # if there is an invariant form, then this can't be PSL(2,r)
    if Length(recognise.ClassicalForms) > 0 and
        First(recognise.ClassicalForms,IsTrivialForm)=fail then
       recognise.isNotPSL := true;
       return NeverApplicable;
    fi;

    # By [NP98, Section 8.4], if we are in that situation then G
    # contains ppd(d,q;e) elements for only two values of e
    if Length(E) > 2 then
        Info(InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,r)");
        recognise.isNotPSL := true;
        return NeverApplicable;
    fi;

    # By [NP98, Table 3], for G' to be PSL(2,r), we must have...
    # - e_2 = e_1 + 1
    # - r_1 = e_2 = e_1 + 1 is a prime
    # - r_2 = r = 2*e_2 + 1 is a prime
    # - d = 1/2 (r \pm 1), or equivalently: r = 2*d \pm 1
    if Length(E) = 2 then
        r := 2 * E[2] + 1;
        if not (E[2] = E[1] + 1 and r in [2*d-1, 2*d+1] and IsPrimeInt(E[1]+1) and IsPrimeInt(r)) then
            Info(InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,r)");
            recognise.isNotPSL := true;
            return NeverApplicable;
        fi;
    fi;

    # Handle some special cases
    if d = 3 then
        # Try to rule out PSL(2,7)
        if q = 2 or q = 5 then
            # Note PSL(2,7) is isomorphic to SL(3,2), so don't print the
            # message if q = 2
            if q = 5 then
                Info( InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,7)");
            fi;
            recognise.isNotPSL := true;
            return NeverApplicable;
        elif ((q+1) mod 3 = 0 and IsPowerOfTwo((q+1)/3)) then
            # q = 3*2^s-1 with s >= 2, so q^2-1 has no large ppd. By
            # [NP98, Table 14] the witnesses are the elements of order
            # dividing q^2-1 but not 6(q-1).
             ord := Order(recognise.g);
             if (q^2-1) mod ord = 0 and (6*(q-1)) mod ord <> 0 then
                 Info( InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,7)");
                 recognise.isNotPSL := true;
                 return NeverApplicable;
            fi;
        elif p = 3 or p = 7 or 2 in LE then
             # we are only certain that PSL(2,7) is ruled if 2 in LE
             # and the cases p=3 or p=7 cannot have the required ppds
             if 2 in LE then
                 Info( InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,7)");
             fi;
             recognise.isNotPSL := true;
             return NeverApplicable;
        fi;
    elif d = 5 then
        # Try to rule out PSL(2,11)
        if q = 5 or q = 11 then
            Info( InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,11)");
            recognise.isNotPSL := true;
            return NeverApplicable;
        elif q = 3 then
            ord := Order(recognise.g);
            if (ord mod 11^2 = 0 or ord mod 20 = 0) then
                Info( InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,11)");
                recognise.isNotPSL := true;
                return NeverApplicable;
            fi;
        elif p <> 5 and p <> 11 then
            if (3 in LE or 4 in LE) then
                Info( InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,11)");
                recognise.isNotPSL := true;
                return NeverApplicable;
            fi;
        fi;
    elif d = 6 then
        # Try to rule out PSL(2,11)
        if q = 2 then
            Info( InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,11)");
            recognise.isNotPSL := true;
            return NeverApplicable;
        elif q = 3 then
            ord := Order(recognise.g);
            if (ord mod (11^2)=0 or 6 in E) then
                Info( InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,11)");
                recognise.isNotPSL := true;
                return NeverApplicable;
            fi;
        elif p <> 5 and p <> 11 then
            if (6 in E or 4 in LE) then
                Info( InfoRecog_ClassicalNaming, 2, "G' is not PSL(2,11)");
                recognise.isNotPSL := true;
                return NeverApplicable;
            fi;
        fi;
    fi;

    if recognise.n > 15 and Length(recognise.E) = 2 then
        str := Concatenation("PSL(2,", String(r), ")");
        Info( InfoRecog_ClassicalNaming, 2, "G' might be ", str);
        AddSet( recognise.possibleNearlySimple, str );
        return TemporaryFailure;
    fi;
    return TemporaryFailure;
end);


#############################################################################
##
## IsPrimitivePrimeDivisor . . . . . . . . . . . . . . ( b, a, p )
##
## Test whether p is a primitive prime divisor of b^a-1.
##
IsPrimitivePrimeDivisor := function( b, a, p )

    local i;

    if not IsPrimeInt(p) then
        return false;
    fi;
    if not IsInt(b) or b <= 1 then
        return false;
    fi;
    if not IsInt(a) or a <= 1 then
        return false;
    fi;

    if (b^a-1) mod p <> 0 then
        return false;
    fi;
    for i in [ 1 .. a-1 ] do
        if b^i-1 mod p = 0 then
            return false;
        fi;
    od;

    return true;
end;

# generate the next random element and its char polynomial
BindRecogMethod("FindHomMethodsClassical", "TestRandomElement",
"makes new random element and stores it and its char poly",
function(recognise)
    local g, ppd, bppd, d, q, cpol, f, deg, facs, r, s, h, gmod,
    ord, bc, phi, kf, kfOrders, o, cf, i, found, p;

    recognise.g := PseudoRandom(recognise.grp);
    recognise.cpol := CharacteristicPolynomial(recognise.g);
    recognise.n := recognise.n + 1;

    d := recognise.d;
    q := recognise.q;
    p := recognise.p;
    f := recognise.field;
    g := recognise.g;
    cpol := recognise.cpol;

    if recognise.needOrders then
        ord := Order(g);
        AddSet( recognise.orders, ord );
    fi;
    if recognise.needPOrders then
        ord := ProjectiveOrder(g);
        AddSet( recognise.porders, ord );
    fi;
    if recognise.needSp4Splitting and not recognise.hasSp4Splitting and
       RECOG.IsSp4SplittingWitness(cpol, q) then
        recognise.hasSp4Splitting := true;
    fi;

    ppd := IsPpdElement(f, cpol, d, q, 1);
    # if the element is no ppd we get out
    if ppd = false then
        recognise.isppd := false;
    else
        AddSet(recognise.E,ppd[1]);
        recognise.currentgcd := GcdInt( recognise.currentgcd, ppd[1] );
        # check whether we have a large ppd-element
        if ppd[2] = true then
            AddSet(recognise.LE,ppd[1]);
        fi;
        recognise.ppd := [ ppd[1], ppd[2], "unknown" ];
        if Length(recognise.BE) < 1 or recognise.needLB then
            #We only need one basic ppd-element
            #Also, each basic ppd element is a ppd-element
            bppd := IsPpdElement (f, cpol, d, recognise.p, recognise.a);
            if bppd <> false then
                AddSet(recognise.BE, bppd[1]);
                if ppd[2] = true and ppd[1] = bppd[1] then
                    AddSet( recognise.LB, ppd[1] );
                    recognise.ppd[3] := true;
                fi;
            fi;
        fi;
    fi;
    if recognise.needE2 = true then
        # these are ppd(d,q;e)-elements with e=d/2
        ppd := IsPpdElementD2(f, cpol, d, recognise.q, 1);
        if ppd <> false then
            AddSet( recognise.E2, ppd[1] );
            if ppd[2] = true then

            ## first we test whether the characteristic polynomial has
            ## two factors of degree d/2.
            facs := Factors( PolynomialRing(f), cpol );
            deg := List(facs, EuclideanDegree );
            if Length(deg) = 2 and deg[1] = deg[2] and deg[1] = d/2 then

              ## Bug fix 29.10.09
              ## Now we compute the r-part h of g
              s := Order(g);
              s := GcdInt(s, ppd[3]);
              h := g^s;
              ## now order(h) is the product of all ppds dividing |g|, see
              ##  Section 6.1 page 250 of [NP99]
              if IsOne(h) then
                  return TemporaryFailure;
              fi;
              gmod := GModuleByMats([h], recognise.field);
              cf := MTX.CollectedFactors(gmod);
              if Length(cf) = 2 and cf[1][2] = cf[2][2] then
                # we have two non-isomorphic composition factors
                Info(InfoRecog_ClassicalNaming, 2, "Found a large and special ppd(",d,", ",q,"; ",ppd[1],")-element" );
                AddSet(recognise.LS, ppd[1] );
              fi;

            fi;
          fi;
        fi;
    fi;


    if ForAny(recognise.E, x -> x mod 2 <> 0) then
        recognise.isSpContained := false;
        recognise.isOmegaContained := false;
    fi;
    if ForAny(recognise.E, x -> x mod 2 = 0) then
        recognise.isSUContained := false;
    fi;

    if recognise.needBaseChange = true and recognise.bc = "unknown" then
        if Length(recognise.ClassicalForms) = 0 then
            recognise.needForms := true;
            return NotEnoughInformation;
        fi;
        i := 1;
        found := false;
        while not found and i <= Length(recognise.ClassicalForms) do
           phi := recognise.ClassicalForms[i];
           if IsSesquilinearForm(phi) then
                if IsOddInt (q) and IsHyperbolicForm(phi) then
                    Info(InfoRecog_ClassicalNaming, 2,"Performing base change");
                    found := true;
                    bc := FindBase (f, phi);
                    Info(InfoRecog_ClassicalNaming, 2,"Computed base change matrix");
                    bc := bc^-1;
                    recognise.bc := bc;
                elif IsEvenInt(q) and recognise.QuadraticForm <> false then
                    bc := FindBaseC2 (f, recognise.QuadraticForm);
                    found := true;
                    Info(InfoRecog_ClassicalNaming,2,
                     "Computed base change matrix for char 2");
                    bc := bc^-1;
                    recognise.bc := bc;
                fi;
            fi;
            i := i + 1;
        od;
        if not found then
            Info(InfoRecog_ClassicalNaming, 2, "need basechange only in O+");
            return TemporaryFailure;
        fi;
     fi;

     if recognise.needKroneckerFactors = true then
            if recognise.bc = "unknown" then
                recognise.needBaseChange := true;
            else
                kf := KroneckerFactors( g^recognise.bc );
                if kf = false then
                    kf := KroneckerFactors( (g^2)^recognise.bc );
                fi;
                recognise.kroneckerFactors := kf;
            fi;
      fi;

      if recognise.needPlusMinus = true then
            if recognise.kroneckerFactors = "unknown" then
                recognise.needKroneckerFactors := true;
                return TemporaryFailure;
            fi;
            if recognise.kroneckerFactors = false then
                return TemporaryFailure;
            fi;
            # Witnesses that G = SL(2,q) o SL(2,q), collected per factor.
            # By Dickson, a subgroup of PSL(2,q) with an element of order
            # dividing q+1 as below and one of order dividing q-1, both of
            # order > 4 (> 2 for q even), is PSL(2,q). By Goursat, a subgroup
            # of PSL(2,q) x PSL(2,q) projecting onto both factors is the
            # whole product or the graph of an automorphism, and an element
            # whose factors have distinct orders rules out the latter.
            kf := recognise.kroneckerFactors;
            kfOrders := List(kf, k -> ProjectiveOrder(k)[1]);
            Info(InfoRecog_ClassicalNaming, 2, kfOrders);
            for i in [1, 2] do
                o := kfOrders[i];
                if o <= 2 or (q mod 2 <> 0 and o <= 4) then
                    continue;
                fi;
                if (q+1) mod o = 0 and
                   RECOG.IsOPlus4PlusWitness(o, q, p, recognise.a) then
                    AddSet(recognise.factorWitnesses, ["plus", i]);
                fi;
                if (q-1) mod o = 0 then
                    AddSet(recognise.factorWitnesses, ["minus", i]);
                fi;
            od;
            if kfOrders[1] <> kfOrders[2] then
                AddSet(recognise.factorWitnesses, ["distinct"]);
            fi;
        fi;

        if recognise.needDecompose = true then
            if recognise.kroneckerFactors = "unknown" then
                recognise.needKroneckerFactors := true;
                return TemporaryFailure;
            elif recognise.kroneckerFactors = false then
                return TemporaryFailure;
            fi;
            kf := recognise.kroneckerFactors;

            if not kf[1] in Group(recognise.sq1) then
                AddSet(recognise.sq1,kf[1]);
            fi;
            if not kf[2] in Group(recognise.sq2) then
                AddSet(recognise.sq2,kf[2]);
            fi;
       fi;

    return TemporaryFailure;

end);



# Compute the degrees of the irreducible factors of
# the characteristic polynomial recognise.cpol
# These might already yield enough information to show
# that the group acts irreducible without calling
# the Meataxe. This function is described in [CLG97b].
BindRecogMethod("FindHomMethodsClassical", "IsReducible",
"tests whether current random element rules out reducible",
function(recognise)
    local deg, dims, g;

    # compute the degrees of the irreducible factors
    deg := List(Factors(PolynomialRing(recognise.field), recognise.cpol), Degree);

    # compute all possible dimensions
    dims := [0];
    for g in deg do
        UniteSet(dims,dims+g);
    od;

    # intersect it with recognise.dimsReducible
    if IsEmpty(recognise.dimsReducible) then
        recognise.dimsReducible := dims;
    else
        IntersectSet(recognise.dimsReducible,dims);
    fi;

    # G acts irreducibly if only 0 and d are possible
    if Length(recognise.dimsReducible)=2 then
        recognise.isReducible := false;
        return NeverApplicable;
    fi;

    return TemporaryFailure;
end);

BindRecogMethod("FindHomMethodsClassical", "NoClassicalForms",
"tests whether we can rule out certain forms",
function(recognise)
    local d,field;
    RECOG.RuleOutFormsByCharPoly(recognise);

    d := recognise.d;
    field := recognise.field;
    if recognise.maybeDual = false and
      recognise.maybeFrobenius = false then
          if First(recognise.ClassicalForms,IsTrivialForm)=fail then
              Add(recognise.ClassicalForms,
              BilinearFormByMatrix(NullMat(d,d,field),field));
          fi;
          return NeverApplicable;
   fi;

    return TemporaryFailure;

end);



BindRecogMethod("FindHomMethodsClassical", "ClassicalForms",
"Find the invariant forms",
function(recognise)
    local   field,  z,  d,  i,  qq,  A,  c,  I,  t,  i0,
            a,  l,  g,  module,  forms,  dmodule,  fmodule,  form;

    if recognise.n > 1 then
        recognise.needForms := true;
    fi;

    if recognise.needForms <> true then
        return NotEnoughInformation;
    fi;

    # the group has to be absolutely irreducible
    if recognise.isReducible = "unknown" then
        recognise.needMeataxe := true;
        return TemporaryFailure;
    fi;

    # set up the field and other information
    field := recognise.field;
    d := recognise.d;
    z := Zero(field);
    module := recognise.module;

    if recognise.maybeFrobenius = true then
        qq := Characteristic(field)^(DegreeOverPrimeField(field)/2);
    fi;

    # if all forms are excluded then we are finished
    if not recognise.maybeDual and not recognise.maybeFrobenius then
        if First(recognise.ClassicalForms,IsTrivialForm)=fail then
            Add(recognise.ClassicalForms,
            BilinearFormByMatrix(NullMat(d,d,field), field ) );
        fi;
        return NeverApplicable;
    fi;


    # now try to find an invariant form
    if recognise.maybeDual then
        dmodule := RECOG.GeneratorsWithoutScalarsDual(recognise.grp);
        if dmodule <> false then
            form := RECOG.InvariantFormDual(module,dmodule);
            if form <> false then
                Add( recognise.ClassicalForms,
                BilinearFormByMatrix(form[2], field));
                if Length(form)=4 then
                    recognise.QuadraticFormType := form[1];
                    recognise.QuadraticForm := QuadraticFormByMatrix(form[4]);
                fi;
                return NeverApplicable;
            else
                recognise.maybeDual := false;
            fi;
        fi;
    fi;

    if recognise.maybeFrobenius then
        fmodule := RECOG.GeneratorsWithoutScalarsFrobenius(recognise.grp);
        if fmodule <> false then
            form := RECOG.InvariantFormFrobenius(module,fmodule);
            if form <> false then
                Add( recognise.ClassicalForms,
                     HermitianFormByMatrix(form[2], field));
               return NeverApplicable;
            else
                recognise.maybeFrobenius := false;
            fi;
        fi;
    fi;


    # if all forms are excluded then we are finished
    if not recognise.maybeDual and not recognise.maybeFrobenius then
        if First(recognise.ClassicalForms,IsTrivialForm)=fail then
            Add(recognise.ClassicalForms,
            BilinearFormByMatrix(NullMat(d,d,field), field));
            return NeverApplicable;
        fi;
    fi;

    return TemporaryFailure;

end);


BindRecogMethod("FindHomMethodsClassical", "MeatAxe",
"Test irreducibility",
function(recognise)
    if recognise.n > 15 then
        recognise.needMeataxe := true;
    fi;

    if recognise.needMeataxe <> true then
        return NotEnoughInformation;
    fi;


    if MTX.IsIrreducible(recognise.module) then
        recognise.isReducible := false;
        return NeverApplicable;
    else
        Info( InfoRecog_ClassicalNaming, 2,
        "The group acts reducibly and thus doesn't contain a classical group");
        recognise.isReducible := true;
        recognise.isSLContained := false;
        recognise.isSpContained := false;
        recognise.isSUContained := false;
        recognise.isOmegaContained := false;
        return Success;
    fi;
end);

## Main function to test whether group contains SL
BindRecogMethod("FindHomMethodsClassical", "IsSLContained",
"tests whether group contains SL",
function(recognise)
    if recognise.isGeneric <> true or
       recognise.isNotExt <> true or
       recognise.isNotPSL <> true or
       recognise.isReducible = true or
       recognise.isNotMathieu <> true or
       recognise.isNotAlternating <> true then
          return TemporaryFailure;
    fi;


    if recognise.isReducible = "unknown" then
        recognise.needMeataxe := true;
        return NotEnoughInformation;
    fi;


    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NotEnoughInformation;
    fi;

    if First(recognise.ClassicalForms, IsTrivialForm) <> fail then
        recognise.isSLContained := true;
        Info(InfoRecog_ClassicalNaming,2,"The group contains SL(", recognise.d, ", ",
             recognise.q, ");");
        return Success;
    else
        recognise.isSLContained := false;
        Info(InfoRecog_ClassicalNaming,2,"The group does not contain SL(",
             recognise.d, ", ", recognise.q, ");");
        return NeverApplicable;
    fi;

end);

## Main function to test whether group contains Sp
BindRecogMethod("FindHomMethodsClassical", "IsSpContained",
"tests whether group contains Sp",
function(recognise)
    local isSpForm;

    isSpForm := f -> IsSesquilinearForm(f) and IsSymplecticForm(f);

    # if the dimension is not even, the group cannot be symplectic
    if recognise.d mod 2 <> 0 or recognise.isSpContained = false then
        recognise.isSpContained := false;
        return NeverApplicable;
    fi;

    if recognise.isGeneric <> true or
       recognise.isReducible = true or
       recognise.currentgcd <> 2 or
       recognise.isNotPSL <> true or
       recognise.isNotMathieu <> true or
       recognise.isNotAlternating <> true then
          return TemporaryFailure;
    fi;



    if recognise.isReducible = "unknown" then
        recognise.needMeataxe := true;
        return NotEnoughInformation;
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NotEnoughInformation;
    fi;

    # if the group preserves a symplectic form but not a
    # form we have found Sp
    if recognise.QuadraticForm = false and
        First(recognise.ClassicalForms,isSpForm) <> fail then
        # symplectic form
        recognise.isNotExt := true;
        recognise.isSpContained := true;
        Info(InfoRecog_ClassicalNaming,2,"The group contains Sp(", recognise.d, ", ",
             recognise.q, ");");
        return Success;
    else
        recognise.isSpContained := false;
        Info(InfoRecog_ClassicalNaming,2,"The group does not contain Sp(",
             recognise.d, ", ", recognise.q, ");");
        return NeverApplicable;
    fi;
end);


## Main function to test whether group contains SU
BindRecogMethod("FindHomMethodsClassical", "IsSUContained",
"tests whether group contains SU",
function(recognise)
    local f, isHermForm, q0;

    isHermForm := f -> IsSesquilinearForm(f) and IsHermitianForm(f);

    f := recognise.field;

    # if size of field not a square, the group cannot be unitary
    if DegreeOverPrimeField(f) mod 2 <> 0 then
        recognise.isSUContained := false;
        return NeverApplicable;
    fi;

    q0 := Characteristic(recognise.field)^(DegreeOverPrimeField(recognise.field)/2);



    if recognise.isSUContained = false then
        return NeverApplicable;
    fi;

    if recognise.isGeneric <> true or
       recognise.isReducible = true or
       recognise.isNotExt <> true or
       recognise.isNotPSL <> true or
       recognise.isNotMathieu <> true or
       recognise.isNotAlternating <> true then
          return TemporaryFailure;
    fi;



    if recognise.isReducible = "unknown" then
        recognise.needMeataxe := true;
        return NotEnoughInformation;
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NotEnoughInformation;
    fi;

    if First(recognise.ClassicalForms,isHermForm)<> fail then
        recognise.isSUContained := true;
        Info(InfoRecog_ClassicalNaming,2,"The group contains SU(", recognise.d, ", ",
             q0, ");");
        return Success;
    else
        recognise.isSUContained := false;
        Info(InfoRecog_ClassicalNaming,2,"The group does not contain SU(",
             recognise.d, ", ", q0, ");");
        return NeverApplicable;
    fi;
end);


## Main function to test whether group contains SO
BindRecogMethod("FindHomMethodsClassical", "isOmegaContained",
"tests whether group contains SO",
function(recognise)
    local f, isParForm, isEllForm, isHypForm;

    isParForm := f -> IsSesquilinearForm(f) and IsParabolicForm(f);
    isEllForm := f -> IsSesquilinearForm(f) and IsEllipticForm(f);
    isHypForm := f -> IsSesquilinearForm(f) and IsHyperbolicForm(f);

    if recognise.isOmegaContained = false then
        return NeverApplicable;
    fi;


    if IsOddInt(recognise.d) and not IsOddInt(recognise.q) then
        return NeverApplicable;
    fi;

    if recognise.isGeneric <> true or
       not recognise.currentgcd in [1,2] or
       recognise.isNotPSL <> true or
       recognise.isReducible = true or
       recognise.isNotMathieu <> true or
       recognise.isNotAlternating <> true then
          return TemporaryFailure;
    fi;


    if recognise.isReducible = "unknown" then
        recognise.needMeataxe := true;
        return NotEnoughInformation;
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NotEnoughInformation;
    fi;

    if First(recognise.ClassicalForms,isParForm)<> fail or
        IsQuadraticForm( recognise.QuadraticForm) and
        recognise.QuadraticFormType = "orthogonalcircle" then
        #orthogonal circle
        if recognise.d mod 2 = 0 then
            return NeverApplicable;
        fi;
        if recognise.currentgcd <> 1 then
            return TemporaryFailure;
        fi;
        recognise.isNotExt := true;
        recognise.isOmegaContained := true;
        Info(InfoRecog_ClassicalNaming,2,"The group contains SO^o(", recognise.d, ", ",
             recognise.q, ");");
        return Success;

    elif First(recognise.ClassicalForms,isHypForm) <> fail or
        IsQuadraticForm( recognise.QuadraticForm) and
        recognise.QuadraticFormType = "orthogonalplus" then
        #orthogonal plus
        if recognise.d mod 2 <> 0 then
            return NeverApplicable;
        fi;
        if recognise.currentgcd <> 2 then
            return TemporaryFailure;
        fi;
        recognise.isNotExt := true;
        recognise.isOmegaContained := true;
        Info(InfoRecog_ClassicalNaming,2,"The group contains SO+(", recognise.d, ", ",
             recognise.q, ");");
        return Success;

    elif First(recognise.ClassicalForms,isEllForm) <> fail or
        IsQuadraticForm( recognise.QuadraticForm) and
        recognise.QuadraticFormType = "orthogonalminus" then
        # orthogonal minus
        if recognise.d mod 2 <> 0 then
            return NeverApplicable;
        fi;
        if recognise.currentgcd <> 2 then
            return TemporaryFailure;
        fi;
        recognise.isNotExt := true;
        recognise.isOmegaContained := true;
        Info(InfoRecog_ClassicalNaming,2,"The group contains SO-(", recognise.d, ", ",
             recognise.q, ");");
        return Success;
    else
        recognise.isOmegaContained := false;
        Info(InfoRecog_ClassicalNaming,2,"The group does not contain SO(",
             recognise.d, ", ", recognise.q, ");");
        return NeverApplicable;
    fi;
end);


# orders: list of observed element orders
# ord: list of required element orders
#
# For all elements n of ord, we must have observed at least one
# element whose order is a multiple of n
HasElementsMultipleOf := function(orders, ord)
    return ForAll(ord, n -> ForAny(orders, i -> i mod n = 0));
end;

############################################################################/
##
##  The following functions deal with the Non-generic cases. See [NP99].
##

############################################################################/
##
##  NonGenericLinear
##
##  Recognise non-generic linear matrix groups over finite fields:
##  In order to prove that a group G <= GL( 3, 2^s-1) contains SL, we need to
##  find an element of order a multiple of 4 and a large and basic ppd(3,q;3)-
##  element
##
BindRecogMethod("FindHomMethodsClassical", "NonGenericLinear",
"tests whether group is non-generic Linear",
function(recognise)
    local CheckFlag;

    # We know that grp has non-generic parameters. Do we know whether the other
    # prerequisites of Theorem 5.1, [NP99] are fulfilled? If one of them is
    # unknown signal that they must be computed.
    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if Length(recognise.ClassicalForms) = 0 then
            recognise.needForms := true;
            return TemporaryFailure;
        fi;
        Info(InfoRecog_ClassicalNaming,2,"The group is not generic and contains SL(",
             recognise.d, ", ", recognise.q, ");");
        recognise.isGeneric := false;
        recognise.isNotExt := true;
        recognise.isSLContained := true;
        return Success;
    end;

    # grp is non-generic if either d = 2 or (d,q) = (3, 2^s-1)
    if recognise.d > 3 then
        return NeverApplicable;
    fi;
    if recognise.d = 3 and not IsPowerOfTwo(recognise.q+1) then
        return NeverApplicable;
    fi;

    if recognise.isReducible = true then
       return NeverApplicable;
    fi;

    if Length( recognise.ClassicalForms ) > 0 and
       First(recognise.ClassicalForms,IsTrivialForm) = fail then
       return NeverApplicable;
    fi;

    if recognise.needLB = false then
        recognise.needLB := true;
        return TemporaryFailure;
    fi;

    # Now we have confirmed all prerequisites of Theorem 5.1 except for that
    # grp contains an element of order 4 and a basic lppd(3, q, 3) element.
    if recognise.n <= 5 then
        return TemporaryFailure;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return TemporaryFailure;
    fi;
    if 3 in recognise.LB
       and HasElementsMultipleOf(recognise.orders, [4]) then
           return CheckFlag();
    fi;

    return TemporaryFailure;
end);

############################################################################/
##
##  Recognise non-generic symplectic matrix groups over finite fields
##
BindRecogMethod("FindHomMethodsClassical", "NonGenericSymplectic",
"tests whether group is non-generic Symplectic",
function(recognise)
    local d, q, CheckFlag, isSpForm;

    isSpForm := f -> IsSesquilinearForm(f) and IsSymplecticForm(f);

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if Length(recognise.ClassicalForms) = 0 then
            recognise.needForms := true;
            return TemporaryFailure;
        fi;
        Info(InfoRecog_ClassicalNaming,2,"The group is not generic and contains Sp(",
             recognise.d, ", ", recognise.q, ");");
        recognise.isGeneric := false;
        recognise.isNotExt := true;
        recognise.isSpContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

    if not IsEvenInt(recognise.d) then
        return NeverApplicable;
    fi;

    if recognise.isReducible = true then
       return NeverApplicable;
    fi;

    if Length( recognise.ClassicalForms ) > 0 and
       recognise.QuadraticForm = false and
       First( recognise.ClassicalForms, isSpForm) = fail then
       return NeverApplicable;
    fi;

    if d > 8 then
        return NeverApplicable;
    fi;

    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n <= 6 and d <> 4 then
        recognise.needOrders := true;
        return TemporaryFailure;
    elif d = 4 then
        recognise.needOrders := true;
        recognise.needLB := true;
        recognise.needE2 := true;
        recognise.needSp4Splitting :=
            RECOG.Sp4SplittingWitnessDivisors(q) <> fail;
    fi;


    if d = 8 and q = 2 then
        if not HasElementsMultipleOf(recognise.orders, [5,9,17]) then
            return TemporaryFailure;
        fi;
    elif d = 6 and q = 2 then
        if not HasElementsMultipleOf(recognise.orders, [5,7,9]) then
            return TemporaryFailure;
        fi;
    elif d = 6 and q = 3 then
        if not HasElementsMultipleOf(recognise.orders, [5,7]) then
            return TemporaryFailure;
        fi;
    elif d = 4 and q = 3 then
        if not HasElementsMultipleOf(recognise.orders, [5,9]) then
            return TemporaryFailure;
        fi;
    elif d = 4 and q = 2 then
        if Size(recognise.grp) mod 720 <> 0 then
            Info(InfoRecog_ClassicalNaming,2,"group does not contain Sp(",
                 recognise.d, ", ", recognise.q, ");");
           recognise.isSpContained := false;
           return NeverApplicable;
        fi;
    elif d = 4 and q = 5 then
        if not HasElementsMultipleOf(recognise.orders, [13,15]) then
            return TemporaryFailure;
        fi;
    elif d = 4 and not IsPowerOfTwo(q+1) and not ((q+1) mod 3 = 0 and
                   IsPowerOfTwo((q+1)/3)) and q<>2 then
        if not 4 in recognise.LB then
            return TemporaryFailure;
        fi;
        if not 2 in recognise.LS then
            return TemporaryFailure;
        fi;
    elif d = 4 and RECOG.Sp4SplittingWitnessDivisors(q) <> fail then
        if not 4 in recognise.LB or not recognise.hasSp4Splitting then
            return TemporaryFailure;
        fi;
    else
        Info(InfoRecog_ClassicalNaming,2,
             "NonGenericSymplectic: d and q must have been generic");
        return NeverApplicable;
    fi;

    return CheckFlag();

end);

############################################################################/
##
##  Recognise non-generic unitary matrix groups over finite fields
##
BindRecogMethod("FindHomMethodsClassical", "NonGenericUnitary",
"tests whether group is non-generic Unitary",
function(recognise)
    local grp, d, q, g, f1, f2, o, CheckFlag, isHermForm, order;
    grp := recognise.grp;

    isHermForm := f -> IsSesquilinearForm(f) and IsHermitianForm(f);

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if Length(recognise.ClassicalForms) = 0 then
            recognise.needForms := true;
            return TemporaryFailure;
        fi;
        Info(InfoRecog_ClassicalNaming,2,"The group is not generic and contains SU(",
             recognise.d, ", ", recognise.q, ");");
        recognise.isGeneric := false;
        recognise.isNotExt := true;
        recognise.isSUContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

    if d > 6 then
        return NeverApplicable;
    fi;

    if recognise.isReducible = true then
       return NeverApplicable;
    fi;

    if Length( recognise.ClassicalForms ) > 0 and
       First( recognise.ClassicalForms, isHermForm )=fail then
       return NeverApplicable;
    fi;

    if recognise.maybeFrobenius = false then
        return NeverApplicable;
    fi;

    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        if d = 6 or d = 4 then
            recognise.needLB := true;
            recognise.needE2 := true;
        fi;
        if d = 4 and q > 9 then
            recognise.needPOrders := true;
        fi;
        if d = 3 then
            recognise.needPOrders := true;
            if q >= 49 then
               recognise.needLB := true;
            fi;
        fi;
        return TemporaryFailure;
    fi;

    if d = 6 and q = 4 then
        if not HasElementsMultipleOf(recognise.orders, [7,10,11]) then
            return TemporaryFailure;
        fi;
    elif d = 6 and q >= 9 then
        if not 3 in recognise.E2 then
            return TemporaryFailure;
        fi;
        if not 5 in recognise.LB then
            return TemporaryFailure;
        fi;
    elif d = 5 and q = 4 then
        if not HasElementsMultipleOf(recognise.orders, [11,12]) then
            return TemporaryFailure;
        fi;
    elif d = 4 and q = 4 then
        #TO DO : check this is same in Magma
        if not HasElementsMultipleOf(recognise.orders, [5,9]) then
            return TemporaryFailure;
        fi;
    elif d = 4 and q = 9 then
        if not HasElementsMultipleOf(recognise.orders, [5,7,9]) then
            return TemporaryFailure;
        fi;
    elif d = 4 and q > 9 then

        if not 3 in recognise.LB then
            return TemporaryFailure;
        fi;

        if not 2 in recognise.E2 then
            return TemporaryFailure;
        fi;

        # ACN 27 Nov 2019 reworked this section.
        # Let r be the ppd of q^3-1 and s that of q^2-1
        # either max{r,s} >= 11 and G contains omega
        # or {r,s} = {5,7} and then we have to rule out 2.A7.

        # check of o is divisible by a prime >= 11; projective orders,
        # since a scalar can bring any prime dividing q-1
        f1 := o -> PositionProperty(Factors(o[1]), i-> i >= 11) <> fail;
        if PositionProperty(recognise.porders, f1) <> fail then
            return CheckFlag();
        fi;

        # Now we know that projective orders only contain primes at most 7
        if not q^3 mod 7 = 1 or q^2 mod 7 = 1 or q mod 7 = 1 then
            # 7 is not ppd of q^3-1
            return CheckFlag();
        fi;
        # Now we know 7 is ppd of q^3 -1
        if not q^2 mod 5 = 1 or q mod 5 = 1 then
            # 5 is not ppd of q^2-1
            return CheckFlag();
        fi;
        if ForAny( recognise.orders, i ->
        (i mod 7 = 0 and     # order divisible by 7
         i <> 7 and          # but not equal to 7
         q^3 mod i = 1 and   # order divides q^3-1
        (7*(q-1)) mod i <> 0 # order does not divide 7*(q-1)
         )) then
            return CheckFlag();
        fi;
        return TemporaryFailure;
    elif d = 3 and q = 4 then
        # Take the natural action of grp, and compute its order
        if Order(grp) mod 216 = 0 then
            return CheckFlag();
        else
            recognise.isSUContained := false;
            return NeverApplicable;
        fi;
    elif d = 3 and q = 9 then
        if not HasElementsMultipleOf(recognise.orders, [7]) then
            return TemporaryFailure;
        fi;
        if recognise.hasSpecialEle = false then
            order := Order( recognise.g );
            if not order mod 6 = 0 then
                return TemporaryFailure;
            fi;
            if not IsCentral(grp, recognise.g ^ (order / 2)) then
                Info( InfoRecog_ClassicalNaming,2,
                      "Found an element of order divisible by 6 such",
                      " that the corresponding involution is not central." );
                recognise.hasSpecialEle := true;
                return CheckFlag();
            else
                return TemporaryFailure;
            fi;
        else
            return CheckFlag();
        fi;
    elif d = 3 and q = 16 then
        if not HasElementsMultipleOf(recognise.orders, [5,13]) then
            return TemporaryFailure;
        fi;
        if recognise.hasSpecialEle = false then
            order := Order( recognise.g );
            if not order mod 5 = 0 then
                return TemporaryFailure;
            fi;
            if not IsCentral(grp, recognise.g ^ (order / 5)) then
                Info( InfoRecog_ClassicalNaming,2,
                      "The element of order equal 5 is not central" );
                recognise.hasSpecialEle := true;
                return CheckFlag();
            else
                return TemporaryFailure;
            fi;
        else
            return CheckFlag();
        fi;
    elif d = 3 and q = 25 then
        if not HasElementsMultipleOf(recognise.orders, [5,7,8]) then
            return TemporaryFailure;
        fi;
        if recognise.hasSpecialEle = false then
            order := Order(recognise.g);
            if order mod 8 <> 0 then
                return TemporaryFailure;
            fi;
            if not IsCentral(grp, recognise.g ^ (order / 2)) then
                Info( InfoRecog_ClassicalNaming,2,
                      "Found an element of order divisible by 8 which powers",
                      " to a non-central involution." );
                recognise.hasSpecialEle := true;
                return CheckFlag();
            else
                return TemporaryFailure;
            fi;
        else
            return CheckFlag();
        fi;
    elif d = 3 and q >= 49 then
        if not 3 in recognise.LE or not 3 in recognise.BE then
           return TemporaryFailure;
        fi;
        if not recognise.ppd[1] = 3 or not recognise.ppd[2]=true
           or not recognise.ppd[3]=true then
            return TemporaryFailure;
        fi;
        if recognise.hasSpecialEle = false then
             Info(InfoRecog_ClassicalNaming,2,
                  "Searching for elements of order > 3 mod scalars",
                  " and dividing ", String(q-1));
             if not ForAny(recognise.porders, i -> i[1] > 3 and q mod i[1] = 1) then
                 return TemporaryFailure;
             fi;
             recognise.hasSpecialEle := true;
             return CheckFlag();
         else
             return CheckFlag();
         fi;
    else
        Info(InfoRecog_ClassicalNaming,2,
            "NonGenericUnitary: d and q must have been be generic");
        return NeverApplicable;
    fi;


    return CheckFlag();
end);

BindRecogMethod("FindHomMethodsClassical", "NonGenericOrthogonalPlus",
"tests whether group is non-generic O+",
function(recognise)
    local grp, d, q, gp1, gp2, CheckFlag, pgrp, sc, isHypForm, ol, ord;
    grp := recognise.grp;

    isHypForm := f -> IsSesquilinearForm(f) and IsHyperbolicForm(f);

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if Length(recognise.ClassicalForms) = 0 then
            recognise.needForms := true;
            return TemporaryFailure;
        fi;
        Info(InfoRecog_ClassicalNaming,2,"The group is not generic and contains SO+(",
             recognise.d, ", ", recognise.q, ");");
        recognise.isGeneric := false;
        recognise.isNotExt := true;
        recognise.isOmegaContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

    if not d in [4,6,8,10] then
        return NeverApplicable;
    fi;
    if d = 10 and q <> 2 then
        return NeverApplicable;
    fi;

    if recognise.isReducible = true then
       return NeverApplicable;
    fi;

    if (Length( recognise.ClassicalForms ) > 0 and
       First(recognise.ClassicalForms, isHypForm)=fail) and
       (not IsQuadraticForm(recognise.QuadraticForm) or not
       recognise.QuadraticFormType = "orthogonalplus") then
       return NeverApplicable;
    fi;

    if d = 6 or d = 8 then
       recognise.needE2 := true;
       recognise.needLB := true;
    fi;

    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return TemporaryFailure;
    fi;

    if d = 10 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [17,31]) then
            return TemporaryFailure;
        fi;
    elif d = 8 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [7,9,10]) and
           not HasElementsMultipleOf( recognise.orders, [7,9,15]) then
            return TemporaryFailure;
        fi;

        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );

        # Both the conformal orthogonal and the omega for d = 8 and q = 2 have
        # orbits of these lengths. The maximal subgroups of the conformal
        # orthogonal don't have these orbit lengths.
        if SortedList(OrbitLengthsDomain(pgrp)) <> [ 120, 135 ] then
           recognise.isOmegaContained := false;
           return NeverApplicable;
        fi;
        StabChain(pgrp, rec(random := 200, limit := 174182400));
        if Size(pgrp) mod 174182400 = 0 then # compare to Size(POmega(+1,8,2))
           return CheckFlag();
        else
           recognise.isOmegaContained := false;
           return NeverApplicable;
         fi;
    elif d = 8 and (q = 3 or q = 5) then
        # For q = 5, the 13 in [NP99, Table 4] stands for a splitting
        # lppd(8,5;4)-element (proportion 1/81, see the proof). Elements of
        # order 13 also lie in Spin(7,5) and in the maximal subgroups of
        # types GU(4,5) and 2.Sz(8); the latter have no elements of order 31.
        if q = 3 and not HasElementsMultipleOf(recognise.orders, [7, 13]) then
            return TemporaryFailure;
        elif q = 5 and
             not HasElementsMultipleOf(recognise.orders, [3, 7, 13, 31]) then
            return TemporaryFailure;
        fi;

        # The maximal subgroups of Omega+(8,q) of order divisible by 7*13
        # (q = 3) or 7*13*31 (q = 5) are two classes of <-1> x Omega(7,q),
        # fixing a non-singular point, and their triality images, four
        # classes of Spin(7,q) in its spin representation [Kle87, Table I].
        # A proper subgroup of Omega(7,q) of such order lies in G2(3) and
        # fixes a unique point. So an irreducible G not containing
        # Omega+(8,q) normalises Spin(7,q), hence fixes its Cayley 4-form up
        # to scalars, while Omega+(8,q) fixes no line of 4-forms. This test
        # replaces the permutation representation of [NP99].
        #
        # If the MeatAxe or the forms are still missing, CheckFlag asks
        # for them.
        if recognise.isReducible = false and
           not IsEmpty(recognise.ClassicalForms) and
           RECOG.FixesFourFormLine(GeneratorsOfGroup(grp),
               First(recognise.ClassicalForms, isHypForm)!.matrix) then
            recognise.isOmegaContained := false;
            return NeverApplicable;
        fi;
        return CheckFlag();
    elif d = 8 and (q = 4 or q > 5) then
        if not 6 in recognise.LB then
            return TemporaryFailure;
        fi;
        if not 4 in recognise.LS then
            return TemporaryFailure;
        fi;
    # For each q we have that OmegaPlus(6,q) is isomorphic to PSL(4,q).
    elif d = 6 and q = 2 then
        # Additionally, OmegaPlus(6,2) is isomorphic to AlternatingGroup(8).
        # Its only maximal subgroup of order divisible by 7*15 is A7, which
        # has no elements of order 15 [NP99, Theorem 5.3].
        if not HasElementsMultipleOf( recognise.orders, [7, 15]) then
            return TemporaryFailure;
        fi;
    elif d = 6 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5, 13]) then
            return TemporaryFailure;
        fi;
    elif d = 6 and q >= 4 then
        if not 4 in recognise.LB then
            return TemporaryFailure;
        fi;
        if not 3 in recognise.E2 then
            return TemporaryFailure;
        fi;
    elif d = 4 and (q = 8 or q >= 11) then
        if recognise.needPlusMinus = false then
            recognise.needPlusMinus := true;
            return NotEnoughInformation;
        fi;
        if not IsSubset(recognise.factorWitnesses, [["distinct"], ["minus", 1],
                ["minus", 2], ["plus", 1], ["plus", 2]]) then
            return TemporaryFailure;
        fi;
    elif d = 4 and q = 2 then
        if Size(grp) mod 36 <> 0 then
            recognise.isOmegaContained := false;
            return NeverApplicable;
        fi;
        if recognise.needDecompose = false then
           recognise.needDecompose := true;
           return TemporaryFailure;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoRecog_ClassicalNaming,2,"Group projects to group of order ",
             Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars));
        if Size(gp1/recognise.scalars) mod 6 = 0 and
           Size(gp2/recognise.scalars) mod 6 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q = 3 then
        if Size(grp) mod 288 <> 0 then
            recognise.isOmegaContained := false;
            return NeverApplicable;
        fi;
        if recognise.needDecompose = false then
           recognise.needDecompose := true;
           return TemporaryFailure;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoRecog_ClassicalNaming,2,"Group projects to group of order ",
             Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars));
        if Size(gp1/recognise.scalars) mod 12 = 0 and
           Size(gp2/recognise.scalars) mod 12 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q = 4 then
        # the conformal group can have orbits of length 75 and 180
        # the group Omega can have orbits of lengths 75 and 60
        ol := Length(Orbit(grp, IdentityMat(d, GF(q))[1]));
        if not ol in [60,75,180] then
            return NeverApplicable;
        fi;

        # HACK to avoid warnings 'Giving up, Schreier tree is not shallow'
        # (in general one shouldn't ignore this kind of warning but here
        # we know which groups are input, and it is acceptable)
        ol := InfoLevel(InfoOrb);
        SetInfoLevel(InfoOrb, 0);
        ord := RECOG.EstimateProjOrder(grp);
        SetInfoLevel(InfoOrb, ol);

        if ord mod 3600 <> 0 then
            recognise.isOmegaContained := false;
             return NeverApplicable;
        fi;
        if recognise.needDecompose = false then
           recognise.needDecompose := true;
           return TemporaryFailure;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoRecog_ClassicalNaming,2,"Group projects to group of order ",
             Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars));
        if Size(gp1/recognise.scalars) mod 3 = 0 and
           Size(gp2/recognise.scalars) mod 3 = 0 then
            return CheckFlag();
        fi;
    elif d = 4 and q = 5 then
        ## Added fast test 4.7.2019 ACN
        # the conformal group can have orbits of length 144 and 480
        # the group Omega can have orbits of lengths 144 and 120
        ol := Length(Orbit(grp, IdentityMat(d, GF(q))[1]));
        if not ol mod 144 = 0 and not ol mod 120 = 0 then
           return NeverApplicable;
        fi;

        ## The projective Group has half order of Omega
        ## Fix 4.7.2019
        if RECOG.EstimateProjOrder(grp) mod 3600 <> 0 then
            recognise.isOmegaContained := false;
            return NeverApplicable;
        else
            return CheckFlag();
        fi;
    elif d = 4 and q = 7 then
        ## Added fast test 4.7.2019 ACN
        # the conformal group can have orbits of length 384 and 2016
        # the group Omega can have orbits of lengths 384 and 336
        ol := Length(Orbit(grp, IdentityMat(d, GF(q))[1]));
        if not ol mod 384 = 0 and not ol mod 336 = 0 then
            return NeverApplicable;
        fi;

        if RECOG.EstimateProjOrder(grp) mod 28224 <> 0 then
            recognise.isOmegaContained := false;
            return NeverApplicable;
        fi;
        if recognise.needDecompose = false then
           recognise.needDecompose := true;
           return TemporaryFailure;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoRecog_ClassicalNaming,2,"Group projects to group of order ",
             Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars));
        if Size(gp1/recognise.scalars) mod 168 = 0 and
           Size(gp2/recognise.scalars) mod 168 = 0 then
            return CheckFlag();
        fi;
    elif d = 4 and q = 9 then
        ## Added fast test 4.7.2019 ACN
        # the conformal group can have orbits of length 800 and 5760
        # the group Omega can have orbits of lengths 800 and 720
        ol := Length(Orbit(grp, IdentityMat(d, GF(q))[1]));
        if not ol mod 800 = 0 and not ol mod 720 = 0 then
            return NeverApplicable;
        fi;

        if RECOG.EstimateProjOrder(grp) mod 129600 <> 0 then
            recognise.isOmegaContained := false;
            return NeverApplicable;
        else
            return CheckFlag();
        fi;
    else
        Info(InfoRecog_ClassicalNaming, 2,
             "NonGenericO+: d and q must have been be generic");
        return NeverApplicable;
    fi;

     return CheckFlag();

end);

BindRecogMethod("FindHomMethodsClassical", "NonGenericOrthogonalMinus",
"tests whether group is non-generic O-",
function(recognise)
    local grp, d, q, pgrp, h, g, ppd, CheckFlag, isEllForm;
    grp := recognise.grp;

    isEllForm := f -> IsSesquilinearForm(f) and IsEllipticForm(f);

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if Length(recognise.ClassicalForms) = 0 then
            recognise.needForms := true;
            return TemporaryFailure;
        fi;
        Info(InfoRecog_ClassicalNaming,2,"The group is not generic and contains SO-(",
             recognise.d, ", ", recognise.q, ");");
        recognise.isGeneric := false;
        recognise.isNotExt := true;
        recognise.isOmegaContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

    if not d in [4,6,8] then
        return NeverApplicable;
    fi;
    if d = 8 and q <> 2 then
        return NeverApplicable;
    fi;
    if d = 6 and q > 3 then
        return NeverApplicable;
    fi;

    if recognise.isReducible = true then
       return NeverApplicable;
    fi;

    if (Length(recognise.ClassicalForms) > 0 and
       First(recognise.ClassicalForms,isEllForm)=fail) and
       (not IsQuadraticForm(recognise.QuadraticForm) or not
       recognise.QuadraticFormType = "orthogonalminus") then
       return NeverApplicable;
    fi;

    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return TemporaryFailure;
    fi;


    if d = 8 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [9,17] ) then
            return TemporaryFailure;
        fi;
    elif d = 6 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5,7,9] ) then
            return TemporaryFailure;
        fi;
    elif d = 6 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [5,9] ) then
            return TemporaryFailure;
        fi;
    elif d = 4 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [3,5] ) then
            return TemporaryFailure;
        fi;
    elif d = 4 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [3,5] ) then
            return TemporaryFailure;
        fi;
        pgrp := ProjectiveActionOnFullSpace( grp, GF(3), 4 );
        if Length(OrbitLengthsDomain(pgrp)) > 3 then # ACN 10/6/08
            recognise.isOmegaContained := false;
            return NeverApplicable;
         fi;
    elif d = 4 and q >= 4 then
        ppd := IsPpdElement( recognise.field, recognise.cpol, d, q, 1 );
        if ppd = false or ppd[1] <> 4 or ppd[2] <> true then
            return TemporaryFailure;
        fi;
        # found a ppd( 4, q; 4)-element
        g := recognise.g;
        for h in GeneratorsOfGroup(grp) do
# ACN May 2007
            if Comm(h,g) <> One(grp) then
                if Comm(Comm(h,g),g) <> One(grp) then
                    return CheckFlag();
                fi;
            fi;
        od;
        Info(InfoRecog_ClassicalNaming, 2, "grp contained in O-(2,", q, "^2)" );
        recognise.isNotExt := false;
        recognise.isOmegaContained := false;
        return NeverApplicable;
    else
      Info(InfoRecog_ClassicalNaming, 2, "NonGenericO-: d and q must be generic" );
        return NeverApplicable;
    fi;

     return CheckFlag();

end);

BindRecogMethod("FindHomMethodsClassical", "NonGenericOrthogonalCircle",
"tests whether group is non-generic Oo",
function(recognise)
    local d, q, g, s, CheckFlag, isParForm;

    isParForm := f -> IsSesquilinearForm(f) and IsParabolicForm(f);

    if not IsOddInt(recognise.d) then
        return NeverApplicable;
    fi;
    if not IsOddInt(recognise.q) then
        return NeverApplicable;
    fi;

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if Length(recognise.ClassicalForms) = 0 then
            recognise.needForms := true;
            return TemporaryFailure;
        fi;
        Info(InfoRecog_ClassicalNaming,2,"The group is not generic and contains Omega(",
             recognise.d, ", ", recognise.q, ");");
        recognise.isGeneric := false;
        recognise.isNotExt := true;
        recognise.isOmegaContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

    if recognise.isReducible = true then
       return NeverApplicable;
   fi;

    if (Length( recognise.ClassicalForms ) > 0 and
       First(recognise.ClassicalForms, isParForm)=fail) and
       (not IsQuadraticForm(recognise.QuadraticForm) or not
       recognise.QuadraticFormType = "orthogonalcircle") then
       return NeverApplicable;
    fi;


    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return TemporaryFailure;
    fi;

    if d = 3 then
        recognise.needLB := true;
    fi;


    if d = 7 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5,7,13]) then
            return TemporaryFailure;
        fi;
    elif d = 5 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5,9]) then
            return TemporaryFailure;
        fi;
    elif d = 5 and q >= 5 then
        if not 4 in recognise.LE then
            return TemporaryFailure;
        fi;
    elif d = 3 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [3]) then
            return TemporaryFailure;
        fi;
    elif d = 3 and q = 5 then
        if not HasElementsMultipleOf( recognise.orders, [3,5]) then
            return TemporaryFailure;
        fi;
    elif d = 3 and q = 7 then
        if not HasElementsMultipleOf( recognise.orders, [4,7]) then
            return TemporaryFailure;
        fi;
    elif d = 3 and q = 9 then
        ## Only the current element can be the special one, so test each
        ## element, not only those after the orders 3 and 5 have appeared.
        ## Projective order: an involution times a scalar of order 4 or 8
        ## has matrix order 4 or 8 and a scalar square
        if recognise.hasSpecialEle = false
           and ProjectiveOrder(recognise.g)[1] in [4,8] then
            g := recognise.g^2;
            if ForAll(GeneratorsOfGroup(recognise.grp), h -> IsOne(Comm(h,g))) then
                recognise.isOmegaContained := false;
                return NeverApplicable;
            fi;
            recognise.hasSpecialEle := true;
        fi;
        if recognise.hasSpecialEle = false
           or not HasElementsMultipleOf( recognise.orders, [3,5]) then
            return TemporaryFailure;
        fi;
    elif d = 3 and q = 11 then
        if not HasElementsMultipleOf( recognise.orders, [3,11]) then
            return TemporaryFailure;
        fi;
    elif d = 3 and q = 19 then
        if not HasElementsMultipleOf( recognise.orders, [5,9,19]) then
            return TemporaryFailure;
        fi;
    elif d = 3 and q >=31 and IsPowerOfTwo(q+1) then
        s := Log2Int(q+1);
        if not ForAny(recognise.orders, i -> i > 2 and (q-1) mod i = 0) then
            return TemporaryFailure;
        fi;
        if not ForAny(recognise.orders, i -> i mod 2^(s-1) = 0) then
            return TemporaryFailure;
        fi;
    elif d = 3 and q>11 and ((q+1) mod 3=0 and
        IsPowerOfTwo((q+1)/3)) then
        s := Log2Int((q+1)/3);
        if not ForAny(recognise.orders, i -> i mod (3*2^(s-1)) = 0) then
            return TemporaryFailure;
        fi;
        if not ForAny(recognise.orders, i -> i > 2 and (q-1) mod i = 0) then
            return TemporaryFailure;
        fi;
    elif d = 3 and ((q+1) mod 3 <> 0 or not IsPowerOfTwo((q+1)/3)) and
                   not IsPowerOfTwo(q+1) then
        if not 2 in recognise.LB then
            return TemporaryFailure;
        fi;
        ## Projective orders: A5 with scalars has elements of order 10
        recognise.needPOrders := true;
        if not ForAny(recognise.porders,
                      i -> i[1] > 2 and (q-1) mod i[1] = 0) then
            return TemporaryFailure;
        fi;
        ## need to check that the basic lppd( 3,q;2) elements have order
        ## greater than 5.
        s := LogInt(q, recognise.p);
        if not ForAny(recognise.porders,
                      i -> HasLBGgt5(i[1], recognise.p, s, 2)) then
            return TemporaryFailure;
        fi;
    else
        Info(InfoRecog_ClassicalNaming, 2, "NonGenericOo: d and q must be generic" );
        return NeverApplicable;
    fi;


    return CheckFlag();

end);

#############################################################################
##
##  Dimension 2.
##
##  The generic machinery above is driven by ppd elements, and at d = 2 every
##  ppd exponent equals 2, so it can conclude nothing.  The methods below form
##  ClassicalMethDbForDegree2 instead: they rule out the subgroups of GL(2,q)
##  that do not contain SL(2,q), class by class, and whatever survives
##  contains it.  This is the algorithm of [NP92, Section 8].
##
#############################################################################

# Largest q for which IsSL2Contained enumerates the q+1 points of the
# projective line to prove that a group lies over a proper subfield
RECOG.Degree2LineEnumerationLimit := 2^12;

BindRecogMethod("FindHomMethodsClassical", "TestRandomElementCase2",
"makes new random element and stores it and its projective order",
function(recognise)
    local g, porder;

    recognise.g := PseudoRandom(recognise.grp);
    recognise.n := recognise.n + 1;
    g := recognise.g;

    # IsSubgroupOfGammaL and IsImprimitive both need an h with h^2 outside the
    # centre
    if recognise.h = fail then
        porder := ProjectiveOrder(g);
        AddSet(recognise.porders, porder);
        if porder[1] > 2 then
            recognise.h := g;
            recognise.hasExp2 := false;
        fi;
    fi;

    return TemporaryFailure;
end);

BindRecogMethod("FindHomMethodsClassical", "Degree2SmallField",
"decides a degree-2 group over GF(2) or GF(3) by direct computation",
function(recognise)
    local q;

    q := recognise.q;
    if q > 3 then
        return NeverApplicable;
    fi;

    # PSL(2,2) = Sym(3) = GammaL(1,4) and PSL(2,3) = Alt(4): here the classes
    # the methods below rule out coincide with the group we are looking for.
    # |GL(2,3)| = 48, so just decide it.
    if IsSubset(recognise.grp, SL(2, q)) then
        recognise.isSLContained := true;
        recognise.isSpContained := true;
        Info(InfoRecog_ClassicalNaming, 2,
             "The group contains SL(2, ", q, ");");
    else
        recognise.isSLContained := false;
        Info(InfoRecog_ClassicalNaming, 2,
             "The group does not contain SL(2, ", q, ");");
    fi;
    return Success;
end);

BindRecogMethod("FindHomMethodsClassical", "IsAbelian",
"tests whether a degree-2 group is abelian",
function(recognise)
    if IsAbelian(recognise.grp) then
        recognise.isAbelian := true;
        recognise.isSLContained := false;
        Info(InfoRecog_ClassicalNaming, 2,
             "The group is abelian and thus does not contain SL(2, ",
             recognise.q, ");");
        return Success;
    fi;

    recognise.isAbelian := false;
    return NeverApplicable;
end);

BindRecogMethod("FindHomMethodsClassical", "ExponentTwoModScalars",
"tests whether a degree-2 group modulo scalars has exponent 2",
function(recognise)
    local gen, porder, pair;

    if recognise.hasExp2 <> "unknown" then
        return NeverApplicable;
    fi;

    # random elements have had their chance by now; fall back on the generators
    if recognise.n <= 15 then
        return TemporaryFailure;
    fi;

    for gen in recognise.generators do
        porder := ProjectiveOrder(gen);
        if porder[1] > 2 then
            recognise.h := gen;
            recognise.hasExp2 := false;
            return NeverApplicable;
        fi;
    od;

    # G/Z of exponent 2 is abelian, so the generators must also commute modulo
    # scalars; if a and b do not, then (ab)^2 is not scalar
    for pair in Combinations(recognise.generators, 2) do
        if not RECOG.IsScalarMat(Comm(pair[1], pair[2])) then
            recognise.h := pair[1] * pair[2];
            recognise.hasExp2 := false;
            return NeverApplicable;
        fi;
    od;

    # G/Z is generated by commuting involutions
    recognise.hasExp2 := true;
    recognise.isSLContained := false;
    Info(InfoRecog_ClassicalNaming, 2,
         "The group modulo scalars has exponent 2 and thus does not contain ",
         "SL(2, ", recognise.q, ");");
    return Success;
end);

BindRecogMethod("FindHomMethodsClassical", "IsSubgroupOfGammaL",
"tests whether a degree-2 group lies in GammaL(1,q^2)",
function(recognise)
    local h, q, gen, x, x2;

    if recognise.h = fail then
        return TemporaryFailure;
    fi;

    h := recognise.h;
    q := recognise.q;
    x := h^2;

    # in GammaL(1,q^2) every square lies in a Singer torus, so the non-scalar
    # x would be irreducible over GF(q) (not just over the field generated by
    # the coefficients)
    if not IsIrreducibleRingElement(PolynomialRing(recognise.field),
                                    CharacteristicPolynomial(x)) then
        recognise.isSubgroupOfGammaL := false;
        return NeverApplicable;
    fi;

    # the centraliser of the irreducible x is a Singer torus, which G
    # normalises iff every x^gen commutes with x [NP92, Lemma 7.1]
    for gen in recognise.generators do
        x2 := x^gen;
        if x2 * x <> x * x2 then
            recognise.isSubgroupOfGammaL := false;
            return NeverApplicable;
        fi;
    od;

    recognise.isSubgroupOfGammaL := true;
    recognise.isSLContained := false;
    Info(InfoRecog_ClassicalNaming, 2,
         "The group is conjugate to a subgroup of GammaL(1, ", q^2,
         ") and thus does not contain SL(2, ", q, ");");
    return Success;
end);

BindRecogMethod("FindHomMethodsClassical", "IsImprimitive",
"tests whether a degree-2 group preserves a pair of 1-spaces",
function(recognise)
    local h, gen, genNew, eigenvectors;

    if recognise.h = fail then
        return TemporaryFailure;
    fi;

    h := recognise.h;
    eigenvectors := Eigenvectors(recognise.field, h^2);

    # fewer than two eigenspaces leaves nothing to permute
    if Length(eigenvectors) <> 2 then
        recognise.isImprimitive := false;
        return NeverApplicable;
    fi;

    # the rows are left eigenvectors, so conjugating by their inverse
    # diagonalises h^2
    for gen in recognise.generators do
        genNew := eigenvectors * gen * eigenvectors^-1;
        if not IsMonomialMatrix(genNew) then
            recognise.isImprimitive := false;
            return NeverApplicable;
        fi;
    od;

    recognise.isImprimitive := true;
    recognise.isSLContained := false;
    Info(InfoRecog_ClassicalNaming, 2,
         "The group is imprimitive and thus does not contain SL(2, ",
         recognise.q, ");");
    return Success;
end);

BindRecogMethod("FindHomMethodsClassical", "IsAlt5Alt4Sym4",
"tests whether a degree-2 group modulo scalars is Alt(4), Sym(4) or Alt(5)",
function(recognise)
    local pts, i, gen, v, pgrp, q;

    q := recognise.q;

    # Spin one point of the projective line [NP92, Section 8]. Reducible and
    # imprimitive groups are ruled out, so the orbit has at least 3 points,
    # and only the identity of PGL(2,q) fixes 3 points, so G/Z acts
    # faithfully on it. An orbit of more than |Alt(5)| = 60 points rules out
    # all three. A list suffices for 61 points, and orb's hash function is
    # slow for fields with more than 2^16 elements.
    pts := [One(recognise.generators[1])[1]];
    i := 1;
    while i <= Length(pts) do
        for gen in recognise.generators do
            v := OnLines(pts[i], gen);
            if not v in pts then
                Add(pts, v);
                if Length(pts) > 60 then
                    recognise.isAlt5Alt4Sym4 := false;
                    return NeverApplicable;
                fi;
            fi;
        od;
        i := i + 1;
    od;
    pgrp := Group(List(recognise.generators,
               g -> PermList(List(pts, p -> Position(pts, OnLines(p, g))))));

    # the exceptions are the q where Alt(4), Sym(4), Alt(5) do contain SL(2,q)
    # modulo scalars: SL(2,3) and GL(2,3) for q = 3, SL(2,4) = Alt(5) for
    # q = 4, SL(2,5) for q = 5
    if (Size(pgrp) = 12 and q <> 3) or
       (Size(pgrp) = 24 and q <> 3) or
       (Size(pgrp) = 60 and q <> 4 and q <> 5) then
        if IsAlternatingGroup(pgrp) or IsSymmetricGroup(pgrp) then
            recognise.isAlt5Alt4Sym4 := true;
            recognise.isSLContained := false;
            Info(InfoRecog_ClassicalNaming, 2,
                 "The group modulo scalars is Alt(4), Sym(4) or Alt(5) ",
                 "and thus does not contain SL(2, ", q, ");");
            return Success;
        fi;
    fi;

    recognise.isAlt5Alt4Sym4 := false;
    return NeverApplicable;
end);

BindRecogMethod("FindHomMethodsClassical", "IsSL2Contained",
"tests whether a degree-2 group contains SL",
function(recognise)
    local e, IsWitness, o;

    if recognise.isReducible = true then
        return NeverApplicable;
    fi;

    if recognise.isReducible <> false or
       recognise.isAbelian <> false or
       recognise.hasExp2 <> false or
       recognise.isSubgroupOfGammaL <> false or
       recognise.isImprimitive <> false or
       recognise.isAlt5Alt4Sym4 <> false then
        return TemporaryFailure;
    fi;

    # every other class is ruled out, so G either contains SL(2,q) or lies in
    # GL(2,r).Z for a proper subfield GF(r) [NP92, Proposition 8.1]. As
    # tr(g)^2/det(g) is invariant under conjugation and scalars, it lies in
    # GF(r) on GL(2,r).Z, so an element on which it generates GF(q) proves the
    # former.
    e := DegreeOverPrimeField(recognise.field);
    IsWitness := g -> DegreeFFE(TraceMat(g)^2 / DeterminantMat(g)) = e;
    if not (ForAny(recognise.generators, IsWitness) or
            IsWitness(recognise.g)) then
        if recognise.q > RECOG.Degree2LineEnumerationLimit then
            return TemporaryFailure;
        fi;

        # GL(2,r).Z preserves the r+1 points of a subline, while SL(2,q) is
        # transitive on all q+1 points of the projective line
        o := Orb(recognise.generators, One(recognise.generators[1])[1],
                 OnLines);
        Enumerate(o);
        if Length(o) < recognise.q + 1 then
            recognise.isRepresentableOverSubfield := true;
            recognise.isSLContained := false;
            Info(InfoRecog_ClassicalNaming, 2,
                 "The group is representable over a proper subfield and ",
                 "thus does not contain SL(2, ", recognise.q, ");");
            return Success;
        fi;
    fi;

    recognise.isRepresentableOverSubfield := false;
    # Sp(2,q) = SL(2,q)
    recognise.isSLContained := true;
    recognise.isSpContained := true;
    Info(InfoRecog_ClassicalNaming, 2,
         "The group contains SL(2, ", recognise.q, ");");
    return Success;
end);


########

# 100 Test Random
#
#  50 - 99 Conclusions
#
#  10 - 49 Termination Conditions
#
# 1 - 10 Workers

AddMethod(ClassicalMethDb, FindHomMethodsClassical.TestRandomElement, 100);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsGenericParameters, 90);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsGeneric, 89);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsReducible, 80);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.RuledOutExtField, 81);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsNotMathieu, 82);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsNotAlternating, 83);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsNotPSL, 84);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NoClassicalForms, 85);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.MeatAxe, 9);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.ClassicalForms, 8);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericLinear, 10);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericUnitary, 11);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericSymplectic, 12);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericOrthogonalPlus, 13);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericOrthogonalMinus, 14);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericOrthogonalCircle, 15);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsSLContained, 16);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsSpContained, 17);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsSUContained, 18);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.isOmegaContained, 19);


# the classes of subgroups of GL(2,q) in the order they are ruled out
AddMethod(ClassicalMethDbForDegree2, FindHomMethodsClassical.TestRandomElementCase2, 100);
AddMethod(ClassicalMethDbForDegree2, FindHomMethodsClassical.Degree2SmallField, 90);
AddMethod(ClassicalMethDbForDegree2, FindHomMethodsClassical.MeatAxe, 80);
AddMethod(ClassicalMethDbForDegree2, FindHomMethodsClassical.IsAbelian, 70);
AddMethod(ClassicalMethDbForDegree2, FindHomMethodsClassical.ExponentTwoModScalars, 60);
AddMethod(ClassicalMethDbForDegree2, FindHomMethodsClassical.IsSubgroupOfGammaL, 50);
AddMethod(ClassicalMethDbForDegree2, FindHomMethodsClassical.IsImprimitive, 40);
AddMethod(ClassicalMethDbForDegree2, FindHomMethodsClassical.IsAlt5Alt4Sym4, 30);
AddMethod(ClassicalMethDbForDegree2, FindHomMethodsClassical.IsSL2Contained, 20);


# For q = 2^s-1 >= 7 and q = 3*2^s-1 >= 11, q+1 has no large ppd, and
# NonGenericSymplectic needs a witness that Sp(4,q) is not in an extension
# field subgroup; returns the divisors in its definition, or fail
RECOG.Sp4SplittingWitnessDivisors := function(q)
    if q >= 7 and IsPowerOfTwo(q+1) then
        return [4];
    elif q >= 11 and (q+1) mod 3 = 0 and IsPowerOfTwo((q+1)/3) then
        return [3, 4];
    fi;
    return fail;
end;

# Whether an element of Sp(4,q) with characteristic polynomial cpol splits V
# into two non-isomorphic irreducible 2-dimensional modules, on which it acts
# by elements l1, l2 of the norm 1 group of GF(q^2), of orders divisible by
# a number in RECOG.Sp4SplittingWitnessDivisors(q), with l2^2 <> l1^(+-2).
#
# [NP99, Proposition 4.4(a)] covers SL(2,q^2) only; elements of Sp(2,q^2):2
# outside it split V like this too. The condition on squares rules out all
# of (Sp(2,q^2):2) Z, also with similitudes of GF(q^2)-type. If g is
# GF(q^2)-linear, det g = l1 l2^(+-1) lies in GF(q) and has norm 1, so it is
# +-1 and l2 = +-l1^(+-1). If g is semilinear, g^2 is GF(q^2)-linear with
# eigenvalues l1^(+-2), l2^(+-2) and a square determinant, which is not -1
# as q = 3 mod 4, so l2^2 = l1^(+-2).
RECOG.IsSp4SplittingWitness := function(cpol, q)
    local divs, facs, l;
    divs := RECOG.Sp4SplittingWitnessDivisors(q);
    facs := Factors(PolynomialRing(GF(q)), cpol);
    if List(facs, Degree) <> [2, 2] then
        return false;
    fi;
    l := List(facs, f -> RootsOfPolynomial(GF(q^2), f)[1]);
    if not ForAll(l, x -> (q+1) mod Order(x) = 0 and
                          ForAny(divs, k -> Order(x) mod k = 0)) then
        return false;
    fi;
    return not l[2] in [l[1], l[1]^-1] and not l[2]^2 in [l[1]^2, l[1]^-2];
end;

# Target probability that RecogniseClassical misses a d = 4 witness of
# NonGenericSymplectic or NonGenericOrthogonalPlus, for independent uniform
# random elements; PseudoRandom elements miss somewhat more often
RECOG.Degree4NamingErrorBound := 1/10000;

# Witnesses enter the collection from about this random element on
RECOG.Degree4FirstWitnessElement := 10;

# Whether a Kronecker factor of projective order o, dividing q+1, is the
# (q+1)-type witness of NonGenericOrthogonalPlus for d = 4
RECOG.IsOPlus4PlusWitness := function(o, q, p, a)
    if IsPowerOfTwo(q+1) then
        return o >= (q+1)/2;
    elif q = 8 then
        return o mod 9 = 0;
    fi;
    return ForAny(PrimeDivisors(o), r -> IsPrimitivePrimeDivisor(p, 2*a, r));
end;

# Proportion of the rarest witness that the d = 4 test of NonGenericSymplectic
# ("symplectic") or NonGenericOrthogonalPlus ("orthogonalplus") needs in
# Sp(4,q) or Omega^+(4,q); 0 if that test uses no such witness for this q
RECOG.Degree4WitnessProportion := function(type, q)
    local p, a, R, n, k, thr, Torus;
    p := SmallestRootInt(q);
    a := LogInt(q, p);
    if type = "symplectic" then
        if RECOG.Sp4SplittingWitnessDivisors(q) <> fail then
            # RECOG.IsSp4SplittingWitness: pairs (x, y) of exponents of a
            # generator of C_N in a torus C_N^2, N = q+1, |N(T)| = 8N^2.
            # All but the 2 elements of order 1 or 2 have an order divisible
            # by a number in RECOG.Sp4SplittingWitnessDivisors(q). For each
            # of these N-2 values of x, y avoids x, -x, x+N/2, -x+N/2: four
            # values, two if x has order 4. So (N-2)^2 - 4(N-2) + 2*2 pairs.
            return (q-3)^2 / (8 * (q+1)^2);
        fi;
        if q in [2, 3, 5] or IsPowerOfTwo(q+1) or
           ((q+1) mod 3 = 0 and IsPowerOfTwo((q+1)/3)) then
            return 0;
        fi;
        # Large special ppd(4,q;2)-elements are the regular elements (x, y) of
        # a torus C_{q+1}^2, |N(T)| = 8(q+1)^2, whose parts in the ppd part
        # C_R are nontrivial with y <> x^(+-1), and for 3 | R the part x of
        # the first factor is not of order 3: R-1 choices of x, less the 2 of
        # order 3, and R-3 of y, as R is odd
        R := PrimitivePrimeDivisors(2*a, p).ppds;
        n := R - 1;
        if R mod 3 = 0 then
            n := n - 2;
        fi;
        return n * (R - 3) / (8 * R^2);
    elif type = "orthogonalplus" then
        if q <> 8 and q < 11 then
            return 0;
        fi;
        # Each Kronecker factor is uniform in PSL(2,q), where a torus of
        # order m has a normaliser of order 2m and Phi(o) elements of order o
        Torus := {m, cond} -> Sum(Filtered(DivisorsInt(m), cond), Phi) / (2*m);
        k := Gcd(2, q-1);
        thr := 2 * k;
        return Minimum(
            Torus((q+1)/k, o -> o > thr and RECOG.IsOPlus4PlusWitness(o, q, p, a)),
            Torus((q-1)/k, o -> o > thr));
    fi;
    return 0;
end;

# Number of further random elements that bring the probability of missing a
# witness of a d = 4 test that is still undecided below
# RECOG.Degree4NamingErrorBound; the bound is shared by up to 4 witnesses.
# The symplectic test also needs a large basic ppd(4,q;4)-element, which has
# proportion about 1/4, so a group without one is not Sp(4,q)
RECOG.Degree4ExtraRandomElements := function(recognise, ms, nrrandels)
    local tests, t, pi, N;
    if recognise.d <> 4 then
        return 0;
    fi;
    tests := [rec(type := "symplectic", method := "NonGenericSymplectic",
                  flag := "isSpContained", ready := r -> 4 in r.LB),
              rec(type := "orthogonalplus", method := "NonGenericOrthogonalPlus",
                  flag := "isOmegaContained", ready := r -> true)];
    for t in tests do
        if recognise.(t.flag) <> "unknown" or
           IsBound(ms.inapplicableMethods.(t.method)) or
           not t.ready(recognise) then
            continue;
        fi;
        pi := RECOG.Degree4WitnessProportion(t.type, recognise.q);
        if pi = 0 then
            continue;
        fi;
        N := RECOG.Degree4FirstWitnessElement +
             Int(Log(Float(RECOG.Degree4NamingErrorBound / 4)) /
                 Log(Float(1 - pi))) + 1;
        return Maximum(0, N - nrrandels);
    od;
    return 0;
end;


InstallGlobalFunction( RecogniseClassical,
function( grp, arg... )
  local ret, recognise, opt, f, q, originalInfoLevel, db, defaultBudget, extra;

  f := FieldOfMatrixGroup(grp);
  q := Size(f);

  opt := rec();
  if Length(arg) > 0 and IsRecord(Last(arg)) then
      opt := Remove(arg);
  fi;
  if Length(arg) > 0 then
      ErrorNoReturn( "Usage: RecogniseClassical( grp[,opt] )" );
  fi;

  # set default
  if not IsBound(opt.case) then
      opt.case := "unknown";
  fi;
  defaultBudget := not IsBound(opt.nrrandels);
  if defaultBudget then
      opt.nrrandels := 30;
      if DimensionOfMatrixGroup(grp) = 8 then
          opt.nrrandels := 200;
      elif DimensionOfMatrixGroup(grp) = 4 and q = 8 then
          opt.nrrandels := 300;
      elif DimensionOfMatrixGroup(grp) <= 10 then
          opt.nrrandels := 50;
      fi;
  fi;
  if not IsBound(opt.infoLevel) then
      opt.infoLevel := 0;
  fi;
  if not opt.case in ["linear", "symplectic", "unitary", "orthogonalplus", "orthogonalcircle", "unknown" ] then
      Error("Unknown case ",opt.case);
  fi;

  # init record recognition...
  recognise := rec( field := f,
                   grp := grp,
                   d := DimensionOfMatrixGroup(grp),
                   p := Characteristic(f),
                   a := DegreeOverPrimeField(f),
                   q := q,
                   # n -> recognise.nrRandomElms
                   # LE = e's of large ppd elements
                   # BE = e's of basic ppd elements
                   # LB = e's of large basic ppd elements
                   # E2 = e's of ppd elements for e=d/2
                   E := [], LE := [], BE := [], LB := [],
                   LS := [], E2 := [],
                   g := fail,
                   cpol := fail,
                   isppd := fail,
                   n := 0,
                   module := GModuleByMats(GeneratorsOfGroup(grp),f),
                   currentgcd := DimensionOfMatrixGroup(grp),
                   isReducible := "unknown",
                   isGeneric := "unknown",
                   isNotExt := "unknown",
                   hint := opt.case,
                   hintIsWrong := false,
                   isNotMathieu := "unknown",
                   isNotAlternating := "unknown",
                   isNotPSL := "unknown",
                   possibleNearlySimple := [],
                   dimsReducible := [],
                   orders := [],
                   porders := [],
                   hasSpecialEle := false,
                   needSp4Splitting := false,
                   hasSp4Splitting := false,
                   bc := "unknown",
                   kroneckerFactors := "unknown",
                   factorWitnesses := [],
                   sq1 := [Z(q)*One(GL(2,q))],
                   sq2 := [Z(q)*One(GL(2,q))],
                   scalars := Group(Z(q)*One(GL(2,q))),
                   needMeataxe := false,
                   needForms := true, # changed 29.10.09
                   needOrders := false,
                   needPOrders := false,
                   needBaseChange := false,
                   needKroneckerFactors := false,
                   needPlusMinus := false,
                   needDecompose := false,
                   needLB := false,
                   needE2 := false,
                   maybeDual := true,
                   maybeFrobenius := (DegreeOverPrimeField(f) mod 2=0),
                   ClassicalForms := [],
                   QuadraticForm := false,
                   QuadraticFormType := "unknown",
                   isSLContained := "unknown",
                   isSpContained := "unknown",
                   isSUContained := "unknown",
                   isOmegaContained := "unknown",
                   # only used by ClassicalMethDbForDegree2
                   generators := GeneratorsOfGroup(grp),
                   h := fail,          # element with projective order > 2
                   isAbelian := "unknown",
                   hasExp2 := "unknown",
                   isSubgroupOfGammaL := "unknown",
                   isImprimitive := "unknown",
                   isAlt5Alt4Sym4 := "unknown",
                   isRepresentableOverSubfield := "unknown",
                  );
  if recognise.d = 2 then
      # at d = 2 the MeatAxe is cheap, while the characteristic polynomials
      # of a group over a subfield of index 2 all split
      recognise.needMeataxe := true;
      db := ClassicalMethDbForDegree2;
  else
      db := ClassicalMethDb;
  fi;

  originalInfoLevel := InfoLevel(InfoRecog_MethSel);
  SetInfoLevel(InfoRecog_MethSel,opt.infoLevel);
  ret := CallMethods( db, opt.nrrandels, recognise );

  # A second round for d = 4 tests whose witnesses are rare, without the
  # methods found inapplicable
  if defaultBudget and ret.result <> Success then
      extra := RECOG.Degree4ExtraRandomElements(recognise, ret, opt.nrrandels);
      if extra > 0 then
          db := Filtered(db,
                    m -> not IsBound(ret.inapplicableMethods.(Stamp(m.method))));
          ret := CallMethods( db, extra, recognise );
      fi;
  fi;
  SetInfoLevel(InfoRecog_MethSel,originalInfoLevel);
  # TODO: honor ret in some way?

  return recognise;
end);

# The following function pretty prints the output of RecogniseClassical.
# This can be helpful when debugging it.
InstallGlobalFunction( DisplayRecog, function( r )

    local q0;

           Print("Reducible : ", r.isReducible, "\n" );
           Print("Forms: " );
           if Length(r.ClassicalForms) = 0 then
              Print("no form preserved\n"); # TODO is this correct?
           elif Length(r.ClassicalForms)> 1 then
              Print("Several Forms preserved\n");
           elif IsTrivialForm( r.ClassicalForms[1] ) then
              Print("linear i.e. no forms\n");
           elif IsQuadraticForm(r.QuadraticForm) then
              Print("quadratic form of type: ", r.QuadraticFormType, "\n");
           elif IsSymplecticForm(r.ClassicalForms[1]) then
              Print("symplectic\n");
           elif IsHermitianForm( r.ClassicalForms[1] ) then
              Print("unitary\n");
           elif IsEllipticForm( r.ClassicalForms[1] ) then
              Print("orthogonal minus\n");
           elif IsParabolicForm( r.ClassicalForms[1] ) then
              Print("orthogonal circle\n");
           elif IsHyperbolicForm( r.ClassicalForms[1] ) then
              Print("orthogonal plus\n");
           fi;
           if Length(r.E) > 0 then
               Print("E : ", r.E, "\n" );
           fi;
           if Length(r.LE) > 0 then
               Print("LE : ", r.LE, "\n" );
           fi;
           if Length(r.BE) > 0 then
               Print("BE : ", r.BE, "\n" );
           fi;
           if Length(r.LS) > 0 then
               Print("LS : ", r.LS, "\n" );
           fi;
           if Length(r.LB) > 0 then
               Print("LB : ", r.LB, "\n" );
           fi;
           if Length(r.E2) > 0 then
               Print("E2 : ", r.E2, "\n" );
           fi;
           if r.isNotMathieu <> "unknown" then
               Print( "Mathieu ruled out: ", r.isNotMathieu, "\n");
           fi;
           if r.isNotAlternating <> "unknown" then
               Print( "An ruled out: ", r.isNotAlternating, "\n");
           fi;
           if r.isNotPSL <> "unknown" then
               Print( "PSL ruled out: ", r.isNotPSL, "\n");
           fi;
#           if Length(r.dimsReducible) > 0 then
#               Print( "dimsred ", r.dimsReducible, "\n");
#           fi;

           if Length(r.orders) > 0 then
               Print( "orders ", r.orders, "\n");
           fi;
           if Length(r.porders) > 0 then
               Print( "porders ", r.porders, "\n");
           fi;

            if r.isSLContained = true then
                Print("--------> contains SL(", r.d, ",", r.q, ")\n");
            fi;

            if r.isSpContained = true then
                Print("--------> contains Sp(", r.d, ",", r.q, ")\n");
            fi;


            if r.isSUContained = true then
                q0 := Characteristic(r.field)^(DegreeOverPrimeField(r.field)/2);
                Print("--------> contains SU(", r.d, ",", q0, ")\n");
            fi;

            if r.isOmegaContained = true then
                Print("--------> contains SO(", r.d, ",", r.q, ")\n");
            fi;

            if r.isReducible = true then
                Print("--------> reducible + not classical \n");
            fi;

end );
