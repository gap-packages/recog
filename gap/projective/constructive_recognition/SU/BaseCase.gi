#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Horn, Daniel Rademacher.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Recognition of SU(4,q) and FinalDescent for special unitary groups,
##  q odd. The recognition of SU(4,q) adapts the algorithm CRecogniseSp4 of
##  [Bro08] (doc/recog.bib), Section 4. [DR] is D. Rademacher,
##  "Constructive recognition of finite classical groups with stingray
##  elements", PhD thesis, RWTH Aachen University (2024).
##
#############################################################################

# Constructive recognition of SU(4,q), q odd, in its natural representation.
#
# The plan is that of [Bro08], Sections 4.1 to 4.3, for Sp(4,q), as in
# RECOG.FindStdGensSp4: the centraliser of an involution j <> -1 by Bray's
# method (J. N. Bray, Arch. Math. 74 (2000)), its factor K1 = SU(E1),
# which is SL(2,q), and Q(b) for b in E1, the unipotent radical of the
# stabiliser of <b>, whose centre is a root group T of K1 and whose
# elements are written by linear algebra in Q(b)/T. Here E1, E2 are the
# eigenspaces of j, non-degenerate planes. For a hyperbolic pair b1, b4 of
# E1 and b2, b3 of E2, each standard generator lies in K1, in Q(b1) or in
# Q(b4), or is a product of such elements. It deviates in three steps:
#  - [Bro08] recognises both factors of the centraliser. Here only K1 is
#    recognised: [Bro08] needs L2 = SU(E2) for Q(b) = <T, u0^L2> (Section
#    4.3), which the next step replaces.
#  - [Bro08] takes u0 = [h, h1] for a torus element h of <T, T^g>, found
#    by recognising <T, T^g> as SL(2,q), and h1 that of K1. Here [n^2, j]
#    for a Weyl element n written down from T and T^g, and its conjugates
#    by the torus of K1, span Q(b)/T (see MakeQ). No success probability
#    is proven for this step; the rank checks keep the result correct, so
#    only the running time is at stake.
#  - [Bro08] returns the generating set (18) of its Section 4.4. Here the
#    standard generators of [EHNPR] (see ../GoingDown.gi) are written from
#    K1, Q(b1) and Q(b4).
#
# Brooksbank's algorithm for SU(4,q) in its natural representation (J.
# Symbolic Comput. 35 (2003), Section 6.4) builds the same Q(b), but finds
# the SL(2,q) from ppd elements and Q(b) from two SU(3,q) subgroups. It
# assumes q >= 16, and recog has no SU(3,q) recognition.
#
# <gens> must generate SU(4,q) as matrices over <f> = GF(q^2).
# Returns a record with the following components:
#  - `slp`: SLP in <gens> whose i-th result is bas^-1 * std[i] * bas for
#    std = RECOG.ClassicalStandardGenerators("SU", 4, <f>).all
#  - `bas`: a 4x4 matrix whose rows are a standard basis (e1,f1,e2,f2) of a
#    scalar multiple of the hermitian form which <gens> preserve
RECOG.FindStdGensSU4 := function(gens, f)
  local q, ext, e, w, alpha, fq, form, h, ord, pr, j, B, Bi, InB, D, Di,
        OnE1, k1, k1mats, c, k, sl2, k1std, fake, InK1, cb, MakeQ, Q1, Q4,
        Elm, Upper, Lower, std, OnB, v, y, res;

  q := RootInt(Size(f), 2);
  ext := DegreeOverPrimeField(f);
  e := ext / 2;
  w := PrimitiveRoot(f);
  alpha := w^((q+1)/2);   # alpha^q = -alpha
  fq := GF(q);
  form := RECOG.ClassicalInvariantForm("SU", gens, f);
  h := GroupWithMemory(gens);
  ord := m -> Order(StripMemory(m));
  pr := ProductReplacer(GeneratorsOfGroup(h));

  repeat
    j := RECOG.InvolutionSearcher(pr, ord, 100);
  until j <> fail and not IsOne(-StripMemory(j));

  # the basis b1, b2, b3, b4 has the antidiagonal Gram matrix of SU(4,q)
  # in GAP; (v,b_i) is the entry 5-i of v on it
  B := RECOG.FormHyperbolicPair(form, RECOG.FixspaceMat(-StripMemory(j)));
  B := Concatenation([B[1]], RECOG.FormHyperbolicPair(form,
                         RECOG.FixspaceMat(StripMemory(j))), [B[2]]);
  ConvertToMatrixRep(B, f);
  Bi := B^-1;
  InB := g -> B * StripMemory(g) * Bi;

  # K1 consists of the matrices over GF(q) on the basis b1, alpha*b4 of E1.
  # For an element c = (A1, A2) of the centraliser of j, c^|A2| is in K1.
  # For small q it is often central, as |A1| divides |A2|; K1 is normal in
  # the centraliser, so a conjugate by c of an element found before is used
  # instead.
  D := DiagonalMat([One(f), alpha]);
  Di := D^-1;
  OnE1 := xb -> ImmutableMatrix(fq, D * xb{[1,4]}{[1,4]} * Di);
  k1 := [];
  k1mats := [];
  repeat
    c := RECOG.CentralisingElementOfInvolution(pr, ord, j);
    k := c^Order(InB(c){[2,3]}{[2,3]});
    if RECOG.IsScalarMat(OnE1(InB(k))) then
      if k1 = [] then
        continue;
      fi;
      k := k1[Length(k1)]^c;
    fi;
    Add(k1, k);
    Add(k1mats, OnE1(InB(k)));
  until Length(k1) >= 2 and RECOG.IsThisSL2Natural(k1mats, fq);
  sl2 := RECOG.RecogniseSL2Natural(Group(GeneratorsWithMemory(k1mats)), fq);
  k1std := ResultOfStraightLineProgram(SLPOfElms(sl2.all), k1);
  fake := RECOG.InitSLfake(fq, 2);
  # the element of K1 which is xb on the basis b1, ..., b4
  InK1 := xb -> ResultOfStraightLineProgram(
              RECOG.ExpressInStd_SL2(sl2.bas * OnE1(xb) * sl2.basi, fake),
              k1std);

  # Q(b), b = b_pos, acts trivially on b^perp/<b>; its centre is the root group
  # T = {v -> v + t*(v,b)*b} of K1, and u in Q(b) maps v in E2 to
  # v + lam(v)*b, which identifies Q(b)/T with the dual of E2.
  # For a random g, T and T^g generate SU(<b,bg>), which contains n^2 = -1
  # on <b,bg> and 1 on its complement for a Weyl element n. Modulo Q(b), j
  # is central in the stabiliser of <b>, and j acts as -1 on Q(b)/T, so
  # [n^2,j] is in Q(b), and outside T unless <b,bg> = E1.
  cb := CanonicalBasis(f);
  MakeQ := function(pos)
    local pos2, Lam, t1, z, U, vecs, g, gb, kappa, t2, n, u, l, i;

    pos2 := 5 - pos;
    Lam := xb -> Concatenation(Coefficients(cb, xb[2,pos]),
                               Coefficients(cb, xb[3,pos]));
    t1 := IdentityMat(4, f);
    t1[pos2,pos] := alpha;
    t1 := InK1(t1);
    # conjugation by z multiplies lam by Z(q) or its inverse
    z := InK1(DiagonalMat([Z(q), One(f), One(f), Z(q)^-1]));
    U := [];
    vecs := [];
    while Length(U) < 2*ext do
      g := PseudoRandom(h);
      gb := InB(g);
      kappa := gb[pos,pos2];
      if IsZero(kappa) then
        continue;
      fi;

      # on the basis b, bg/kappa of <b,bg>, n = [[0,beta],[-1/beta,0]] for
      # beta = alpha*kappa^(q+1)
      t2 := IdentityMat(4, f);
      t2[pos2,pos] := -1 / (alpha * kappa^(q+1));
      n := g^-1 * t1 * g * InK1(t2) * g^-1 * t1 * g;
      u := Comm(n^2, j);
      for i in [1..e] do
        l := Lam(InB(u));
        if RankMat(Concatenation(vecs, [l])) > Length(vecs) then
          Add(vecs, l);
          Add(U, u);
        fi;
        u := u^z;
      od;
    od;
    return rec( U := U, inv := vecs^-1, Lam := Lam );
  end;
  Q1 := MakeQ(1);
  Q4 := MakeQ(4);

  # the element of Q which is xb on the basis b1, ..., b4
  Elm := function(Q, xb)
    local sol, Y;
    sol := IntVecFFE(Q.Lam(xb) * Q.inv);
    Y := Product([1..Length(Q.U)], i -> Q.U[i]^sol[i]);
    return Y * InK1(InB(Y)^-1 * xb);
  end;

  # root elements of the Levi factor SL(2,q^2) on <b1,b2> + <b3,b4>
  Upper := function(a)
    local m;
    m := IdentityMat(4, f);
    m[1,2] := a;
    m[3,4] := -a^q;
    return Elm(Q4, m);
  end;
  Lower := function(a)
    local m;
    m := IdentityMat(4, f);
    m[2,1] := a;
    m[4,3] := -a^q;
    return Elm(Q1, m);
  end;

  # the standard basis is (b1, b4, b2, b3), and OnB gives the matrix on
  # b1, ..., b4 of a matrix relative to it
  std := RECOG.ClassicalStandardGenerators("SU", 4, f);
  OnB := m -> m{[1, 3, 4, 2]}{[1, 3, 4, 2]};
  # u = v swaps b1, b2 and b3, b4; y is diag(w, 1/w) on <b1,b2>
  v := Upper(One(f)) * Lower(-One(f)) * Upper(One(f))
       * InK1(DiagonalMat([-1, 1, 1, -1] * One(f)));
  y := Upper(w) * Lower(-1/w) * Upper(w)
       * Upper(-One(f)) * Lower(One(f)) * Upper(-One(f));
  res := [InK1(OnB(std.s)), InK1(OnB(std.t)), InK1(OnB(std.delta)), v, v,
          Elm(Q4, OnB(std.x)), y];
  B := B{[1, 4, 2, 3]};
  Assert(1, List(res, g -> B * StripMemory(g) * B^-1) = std.all);
  return rec( slp := SLPOfElms(res), bas := B );
end;

# FinalDescent of [EHNPR] (see ../GoingDown.gi; 'Terminal groups and
# initial groups', 'The final descent') for SU, q0 odd: <gens> are 6x6
# matrices generating SU(6,q0) over <f> = GF(q0^2). The centraliser of an
# involution with eigenspaces of dimension 4 and 2 contains SU(4,q0) on
# the first; elements of it, powered to act trivially on the second,
# generate it.
# [EHNPR] leaves the final descent open, with [LGO09] as a reference
# solution. This follows the route of [DR] which [EHNPR] sketches in that
# section: Algorithm 16 of [DR] (Section 5.1.3, after [LGO09], Sections 8,
# 11 and 12), with the centraliser from Bray's method. Unlike [DR], it
# takes either eigenspace of dimension 4, as -1 is in SU(6,q0), and tests
# pairs of powered elements instead of accumulating them.
# Returns a record with the following components:
#  - `slp`: SLP in <gens> for the standard generators of an SU(4,q0)
#  - `bas`: a 6x6 matrix whose first four rows are a standard basis
#    (e1,f1,e2,f2), for a scalar multiple of the form, of the space on
#    which this SU(4,q0) acts and whose last two span its fixed space;
#    relative to bas the standard generators are those of
#    RECOG.ClassicalStandardGenerators("SU",4,<f>), extended by the
#    identity on the last two rows
RECOG.SU_FinalDescent := function(gens, f)
  local q, q0, h, isNamed, pr, invo, plus, minus, four, two, newbasis,
        cent, x, y, H4, su4;

  if NrRows(gens[1]) <> 6 then
    ErrorNoReturn("RECOG.SU_FinalDescent: <gens> must be 6x6 matrices");
  fi;

  q := Size(f);
  q0 := RootInt(q, 2);
  h := GroupWithMemory(gens);
  isNamed := H -> FieldOfMatrixList(H) = f and
                  RecogniseClassical(Group(H),
                      rec(case := "unitary")).isSUContained = true;

  # As q0 is odd, an involution is diagonalisable with eigenvalues 1 and
  # -1, and its determinant 1 makes the dimension of the (-1)-eigenspace
  # even. So an involution other than -1 has eigenspaces of dimension 4
  # and 2, which are orthogonal.
  Info(InfoRecog_ClassicalNatural,1,"SU_n: base case SU(4,",q0,")");
  pr := ProductReplacer(GeneratorsOfGroup(h));
  repeat
    invo := RECOG.InvolutionSearcher(pr, g -> Order(StripMemory(g)), 100);
  until invo <> fail and not IsOne(-StripMemory(invo));
  plus := RECOG.FixspaceMat(StripMemory(invo));
  minus := RECOG.FixspaceMat(-StripMemory(invo));
  if Length(plus) = 4 then
    four := plus;
    two := minus;
  else
    four := minus;
    two := plus;
  fi;
  newbasis := Concatenation(four, two);
  ConvertToMatrixRep(newbasis, f);

  cent := GroupByGenerators(RECOG.InvolutionCentraliser(pr,
              RECOG.ProjectiveOrder, invo, 8));
  repeat
    x := [PseudoRandom(cent), PseudoRandom(cent)];
    y := List(x, g -> g^Order((newbasis * StripMemory(g) * newbasis^-1){[5,6]}{[5,6]}));
    H4 := List(y, g -> (newbasis * StripMemory(g) * newbasis^-1){[1..4]}{[1..4]});
  until isNamed(H4);

  su4 := RECOG.FindStdGensSU4(H4, f);
  return rec( slp := CompositionOfStraightLinePrograms(su4.slp, SLPOfElms(y)),
              bas := Concatenation(su4.bas * four, two) );
end;
