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
##  FinalDescent for symplectic groups, and constructive recognition of
##  Sp(4,q), q odd, in its natural representation. The latter adapts the
##  algorithm CRecogniseSp4 of [Bro08] (doc/recog.bib), Section 4.
##
#############################################################################

# The basis e1, f1, e2, f2 of eigenvectors of the involution <j> <> -1 in
# Sp(4,q), with e1, f1 in the fixed space E1 of <j> and e2, f2 in that of
# -<j>, scaled so that (e1,f1) = (e2,f2) for the alternating form with Gram
# matrix <F>. As E1 and E2 are orthogonal, it is a standard basis of a
# scalar multiple of the form.
RECOG.Sp4_EigenspaceBasis := function(j, F)
  local E1, E2;

  E1 := RECOG.FixspaceMat(j);
  E2 := RECOG.FixspaceMat(-j);
  return [E1[1], E1[2], E2[1],
          E2[2] * (E1[1] * F * E1[2]) / (E2[1] * F * E2[2])];
end;

# K1 = Sp(E1) for the fixed space E1 of the involution <j> in Sp(4,q),
# spanned by the first two rows of the basis <B> of RECOG.Sp4_EigenspaceBasis.
# K1 is the factor L1 of [Bro08], Sections 4.1 and 4.2.
# <pr> is a product replacer of a group with memory which contains <j>.
# Returns a function which maps the matrix, relative to <B>, of an element of
# K1 to that element, with memory.
RECOG.Sp4_InvolutionFactor := function(pr, j, B, f)
  local Bi, OnE, k1, c, k, sl2, k1std, fake;

  Bi := B^-1;
  # the block of <g> relative to B on E1 (<idx> = [1,2]) or E2 ([3,4])
  OnE := {g, idx} -> ImmutableMatrix(f, (B * StripMemory(g) * Bi){idx}{idx});

  # For c = (A1, A2) in the centraliser Sp(E1) x Sp(E2) of j, c^|A2| lies
  # in K1. For small q, c^|A2| is often central, as |A1| divides |A2|; K1
  # is normal in the centraliser, so the conjugate by c of an element found
  # before is used instead.
  k1 := [];
  repeat
    c := RECOG.CentralisingElementOfInvolution(pr,
             g -> Order(StripMemory(g)), j);
    k := c^Order(OnE(c, [3, 4]));
    if RECOG.IsScalarMat(OnE(k, [1, 2])) then
      if k1 = [] then
        continue;
      fi;
      k := Last(k1)^c;
    fi;
    Add(k1, k);
  until Length(k1) >= 2 and
        RECOG.IsThisSL2Natural(List(k1, g -> OnE(g, [1, 2])), f);

  sl2 := RECOG.RecogniseSL2Natural(
             Group(GeneratorsWithMemory(List(k1, g -> OnE(g, [1, 2])))), f);
  k1std := ResultOfStraightLineProgram(SLPOfElms(sl2.all), k1);
  fake := RECOG.InitSLfake(f, 2);
  return xb -> ResultOfStraightLineProgram(
                   RECOG.ExpressInStd_SL2(
                       sl2.bas * xb{[1, 2]}{[1, 2]} * sl2.basi, fake),
                   k1std);
end;

# The unipotent radical Q(b) of the stabiliser of the point <b> in Sp(4,q),
# for b = b_pos, <pos> in [1, 2], of the basis b1, b2, b3, b4 = <B> of
# RECOG.Sp4_EigenspaceBasis for the involution <j> of the group <h> with
# memory. <InK1> is the function returned by RECOG.Sp4_InvolutionFactor.
#
# Q(b) acts trivially on b^perp/<b>. Its centre is the root group
# T = {v -> v + c*(v,b)*b} of K1, and u in Q(b) maps v in E2 = <b3,b4> to
# v + lam(v)*b, which identifies Q(b)/T with the dual of E2.
# For a random g with (b,bg) <> 0, T and T^g generate Sp(<b,bg>), which
# contains n^2 = -1 on <b,bg> and 1 on its complement, for a Weyl element
# n. Modulo Q(b), j and n^2 are central in the stabiliser of <b>, so
# [n^2,j] is in Q(b), and outside T unless <b,bg> = E1. Such elements and
# their conjugates by the torus of K1 span Q(b)/T over GF(p). This
# replaces ConstructQ of [Bro08], Section 4.2 (see RECOG.FindStdGensSp4).
# Returns a function which maps the matrix, relative to <B>, of an element of
# Q(b) to that element, with memory.
RECOG.Sp4_UnipotentRadical := function(h, j, B, InK1, pos, f)
  local Bi, InB, ext, partner, Lam, Transvection, t1, z, U, vecs, g, kappa,
        u, l, i, inv;

  Bi := B^-1;
  InB := g -> B * StripMemory(g) * Bi;
  ext := DegreeOverPrimeField(f);
  partner := 3 - pos;
  Lam := xb -> Concatenation(List([3, 4],
                 r -> Coefficients(CanonicalBasis(f), xb[r, pos])));
  # the element of T which adds <c> * b to b_partner
  Transvection := function(c)
    local m;
    m := IdentityMat(4, f);
    m[partner, pos] := c;
    return InK1(m);
  end;
  t1 := Transvection(One(f));
  # conjugation by z multiplies lam by Z(q) or its inverse
  z := InK1(DiagonalMat([Z(Size(f)), Z(Size(f))^-1, One(f), One(f)]));

  U := [];
  vecs := [];
  while Length(U) < 2 * ext do
    # t1^g is a transvection with centre bg, and t1^g * Transvection(c) * t1^g
    # is a Weyl element of Sp(<b,bg>) for c = 1/kappa^2, kappa = +-(b,bg)
    g := PseudoRandom(h);
    kappa := InB(g)[pos, partner];
    if IsZero(kappa) then
      continue;
    fi;
    u := Comm((t1^g * Transvection(1 / kappa^2) * t1^g)^2, j);
    for i in [1 .. ext] do
      l := Lam(InB(u));
      if RankMat(Concatenation(vecs, [l])) > Length(vecs) then
        Add(vecs, l);
        Add(U, u);
      fi;
      u := u^z;
    od;
  od;

  inv := vecs^-1;
  return function(xb)
    local y;
    y := Product(ListN(U, IntVecFFE(Lam(xb) * inv), \^));
    return y * InK1(InB(y)^-1 * xb);
  end;
end;

# Constructive recognition of Sp(4,q), q odd, in its natural
# representation.
#
# As q is odd, an involution j <> -1 is diagonalisable with eigenvalues 1
# and -1. Its eigenspaces E1, E2 are orthogonal, hence non-degenerate and
# of even dimension, so both have dimension 2. The centraliser of j
# contains K1 = Sp(E1) = SL(2,q), which RECOG.RecogniseSL2Natural
# recognises. Relative to a standard basis
# e1, f1, e2, f2 of eigenvectors of j, the standard generators s, t, delta
# lie in K1, and x lies in the unipotent radical Q(e1) of the stabiliser of
# the point <e1>. The elements of Q(e1) and Q(f1) are written by linear
# algebra modulo their centres, root groups of K1. On the totally isotropic
# planes <e1,f2> and <e2,f1>, x and an element y of Q(f1) act as opposite
# root elements, so x*y*x maps E1 to E2; it yields u.
#
# The plan is that of [Bro08], Sections 4.1 to 4.3: the centraliser of j
# by Bray's method (J. N. Bray, Arch. Math. 74 (2000)), its SL(2,q)
# factor L1 = K1, and Q(b) for b in E1, with centre T. It deviates in
# three steps:
#  - [Bro08] splits the derived group of the centraliser into L1 and
#    L2 = Sp(E2) and recognises both. Here only K1 is built: [Bro08]
#    needs L2 for Q(b) = <T, u0^L2> (Section 4.3), which the next step
#    replaces.
#  - [Bro08] takes u0 = [h, h1] for a torus element h of <T, T^g>, found
#    by recognising <T, T^g> as SL(2,q), and h1 that of L1. Here [n^2, j]
#    for a Weyl element n written down from transvections, and its
#    conjugates by the torus of K1, span Q(b)/T (see
#    RECOG.Sp4_UnipotentRadical). No success probability is proven for
#    this step; the rank checks keep the result correct, so only the
#    running time is at stake.
#  - [Bro08] returns the generating set (18) of its Section 4.4. Here the
#    standard generators of [EHNPR] (see ../GoingDown.gi) are written from
#    K1, Q(e1) and Q(f1).
#
# <gens> must be 4x4 matrices over <f> generating Sp(4,q), q = Size(<f>)
# odd.
# Returns either fail, or else a record with the following components:
#  - `slp`: SLP in <gens> whose i-th result is bas^-1 * std[i] * bas for
#    std = RECOG.ClassicalStandardGenerators("Sp", 4, <f>).all
#  - `bas`: a 4x4 matrix whose rows are a standard basis (e1,f1,e2,f2) of a
#    scalar multiple of the alternating form which <gens> preserve
RECOG.FindStdGensSp4 := function(gens, f)
  local h, pr, j, B, InK1, InQe1, InQf1, std, y, x, w, s, u, res;

  if NrRows(gens[1]) <> 4 then
    ErrorNoReturn("RECOG.FindStdGensSp4: <gens> must be 4x4 matrices");
  fi;
  if IsEvenInt(Size(f)) then
    ErrorNoReturn("RECOG.FindStdGensSp4: <f> must have odd order");
  fi;

  gens := StripMemory(gens);
  h := GroupWithMemory(gens);
  pr := ProductReplacer(GeneratorsOfGroup(h));
  # more than half of the involutions found are -1
  repeat
    j := RECOG.InvolutionSearcher(pr, g -> Order(StripMemory(g)), 30);
  until j = fail or not IsOne(-StripMemory(j));
  if j = fail then
    return fail;
  fi;

  B := RECOG.Sp4_EigenspaceBasis(StripMemory(j),
           MTX.InvariantBilinearForm(GModuleByMats(gens, f)));
  ConvertToMatrixRep(B, f);
  InK1 := RECOG.Sp4_InvolutionFactor(pr, j, B, f);
  InQe1 := RECOG.Sp4_UnipotentRadical(h, j, B, InK1, 1, f);
  InQf1 := RECOG.Sp4_UnipotentRadical(h, j, B, InK1, 2, f);

  # y in Q(f1) maps e1 to e1 - f2 and e2 to e2 - f1. On both <e1,f2> and
  # <e2,f1>, x and y act as [[1,0],[1,1]] and [[1,-1],[0,1]], so w = xyx
  # acts as [[0,-1],[1,0]] on them. Hence u = w * s * s^w, where s^w is s
  # on E2.
  std := RECOG.ClassicalStandardGenerators("Sp", 4, f);
  y := IdentityMat(4, f);
  y[1, 4] := -One(f);
  y[3, 2] := -One(f);
  x := InQe1(std.x);
  w := x * InQf1(y) * x;
  s := InK1(std.s);
  u := w * s * s^w;

  res := [s, InK1(std.t), InK1(std.delta), u, x, u];
  Assert(1, List(res, g -> B * StripMemory(g) * B^-1) = std.all);
  return rec( slp := SLPOfElms(res), bas := B );
end;

# Sp(n,3), n <= 8, is small enough for constructive membership via a
# stabiliser chain
RECOG.Sp_FinalDescentByBSGS := function(gens, f)
  local n, form, B, std;

  n := NrRows(gens[1]);

  # B maps the form of <gens> to the standard form, whose restriction to
  # the first four basis vectors is that of Sp(4,q)
  form := MTX.InvariantBilinearForm(GModuleByMats(gens, f));
  B := BaseChangeToCanonical(BilinearFormByMatrix(
           RECOG.ClassicalStandardForm("Sp", n, f), f))^-1
       * BaseChangeToCanonical(BilinearFormByMatrix(form, f));
  ConvertToMatrixRep(B, f);

  std := List(RECOG.ClassicalStandardGenerators("Sp", 4, f).all,
              x -> B^-1 * DirectSumMat(x, IdentityMat(n-4, f)) * B);
  return rec( slp := RECOG.FindStdGensUsingBSGS(Group(gens), std, false, false),
              bas := B );
end;

# FinalDescent of [EHNPR] ('Terminal groups and initial groups', 'The
# final descent') for Sp, q odd: <gens> generate Sp(n,q),
# n in [4, 6, 8], q = Size(<f>).
# Returns a record with the following components:
#  - `slp`: SLP in <gens> for the standard generators of an Sp(4,q)
#  - `bas`: an nxn matrix whose first four rows are a standard basis
#    (e1,f1,e2,f2), for a scalar multiple of the form, of the space on
#    which this Sp(4,q) acts and whose other rows span its fixed space;
#    relative to bas the standard generators are those of
#    RECOG.ClassicalStandardGenerators("Sp",4,<f>), extended by the
#    identity on the other rows
# For q > 3 and n > 4 this is one more GoingDownStep, with bodies of
# dimension 2, followed by RECOG.FindStdGensSp4. Over GF(3) there are no
# stingray elements with bodies of dimension 2 to be found by powering:
# such a body carries an element of order 4, and the exponent B is even.
# [EHNPR] leaves the final descent open, with [LGO09] as a reference
# solution, and excludes bodies of dimension 2 from GoingDown, as the
# generation results it relies on need degree > 8 ('Algorithm
# GoingDownStep'); no success probability is proven for this step.
# [EHNPR] leaves n = 4, 6 to other algorithms ('Small degrees').
RECOG.Sp_FinalDescent := function(gens, f)
  local n, q, params, step, res;

  n := NrRows(gens[1]);
  if not n in [4, 6, 8] then
    ErrorNoReturn("RECOG.Sp_FinalDescent: <gens> must be nxn matrices, ",
                  "n in [4, 6, 8]");
  fi;

  q := Size(f);
  if q = 3 then
    Info(InfoRecog_ClassicalNatural,1,"Sp_n: base case Sp(",n,",3)");
    return RECOG.Sp_FinalDescentByBSGS(gens, f);
  fi;

  Info(InfoRecog_ClassicalNatural,1,"Sp_n: base case Sp(4,",q,")");
  if n = 4 then
    step := rec( gens := gens, slp := fail, basis := IdentityMat(4, f) );
  else
    params := ShallowCopy(RECOG.GoingDownParameters("Sp", q));
    params.minBody := 2;
    repeat
      step := RECOG.GoingDownStep(GroupWithMemory(gens), params,
                                  RECOG.GoingDownRandomBound);
    until step <> fail;
  fi;
  repeat
    res := RECOG.FindStdGensSp4(step.gens, f);
  until res <> fail;

  if step.slp <> fail then
    res.slp := CompositionOfStraightLinePrograms(res.slp, step.slp);
  fi;
  return rec( slp := res.slp,
              bas := Concatenation(res.bas * step.basis{[1..4]},
                                   step.basis{[5..n]}) );
end;
