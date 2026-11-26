#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Horn.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  The orthogonal groups in Sp(6,q) and Sp(8,q), q even, from which
##  RECOG.FindStdGens_SpEven (see main.gi) starts the GoingUp of
##  RECOG.Sp_EvenGoingUp (see GoingUp.gi).
##
#############################################################################

# Omega^+(6,q) in Sp(6,q), q >= 4 even, by the pair of RECOG.Omega_FinalDescent:
# a 4-stingray element s and an element j of odd order whose support D is
# a non-degenerate plane, with W = im(s-1) meeting D trivially, so that
# W + D = V. The quadratic forms with polar form beta which s preserves
# form a coset of {beta(-, c)^2 : c in Fix(s)}, and those of j one of
# {beta(-, c)^2 : c in Fix(j)}; as Fix(s) + Fix(j) = (W meet D)^perp = V,
# exactly one form Q is common to both. If it has type + and the Klein
# lifts of s and j generate SL(4,q), then <s, j> = Omega(V, Q). For q = 2
# no such pair generates Omega^+(6,2) (see RECOG.Omega_FinalDescent).
# <gens> generate Sp(6,q), and <form> is their alternating form, as a form
# record. Returns a record with components `slp`, for the standard
# generators of Omega^+(6,q) relative to `bas`, a standard basis of Q.
RECOG.Sp_EvenOmega6 := function(gens, f, form)
  local h, ord, pr, N, r, j, s, jm, quad, form6, base;

  h := GroupWithMemory(gens);
  ord := g -> Order(StripMemory(g));
  pr := ProductReplacer(GeneratorsOfGroup(h));
  repeat
    N := RECOG.GoingDownRandomBound;
    r := RECOG.FindStingrayElement(h, [4], N);
    j := fail;
    while r <> fail and j = fail and N > 0 do
      N := N - 1;
      j := RECOG.Omega_PlanePower(Next(pr), ord);
    od;
    if j = fail then
      continue;
    fi;
    s := r.element;
    jm := StripMemory(j);
    if RankMat(Concatenation(SemiEchelonMat(s - One(s)).vectors,
                             SemiEchelonMat(jm - One(jm)).vectors)) < 6 then
      continue;
    fi;
    quad := RECOG.InvariantQuadraticForm([s, jm], form.gram, f);
    if quad = fail then
      continue;
    fi;
    form6 := rec( gram := form.gram, frob := 1, field := f, quad := quad );
    if RECOG.FormOrthogonalType(form6, IdentityMat(6, f)) = "O+"
       and RECOG.GeneratesOmega6([s, jm], form6, f) <> fail then
      base := RECOG.FindStdGensOmega6([s, jm], form6, f);
      return rec( slp := CompositionOfStraightLinePrograms(base.slp,
                             RECOG.StingraySLP([r], [j])),
                  bas := base.bas );
    fi;
  until false;
end;

# Omega^+-(8,q) in Sp(8,q), q even, with generators with memory <G>: two
# 4-stingray elements whose bodies meet trivially span V and preserve
# exactly one common quadratic form, as in RECOG.Sp_EvenOmega6. Returns a
# record like that of RECOG.GoingDown, or fail after <N> random
# selections.
RECOG.Sp_EvenDuo8 := function(G, f, N)
  local r1, r2, s1, s2;

  while N > 0 do
    r1 := RECOG.FindStingrayElement(G, [4], N);
    if r1 = fail then
      return fail;
    fi;
    r2 := RECOG.FindStingrayElement(G, [4], r1.remaining);
    if r2 = fail then
      return fail;
    fi;
    N := r2.remaining;
    s1 := r1.element;
    s2 := r2.element;
    if RankMat(Concatenation(SemiEchelonMat(s1 - One(s1)).vectors,
                             SemiEchelonMat(s2 - One(s2)).vectors)) = 8 then
      return rec( gens := [s1, s2],
                  slp := RECOG.StingraySLP([r1, r2], []),
                  bas := IdentityMat(8, f) );
    fi;
  od;
  return fail;
end;
