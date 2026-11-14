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
##  Standard bases and standard generators of classical groups, as in
##  [EHNPR] (see GoingDown.gi), Section 'Standard generators and stingray
##  embeddings'. A standard basis is ordered
##  (e_1, f_1, e_2, f_2, ..., e_m, f_m), with hyperbolic pairs (e_i, f_i).
##
#############################################################################

# The matrix which acts as <M> on the basis vectors with indices <idx> and
# fixes the other basis vectors of GF(q)^<d>
RECOG.EmbedBlock := function(d, f, idx, M)
  local g;
  g := IdentityMat(d, f);
  g{idx}{idx} := M * One(f);
  return g;
end;

# The signed cycle (x_1, ..., x_k)^sign on the basis vectors with indices
# <idx>: x_i -> x_(i+1) for i < k and x_k -> <sign> * x_1
RECOG.SignedCycle := function(d, f, idx, sign)
  local g, k, i;
  k := Length(idx);
  g := IdentityMat(d, f);
  for i in idx do
    g[i] := ZeroMutable(g[i]);
  od;
  for i in [1 .. k - 1] do
    g[idx[i], idx[i + 1]] := One(f);
  od;
  g[idx[k], idx[1]] := sign * One(f);
  ConvertToMatrixRep(g, f);
  return g;
end;

# The standard generators of CL(<d>, q) of type <type> relative to the
# standard basis of GF(q)^<d>, q = Size(<f>), with gamma = Z(q) ([EHNPR],
# Definition of standard generators). For SL, they are those of
# Leedham-Green and O'Brien, J. Algebra 322 (2009), Section 3, Table 1,
# except u and y, which are the identity there.
# Returns a record with the following components:
#  - `s`, `t`, `delta`: [[0,1],[-1,0]], [[1,1],[0,1]] and
#    diag(gamma, gamma^-1) on (e_1, f_1)
#  - `x`: for "SL" and d even, the signed cycle
#    (e_1, f_1, e_2, f_2)^-; the identity if it does not fit
#  - `v`: (e_1, ..., e_m)(f_1, ..., f_m); for "SL" and d odd, the map
#    v_1 -> v_d, v_i -> -v_(i-1)
#  - `all`: the list of these, in the order of
#    RECOG.ClassicalStandardGeneratorNames
RECOG.ClassicalStandardGenerators := function(type, d, f)
  local gamma, m, odd, e, res, i;

  if type <> "SL" then
    ErrorNoReturn("RECOG.ClassicalStandardGenerators: unsupported type ",
                  type);
  fi;

  gamma := Z(Size(f));
  m := QuoInt(d, 2);
  odd := [1, 3 .. 2 * m - 1];
  e := [2, 4 .. 2 * m];

  res := rec(
    s := RECOG.EmbedBlock(d, f, [1, 2], [[0, 1], [-1, 0]]),
    t := RECOG.EmbedBlock(d, f, [1, 2], [[1, 1], [0, 1]]),
    delta := RECOG.EmbedBlock(d, f, [1, 2], [[gamma, 0], [0, gamma^-1]]),
  );

  if IsEvenInt(d) then
    if d >= 4 then
      res.x := RECOG.SignedCycle(d, f, [1 .. 4], -1);
    else
      res.x := IdentityMat(d, f);
    fi;
    res.v := RECOG.SignedCycle(d, f, odd, 1) * RECOG.SignedCycle(d, f, e, 1);
  else
    # v_1 -> v_d and v_i -> -v_(i-1) for i >= 2
    res.v := NullMat(d, d, f);
    res.v[1, d] := One(f);
    for i in [2 .. d] do
      res.v[i, i - 1] := -One(f);
    od;
    res.x := IdentityMat(d, f);
  fi;

  res.all := List(RECOG.ClassicalStandardGeneratorNames(type), x -> res.(x));
  for i in [1 .. Length(res.all)] do
    ConvertToMatrixRep(res.all[i], f);
  od;
  return res;
end;

# The names of the standard generators of type <type>, in the order of
# the component `all` of RECOG.ClassicalStandardGenerators
RECOG.ClassicalStandardGeneratorNames := function(type)
  if type = "SL" then
    return ["s", "t", "delta", "v", "x"];
  fi;
  ErrorNoReturn("RECOG.ClassicalStandardGeneratorNames: unsupported type ",
                type);
end;
