#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  What a leaf knows about the isomorphism type of its group (LeafData),
##  and the composition factors of a recognition tree derived from it.
##
#############################################################################

RECOG.LeafDataTypes := Immutable(
    [ "soluble", "simple", "quasisimple", "almostsimple", "unknown" ]);

# The sporadic groups among RECOG.SporadicsNames; the entries after them are
# extensions and the Tits group.
BindConstant("RECOG_NrSporadicGroups", 26);

# For the series of exceptional groups with a Weyl group: the number of
# positive roots and the degrees of the Weyl group.
RECOG.ExceptionalGroupDegrees := rec(
    G := [ 6, [ 2, 6 ] ],
    F := [ 24, [ 2, 6, 8, 12 ] ],
    E6 := [ 36, [ 2, 5, 6, 8, 9, 12 ] ],
    E7 := [ 63, [ 2, 6, 8, 10, 12, 14, 18 ] ],
    E8 := [ 120, [ 2, 8, 12, 14, 18, 20, 24, 30 ] ] );

# The order of the simple group with the given series and parameter, see
# LeafData.
RECOG.SimpleGroupOrder := function(series, parameter)
  local d, m, q, pos, degrees, sign, centre;
  if series = "Z" then
      return parameter[1];
  elif series = "A" then
      return Factorial(parameter[1]) / 2;
  elif series = "Spor" then
      pos := Position(RECOG.SporadicsNames, parameter[1]);
      if pos = fail or pos > RECOG_NrSporadicGroups then
          ErrorNoReturn("unknown sporadic group ", parameter[1]);
      fi;
      return RECOG.SporadicsSizes[pos];
  fi;

  q := Last(parameter);
  if series = "Sz" then
      return q^2 * (q^2+1) * (q-1);
  elif series = "2G" then
      return q^3 * (q^3+1) * (q-1);
  elif series = "2F" then
      m := q^12 * (q^6+1) * (q^4-1) * (q^3+1) * (q-1);
      if q = 2 then
          # the Tits group has index 2 in 2F4(2)
          m := m / 2;
      fi;
      return m;
  elif series = "3D" then
      return q^12 * (q^8+q^4+1) * (q^6-1) * (q^2-1);
  fi;

  d := parameter[1];
  if series in [ "G", "F", "E", "2E" ] then
      # 2E6 differs from E6 by the sign of q
      sign := 1;
      centre := 1;
      if series = "2E" then
          sign := -1;
          centre := Gcd(3, q+1);
          degrees := RECOG.ExceptionalGroupDegrees.E6;
      elif series = "E" then
          degrees := RECOG.ExceptionalGroupDegrees.(Concatenation("E", String(d)));
          # 3, 2, 1 for E6, E7, E8
          centre := Gcd(9-d, q-1);
      else
          degrees := RECOG.ExceptionalGroupDegrees.(series);
      fi;
      return q^degrees[1] * Product(degrees[2], i -> q^i - sign^i) / centre;
  fi;

  m := QuoInt(d, 2);
  if series = "L" then
      return q^(d*(d-1)/2) * Product([2..d], i -> q^i - 1) / Gcd(d, q-1);
  elif series = "U" then
      return q^(d*(d-1)/2) * Product([2..d], i -> q^i - (-1)^i) / Gcd(d, q+1);
  elif series in [ "S", "O" ] then
      return q^(m^2) * Product([1..m], i -> q^(2*i) - 1) / Gcd(2, q-1);
  elif series = "O+" then
      return q^(m*(m-1)) * (q^m - 1) * Product([1..m-1], i -> q^(2*i) - 1)
             / Gcd(4, q^m - 1);
  elif series = "O-" then
      return q^(m*(m-1)) * (q^m + 1) * Product([1..m-1], i -> q^(2*i) - 1)
             / Gcd(4, q^m + 1);
  fi;
  ErrorNoReturn("unknown series ", series);
end;

# Replace a classical name by its normal form across the exceptional
# isomorphisms: alternating before linear before symplectic before unitary
# before orthogonal, and the smallest dimension within a series. Returns
# the pair [series, parameter].
RECOG.SimpleGroupNormalForm := function(series, parameter)
  local d, q;
  if not series in [ "L", "U", "S", "O", "O+", "O-" ] then
      return [ series, parameter ];
  fi;
  d := parameter[1];
  q := parameter[2];

  if series = "O" and d = 3 then
      series := "L"; d := 2;
  elif series = "O" and (d = 5 or IsEvenInt(q)) then
      series := "S"; d := d - 1;
  elif series = "O+" and d = 6 then
      series := "L"; d := 4;
  elif series = "O-" and d = 4 then
      series := "L"; d := 2; q := q^2;
  elif series = "O-" and d = 6 then
      series := "U"; d := 4;
  fi;

  if series in [ "U", "S" ] and d = 2 then
      series := "L";
  elif series = "U" and d = 4 and q = 2 then
      series := "S"; q := 3;
  fi;

  if series = "L" then
      if d = 2 and q in [ 4, 5 ] then
          return [ "A", [ 5 ] ];
      elif d = 2 and q = 9 then
          return [ "A", [ 6 ] ];
      elif d = 4 and q = 2 then
          return [ "A", [ 8 ] ];
      elif d = 3 and q = 2 then
          d := 2; q := 7;
      fi;
  fi;
  return [ series, [ d, q ] ];
end;

# Whether series and parameter, in normal form, name a simple group.
RECOG.IsSimpleGroupName := function(series, parameter)
  local d, q;
  if series = "Z" then
      return IsPrimeInt(parameter[1]);
  elif series = "A" then
      return parameter[1] >= 5;
  elif series = "Spor" then
      return Position(RECOG.SporadicsNames, parameter[1])
             in [1..RECOG_NrSporadicGroups];
  fi;
  q := Last(parameter);
  if not IsPrimePowerInt(q) then
      return false;
  fi;
  d := parameter[1];
  if series = "L" then
      return d >= 2 and [ d, q ] <> [ 2, 2 ] and [ d, q ] <> [ 2, 3 ];
  elif series = "U" then
      return d >= 3 and [ d, q ] <> [ 3, 2 ];
  elif series = "S" then
      return IsEvenInt(d) and d >= 4 and [ d, q ] <> [ 4, 2 ];
  elif series = "O" then
      return IsOddInt(d) and d >= 7 and IsOddInt(q);
  elif series in [ "O+", "O-" ] then
      return IsEvenInt(d) and d >= 8;
  elif series = "G" then
      return d = 2 and q > 2;
  elif series = "F" then
      return d = 4;
  elif series = "E" then
      return d in [ 6, 7, 8 ];
  elif series = "2E" then
      return d = 6;
  elif series = "3D" then
      return d = 4;
  elif series in [ "Sz", "2F" ] then
      # the Tits group is 2F with q = 2
      return IsEvenInt(q) and IsOddInt(LogInt(q, 2))
             and (q > 2 or series = "2F");
  elif series = "2G" then
      return q mod 3 = 0 and IsOddInt(LogInt(q, 3)) and q > 3;
  fi;
  return false;
end;

# The name of a simple group in the style of the Atlas, for display.
RECOG.SimpleGroupName := function(series, parameter)
  local q;
  if series = "Z" then
      return Concatenation("C", String(parameter[1]));
  elif series = "A" then
      return Concatenation("A", String(parameter[1]));
  elif series = "Spor" then
      return parameter[1];
  fi;
  q := Concatenation("(", String(Last(parameter)), ")");
  if series = "Sz" then
      return Concatenation("Sz", q);
  elif series = "2G" then
      return Concatenation("R", q);
  elif series = "2F" and parameter[1] = 2 then
      return "2F4(2)'";
  elif series = "2F" then
      return Concatenation("2F4", q);
  elif series in [ "O+", "O-" ] then
      return Concatenation("O", String(parameter[1]), series{[2]}, q);
  fi;
  return Concatenation(series, String(parameter[1]), q);
end;

# The factor record of the simple group with the given series and
# parameter, in normal form.
RECOG.SimpleFactor := function(series, parameter)
  local nf;
  nf := RECOG.SimpleGroupNormalForm(series, parameter);
  if not RECOG.IsSimpleGroupName(nf[1], nf[2]) then
      ErrorNoReturn("<series> = ", series, " and <parameter> = ", parameter,
                    " do not describe a simple group");
  fi;
  return Immutable(rec( series := nf[1], parameter := nf[2],
                        order := RECOG.SimpleGroupOrder(nf[1], nf[2]),
                        name := RECOG.SimpleGroupName(nf[1], nf[2]) ));
end;

# The composition factors of a cyclic group of order n.
RECOG.CyclicFactors := function(n)
  if n = 1 then
      return [];
  fi;
  return List(Factors(Integers, n), p -> RECOG.SimpleFactor("Z", [ p ]));
end;

# The factor record for a record <info> as returned by
# IsomorphismTypeInfoFiniteSimpleGroup.
RECOG.SimpleFactorFromTypeInfo := function(info)
  local t;
  if info.series = "Spor" then
      if info.shortname = "F3+" then
          return RECOG.SimpleFactor("Spor", [ "Fi24'" ]);
      fi;
      return RECOG.SimpleFactor("Spor", [ info.shortname ]);
  elif info.series = "2F" then
      # GAP files the Tits group under the sporadic groups
      return RECOG.SimpleFactor("2F", [ info.parameter ]);
  fi;
  t := ClassicalIsomorphismTypeFiniteSimpleGroup(info);
  return RECOG.SimpleFactor(t.series, t.parameter);
end;

# The factor record of the simple group U/N, for permutation groups U and N.
RECOG.SimpleFactorOfSection := function(U, N)
  local info;
  info := IsomorphismTypeInfoFiniteSimpleGroup(Size(U) / Size(N));
  if not IsBound(info.series) then
      # two simple groups have this order
      info := IsomorphismTypeInfoFiniteSimpleGroup(
                  Image(NaturalHomomorphismByNormalSubgroup(U, N)));
  fi;
  return RECOG.SimpleFactorFromTypeInfo(info);
end;

# LeafData for a leaf that has only a stabiliser chain, with its strong
# generators as nice generators.
RECOG.LeafDataStabilizerChain := function()
  return rec( type := "unknown", proven := true, nicegens := "strong" );
end;

# LeafData for a soluble leaf whose nice generators at <positions> form a
# pcgs with the given relative orders.
RECOG.LeafDataPcgs := function(positions, relativeOrders)
  return rec( type := "soluble", proven := true, nicegens := "pcgs",
              pcgs := positions, relativeOrders := relativeOrders );
end;

# LeafData for a leaf representing PSL(d,q).
RECOG.LeafDataPSL := function(d, q, nicegens)
  local data;
  data := rec( type := "simple", proven := true, nicegens := nicegens );
  if d = 2 and q = 2 then
      # S_3
      data.type := "soluble";
      data.factors := Concatenation(RECOG.CyclicFactors(3),
                                    RECOG.CyclicFactors(2));
  elif d = 2 and q = 3 then
      # A_4
      data.type := "soluble";
      data.factors := Concatenation(RECOG.CyclicFactors(4),
                                    RECOG.CyclicFactors(3));
  else
      data.factors := [ RECOG.SimpleFactor("L", [ d, q ]) ];
  fi;
  return data;
end;

# LeafData for a leaf representing a quotient of SL(d,q) by a central
# subgroup, whose centre has order <centre>.
RECOG.LeafDataSLQuotient := function(d, q, centre, nicegens)
  local data;
  data := RECOG.LeafDataPSL(d, q, nicegens);
  if centre = 1 then
      return data;
  fi;

  if data.type = "simple" then
      data.type := "quasisimple";
  fi;
  data.factors := Concatenation(RECOG.CyclicFactors(centre), data.factors);
  return data;
end;

# LeafData for a leaf representing S_n (<isSn> true) or A_n, n >= 5, on
# the standard generators.
RECOG.LeafDataSnAn := function(isSn, n)
  local data;
  data := rec( type := "simple", proven := true, nicegens := "SnAn",
               factors := [ RECOG.SimpleFactor("A", [ n ]) ] );
  if isSn then
      data.type := "almostsimple";
      Append(data.factors, RECOG.CyclicFactors(2));
  fi;
  return data;
end;

# LeafData for a stabiliser chain computed for the hint <name>: a sporadic
# group, the Tits group, or one of these extended by an automorphism of
# order 2. The name comes from a Monte Carlo algorithm.
RECOG.LeafDataForHint := function(name)
  local data, simple;
  data := RECOG.LeafDataStabilizerChain();

  simple := name;
  if EndsWith(name, ".2") then
      simple := name{[1..Length(name)-2]};
  fi;
  if simple = "2F4(2)'" then
      data.factors := [ RECOG.SimpleFactor("2F", [ 2 ]) ];
  elif RECOG.IsSimpleGroupName("Spor", [ simple ]) then
      data.factors := [ RECOG.SimpleFactor("Spor", [ simple ]) ];
  else
      return data;
  fi;

  data.proven := false;
  data.type := "simple";
  if simple <> name then
      data.type := "almostsimple";
      Append(data.factors, RECOG.CyclicFactors(2));
  fi;
  return data;
end;

InstallMethod( LeafData, "for a leaf whose method set no data",
  [ IsRecogNode and IsLeaf and IsReady ],
  function(ri)
    if Size(ri) = 1 then
        return rec( type := "soluble", proven := true, factors := [] );
    fi;
    return rec( type := "unknown", proven := true );
  end );

# A faithful permutation representation of the group of the leaf <ri>,
# for leaves that have a stabiliser chain only.
RECOG.PermGroupOfLeaf := function(ri)
  local P;
  if IsPermGroup(Grp(ri)) then
      return Grp(ri);
  fi;
  if not IsBound(ri!.stabilizerchain) then
      ErrorNoReturn("the leaf <ri> has neither composition factors in ",
                    "LeafData(<ri>) nor a stabiliser chain");
  fi;
  P := Group(ActionOnOrbit(ri!.stabilizerchain!.orb,
                           GeneratorsOfGroup(Grp(ri))));
  if Size(P) <> Size(ri) then
      ErrorNoReturn("the first orbit of the stabiliser chain of the leaf ",
                    "<ri> is not faithful");
  fi;
  return P;
end;

# The composition factors of the leaf <ri>, ascending. If the leaf method
# did not provide them, they are computed and stored in LeafData(ri).
RECOG.LeafFactors := function(ri)
  local data, series;
  data := LeafData(ri);
  if IsBound(data.factors) then
      return data.factors;
  fi;

  if IsBound(data.relativeOrders) then
      # the last element of a pcgs generates the bottom of the series
      data.factors := Concatenation(List(Reversed(data.relativeOrders),
                                         RECOG.CyclicFactors));
      return data.factors;
  fi;

  # GAP's series descends
  series := CompositionSeries(RECOG.PermGroupOfLeaf(ri));
  data.factors := List(Reversed([1..Length(series)-1]),
                    i -> RECOG.SimpleFactorOfSection(series[i], series[i+1]));

  # the factors determine these two types
  if data.type = "unknown" then
      if ForAll(data.factors, f -> f.series = "Z") then
          data.type := "soluble";
      elif Length(data.factors) = 1 then
          data.type := "simple";
      fi;
  fi;
  return data.factors;
end;

# Check LeafData of the leaf <ri>: the shape of the record, and the orders
# it implies against Size(ri). Returns true or a string naming the problem.
RECOG.CheckLeafData := function(ri)
  local data, factors, nonabelian;
  data := LeafData(ri);
  if not IsRecord(data) or not IsBound(data.type)
     or not data.type in RECOG.LeafDataTypes then
      return "no valid type";
  fi;
  if not IsBound(data.proven) or not IsBool(data.proven) then
      return "proven is not a boolean";
  fi;

  if IsBound(data.pcgs) then
      if data.type <> "soluble" or not IsBound(data.relativeOrders)
         or Length(data.pcgs) <> Length(data.relativeOrders)
         or not IsSubset([1..Length(NiceGens(ri))], data.pcgs) then
          return "pcgs does not fit";
      fi;
      if Product(data.relativeOrders) <> Size(ri) then
          return "relative orders do not multiply to the size";
      fi;
  fi;

  if not IsBound(data.factors) then
      if data.type <> "unknown" and not IsBound(data.pcgs) then
          return "factors missing";
      fi;
      return true;
  fi;

  factors := data.factors;
  if Product(factors, f -> f.order) <> Size(ri) then
      return "factor orders do not multiply to the size";
  fi;
  nonabelian := Filtered([1..Length(factors)], i -> factors[i].series <> "Z");
  if data.type = "soluble" and nonabelian <> [] then
      return "nonabelian factor in a soluble leaf";
  elif data.type = "simple" and (Length(factors) <> 1 or nonabelian <> [1]) then
      return "simple leaf without a single nonabelian factor";
  elif data.type = "almostsimple" and nonabelian <> [1] then
      return "almost simple leaf whose socle is not the first factor";
  elif data.type = "quasisimple" and nonabelian <> [Length(factors)] then
      return "quasisimple leaf whose simple quotient is not the last factor";
  fi;
  return true;
end;

# The leaves of the tree <ri>, kernel before image.
RECOG.Leaves := function(ri)
  local leaves;
  if IsLeaf(ri) then
      return [ ri ];
  fi;
  leaves := [];
  if HasKernelRecogNode(ri) and KernelRecogNode(ri) <> fail then
      leaves := RECOG.Leaves(KernelRecogNode(ri));
  fi;
  Append(leaves, RECOG.Leaves(ImageRecogNode(ri)));
  return leaves;
end;

InstallGlobalFunction( CompositionFactorsOfRecogNode,
  function(ri)
    if not IsReady(ri) then
        ErrorNoReturn("the recognition described by this recognition node",
                      " has failed!");
    fi;
    return Concatenation(List(RECOG.Leaves(ri), RECOG.LeafFactors));
  end );

InstallGlobalFunction( DisplayCompositionFactors,
  function(ri)
    local factors, size, f;
    if not IsReady(ri) then
        Print("Recognition failed\n");
        return;
    fi;
    factors := CompositionFactorsOfRecogNode(ri);
    size := Product(factors, f -> f.order);
    for f in Reversed(factors) do
        Print("Group of size ", size, "\n | ", f.name, "\n");
        size := size / f.order;
    od;
    Print("1\n");
  end );
