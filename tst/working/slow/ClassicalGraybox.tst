# Classical graybox recognition in natural and non-natural representations.
# This draft includes large cases up to dimension 595 and is not a quick test.
#
# Scope: SL, SU, Sp, Omega+, Omega-, and odd-dimensional Omega.
# Only absolutely irreducible natural modules with simple projective image
# are included. SU(d,q) uses group parameter q, not matrix field size q^2.
# Excluded: SL(2,2/3), SU(2,2/3), SU(3,2), Sp(2,2/3), Sp(4,2),
# Omega(0,3,3), orthogonal dimension 2 and Omega+(4,q) (not simple).
# Sp and Omega+/- require even d. Odd-dimensional Omega in even characteristic
# has a reducible natural module, so it is outside the recognition contract.
#

gap> START_TEST("ClassicalGraybox.tst");
gap> IsBound(RECOG.RecogniseClassicalGraybox);
true

# Construct the six classical families. q is always the group parameter.
gap> grayboxGroup := function(family, d, q)
>     if family = "SL" then return SL(d,q);
>     elif family = "SU" then return SU(d,q);
>     elif family = "Sp" then return Sp(d,q);
>     elif family = "O+" then return Omega(1,d,q);
>     elif family = "O-" then return Omega(-1,d,q);
>     elif family = "O" then return Omega(0,d,q);
>     else Error("Unknown classical family: ",family);
>     fi;
> end;;

# Require a unique "probable" answer. An inconclusive record also fails the test.
# Use the matrices without constructor metadata; do not retry failed recognition.
gap> grayboxResult := function(G, q)
>     local result;
>     G := Group(GeneratorsOfGroup(G));
>     result := RECOG.RecogniseClassicalGraybox(G,q);
>     if result.status = "probable" and result.name <> fail
>         and result.candidates = [result.name] then
>         return result.name;
>     fi;
>     return result;
> end;;
gap> grayboxName := function(family, d, q)
>     return grayboxResult(grayboxGroup(family,d,q),q);
> end;;

# Build an absolutely irreducible non-natural module of the stated dimension.
# For Sp's exterior square and Omega's symmetric square, remove the trivial
# constituent by selecting the unique composition factor of the expected size.
# A Frobenius tensor means V tensor V^(p), with entrywise p-th powers, not g^p.
gap> grayboxModule := function(family, d, q, construction, dimension)
>     local G, F, p, gens, module, factors;
>     G := grayboxGroup(family,d,q);
>     F := FieldOfMatrixGroup(G);
>     p := Characteristic(F);
>     gens := GeneratorsOfGroup(G);
>     if construction = "exterior" then
>         gens := List(gens,g -> ExteriorPower(g,2));
>     elif construction = "symmetric" then
>         gens := List(gens,g -> SymmetricPower(g,2));
>     elif construction = "frobenius" then
>         gens := List(gens,g -> KroneckerProduct(g,
>             List(g,row -> List(row,x -> x^p))));
>     else Error("Unknown module construction: ",construction);
>     fi;
>     module := GModuleByMats(gens,F);
>     if (family = "Sp" and construction = "exterior") or
>         (family in ["O","O+","O-"] and construction = "symmetric") then
>         factors := Filtered(MTX.CompositionFactors(module),
>             factor -> MTX.Dimension(factor) = dimension);
>         if Length(factors) <> 1 then
>             Error("Expected one composition factor of dimension ",dimension);
>         fi;
>         module := factors[1];
>     fi;
>     if MTX.Dimension(module) <> dimension then
>         Error("Unexpected module dimension: ",MTX.Dimension(module));
>     fi;
>     if not MTX.IsAbsolutelyIrreducible(module) then
>         Error("The test representation is not absolutely irreducible");
>     fi;
>     return Group(MTX.Generators(module));
> end;;

# Small cases: every admissible pair d=2..8, q=2,3,4,5, in each family.

# SL: small natural dimensions.

# q=2
gap> grayboxName("SL", 3, 2);
"L3(2)"
gap> grayboxName("SL", 4, 2);
"L4(2)"
gap> grayboxName("SL", 5, 2);
"L5(2)"
gap> grayboxName("SL", 6, 2);
"L6(2)"
gap> grayboxName("SL", 7, 2);
"L7(2)"
gap> grayboxName("SL", 8, 2);
"L8(2)"

# q=3
gap> grayboxName("SL", 3, 3);
"L3(3)"
gap> grayboxName("SL", 4, 3);
"L4(3)"
gap> grayboxName("SL", 5, 3);
"L5(3)"
gap> grayboxName("SL", 6, 3);
"L6(3)"
gap> grayboxName("SL", 7, 3);
"L7(3)"
gap> grayboxName("SL", 8, 3);
"L8(3)"

# q=4
gap> grayboxName("SL", 2, 4);
"L2(4)"
gap> grayboxName("SL", 3, 4);
"L3(4)"
gap> grayboxName("SL", 4, 4);
"L4(4)"
gap> grayboxName("SL", 5, 4);
"L5(4)"
gap> grayboxName("SL", 6, 4);
"L6(4)"
gap> grayboxName("SL", 7, 4);
"L7(4)"
gap> grayboxName("SL", 8, 4);
"L8(4)"

# q=5
gap> grayboxName("SL", 2, 5);
"L2(5)"
gap> grayboxName("SL", 3, 5);
"L3(5)"
gap> grayboxName("SL", 4, 5);
"L4(5)"
gap> grayboxName("SL", 5, 5);
"L5(5)"
gap> grayboxName("SL", 6, 5);
"L6(5)"
gap> grayboxName("SL", 7, 5);
"L7(5)"
gap> grayboxName("SL", 8, 5);
"L8(5)"

# SU: small natural dimensions.

# q=2
gap> grayboxName("SU", 4, 2);
"U4(2)"
gap> grayboxName("SU", 5, 2);
"U5(2)"
gap> grayboxName("SU", 6, 2);
"U6(2)"
gap> grayboxName("SU", 7, 2);
"U7(2)"
gap> grayboxName("SU", 8, 2);
"U8(2)"

# q=3
gap> grayboxName("SU", 3, 3);
"U3(3)"
gap> grayboxName("SU", 4, 3);
"U4(3)"
gap> grayboxName("SU", 5, 3);
"U5(3)"
gap> grayboxName("SU", 6, 3);
"U6(3)"
gap> grayboxName("SU", 7, 3);
"U7(3)"
gap> grayboxName("SU", 8, 3);
"U8(3)"

# q=4
gap> grayboxName("SU", 2, 4);
"L2(4)"
gap> grayboxName("SU", 3, 4);
"U3(4)"
gap> grayboxName("SU", 4, 4);
"U4(4)"
gap> grayboxName("SU", 5, 4);
"U5(4)"
gap> grayboxName("SU", 6, 4);
"U6(4)"
gap> grayboxName("SU", 7, 4);
"U7(4)"
gap> grayboxName("SU", 8, 4);
"U8(4)"

# q=5
gap> grayboxName("SU", 2, 5);
"L2(5)"
gap> grayboxName("SU", 3, 5);
"U3(5)"
gap> grayboxName("SU", 4, 5);
"U4(5)"
gap> grayboxName("SU", 5, 5);
"U5(5)"
gap> grayboxName("SU", 6, 5);
"U6(5)"
gap> grayboxName("SU", 7, 5);
"U7(5)"
gap> grayboxName("SU", 8, 5);
"U8(5)"

# Sp: small natural dimensions.

# q=2
gap> grayboxName("Sp", 6, 2);
"S6(2)"
gap> grayboxName("Sp", 8, 2);
"S8(2)"

# q=3
gap> grayboxName("Sp", 4, 3);
"S4(3)"
gap> grayboxName("Sp", 6, 3);
"S6(3)"
gap> grayboxName("Sp", 8, 3);
"S8(3)"

# q=4
gap> grayboxName("Sp", 2, 4);
"L2(4)"
gap> grayboxName("Sp", 4, 4);
"S4(4)"
gap> grayboxName("Sp", 6, 4);
"S6(4)"
gap> grayboxName("Sp", 8, 4);
"S8(4)"

# q=5
gap> grayboxName("Sp", 2, 5);
"L2(5)"
gap> grayboxName("Sp", 4, 5);
"S4(5)"
gap> grayboxName("Sp", 6, 5);
"S6(5)"
gap> grayboxName("Sp", 8, 5);
"S8(5)"

# O+: small natural dimensions.

# q=2
gap> grayboxName("O+", 6, 2);
"L4(2)"
gap> grayboxName("O+", 8, 2);
"O+8(2)"

# q=3
gap> grayboxName("O+", 6, 3);
"L4(3)"
gap> grayboxName("O+", 8, 3);
"O+8(3)"

# q=4
gap> grayboxName("O+", 6, 4);
"L4(4)"
gap> grayboxName("O+", 8, 4);
"O+8(4)"

# q=5
gap> grayboxName("O+", 6, 5);
"L4(5)"
gap> grayboxName("O+", 8, 5);
"O+8(5)"

# O-: small natural dimensions.

# q=2
gap> grayboxName("O-", 4, 2);
"L2(4)"
gap> grayboxName("O-", 6, 2);
"U4(2)"
gap> grayboxName("O-", 8, 2);
"O-8(2)"

# q=3
gap> grayboxName("O-", 4, 3);
"L2(9)"
gap> grayboxName("O-", 6, 3);
"U4(3)"
gap> grayboxName("O-", 8, 3);
"O-8(3)"

# q=4
gap> grayboxName("O-", 4, 4);
"L2(16)"
gap> grayboxName("O-", 6, 4);
"U4(4)"
gap> grayboxName("O-", 8, 4);
"O-8(4)"

# q=5
gap> grayboxName("O-", 4, 5);
"L2(25)"
gap> grayboxName("O-", 6, 5);
"U4(5)"
gap> grayboxName("O-", 8, 5);
"O-8(5)"

# O: small natural dimensions.

# q=3
gap> grayboxName("O", 5, 3);
"S4(3)"
gap> grayboxName("O", 7, 3);
"O7(3)"

# q=5
gap> grayboxName("O", 3, 5);
"L2(5)"
gap> grayboxName("O", 5, 5);
"S4(5)"
gap> grayboxName("O", 7, 5);
"O7(5)"

# Larger cases: d=10,20,60 and q=11,16.
# Odd-dimensional Omega is covered by the small and non-natural cases.

# SL: larger natural dimensions.

# q=11
gap> grayboxName("SL", 10, 11);
"L10(11)"
gap> grayboxName("SL", 20, 11);
"L20(11)"
gap> grayboxName("SL", 60, 11);
"L60(11)"

# q=16
gap> grayboxName("SL", 10, 16);
"L10(16)"
gap> grayboxName("SL", 20, 16);
"L20(16)"
gap> grayboxName("SL", 60, 16);
"L60(16)"

# SU: larger natural dimensions.

# q=11
gap> grayboxName("SU", 10, 11);
"U10(11)"
gap> grayboxName("SU", 20, 11);
"U20(11)"
gap> grayboxName("SU", 60, 11);
"U60(11)"

# q=16
gap> grayboxName("SU", 10, 16);
"U10(16)"
gap> grayboxName("SU", 20, 16);
"U20(16)"
gap> grayboxName("SU", 60, 16);
"U60(16)"

# Sp: larger natural dimensions.

# q=11
gap> grayboxName("Sp", 10, 11);
"S10(11)"
gap> grayboxName("Sp", 20, 11);
"S20(11)"
gap> grayboxName("Sp", 60, 11);
"S60(11)"

# q=16
gap> grayboxName("Sp", 10, 16);
"S10(16)"
gap> grayboxName("Sp", 20, 16);
"S20(16)"

# O+: larger natural dimensions.

# q=11
gap> grayboxName("O+", 10, 11);
"O+10(11)"
gap> grayboxName("O+", 20, 11);
"O+20(11)"
gap> grayboxName("O+", 60, 11);
"O+60(11)"

# q=16
gap> grayboxName("O+", 10, 16);
"O+10(16)"
gap> grayboxName("O+", 20, 16);
"O+20(16)"
gap> grayboxName("O+", 60, 16);
"O+60(16)"

# O-: larger natural dimensions.

# q=11
gap> grayboxName("O-", 10, 11);
"O-10(11)"
gap> grayboxName("O-", 20, 11);
"O-20(11)"

# q=16
gap> grayboxName("O-", 10, 16);
"O-10(16)"
gap> grayboxName("O-", 20, 16);
"O-20(16)"

# Three non-natural modules per family: exterior square, symmetric square,
# and a Frobenius tensor. Squares use q=11, avoiding small-characteristic issues;
# tensors use q=11^2, so the p-Frobenius twist gives a different restricted factor.
# The helper checks the stated dimension and absolute irreducibility BEFORE naming.

# SL: resulting module dimensions 6, 10, 16.
gap> grayboxResult(grayboxModule("SL", 4, 11, "exterior", 6), 11);
"L4(11)"
gap> grayboxResult(grayboxModule("SL", 4, 11, "symmetric", 10), 11);
"L4(11)"
gap> grayboxResult(grayboxModule("SL", 4, 11^2, "frobenius", 16), 11^2);
"L4(121)"

# SU: resulting module dimensions 6, 10, 16.
gap> grayboxResult(grayboxModule("SU", 4, 11, "exterior", 6), 11);
"U4(11)"
gap> grayboxResult(grayboxModule("SU", 4, 11, "symmetric", 10), 11);
"U4(11)"
gap> grayboxResult(grayboxModule("SU", 4, 11^2, "frobenius", 16), 11^2);
"U4(121)"

# Sp: resulting module dimensions 14, 21, 36.
gap> grayboxResult(grayboxModule("Sp", 6, 11, "exterior", 14), 11);
"S6(11)"
gap> grayboxResult(grayboxModule("Sp", 6, 11, "symmetric", 21), 11);
"S6(11)"
gap> grayboxResult(grayboxModule("Sp", 6, 11^2, "frobenius", 36), 11^2);
"S6(121)"

# O: resulting module dimensions 21, 27, 49.
gap> grayboxResult(grayboxModule("O", 7, 11, "exterior", 21), 11);
"O7(11)"
gap> grayboxResult(grayboxModule("O", 7, 11, "symmetric", 27), 11);
"O7(11)"
gap> grayboxResult(grayboxModule("O", 7, 11^2, "frobenius", 49), 11^2);
"O7(121)"

# O+: resulting module dimensions 28, 35, 64.
gap> grayboxResult(grayboxModule("O+", 8, 11, "exterior", 28), 11);
"O+8(11)"
gap> grayboxResult(grayboxModule("O+", 8, 11, "symmetric", 35), 11);
"O+8(11)"
gap> grayboxResult(grayboxModule("O+", 8, 11^2, "frobenius", 64), 11^2);
"O+8(121)"

# O-: resulting module dimensions 28, 35, 64.
gap> grayboxResult(grayboxModule("O-", 8, 11, "exterior", 28), 11);
"O-8(11)"
gap> grayboxResult(grayboxModule("O-", 8, 11, "symmetric", 35), 11);
"O-8(11)"
gap> grayboxResult(grayboxModule("O-", 8, 11^2, "frobenius", 64), 11^2);
"O-8(121)"

# Extend scalars and change basis so the entries generate the larger field.
# The group parameter q stays unchanged; absolute irreducibility must survive.
gap> grayboxOverField := function(G, q, Q)
>     local F, basis, gens, module;
>     F := GF(Q);
>     basis := IdentityMat(DimensionOfMatrixGroup(G),F);
>     basis[1][1] := Z(Q);
>     gens := List(GeneratorsOfGroup(G),g -> g^basis);
>     G := Group(gens);
>     if Size(FieldOfMatrixGroup(G)) <> Q then
>         Error("The matrices do not generate the requested field");
>     fi;
>     module := GModuleByMats(gens,F);
>     if not MTX.IsAbsolutelyIrreducible(module) then
>         Error("The extended representation is not absolutely irreducible");
>     fi;
>     return grayboxResult(G,q);
> end;;

# SL(3,3): GF(3) -> GF(9); SU(3,3): GF(9) -> GF(81).
gap> grayboxOverField(SL(3,3), 3, 9);
"L3(3)"
gap> grayboxOverField(SU(3,3), 3, 81);
"U3(3)"
gap> STOP_TEST("ClassicalGraybox.tst");
