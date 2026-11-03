# Reusable data returned by classical graybox naming.
gap> START_TEST("quick/classicalgraybox.tst");

# L5(3) needs witnesses for all three indices. Check the returned certificates
# against independently computed projective orders, and evaluate their SLPs.
gap> grayboxG := Group(GeneratorsOfGroup(SL(5,3)));;
gap> grayboxR := RECOG.RecogniseClassicalGraybox(grayboxG,3);;
gap> [grayboxR.status, grayboxR.name, grayboxR.candidates];
[ "probable", "L5(3)", [ "L5(3)" ] ]
gap> ForAll([3,4,5], k -> ForAny(grayboxR.elements, e -> k in e.ppds));
true
gap> Length(grayboxR.elements) = 3;
true
gap> not IsEmpty(grayboxR.elements) and
>     ForAll(grayboxR.elements, e -> IsObjWithMemory(e.el) and
>     ResultOfStraightLineProgram(SLPOfElm(e.el),GeneratorsOfGroup(grayboxG))
>     = StripMemory(e.el));
true
gap> not IsEmpty(grayboxR.elements) and
>     ForAll(grayboxR.elements, e -> Product(e.factors) = e.charpoly and
>     e.charpoly = CharacteristicPolynomial(GF(3),GF(3),StripMemory(e.el)));
true
gap> grayboxCheckPpds := function(e, p)
>     local primes;
>     primes := Filtered(PrimeDivisors(RECOG.ProjectiveOrder(StripMemory(e.el))),
>         r -> r <> 2 and r <> p);
>     return ForAll(e.ppds, k -> ForAny(primes, r -> OrderMod(p,r) = k));
> end;;
gap> not IsEmpty(grayboxR.elements) and
>     ForAll(grayboxR.elements, e -> grayboxCheckPpds(e,3));
true

# Preserve an existing memory context, including that of a recognition node.
gap> grayboxRi := RecogNode(grayboxG);;
gap> grayboxMemG := Group(grayboxRi!.gensHmem);;
gap> grayboxMemR := RECOG.RecogniseClassicalGraybox(grayboxMemG,3);;
gap> not IsEmpty(grayboxMemR.elements) and
>     ForAll(grayboxMemR.elements, e ->
>     IsIdenticalObj(e.el!.slp,grayboxRi!.gensHmem[1]!.slp));
true
gap> not IsEmpty(grayboxMemR.elements) and
>     ForAll(grayboxMemR.elements, e ->
>     ResultOfStraightLineProgram(SLPOfElm(e.el),GeneratorsOfGroup(grayboxG))
>     = StripMemory(e.el));
true

# This input is outside the naming promise and has no PPD witnesses.
gap> grayboxScalar := Group(-IdentityMat(5,GF(3)));;
gap> grayboxScalarR := RECOG.RecogniseClassicalGraybox(grayboxScalar,3);;
gap> [grayboxScalarR.status, grayboxScalarR.name, IsEmpty(grayboxScalarR.elements)];
[ "inconclusive", fail, true ]

# A joint PPD search must find both primes in ONE element.
gap> grayboxA := CompanionMat(MinimalPolynomial(GF(3),Z(27)));;
gap> grayboxB := CompanionMat(MinimalPolynomial(GF(3),Z(81)));;
gap> grayboxJoint := DirectSumMat(grayboxA,grayboxB);;
gap> grayboxData := rec(field := GF(3), p := 3, Q := 3, a := 1,
>     unipotentBound := 9, parts := [], samples := [],
>     searches := rec(), invar := [],
>     random := ProductReplacer(GeneratorsWithMemory([grayboxJoint])));;
gap> grayboxSample := RECOG.ClassicalGrayboxSample(grayboxData);;
gap> RECOG.FindPPD(grayboxData,[3,4],30);
true
gap> grayboxWitness := grayboxData.samples[grayboxData.searches.(String([3,4])).witness];;
gap> grayboxWitness.ppds{[3,4]} = [true,true] and
>     ForAll([3,4], k -> Gcd(RECOG.ProjectiveOrder(StripMemory(grayboxWitness.el)),
>         PrimitivePrimeDivisors(k,3).ppds) > 1);
true
gap> grayboxBefore := Length(grayboxData.samples);;
gap> RECOG.FindPPD(grayboxData,[3,4],30);
true
gap> Length(grayboxData.samples) = grayboxBefore;
true

# Fresh order tests retain their elements and orders. Divisibility by 9 is
# not reported as ppd(6,2), which does not exist.
gap> grayboxNine := CompanionMat(MinimalPolynomial(GF(2),Z(64)^7));;
gap> grayboxOrderData := rec(p := 2, invar := [], orderSamples := [],
>     random := ProductReplacer(GeneratorsWithMemory([grayboxNine])));;
gap> RECOG.DistinguishSmallCases(grayboxOrderData,9,[],30);
true
gap> ForAny(grayboxOrderData.orderSamples, e -> e.projectiveOrder = 9);
true
gap> not IsEmpty(grayboxOrderData.orderSamples) and
>     ForAll(grayboxOrderData.orderSamples, e -> IsEmpty(e.ppds) and
>     e.projectiveOrder = RECOG.ProjectiveOrder(StripMemory(e.el)) and
>     ResultOfStraightLineProgram(SLPOfElm(e.el),[grayboxNine]) = StripMemory(e.el));
true

# Legacy PPD samples keep their return format and collect reusable witnesses.
gap> grayboxLegacyGens := GeneratorsWithMemory([grayboxJoint]);;
gap> grayboxLegacyG := Group(grayboxLegacyGens);;
gap> grayboxLegacyElements := [];;
gap> grayboxLegacyR := RECOG.ppdSample(grayboxLegacyG,[],3,[3,4],30
>     : recogElements := grayboxLegacyElements);;
gap> Length(grayboxLegacyR) = 3 and
>     ForAny(grayboxLegacyElements, e -> e.ppds = [3,4]);
true
gap> not IsEmpty(grayboxLegacyElements) and
>     ForAll(grayboxLegacyElements, e -> grayboxCheckPpds(e,3) and
>     e.projectiveOrder = RECOG.ProjectiveOrder(StripMemory(e.el)) and
>     IsIdenticalObj(e.el!.slp,grayboxLegacyGens[1]!.slp) and
>     ResultOfStraightLineProgram(SLPOfElm(e.el),[grayboxJoint]) = StripMemory(e.el));
true
gap> grayboxBefore := Set(grayboxLegacyElements, e -> e.ppds);;
gap> RECOG.ppdSample(grayboxLegacyG,[],3,[3,4],30
>     : recogElements := grayboxLegacyElements);;
gap> grayboxAfter := Set(grayboxLegacyElements, e -> e.ppds);;
gap> IsSubset(grayboxAfter,grayboxBefore) and
>     Length(grayboxAfter) = Length(grayboxLegacyElements);
true

# Artin's replacement index 6 and scalar orders are not projective PPDs.
gap> grayboxLegacyElements := [];;
gap> RECOG.ppdSample(Group(GeneratorsWithMemory([grayboxNine])),[],2,[6],30
>     : recogElements := grayboxLegacyElements);;
gap> List(grayboxLegacyElements, e -> e.ppds);
[ [ 2 ] ]
gap> grayboxLegacyElements := [];;
gap> RECOG.ppdSample(Group(GeneratorsWithMemory([Z(7)^2*IdentityMat(3,GF(7))])),
>     [],7,[1],30 : recogElements := grayboxLegacyElements);;
gap> IsEmpty(grayboxLegacyElements);
true

# The even-rank involution test also collects its derived PPD witness.
gap> grayboxSp := Sp(8,3);;
gap> grayboxSpGens := GeneratorsOfGroup(grayboxSp);;
gap> grayboxSpMem := GeneratorsWithMemory(grayboxSpGens);;
gap> grayboxOrders := Set(List([1..200],
>     i -> RECOG.ProjectiveOrder(PseudoRandom(grayboxSp))));;
gap> grayboxLegacyElements := [];;
gap> RECOG.DistinguishSpO(Group(grayboxSpMem),4,3,1,grayboxOrders
>     : recogElements := grayboxLegacyElements);
"S8(3)"
gap> ForAny(grayboxLegacyElements, e -> 4 in e.ppds) and
>     ForAny(grayboxLegacyElements, e -> 6 in e.ppds or 8 in e.ppds);
true
gap> not IsEmpty(grayboxLegacyElements) and
>     ForAll(grayboxLegacyElements, e -> grayboxCheckPpds(e,3) and
>     e.projectiveOrder = RECOG.ProjectiveOrder(StripMemory(e.el)) and
>     IsIdenticalObj(e.el!.slp,grayboxSpMem[1]!.slp) and
>     ResultOfStraightLineProgram(SLPOfElm(e.el),grayboxSpGens) = StripMemory(e.el));
true

# Helper witnesses reach the final graybox result.
gap> grayboxSymGens := List(GeneratorsOfGroup(Sp(6,3)),g -> SymmetricPower(g,2));;
gap> grayboxSymR := RECOG.RecogniseClassicalGraybox(Group(grayboxSymGens),3);;
gap> grayboxSymR.name;
"S6(3)"
gap> grayboxLegacyElements := Filtered(grayboxSymR.elements,
>     e -> IsBound(e.projectiveOrder));;
gap> ForAny(grayboxLegacyElements, e -> 6 in e.ppds);
true
gap> not IsEmpty(grayboxLegacyElements) and
>     ForAll(grayboxLegacyElements, e -> grayboxCheckPpds(e,3) and
>     e.projectiveOrder = RECOG.ProjectiveOrder(StripMemory(e.el)) and
>     ResultOfStraightLineProgram(SLPOfElm(e.el),grayboxSymGens) = StripMemory(e.el));
true
gap> STOP_TEST("quick/classicalgraybox.tst");
