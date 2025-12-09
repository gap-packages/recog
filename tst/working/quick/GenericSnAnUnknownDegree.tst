#@local d, sets, SdOn2Sets, ri, success, x, slp, db
#
# HACK to insert the method
gap> AddMethod(FindHomDbPerm, FindHomMethodsGeneric.SnAnUnknownDegree, 58);;
gap> AddMethod(FindHomDbMatrix, FindHomMethodsGeneric.SnAnUnknownDegree, 1070);;
gap> AddMethod(FindHomDbProjective, FindHomMethodsGeneric.SnAnUnknownDegree, 1220);;

# FindHomMethodsGeneric.SnAnUnknownDegree
# Sn
gap> for d in [11] do
> sets := Combinations([1 .. d], 2);;
> SdOn2Sets := Action(SymmetricGroup(d), sets, OnSets);;
> ri := RecogNode(SdOn2Sets);;
> success := FindHomMethodsGeneric.SnAnUnknownDegree(ri, SdOn2Sets);
> if not success or not Size(ri) = Factorial(d) then
>   Print("wrong result! degree ", d, "\n");
> fi;
> od;

# An
gap> for d in [11] do
> sets := Combinations([1 .. d], 2);;
> SdOn2Sets := Action(AlternatingGroup(d), sets, OnSets);;
> ri := RecogNode(SdOn2Sets);;
> success := FindHomMethodsGeneric.SnAnUnknownDegree(ri, SdOn2Sets);
> if not success or not Size(ri) = Factorial(d)/2 then
>   Print("wrong result! degree ", d, "\n");
> fi;
> od;

# Check Slp function
gap> ri := RecogNode(SdOn2Sets);;
gap> FindHomMethodsGeneric.SnAnUnknownDegree(ri, SdOn2Sets);
true
gap> x := PseudoRandom(Grp(ri));;
gap> slp := SLPforElement(ri, x);;
gap> x = ResultOfStraightLineProgram(slp, NiceGens(ri));
true

#
# Remove Hacky injection of our method
gap> for db in [FindHomDbPerm, FindHomDbMatrix, FindHomDbProjective] do
>       Remove(db,
>              PositionProperty(db, x -> Stamp(x.method) = "SnAnUnknownDegree"));;
> od;
