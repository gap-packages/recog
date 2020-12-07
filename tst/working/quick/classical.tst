#
# tests for auxiliary functions in classical.gi
#

#
# KroneckerFactors
#
gap> g:=[[1,2],[3,4]]*One(GF(5));;
gap> h:=[[1,1],[3,-1]]*One(GF(5));;
gap> KroneckerFactors(KroneckerProduct(g,h)) = [g,h];
true

# brute force test
gap> G := SL(2,5);;
gap> SetX(G, G, function(g,h)
>   local gh;
>   gh:=KroneckerFactors(KroneckerProduct(g,h));
>   return gh = false or (IsEqualProjective(gh[1], g) and IsEqualProjective(gh[2], h));
> end);
[ true ]
