DirectProductOfMatrixGroup := function(G,H)
  local gens,g,h,dG,dH,M,i,j;
  gens := [];
  dG:=DimensionOfMatrixGroup(G);
  dH:=DimensionOfMatrixGroup(H);
  for g in GeneratorsOfGroup(G) do
    M:=One(MatrixAlgebra(FieldOfMatrixGroup(G),dG+dH));
    M:=MutableCopyMat(M);
    for i in [1..dG] do
      for j in [1..dG] do
        M[i,j]:=g[i,j];
      od;
    od;
    Add(gens,M);
  od;
  for h in GeneratorsOfGroup(H) do
    M:=One(MatrixAlgebra(FieldOfMatrixGroup(G),dG+dH));
    M:=MutableCopyMat(M);
    for i in [1..dH] do
      for j in [1..dH] do
        M[dG+i,dG+j]:=h[i,j];
      od;
    od;
    Add(gens,M);
  od;
  return GroupWithGenerators(gens);
end;

TensorProductOfMatrixGroup := function(G,H)
 local gens,g,h;

 gens := [];
 for g in GeneratorsOfGroup(G) do
   Add(gens,KroneckerProduct(g,One(H)));
 od;
 for h in GeneratorsOfGroup(H) do
   Add(gens,KroneckerProduct(One(G),h));
 od;

 return GroupWithGenerators(gens);
end;

WreathProductOfMatrixGroupTensor := function( M, P )
    local   m,  d,  id,  gens,  b,  ran,  raN,  mat,  gen,  G;

    # FIXME: Still needs completing.
    m := DimensionOfMatrixGroup( M );
    d := LargestMovedPoint( P );
    id := IdentityMat( m ^ d, DefaultFieldOfMatrixGroup( M ) );
    gens := [  ];
    for b  in [ 1 .. d ]  do
        ran := ( b - 1 ) * m + [ 1 .. m ];
        for mat  in GeneratorsOfGroup( M )  do
            gen := StructuralCopy( id );
            gen{ ran }{ ran } := mat;
            Add( gens, gen );
        od;
    od;
    for gen  in GeneratorsOfGroup( P )  do
        mat := StructuralCopy( id );
        for b  in [ 1 .. d ]  do
            ran := ( b - 1 ) * m + [ 1 .. m ];
            raN := ( b^gen - 1 ) * m + [ 1 .. m ];
            mat{ ran } := id{ raN };
        od;
        Add( gens, mat );
    od;
    G := GroupWithGenerators( gens );
    if HasName( M )  and  HasName( P )  then
        SetName( G, Concatenation( Name( M ), " wr ", Name( P ) ) );
    fi;
    return G;
end;


