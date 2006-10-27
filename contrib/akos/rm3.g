z:=Z(3);
n:=z*0;
i:=z^0;
generatorsOfGroup := [ [ [ z , n ] , [ n, i ] ] , [ [ z , i ] , [ z , n ] ] ] ;
glMakers := StructuralCopy(generatorsOfGroup );
glMakers2:=StructuralCopy(generatorsOfGroup ) ;
glMakers3:=[];
glMakers4:=[];
for ij in glMakers do
  ii:=StructuralCopy(ij);
  ii[1][3]:=n;
  ii[1][4]:=n;
  ii[2][3]:=n;
  ii[2][4]:=n ;

  ii [ 3 ] := [ n , n, i, n] ;
  ii [ 4 ] := [ n, n, n, i ] ;
  Add( glMakers3 , ii ) ;
od ;
for ij in glMakers2 do
  ii :=StructuralCopy(ij);
  ii [ 3 ] := [ n , n ] ;
  ii [ 4 ] := [ n , n ] ;
  ii [ 3 ][3] := ii [ 1 ][1];
   ii [ 3 ][4]:= ii [ 1 ][2];
  ii [ 4 ][3] := ii [ 2 ][1];
   ii [ 4 ][4]:= ii [ 2 ][2];


  ii [ 1 ] := [ i, n ,n ,n ] ;
  ii [ 2 ] := [ n, i, n, n ] ;
Add(glMakers4,ii);
od ;

# k:=[z*[[1,0,0,0],[0,z^(-1),0,0],[0,0,z^(-1),0],[0,0,0,z^(-1)]],    z*[[1,z^(-1),0,0],[1,0,0,0],[0,0,z^(-1),0],[0,0,0,z^(-1)]], z*[[z^(-1),0,0,0],[0,z^(-1),0,0],[0,0,1,z^(-1)],[0,0,1,0]], z*[[z^(-1),0,0,0],[0,z^(-1),0,0],[0,0,1,0],[0,0,0,z^(-1)]]];

k := Union ( glMakers3 , glMakers4 ) ;

kk:=k*[[n,n,i,n],[n,n,n,i],[i,n,n,n],[n,i,n,n]];

un:=Union(k,kk);

g:=Group(un);

skew := PseudoRandom ( GL(4, GF(9)));

temp := [ ] ;

for i in GeneratorsOfGroup ( g ) do
  Add ( temp , skew^(-1) * i * skew * PseudoRandom(Units(GF(9)))) ;
od ;

skewedG := Group ( temp ) ;
