g:=SL(7,q);
basechangemat:=IdentityMat(7,GF(q));
a1:=IdentityMat(7);
a2:=IdentityMat(7);
a3:=NullMat(7,7);
a1[1][2]:=1;
a2[2][1]:=1;
a3[1][2]:=1; 
a3[2][3]:=1;
a3[3][1]:=1;
for i in [4..7] do
    a3[i][i]:=1;
od;
a1:=Z(q)^0*a1;
a2:=Z(q)^0*a2;
a3:=Z(q)^0*a3;
basis:=IdentityMat(7,GF(q));
v1:=VectorSpace(GF(q),basis{[1..3]});
v2:=VectorSpace(GF(q),basis{[4..7]});

s:=a3*(a1*a2^(-1)*a1)^(-1);
count:=0;
repeat 
  Print(".");
  count:=count+1;
  c1:=PseudoRandom(g);
  image1:=basis{[1,4,5,6,7]}*c1;
  image2:=basis{[2,3]}*c1;
  bb:=VectorSpace(GF(q),image1);
  bbb:=VectorSpace(GF(q),Concatenation(image2,basis{[1..3]}));
  dd:=Intersection(bb,v2);
  ddd:=Intersection(bbb,v2);
until Dimension(dd)=2
 and Dimension(ddd)=2
 and Dimension(Intersection(bb,v1))=1
 and Dimension(Intersection(dd,ddd))=0;

newbasis:=basis{[1..3]};
for vec in image2 do
    vec{[1..3]}:=List([1..3],x->0*Z(q));
    Add(newbasis,vec);
od;
int:=Intersection(bb,v2);
intbasis:=Basis(int);
for vec in intbasis do
    Add(newbasis,vec);
od;    
Print("\n");
basechangemat := basechangemat * newbasis;
c:=s*s^c1*s*(a1^a3)^c1;
Display(newbasis*a1*newbasis^(-1));
Display(newbasis*a2*newbasis^(-1));
Display(newbasis*a3*newbasis^(-1));
Display(newbasis*c*newbasis^(-1));
c := newbasis*c*newbasis^(-1);
v2 := VectorSpace(GF(q),newbasis{[1..3]}*c);
int := Intersection(v1,v2);
if Dimension(int) <> 1 then Error("not good"); fi;
v := Basis(int)[1];
ch := IdentityMat(7,GF(q));
ch[3] := v;
basechangemat := basechangemat * ch;
c := ch * c * ch^-1;
w := basis[3]*c^-1;
t1 := IdentityMat(7,GF(q));
t1[1] := t1[1] + w;
Display(t1^c);
t2 := IdentityMat(7,GF(q));
t2[2] := t2[2] + w;
Display(t2^c);

#horizontal 
t3 := IdentityMat(7,GF(q));
t3[3] := t3[3] + t3[1];
Display(t3^c);
t4 := IdentityMat(7,GF(q));
t4[3] := t4[3] + t4[2];
Display(t4^c);




#Display(newbasis*(a1^a3)^c1*newbasis^(-1));
#Display(newbasis*(a1^a3)^c*newbasis^(-1));
#Display(newbasis*(a1^a2)^c*newbasis^(-1));
Print("ccccccccccc", "\n");
#Display(newbasis*(a1^a3)^cc*newbasis^(-1));
