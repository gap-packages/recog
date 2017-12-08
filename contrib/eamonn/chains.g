MyCommutator := function (x, y)
    return x^-1 * y^-1 * x * y;
end;

# list of subgroups of M11 for use in BSGS calculation

Finish := function(L)
   local r;
   for r in L do
       r.generators := SLPOfElms(r.generators);
   od;
end;

SubgroupChainsM11 := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "M11", generators :=
      [a, b], order := 95040, index := 1),

   rec( name := "A6.2", parent := "M11", generators :=
      [(a*b)^-4*a*(a*b)^4, (a*b*b)^-2*(a*b*a*b*a*b*b*a*b)*(a*b*b)^2],
      order := 720, index := 11),

   rec( name := "L2(11)", parent := "M11", generators :=
          [a, b*a*b*b*a*b], order := 660, index := 12),

   rec( name := "M9.2", parent := "M11", generators :=
       [(a*b)^-2*b*a*b, (a*b*b)^-1*b*a*b*b], order := 144, index := 110)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of M12 for use in BSGS calculation

SubgroupChainsM12 := function ()
   local g,a,b,c,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   c := ((a*b)^3 * a * b^2 * a*b*a*b^2*a*b^2)^((a*b^2)^3);
   L := [
   rec( name := "M12", generators :=
      [a, b], order := 95040, index := 1),

   rec( name := "L2(11)", parent := "M12", generators :=
      [a, (c * a * c)^3],
      order := 660, index := 144),

   rec( name := "2xS5", parent := "M12", generators :=
      [(a*b*a*b^2*a*b)^3, (a*b*(a*b*a*b^2)^2*a*b^2)^((a*b^2)^3) ],
      order := 240, index := 396)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of M22 for use in BSGS calculation

SubgroupChainsM22 := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "M22", generators :=
      [a, b], order := 443520, index := 1),

   rec( name := "L2(11)", parent := "M22", generators :=
      [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)],
      order := 660, index := 672),

   rec( name := "2^3L32", parent := "M22", generators :=
      [a, b^((a*b)^2*(a*b*a*b^2)^3)], order := 1344, index := 330)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of M23 for use in BSGS calculation

SubgroupChainsM23 := function ()
   local g,a,b,c,d,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   c := (a*b)^2*a*b^2*(a*b)^3*a*b^2*a*b*(a*b^2)^2;
   d := (((a*b)^2*a*b^2*a*b)^2*a*b^2)^2;

   L := [
   rec( name := "M23", generators :=
      [a, b], order := 10200960, index := 1),

   rec( name := "M22", parent := "M23", generators :=
      [a, (b*a)^2 * b^3 * a * b], order := 443520, index := 23),

   rec( name := "L2(11)", parent := "M22", generators :=
      [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)],
      order := 660, index := 672),

   rec( name := "A8", parent := "M23", generators :=
      [a^((a*b)^3), b^((b*a)^5)], order := 20160, index := 506),

   rec( name := "23.11", parent := "M23", generators :=
      [(a^2*b*(a*b*a*b^2)^2)^((a*b)^6), c^(d^-1)], order := 253, index := 40320)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of M24 for use in BSGS calculation

SubgroupChainsM24 := function ()
   local g,a,b,c,d,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   # standard generators for M23
   c := ((a*b*a*b*a*b^2*a*b)^4)^((a*b)^4);
   d := ((a*b*a*b*a*b^2*a*b)^2)^((a*b^2)^3);

   L := [
   rec( name := "M24", generators :=
      [a, b], order := 244823040, index := 1),

   rec( name := "M22", parent := "M24", generators :=
      [c, (d*c)^2 * d^3 * c * d], order := 443520, index :=552 ),

   rec( name := "L2(23)", parent := "M24", generators :=
      [a^(b*a*b^2), ((a*b*a*b^2)^3)^((a*b)^7)], order := 6072, index := 40320),

   rec( name := "M12.2", parent := "M24", generators :=
      [a, b^((a*b)^12*(a*b*a*b^2)^5)], order := 190080, index := 1288),

   rec( name := "L2(11):2", parent := "M12.2", generators :=
      [a, (a*b)^4], order := 1320, index := 288),

   rec( name := "L2(11)", parent := "M22", generators :=
      [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)],
      order := 660, index := 672)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of HS for use in BSGS calculation

SubgroupChainsHS := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "HS", generators :=
      [a, b], order := 44352000, index := 1),

   rec( name := "M22", parent := "HS", generators :=
      [a, ((b*a*b*a*b^2)^2)^((a*b^2)^5)], order := 443520, index :=100 ),

   rec( name := "U35:2", parent := "HS", generators :=
      [ (a*b*a*b*b)^5*(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^3*(a*b*a*b*b)^-5,
(a*b)^4*(a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b)^-4
], order := 252000, index := 176),

   rec( name := "2A5", parent := "U35:2", generators :=
      [a*b*a*b^2, b * MyCommutator((a*b*a*b^2)^5, b)],
      order := 120, index := 2100),

   rec( name := "U35:2b", parent := "HS", generators :=
      [ (a*b*a*b*b)^5*(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^3*(a*b*a*b*b)^-5,
(a*b*b)^-2*(a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b*b)^2
], order := 252000, index := 176),

   rec( name := "2A5b", parent := "U35:2b", generators :=
      [a*b*a*b^2, b * MyCommutator((a*b*a*b^2)^5, b)],
      order := 120, index := 2100),

   rec( name := "L3(4):2", parent := "HS", generators :=
      [(a*b)^-2*(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^3*(a*b)^2,
(a*b*b)^-4*(a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b*b)^4
], order := 40320, index := 1100),

   rec( name := "A5", parent := "L3(4):2", generators :=
      [b^2, a * b * (a*b*a*b^2)^2], order := 60, index := 672),

   rec( name := "S8", parent := "HS", generators :=
      [(a*b)^-6*(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^3*(a*b)^6, (a*b*b)^-7*(a*b*a*b*a*b*b)*(a*b*b)^7], order := 40320, index := 1100),

   rec( name := "M11", parent := "HS", generators :=
      [b^-1*a*b, (a*b*b)^-5*(a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b*b)^5], order := 7920, index := 5600),

   rec( name := "L2(11)", parent := "M22", generators :=
      [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)],
      order := 660, index := 672)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of McL for use in BSGS calculation

SubgroupChainsMcL := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "McL", generators :=
      [a, b], order :=  898128000, index := 1),

   rec( name := "M22", parent := "McL", generators :=
      [a^((a * b^2)^2), ((a * b * a * b * a * b^2)^2 * (a * b))^((a * b)^-4)], order := 443520, index := 2025),

   rec( name := "L2(11)", parent := "M22", generators :=
      [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)], order := 660, index := 672),

   rec( name := "U43", parent := "McL", generators :=
      [a, (a*b*b)^-5*(b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b*b)^5
], order := 3265920, index := 275),

   rec( name := "A7", parent := "U43", generators :=
    [a, (a*b*a*b*a*b*a*b*b*a*b*a*b*b)^(a*b^2)], order := 2520, index := 1296),

   rec( name := "U33", parent := "U43", generators :=
    [a, (a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b^2)], order := 6048,
index := 540),

   rec( name := "U35", parent := "McL", generators :=
      [(a*b*a*b*a*b*a*b*b*a*b*a*b*b)^-3*
(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b*a*b*b
*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b*a*b*b*a*b*a*b*b)^2 *
(a*b*a*b*a*b*a*b*b*a*b*a*b*b)^3,
(a*b*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^15 * b * (a*b*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^15 ], order := 126000, index := 7128),

   rec( name := "2S5", parent := "U35", generators :=
      [a*b^2, b * MyCommutator((a*b^2)^4, b)], order := 240, index := 525)

   ];

   Finish(L);
   return L;
end;

GeneratorsCo3Max3 := function (a,b)
   local w;

   w[1] := a; w[2] := b;

w[3]:=w[1]*w[2];
w[4]:=w[3]*w[2];
w[5]:=w[3]*w[4];
w[6]:=w[3]*w[5];
w[7]:=w[1]*w[6];
w[1]:=w[7]^11;
w[7]:=w[5]^7;
w[8]:=w[3]*w[7];
w[7]:=w[8]^-1;
w[9]:=w[7]*w[2];
w[2]:=w[9]*w[8];

   return [w[1],w[2]];

end;

GeneratorsCo3Max4 := function (a,b)
  local w;

   w[1] := a; w[2] := b;

w[3]:=w[1]*w[2];
w[4]:=w[3]*w[2];
w[5]:=w[3]*w[4];
w[1]:=w[2]*w[2];
w[7]:=w[5]^6;
w[6]:=w[3]*w[5];
w[8]:=w[6]^-1;
w[9]:=w[8]*w[7];
w[2]:=w[9]*w[6];

   return [w[1],w[2]];

end;

GeneratorsCo3Max6 := function (a,b)
  local w;

   w[1] := a; w[2] := b;

w[3]:=w[1]*w[2];
w[4]:=w[3]*w[2];
w[5]:=w[3]*w[4];
w[6]:=w[3]*w[3];
w[7]:=w[5]^3;
w[8]:=w[6]*w[7];
w[9]:=w[8]^-1;
w[6]:=w[9]*w[2];
w[2]:=w[6]*w[8];

   return [w[1],w[2]];

end;

# list of subgroups of Co3 for use in BSGS calculation

SubgroupChainsCo3 := function ()
   local g,a,b,c,d,e,f,c1,d1,a1,b1,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   e := b^(a * b * a * b * a * b^2);
   c := (e^2)^((a * e)^7);
   d := ((a * e * a * e * a * e^2 * a * e)^2)^(a * e^2);
   f := (a * b)^2 * (a*b*a*b^2)^2 * (a * b^2);

   c1 := a^((a*b^2)^3);
   d1 := ((b*(a*b)^2*a*b^2*a*b*a*b^2)^((a*b)^7))^2;

   a1 := (a^2*b*a*b*a*b*a*b^2*a*b*a*b^2)^5;
   b1 := ((a*b*a*b*a*b^2)^2)^(a*b^2);

   L := [
   rec( name := "Co3", generators :=
      [a, b], order := 495766656000, index := 1),

   rec( name := "McL", parent := "Co3", generators :=
      [(e^2)^((a * e)^2), (e * a * e * a * e * a * e^2 * a * e)^6], order :=  898128000, index := 552),

   rec( name := "M22", parent := "McL", generators :=
      [a^((a * b^2)^2), ((a * b * a * b * a * b^2)^2 * (a * b))^((a * b)^-4)], order := 443520, index := 2025),

   rec( name := "L2(11)", parent := "M22", generators :=
      [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)], order := 660, index := 672),

   rec( name := "U43", parent := "McL", generators :=
      [a, (a*b*b)^-5*(b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b*b)^5
], order := 3265920, index := 275),

   rec( name := "U35", parent := "McL", generators :=
      [(a*b*a*b*a*b*a*b*b*a*b*a*b*b)^-3*
(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b*a*b*b
*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b*a*b*b*a*b*a*b*b)^2 *
(a*b*a*b*a*b*a*b*b*a*b*a*b*b)^3,
(a*b*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^15 * b * (a*b*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^15 ], order := 126000, index := 7128),

   rec( name := "2S5", parent := "U35", generators :=
      [a*b^2, b * MyCommutator((a*b^2)^4, b)], order := 240, index := 525),

   rec( name := "HS", parent := "Co3", generators :=
      [(f^10)^((a*b)^3), f^4], order := 44352000, index := 11178),

   rec( name := "M22a", parent := "HS", generators :=
      [a, ((b*a*b*a*b^2)^2)^((a*b^2)^5)], order := 443520, index :=100),

   rec( name := "U35:2", parent := "HS", generators :=
      [ (a*b*a*b*b)^5*(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^3*(a*b*a*b*b)^-5,
(a*b)^4*(a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b)^-4
], order := 252000, index := 176),

   rec( name := "U35:2b", parent := "HS", generators :=
      [ (a*b*a*b*b)^5*(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^3*(a*b*a*b*b)^-5,
(a*b*b)^-2*(a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b*b)^2
], order := 252000, index := 176),

   rec( name := "L3(4):2", parent := "HS", generators :=
      [(a*b)^-2*(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^3*(a*b)^2,
(a*b*b)^-4*(a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b*b)^4
], order := 40320, index := 1100),

   rec( name := "S8", parent := "HS", generators :=
      [(a*b)^-6*(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^3*(a*b)^6, (a*b*b)^-7*(a*b*a*b*a*b*b)*(a*b*b)^7], order := 40320, index := 1100),

   rec( name := "M11", parent := "HS", generators :=
      [b^-1*a*b, (a*b*b)^-5*(a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b*b)^5], order := 7920, index := 5600),

   rec( name := "L2(11)a", parent := "M22a", generators :=
      [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)],
      order := 660, index := 672),

   rec( name := "U43.2^2", parent := "Co3", generators :=
      GeneratorsCo3Max3 (a,b), order := 13063680, index := 37950),

   rec( name := "2S6(2)", parent := "Co3", generators :=
      GeneratorsCo3Max6(a, b), order := 2903040, index := 170775),

   rec( name := "M23", parent := "Co3", generators :=
     GeneratorsCo3Max4 (a,b), order := 10200960, index := 48600),

   rec( name := "M22b", parent := "M23", generators :=
      [c1, (d1*c1)^2 * d1^3 * c1 * d1], order := 443520, index := 23),

   rec( name := "L2(11)b", parent := "M22b", generators :=
      [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)],
      order := 660, index := 672),

   rec( name := "A7", parent := "U43.2^2", generators :=
      [((a*b*a*b^2)^4)^((a*b)^7), (a*b*a*b*a*b^2)^2], order := 2520, index := 5184),

   rec( name := "U33", parent := "U43.2^2", generators :=
      [((a*b*a*b^2)^4)^((a*b)^5), ((a*b*a*b*a*b*a*b^2*a*b*a*b^2)^2)^((a*b^2)^3)], order := 6048, index := 2160),

   rec( name := "L28.3", parent := "2S6(2)", generators :=
   [(a1 * b1* a1 * b1^2)^2 * (a1 * b1^3 * a1 * b1^-1 * a1), b1],
    order := 1512, index := 1920),

   rec( name := "U33.2", parent := "2S6(2)", generators :=
   [a1 * b1^2 * a1 * b1 * a1 * b1^3 * a1 * b1^4 * a1, b1], order := 12096, index := 240)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of Co2 for use in BSGS calculation

SubgroupChainsCo2 := function ()
   local g,a,b,c,d,e,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   c := a * b^2 * a * b * a * b^2;
   d := a * b * a * b^2 * a * b * a * b * a * b^2;
   e := (c * d * c * d * c * d^2)^5;

   L := [
   rec( name := "Co2", generators :=
   [a, b], order := 42305421312000, index := 1),

   rec( name := "U62.2", parent := "Co2", generators :=
   [a, (a * b)^2], order := 18393661440, index := 2300),

   rec( name := "Sp62", parent := "U62.2", generators :=
   [e, d^3 * e * d^2 * e * d^4], order := 1451520, index := 12672),

   rec( name := "2^(1+8)U42", parent := "U62.2", generators :=
   [e^-1 * d^-1 * e * d, (d * e * d^4)^2], order := 13271040, index := 1386),

   rec( name := "M", parent := "2^(1+8)U42", generators :=
   [(a*b^2)^6, (a*b*a*b^2)], order := 4608, index := 2880),

   rec( name := "U52", parent := "U62.2", generators :=
   [e, e*d*e*d*e*d^3], order := 13685760, index := 1344),

   rec( name := "U42", parent := "U52", generators :=
   [a^((b * a)^5), (b^4 * a * b^3)^3], order := 25920, index := 528),

   rec( name := "L28.3", parent := "Sp62", generators :=
   [(a * b* a * b^2)^2 * (a * b^3 * a * b^-1 * a), b], order := 1512, index := 960),

   rec( name := "U33.2", parent := "Sp62", generators :=
   [a * b^2 * a * b * a * b^3 * a * b^4 * a, b], order := 12096, index := 120)
   ];

   Finish(L);
   return L;

end;

# list of subgroups of Co1 for use in BSGS calculation

SubgroupChainsCo1 := function ()
   local g,a,b,c,d,e,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   c := a * b^2 * a * b * a * b^2;
   d := a * b * a * b^2 * a * b * a * b * a * b^2;
   e := (c * d * c * d * c * d^2)^5;

   L := [
   rec( name := "Co1", generators :=
   [a, b], order := 4157776806543360000, index := 1),

   rec( name := "Co2", parent := "Co1", generators :=
   [(a*b*b)^22*(a*b)^20*(a*b*b)^18, (a*b*a*b*a*b*b*a*b*a*b*b)^28*
    (a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)^6*
    (a*b*a*b*a*b*b*a*b*a*b*b)^14
   ], order := 42305421312000, index := 98280),

   rec( name := "U62.2", parent := "Co2", generators :=
   [a, (a * b)^2], order := 18393661440, index := 2300),

   rec( name := "Sp62", parent := "U62.2", generators :=
   [e, d^3 * e * d^2 * e * d^4], order := 1451520, index := 12672),

   rec( name := "2^(1+8)U42", parent := "U62.2", generators :=
   [e^-1 * d^-1 * e * d, (d * e * d^4)^2], order := 13271040, index := 1386),

   rec( name := "M", parent := "2^(1+8)U42", generators :=
   [(a*b^2)^6, (a*b*a*b^2)], order := 4608, index := 2880),

   rec( name := "U52", parent := "U62.2", generators :=
   [e, e*d*e*d*e*d^3], order := 13685760, index := 1344),

   rec( name := "U42", parent := "U52", generators :=
   [a^((b * a)^5), (b^4 * a * b^3)^3], order := 25920, index := 528),

   rec( name := "L28.3", parent := "Sp62", generators :=
   [(a * b* a * b^2)^2 * (a * b^3 * a * b^-1 * a), b], order := 1512, index := 960),

   rec( name := "U33.2", parent := "Sp62", generators :=
   [a * b^2 * a * b * a * b^3 * a * b^4 * a, b], order := 12096, index := 120)
   ];

   Finish(L);
   return L;

end;

# list of subgroups of J2 for use in BSGS calculation

SubgroupChainsJ2 := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "J2",  generators :=
      [a, b], order := 604800, index := 1),

   rec( name := "U3(3)", parent := "J2", generators :=
      [(a*b*a*b^2)^6, ((a*b*a*b^2)^2)^((a*b*a*b*a*b^2)^2*(a*b*a*b))
], order :=  6048, index := 100),

   rec( name := "L3(2):2", parent := "J2", generators :=
      [a, (a*b*a*b^2*a*b)^3
], order := 336, index := 1800),

   rec( name := "2^(1+4)A5", parent := "J2", generators :=
      [a, ((a*b*a*b^2)^2)^(a*b*a*b*a*b^2*a*b) ], order := 1920, index := 315)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of Suz for use in BSGS calculation

SubgroupChainsSuz := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "Suz", generators :=
      [a, b], order := 448345497600, index := 1),

   rec( name := "G24", parent := "Suz", generators :=
      [(a*b)^-5*(a*b*a*b*a*b*b)^6*(a*b)^5,
      (a*b*b)^-4*(a*b*a*b*b)^3*(a*b*b)^4],
      order := 251596800, index := 1782),

   rec( name := "U52", parent := "Suz", generators :=
      [ (a*b*a*b*a*b*b*a*b*a*b*b)^4, (a*b*a*b*a*b*b*a*b)^9*(a*b*a*b*a*b*b*a*b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)^6*(a*b*a*b*a*b*b*a*b)^-9 ],
     order := 13685760, index := 32760),

   rec( name := "L2(11)", parent := "U52", generators :=
      [((a*b*a*b*a*b*a*b^2*a*b*a*b^2*a*b^2)^3)^((a*b)^4), (b*a*b*a*b^2*(a*b)^3*(a*b*a*b^2)^2)^2], order := 660, index := 20736),

   rec( name := "J2", parent := "G24", generators :=
      [(a*b*a*b*a*b*a*b^2*a*b*a*b^2*a*b^2)^3, ((a*b*a*b*a*b^2*a*b*a*b^2)^5)^((a*b^2)^4)], order := 604800, index := 416),

   rec( name := "U3(3)", parent := "J2", generators :=
      [(a*b*a*b^2)^6, ((a*b*a*b^2)^2)^((a*b*a*b*a*b^2)^2*(a*b*a*b))
], order :=  6048, index := 100),

   rec( name := "L3(2):2", parent := "J2", generators :=
      [a, (a*b*a*b^2*a*b)^3
], order := 336, index := 1800),

   rec( name := "U3(4):2", parent := "G24", generators :=
      [((a*b*a*b*a*b*a*b^2*a*b*a*b^2*a*b^2)^3)^((a*b)^4),
       ((a*b*a*b*a*b^2*a*b*a*b^2)^10)^((a*b^2)^4)],
     order := 124800, index := 2016),

   rec( name := "2xA5", parent := "U3(4):2", generators :=
   [a * b * a * b * a * b^2, MyCommutator ((a * b * a * b * a * b^2)^5,
b)^5 ], order := 120, index := 1040),

   rec( name := "U42", parent := "U52", generators :=
   [a^((b * a)^5), (b^4 * a * b^3)^3], order := 25920, index := 528)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of Fi22 for use in BSGS calculation

SubgroupChainsFi22 := function ()
   local L,a,b,c,d,e,g;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   c := (a * b * a * b * a * b^2)^2 * (a * b);
   d := (c^13)^((a * b)^-13);
   e := (c^24)^((a*b^2)^-11);

   L := [
   rec( name := "Fi22", generators :=
   [a, b], order := 64561751654400, index := 1),

   rec( name := "2.U62", parent := "Fi22", generators :=
   [(a*b)^-5*a*(a*b)^5, (a*b*b)^3], order := 18393661440, index := 3510),

   rec( name := "Sp62", parent := "2.U62", generators :=
   [a, b^3 * a * b^2 * a * b^4], order := 1451520, index := 12672),

   rec( name := "2.2^(1+8)U42", parent := "2.U62",
   generators := [a^-1 * b^-1 * a * b, (b * a * b^4)^2],
   order := 26542080, index := 1386),

   rec( name := "M", parent := "2.2^(1+8)U42", generators :=
   [(a*b^2)^6, (a*b*a*b^2)], order := 9216, index := 5760),

   rec( name := "2xU52", parent := "2.U62", generators :=
   [a, a*b*a*b*a*b^3], order := 27371520, index := 672),

   rec( name := "2xU42", parent := "2xU52", generators :=
   [a^((b * a)^5), (b^4 * a * b^3)^3], order := 51840, index := 528),

   rec( name := "L28.3", parent := "Sp62", generators :=
   [(a * b* a * b^2)^2 * (a * b^3 * a * b^-1 * a), b], order := 1512, index := 960)
,
   rec( name := "U33.2", parent := "Sp62", generators :=
   [a * b^2 * a * b * a * b^3 * a * b^4 * a, b], order := 12096, index := 120)
   ];

   Finish(L);
   return L;

end;

# list of subgroups of Fi23 for use in BSGS calculation

SubgroupChainsFi23 := function ()
   local L,a,b,c,d,e,g;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   c := (a * b * a * b * a * b^2)^2 * (a * b);
   d := (c^13)^((a * b)^-13);
   e := (c^24)^((a*b^2)^-11);

   L := [

   rec( name := "Fi23",  generators :=
   [a, b], order := 4089470473293004800, index := 1),

   rec( name := "2.Fi22", parent := "Fi23", generators :=
   [(d * e)^11 * d, e], order := 129123503308800, index := 31671),

   rec( name := "2^2.U62", parent := "2.Fi22", generators :=
   [(a*b)^-5*a*(a*b)^5, (a*b*b)^3], order := 36787322880, index := 3510),

   rec( name := "2.Sp62", parent := "2^2.U62", generators :=
   [a, b^3 * a * b^2 * a * b^4], order := 2903040, index := 12672),

   rec( name := "2^(3+8)U42", parent := "2^2.U62",
   generators := [a^-1 * b^-1 * a * b, (b * a * b^4)^2],
   order := 53084160, index := 693),

   rec( name := "M", parent := "2^(3+8)U42", generators :=
   [(a*b^2)^6, (a*b*a*b^2)], order := 9216, index := 5760),

   rec( name := "2^2xU52", parent := "2^2.U62", generators :=
   [a, a*b*a*b*a*b^3], order := 54743040, index := 672),

   rec( name := "2^2xU42", parent := "2^2xU52", generators :=
   [a^((b * a)^5), (b^4 * a * b^3)^3], order := 103680, index := 528),

   rec( name := "2xL28.3", parent := "2.Sp62", generators :=
   [(a * b* a * b^2)^2 * (a * b^3 * a * b^-1 * a), b], order := 3024, index := 960),

   rec( name := "2xU33.2", parent := "2.Sp62", generators :=
   [a * b^2 * a * b * a * b^3 * a * b^4 * a, b], order := 24192, index := 120)

   ];

   Finish(L);
   return L;

end;

# list of subgroups of Fi24 for use in BSGS calculation

SubgroupChainsFi24 := function ()
   local L,a,b,c,d,e,g;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   c := (a * b * a * b * a * b^2)^2 * (a * b);
   d := (c^13)^((a * b)^-13);
   e := (c^24)^((a*b^2)^-11);

   L := [
   rec( name := "Fi24", generators :=
   [a, b], order := 1255205709190661721292800, index := 1),

   rec( name := "Fi23", parent := "Fi24", generators :=
   [a, ((a * b * a * b^2 * (a * b)^4 * (a * b^2 * a * b * a * b^2 * a * b^2)^2 * a * b * a * b^2)^4)^((a * b^2)^5)], order :=4089470473293004800,
index := 306936),

   rec( name := "2.Fi22", parent := "Fi23", generators :=
   [(d * e)^11 * d, e], order := 129123503308800, index := 31671),

   rec( name := "2^2.U62", parent := "2.Fi22", generators :=
   [(a*b)^-5*a*(a*b)^5, (a*b*b)^3], order := 36787322880, index := 3510),

   rec( name := "Sp62", parent := "2^2.U62", generators :=
   [a, b^3 * a * b^2 * a * b^4], order := 1451520, index := 12672),

   rec( name := "2^(1+8)U42", parent := "2^2.U62",
   generators := [a^-1 * b^-1 * a * b, (b * a * b^4)^2],
   order := 13271040, index := 1386),

   rec( name := "M", parent := "2^(1+8)U42", generators :=
   [(a*b^2)^6, (a*b*a*b^2)], order := 4608, index := 2880),

   rec( name := "U52", parent := "2^2.U62", generators :=
   [a, a*b*a*b*a*b^3], order := 13685760, index := 1344),

   rec( name := "U42", parent := "U52", generators :=
   [a^((b * a)^5), (b^4 * a * b^3)^3], order := 25920, index := 528),

   rec( name := "L28.3", parent := "Sp62", generators :=
   [(a * b* a * b^2)^2 * (a * b^3 * a * b^-1 * a), b], order := 1512, index := 960),

   rec( name := "U33.2", parent := "Sp62", generators :=
   [a * b^2 * a * b * a * b^3 * a * b^4 * a, b], order := 12096, index := 120)

   ];

   Finish(L);
   return L;

end;

# list of subgroups of He for use in BSGS calculation

SubgroupChainsHe := function ()
   local L,a,b,c,g;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   c := (a*b)^3*(a*b^2*a*b*a*b^2);
   L := [
   rec( name := "He", generators :=
      [a, b], order := 4030387200, index := 1),

   rec( name := "S4(4):2", parent := "He", generators :=
     [a, (a*b*b)^-7*(b*a*b*a*b*a*b*a*b*b*a*b*a*b*b)^7*(a*b*b)^7],
      order := 1958400, index := 2058),

   rec( name := "2^2.L3(4).S3,", parent := "He", generators :=
      [a, a*b*a*b^2 ], order := 483840, index := 8330),

   rec( name := "2^6A5", parent := "S4(4):2", generators :=
     [c^2, (c^2)^(a*b^2)], order := 3840, index := 510),

   rec( name := "L2(16)", parent := "S4(4):2", generators :=
     [b^2 * a*b*(a*b*a*b^2)^2, (a*b*(a*b*a*b^2)^2)*(b^2)], order := 4080, index := 480)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of HN for use in BSGS calculation

SubgroupChainsHN := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "HN", generators :=
   [a, b], order := 273030912000000, index := 1),

   rec( name := "A12", parent := "HN", generators :=
       [a, (a * b * a * b * a * b * a * b^2 * a * b * a * b^2 * a * b^2)^5], order := 239500800, index := 1140000),

   rec( name := "A9", parent := "A12", generators :=
       [(a * b * a * b^2)^2, (a * b * a * b * a * b^2 * a * b)^2],
         order := 181440, index := 1320),

   rec( name := "A6", parent := "A9", generators :=
       [(a * b * a * b^2)^4, (a * b * a * b * a * b * a * b^2 *
                  a * b * a * b^2 * a * b^2 * a * b^2)^3],
       order := 360, index := 504)
   ];

   Finish(L);
   return L;

end;

# list of subgroups of Th for use in BSGS calculation

SubgroupChainsTh := function ()
   local L,a,b,c,d,g;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   c := ((a*b*a*b^2)^9)^((a*b)^5);
   d := ((a*b*a*b^2)^2)^((a*b^2)^6);

   L := [
   rec( name := "Th", generators :=
      [a, b], order := 90745943887872000, index := 1),

   rec( name := "3D4(2):3", parent := "Th", generators :=
      [(a*b)^-8*a*(a*b)^8, (a*b*a*b*a*b*b*(a*b)^4*a*b*b*a*b*a*b*b)^5],
     order := 634023936, index := 143127000),

   rec( name := "2^5.L52", parent := "Th", generators :=
      [a, ((a*b*b*a*b)^2)^((a*b)^15*(a*b*b)^9*(a*b)^12*(a*b*b)^16*(a*b)^17) ], order := 319979520, index := 283599225),

   rec( name := "2^(1+8):L28", parent := "3D4(2):3",
     generators :=
      [(c*d*c*d*c*d^2)^3, (c*d*c*d*c*d^2*c*d)^2], order := 258048,
       index := 2457),

   rec( name := "2^11(7xS3)", parent := "3D4(2):3", generators :=
      [c, (c*d*c*d^4)^2], order := 86016, index := 7371),

   rec( name := "U33.2", parent := "3D4(2):3", generators :=
      [(c*d*c*d*c*d^2)^3, d^((c*d*c*d^2)^7)], order := 12096, index :=52416 ),

   rec( name := "L28", parent := "2^(1+8):L28", generators :=
      [a, b^((a*b^2)^6)], order := 504, index := 512)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of J1 for use in BSGS calculation

SubgroupChainsJ1 := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "J1", generators :=
   [a, b], order := 175560, index := 1),

   rec( name := "L211", parent := "J1", generators :=
   [(a*b)^-2*b*a*b, (a*b*a*b*b)^-4*b*(a*b*a*b*b)^4], order := 660,
   index := 266),

   rec( name := "2xA5", parent := "J1", generators :=
      [a, ((a*b*(a*b*a*b^2)^2)^3)^(a*b*(a*b*a*b^2)^4)],
      order := 120, index := 1463)
   ];

   Finish(L);
   return L;

end;

# list of subgroups of O'Nan for use in BSGS calculation

SubgroupChainsON := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "ON", generators :=
   [a, b], order := 460815505920, index := 1),

   rec( name := "4.L3(4):2", parent := "ON", generators :=
   [MyCommutator((a*b*a*b*b)^10,b)^14, a*b*a*b*b],
    order := 161280, index := 2857239),

   rec( name := "J1", parent := "ON", generators :=
   [(a*b*b)^-7 * a*(a*b*b)^7, (a*b*a*b*b)^-6 * (a*b*a*b*a*b*a*b*
    b*a*b*a*b*b)^4 * (a*b*a*b*b)^6], order := 175560, index := 2624832),

   rec( name := "L3(7):2", parent := "ON", generators :=
   [b^-1*a*b, (a*b*b)^-2 * b * (a*b*b)^2],
   order := 3753792, index := 122760),

   rec( name := "L3(7):2b", parent := "ON", generators :=
   [b*a*b^-1, (a*b*b)^-2 * b*b * b * (a*b*b)^2],
   order := 3753792, index := 122760),

   rec( name := "M", parent := "4.L3(4):2", generators :=
   [a, (a * b)^2], order := 336, index := 480),

   rec( name := "2.(2 x L2(7)).2", parent := "L3(7):2",
   generators := [((a^b)*(a*b*a*b*a*b*b)^14)^3, a*b*a*b*a*b*b],
   order := 1344, index := 2793),

   rec( name := "2.(2 x L2(7)).2b", parent := "L3(7):2b",
   generators := [((a^b)*(a*b*a*b*a*b*b)^14)^3, a*b*a*b*a*b*b],
   order := 1344, index := 2793),

   rec( name := "7^(1 + 2):(3 x D8)", parent := "L3(7):2",
   generators := [a^((a* b)^2), (a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^2],
   order := 8232, index := 456),

   rec( name := "7^(1 + 2):(3 x D8)b", parent := "L3(7):2b",
   generators := [a^((a* b)^2), (a*b*a*b*a*b*b*a*b*a*b*b*a*b*b)^2],
   order := 8232, index := 456),

   rec( name := "L211", parent := "J1", generators :=
   [(a*b)^-2*b*a*b, (a*b*a*b*b)^-4*b*(a*b*a*b*b)^4], order := 660,
   index := 266)

   ];

   Finish(L);
   return L;

end;

# list of subgroups of Ly for use in BSGS calculation

SubgroupChainsLy := function ()
   local L,a,b,c,d,g;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   # standard generators for 3McL in 3McL.2
   c := (a*b)^-1*(a*b*a*b*a*b*b*a*b*a*b*a*b*b*a*b)^12*a*b;
   d := (a*b*b)^-3*(a*b*a*b*b)^3*(a*b*b)^3;

   L := [
   rec( name := "Ly", generators :=
      [a, b], order :=  51765179004000000, index := 1),

   rec( name := "G25", parent := "Ly", generators :=
      [(a*b*a*b*b*b)^7*a*(a*b*a*b*b*b)^-7,
(a*b*a*b*a*b*b)^-25*(a*b*a*b*a*b*b*a*b)^3*(a*b*a*b*a*b*b)^25
], order := 5859000000, index := 8835156),

   rec( name := "3.McL.2", parent := "Ly", generators :=
      [ (a*b*a*b*a*b*b)^15*a*(a*b*a*b*a*b*b)^-15,
(b*a*b*a*b*b)^-12*(a*b*a*b*a*b*b*a*b)^3*(b*a*b*a*b*b)^12
], order :=  5388768000, index := 9606125),

   rec( name := "3M22", parent := "3.McL.2", generators :=
  [c^((c * d^2)^2), ((c * d * c * d * c * d^2)^2 * (c * d))^((c * d)^-4)], order := 443520, index := 4050),

   rec( name := "3xL2(11)", parent := "3M22", generators :=
 [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)], order := 1980,
     index := 672),

   rec( name := "3U43", parent := "3.McL.2", generators :=
  [c, (c*d*d)^-5*(d*c*d*c*d*c*d*c*d*d*c*d*c*d*d)*(c*d*d)^5
], order := 9797760, index := 550),

   rec( name := "3A7", parent := "3U43", generators :=
    [a, (a*b*a*b*a*b*a*b*b*a*b*a*b*b)^(a*b^2)], order := 7560, index := 1296),

   rec( name := "3U33", parent := "3U43", generators :=
    [a, (a*b*a*b*a*b*a*b*b*a*b*a*b*b)*(a*b^2)], order := 18144,
index := 540),

   rec( name := "3U35", parent := "3.McL.2", generators :=
     [(c*d*c*d*c*d*c*d*d*c*d*c*d*d)^-3*
(c*d*c*d*c*d*c*d*d*c*d*c*d*d*c*d*d*c*d*d
*c*d*c*d*c*d*c*d*c*d*d*c*d*c*d*d*c*d*d*c*d*d*c*d*c*d*d)^2 *
(c*d*c*d*c*d*c*d*d*c*d*c*d*d)^3,
(c*d*d*c*d*c*d*c*d*c*d*d*c*d*c*d*d*c*d*d)^15 * d * (c*d*d*c*d*c*d*c*d*c*d*d*c*d*c*d*d*c*d*d)^15 ],
order := 378000, index := 14256),

   rec( name := "3x2S5", parent := "3U35", generators :=
      [a*b^2, b * MyCommutator((a*b^2)^4, b)], order := 720, index := 525),

   rec( name := "L35.2", parent := "G25", generators :=
      [a, b^((a*b*a*b*a*b^2)^12)], order :=  744000, index := 7875),

   rec( name := "3U35.2", parent := "G25", generators :=
      [a * b * a * b^2 * (a * b)^4, (a*b^2)^5*
       (a*b* a* b* a * b^2 * a * b* a * b^2)^3 * (a * b^2)^2],
       order :=  756000, index := 7750),

   rec( name := "2A5", parent := "3U35.2", generators :=
      [ a * b, (a * (a * b)^5)^4], order := 120, index := 6300),

   rec( name := "2xS5", parent := "L35.2", generators :=
      [ a * b, (a * (a * b)^5)^2 * a], order := 240, index := 3100)
   ];

   Finish(L);
   return L;
end;

#  list of subgroups of J3 for use in BSGS calculation

SubgroupChainsJ3 := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "J3", generators :=
      [a, b], order := 50232960, index := 1),

   rec( name := "L2(19)", parent := "J3", generators :=
      [a^b, ((a*b*a*b*b)^3)^((a*b*b)^4)], order :=  3420, index := 14688),

   rec( name := "L2(19)b", parent := "J3", generators :=
      [a^(b^2), ((a*b*b*a*b)^3)^((a*b)^4)], order :=  3420, index := 14688),
   rec( name := "L2(16):2", parent := "J3", generators :=
      [a, (a*b*a*b*a*b*b*a*b*a*b*b)^6], order :=  8160, index := 6156),

   rec( name := "L2(17)", parent := "J3", generators :=
      [a^((a*b)^2), ((a*b*a*b^2)^3)^((a*b^2)^5)], order :=  2448,
      index := 20520 )
   ];

   Finish(L);
   return L;
end;

# list of subgroups of J4 for use in BSGS calculation

SubgroupChainsJ4 := function ()
   local L,a,b,c,d,g;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   # standard generators for M23
   c := ((a*b*a*b*a*b^2*a*b)^4)^((a*b)^4);
   d := ((a*b*a*b*a*b^2*a*b)^2)^((a*b^2)^3);

   L := [
   rec( name := "J4", generators :=
      [a, b], order := 86775571046077562880, index := 1),

   rec( name := "2^11.M24", parent := "J4", generators :=
      [ b^-1*a*b, (a*b^3)^-1*(a*b*a*b*a*b*b)^8*a*b^3], order := 501397585920, index := 173067389),

   rec( name := "M24", parent := "2^11.M24", generators :=
      [a, ((a*b*a*b*a*b^2*a*b*a*b^2)^8)^((a*b^2)^12)], order := 244823040, index := 2048),

   rec( name := "M22", parent := "M24", generators :=
      [c, (d*c)^2 * d^3 * c * d], order := 443520, index := 552),

   rec( name := "L2(11)", parent := "M22", generators :=
      [a, (a * b^2)^((a * b)^2 * (a * b * a * b^2)^3)],
      order := 660, index := 672)
   ];

   Finish(L);
   return L;
end;

# list of subgroups of Ru for use in BSGS calculation

SubgroupChainsRu := function ()
   local g,a,b,L;

   g:=GeneratorsWithMemory([(),()]); a := g[1]; b := g[2];

   L := [
   rec( name := "Ru", generators :=
      [a, b], order := 145926144000, index := 1),

   rec( name := "TF42", parent := "Ru", generators :=
      [b^2, (a*b*a*b*a*b*b*(a*b*a*b*a*b*b*a*b*a*b*b)^3)^-1*b*(a*b*a*b*a*b*b*(a*b*a*b*a*b*b*a*b*a*b*b)^3)
], order := 35942400, index := 4060),

   rec( name := "2^6U33.2", parent := "Ru", generators :=
      [b*b, (a*b*a*b*a*b*b)^-1*(a*b*a*b*a*b*b*a*b*a*b*b)^5*(a*b*a*b*a*b*b) ],
      order := 774144, index := 188500),

   rec( name := "L2(25)", parent := "TF42", generators :=
      [(a*b*b)^4, ((a*b)^4)^((a*b*a*b*a*b^2)^5)], order := 7800,
      index := 4608),

   rec( name := "L33", parent := "TF42", generators :=
      [(a*b*b)^4, ((a*b)^4)^((a*b*a*b*a*b^2*a*b*a*b^2)^6) ],
      order := 5616, index := 6400)
   ];

   Finish(L);
   return L;
end;

