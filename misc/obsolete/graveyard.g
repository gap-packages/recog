          # They even differ only by a scalar from the base field:
          pos := PositionNonZero(newgens[1][1]);
          blpos := QuoInt(blpos+subdim-1,subdim);
          prototype := ExtractSubMatrix(newgens[1],[1..subdim],
                                        [(blpos-1)*subdim..blpos*subdim]);
          inblpos := pos - (blpos-1)*subdim;
          # now pos = (blpos-1)*subdim + inblpos and 1 < inblpos <= subdim
          homgens := [];
          for i in [1..Length(newgens)] do


  # First find a (projective) involution:
  count := 0;
  while true do   # will be left by break or return
      x := PseudoRandom(G);
      o := ProjectiveOrder(x)[1];
      if IsEvenInt(o) then
          x := x^(o/2);
          break;
      fi;
      count := count + 1;
      if count > 100 then 
          Info(InfoRecog,2,"D247: Did not find projective involution.");
          return fail; 
      fi;
  od;

  Print("D247: Trying 21 involutions...\n");

  for i in [1..20] do
      count := 0;
      while true do  # will be left by break or return
          y := PseudoRandom(G);
          c := Comm(x,y);
          o := ProjectiveOrder(c)[1];
          if IsEvenInt(o) then
            x := c^(o/2);
            break;
          else
            z := y*c^((o-1)/2);   # this is evenly distributed in C_g(x)
            o := ProjectiveOrder(z)[1];
            if IsEvenInt(o) then
                x := z^(o/2);
                break;
            fi;
            # otherwise simply try again
          fi;
          count := count + 1;
          if count > 100 then
              Info(InfoRecog,2,"D247: Did not find projective involution (2).");
              return fail;
          fi;
      od;
      Print(".\c");
      res := CheckNormalClosure(x);
      if res in [true,false] then return res; fi;
  od;

# From tensor.gi:

#  # Now we really have a tensor decomposition!
#   # Try to do recognition of the normal subgroup:
#   gensNbig := List(StripMemory(GeneratorsOfGroup(N)),x->r.t*x*r.ti);
#   gensNsmall := List(gensNbig,x->x{[1..r.blocksize]}{[1..r.blocksize]});
#   for i in gensNsmall do ConvertToMatrixRep(i); od;
# 
#   # Throw in the scalars for any case:
#   Add(gensNbig,gensNbig[1]^0);
#   Add(gensNsmall,gensNsmall[1]^0 * PrimitiveRoot(f));
#   Nsmall := GroupWithGenerators(gensNsmall);
# 
#   # Now try to recognise the small matrix group:
#   Info(InfoRecog,2,"Going to the kernel...");
#   riker := RecogniseGeneric(Nsmall,FindHomDbMatrix,ri!.depth+1);
#   if not(IsReady(riker)) then
#       return fail;
#   fi;
# 
#   # First part of our "nice" gens:
#   niceN := CalcNiceGens(riker,gensNbig);
# 
#   # Divide away elements of N from the generators of G:
#   gensGN := GeneratorsWithMemory(Concatenation(conjgensG,niceN));
#   conjgensG := gensGN{[1..Length(conjgensG)]};
#   niceN := gensGN{[Length(conjgensG)+1..Length(gensGN)]};
#   gensH := [];
#   for g in gensGN{[1..Length(conjgensG)]} do
#       gg := StripMemory(g);
#       pos := PositionNonZero(gg[1]);
#       blockpos := QuoInt(pos-1,r.blocksize)+1;
#       gsmall := gg{[1..r.blocksize]}
#                   {[(blockpos-1)*r.blocksize+1..blockpos*r.blocksize]};
#       ConvertToMatrixRep(gsmall);
#       s := SLPforElement(riker,gsmall);
#       if s = fail then
#           # Something is seriously wrong, we give up:
#           Error();
#           Info(InfoRecog,1,"Something is seriously wrong, giving up.");
#           return fail;
#       fi;
#       n := ResultOfStraightLineProgram(s,niceN);
#       gg := n^-1*g;
#       # Now gg should be a block matrix having only scalar blocks:
#       Add(gensH,gg);
#   od;
# 
#   # Check and collaps gensH:
#   gensHcol := [];
#   for g in gensH do
#       gg := StripMemory(g);
#       col := RECOG.IsKroneckerProduct(g,r.blocksize);
#       if col[1] = false or not(IsOne(col[2])) then
#           Info(InfoRecog,1,"Something is seriously wrong (2), ",
#                "giving up.");
#           return fail;
#       fi;
#       Add(gensHcol,col[3]);
#   od;
#   Add(gensH,gensH[1]^0);
#   Add(gensHcol,gensHcol[1]^0*PrimitiveRoot(f));
# 
#   # Recognise this covering group of the group H:
#   rifac := RecogniseGeneric(GroupWithGenerators(gensHcol),
#                             FindHomDbMatrix,ri!.depth+1);
# 
#   if not(IsReady(rifac)) then
#       Info(InfoRecog,2,"Failed to recognise collapsed group, giving up.");
#       return fail;
#   fi;
# 
#   # Determine our "nicegens":
#   niceH := CalcNiceGens(rifac,StripMemory(gensH));
# 
#   # Now store all the necessary information:
#   ri!.t := r.t;
#   ri!.ti := r.ti;
#   ri!.blocksize := r.blocksize;
#   SetRIKer(ri,riker);
#   SetRIParent(riker,ri);
#   SetRIFac(ri,rifac);
#   SetRIParent(rifac,ri);
#   ri!.nicegensconj := Concatenation(StripMemory(niceN),niceH);
#   SetNiceGens(ri,List(ri!.nicegensconj,x->ri!.ti * x * ri!.t));
#   ri!.nrniceN := Length(niceN);
#   ri!.nrniceH := Length(niceH);
#   ri!.gensHslp := SLPOfElms(gensH);
#   SetgensN(ri,gensNbig);
#   SetgensNslp(ri,SLPOfElms(GeneratorsOfGroup(N)));
#   SetFilterObj(ri,IsReady);
#   ri!.donotrecurse := true;
#   Setcalcnicegens(ri,CalcNiceGensTensor);
#   Setslpforelement(ri,SLPforElementTensor);
#   SetFilterObj(ri,IsTensorNode);
# 
#   return true;
# end;
#   
# InstallGlobalFunction( CalcNiceGensTensor, 
#   function( ri, origgens )
#   local geH,geHnice,geN,geNnice,gensGN;
#   # Calc preimages of the generators of N, then ask kernel to calc
#   # preimages of the nice generators:
#   geN := ResultOfStraightLineProgram(gensNslp(ri),origgens);
#   Add(geN,geN[1]^0);  # The subnode wants the extra generator
#   geNnice := CalcNiceGens(RIKer(ri),geN);
#   # Make preimages of generators of H:
#   gensGN := Concatenation(origgens,geNnice);
#   geH := ResultOfStraightLineProgram(ri!.gensHslp,gensGN);
#   # and go to preimages of nice generators:
#   Add(geH,geH[1]^0);
#   geHnice := CalcNiceGens(RIFac(ri),geH);
#   return Concatenation(geNnice,geHnice);
# end);
# 
# InstallGlobalFunction( SLPforElementTensor,
#   function( ri, x)
#   # First do the basechange:
#   local blockpos,col,h,n,nr1,nr2,pos,s1,s2,sublist,xx,xxsmall,yy;
#   xx := ri!.t * x * ri!.ti;
#   # Now cut out a non-vanishing block for the N-part:
#   pos := PositionNonZero(xx[1]);
#   blockpos := QuoInt(pos-1,ri!.blocksize)+1;
#   xxsmall := ExtractSubMatrix(xx,[1..ri!.blocksize],
#                [(blockpos-1)*ri!.blocksize+1..blockpos*ri!.blocksize]);
#   # FIXME:
#   ConvertToMatrixRep(xxsmall);
#   s2 := SLPforElement(RIKer(ri),xxsmall);
#   if s2 = fail then return fail; fi;  
#   n := ResultOfStraightLineProgram(s2,ri!.nicegensconj{[1..ri!.nrniceN]});
#   yy := n^-1 * xx;
#   sublist := [1,ri!.blocksize+1 .. Length(yy)-ri!.blocksize+1];
#   col := ExtractSubMatrix(yy,sublist,sublist);   # Collapse
#   s1 := SLPforElement(RIFac(ri),col);
#   h := ResultOfStraightLineProgram(s1,
#                 ri!.nicegensconj{[ri!.nrniceN+1..Length(ri!.nicegensconj)]});
#   if n*h <> xx then   # something is wrong, maybe with the center?
#       Error("Something is wrong!");
#   fi;
#   nr2 := NrInputsOfStraightLineProgram(s2);
#   nr1 := NrInputsOfStraightLineProgram(s1);
#   return NewProductOfStraightLinePrograms( s2,[1..nr2],s1,[nr2+1..nr1+nr2],
#                                            nr1+nr2 );
# end);

#AddMethod( FindHomDbMatrix, FindHomMethodsMatrix.TensorDecomposable,
#           550, "TensorDecomposable",
#           "tries to find a tensor decomposition" );

  v := ZeroMutable(int[1]);
  w := ZeroMutable(int[2]);
  one := One(r.f);
  v[2*r.n-1] := one;
  w[2*r.n]   := one;
  vorig := ShallowCopy(v);
  worig := ShallowCopy(w);
  vv := int[1];
  ww := int[2];
  n := r.n;
  # We want to put together an element that maps e_n to vv and f_n to ww:
  # We start with (v,w)=(e_n,f_n) and apply transvections...
  t := One(r.g);
  for i in [1..r.n-1] do
    ei := 2*i-1;  # these are the coordinates to modify
    fI := 2*i;
    if IsZero(vv[ei]) then
      if not(IsZero(vv[fI])) then
        s := vv[fI];
        si := IntFFE(s);
        t := t * fnfi[i]^si;
        v[fI] := vv[fI];
        v[2*n] := v[2*n] + s;
        Assert(0,v=vorig*t and w = worig*t);
        Print("Hallo1\n");
      fi;
    elif not(IsZero(vv[ei] + one)) then   
      # one easy case:
      # we know that v[pos+1] = 0 and v[2*n-1] = 1 and
      #              w[pos+1] = 0 and w[2*n-1] = 0
      s := vv[ei];
      si := IntFFE(s);
      t := t * fnei[i]^si;
      v[ei] := vv[ei];
      v[2*n] := v[2*n] + s;
      Assert(0,v=vorig*t and w = worig*t);
      Print("Hallo2\n");
      if not(IsZero(vv[fI])) then
        s := vv[fI]/(one+vv[ei]);
        si := IntFFE(s);
        t := t * fnfi[i]^si;
        v[fI] := vv[fI];
        v[2*n] := v[2*n] + vv[fI];
        Assert(0,v=vorig*t and w = worig*t);
        Print("Hallo3\n");
      fi;
    elif not(IsZero(vv[fI] - one)) then
      # another easy case:
      # we know that v[pos+1] = 0 and v[2*n-1] = 1 and
      #              w[pos+1] = 0 and w[2*n-1] = 0
      s := vv[fI];
      si := IntFFE(s);
      t := t * fnfi[i]^si;
      v[fI] := vv[fI];
      v[2*n] := v[2*n] + s;
      Assert(0,v=vorig*t and w = worig*t);
      Print("Hallo4\n");
      s := vv[ei]/(one-vv[fI]);
      si := IntFFE(s);
      t := t * fnei[i]^si;
      v[ei] := vv[ei];
      v[2*n] := v[2*n] + vv[ei];
      Assert(0,v=vorig*t and w = worig*t);
      Print("Hallo5\n");
    else
      # now the difficult case vv[ei] = -one and vv[fI] = one
      # multiply by [[a,0],[0,a^-1]], then standard case, then back...
      if Size(r.f) = 2 then
          Error("Does not work for GF(2).");
      fi;
      t := t * zn;
      v[2*n-1] := v[2*n-1] * zeta;
      v[2*n] := v[2*n] * zeta^-1;
      w[2*n-1] := w[2*n-1] * zeta;
      w[2*n] := w[2*n] * zeta^-1;
      Assert(0,v=vorig*t and w = worig*t);
      Print("Hallo6\n");
      s := vv[ei]/zeta;
      si := IntFFE(s);
      t := t * fnei[i]^si;
      v[ei] := vv[ei];
      v[2*n] := v[2*n] + vv[ei];
      Assert(0,v=vorig*t and w = worig*t);
      Print("Hallo7\n");
      s := vv[fI]/(zeta+vv[ei]);
      si := IntFFE(s);
      t := t * fnfi[i]^si;
      v[fI] := vv[fI];
      v[2*n] := v[2*n] + vv[fI];
      Assert(0,v=vorig*t and w = worig*t);
      Print("Hallo8\n");
      t := t * zn^-1;
      v[2*n-1] := v[2*n-1] * zeta^-1;
      v[2*n] := v[2*n] * zeta;
      w[2*n-1] := w[2*n-1] * zeta^-1;
      w[2*n] := w[2*n] * zeta;
      Assert(0,v=vorig*t and w = worig*t);
      Print("Hallo9\n");
    fi;
  od;
  # Finally arrange fn component to what it ought to be:
  if not(IsZero(vv[2*n]-v[2*n])) then
      s := vv[2*n]-v[2*n];
      si := IntFFE(s);
      t := t * fn^si;
      v[2*n] := vv[2*n];
      Assert(0,v=vorig*t and w = worig*t);
      Print("Hallo10\n");
  fi;
