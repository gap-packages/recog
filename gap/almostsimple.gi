#############################################################################
##
##  almostsimple.gi        
##                                recog package                   
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2006-2009 by the authors.
##  This file is free software, see license information at the end.
##
##  Code to recognise (simple) groups by their two largest element orders.
##  At least recognise the "natural" characteristic.
##
#############################################################################

RECOG.ParseNumber := function( number, d, default )
  if IsInt(number) then 
      return number; 
  fi;
  if IsString(number) then
      if number = "logd" then return LogInt(d,2); fi;
      if number[Length(number)] = 'd' then
          return d * Int(number{[1..Length(number)-1]});
      fi;
  fi;
  return default;
end;

# FIXME: unused?
RECOG.MakeStabChainHint := function( chain, stdgens )
  local b,bb,choice,dims,f,gens,grpnum,grps,i,j,lens,llens,m,name,names,nams,nrs,o,orblens,pts,r,size,slps;
  f := FieldOfMatrixList(stdgens);
  name := chain[1].name;
  size := chain[1].order;
  slps := [];
  names := [];
  dims := [];
  orblens := [];
  pts := [];
  gens := stdgens;
  repeat
      Print("Working on ",name,"\n");
      grps := [];
      nams := [];
      nrs := [];
      for i in [1..Length(chain)] do
          r := chain[i];
          if IsBound(r.parent) and r.parent = name then
              Add(grps,ResultOfStraightLineProgram(r.generators,gens));
              Add(nams,r.name);
              Add(nrs,i);
          fi;
      od;
      if Length(grps) = 0 then break; fi;
      Print("Considering subgroups: ",nams,"\n");
      bb := [];
      llens := [];
      grpnum := [];
      for i in [1..Length(grps)] do
          # will be left by break in case of success
          Print("  Considering ",nams[i],"\n");
          m := GModuleByMats(grps[i],f);
          if not MTX.IsIrreducible(m) then
              b := List(MTX.BasesMinimalSubmodules(m),MutableCopyMat);
              Sort(b,function(a,b) return Length(a) < Length(b); end );
              Print("    Dimensions: ",List(b,Length),"\n");
              lens := [];
              for j in [1..Length(b)] do
                  TriangulizeMat(b[j]);
                  if Length(b[j]) = 1 then
                      o := Orb(gens,b[j][1],OnLines,rec( report := 10000,
                             treehashsize := 1000, storenumbers := true ));
                  else
                      o := Orb(gens,b[j],OnSubspacesByCanonicalBasis,
                         rec( report := 10000, treehashsize := 1000, 
                              storenumbers := true ));
                  fi;
                  Enumerate(o);
                  Print("    Found orbit of length ",Length(o),"\n");
                  lens[j] := Length(o);
              od;
              Append(bb,b);
              Append(llens,lens);
              Append(grpnum,ListWithIdenticalEntries(Length(b),i));
          else
              Print("    Restriction is irreducible!\n");
          fi;
      od;
      choice := 1;
      Print("Dimensions: ",List(bb,Length),"\n");
      Print("Orbit lengths: ",llens,"\n");
      Error("now decide which orbit to take, set choice");
      if choice > 0 then
          i := grpnum[choice];
          Add(names,nams[i]);
          Add(dims,Length(bb[choice]));
          name := nams[i];
          gens := grps[i];
          size := size / llens[choice];
          Add(orblens,llens[choice]);
          Add(slps,chain[nrs[i]].generators);
          Add(pts,bb[choice]);
      fi;
  until size = 1 or choice = 0;
  return rec( slps := slps, names := names, dims := dims, orblens := orblens,
              pts := pts );
end;

InstallGlobalFunction( DoHintedStabChain, function(ri,G,hint)
    local S,b,bra,c,cf,elm,finder,fu,gm,homs,m,max,maxes,maxgens,opt,s,stdgens;
    finder := AtlasProgram(hint.name,"find");
    if finder = fail then
        Info(InfoRecog,1,"Expected BBox finder for stdgens of ",hint.name,
             " not availabe!");
        Info(InfoRecog,1,"Check your AtlasRep installation!");
        return fail;
    fi;
    gm := Group(ri!.gensHmem);
    gm!.pseudorandomfunc := [rec( 
       func := function(ri) return RandomElm(ri,"StdGens",true).el; end,
       args := [ri])];
    Info(InfoRecog,2,"Finding standard generators with bbox program...");
    stdgens := RunBBoxProgram(finder.program,gm,ri!.gensHmem,
                              rec( orderfunction := RECOG.ProjectiveOrder ) );
    if stdgens = fail or stdgens = "timeout" then
        Info(InfoRecog,2,"Stdgens finder did not succeed for ",hint.name);
        return fail;
    fi;
    stdgens := stdgens.gens;
    Setslptostd(ri,SLPOfElms(stdgens));
    SetStdGens(ri,StripMemory(stdgens));
    if IsBound(hint.usemax) then
        if IsBound(hint.brauercharelm) then
            elm := ResultOfStraightLineProgram(hint.brauercharelm,stdgens);
            bra := BrauerCharacterValue(elm!.el);
            maxes := hint.usemax{Filtered([1..Length(hint.usemax)],
                                          i->hint.brauercharvals[i] = bra)};
        else
            maxes := hint.usemax;
        fi;
        for max in maxes do
            s := AtlasProgram(hint.name,max);
            if s = fail then
                Info(InfoRecog,1,"Expected maximal subgroup slp of ",hint.name,
                     " not available!");
                Info(InfoRecog,1,"Check your AtlasRep installation!");
                return fail;
            fi;
            maxgens := ResultOfStraightLineProgram(s.program,
                                                   StripMemory(stdgens));
            m := GModuleByMats(maxgens,ri!.field);
            if MTX.IsIrreducible(m) then
                Info(InfoRecog,2,"Found irreducible submodule!");
                continue;
            fi;
            cf := List(MTX.CollectedFactors(m),x->x[1]);
            Sort(cf,function(a,b) return a.dimension < b.dimension; end);
            for c in cf do
                homs := MTX.Homomorphisms(c,m);
                if Length(homs) > 0 then
                    ConvertToMatrixRep(homs[1],ri!.field);
                    b := MutableCopyMat(homs[1]);
                    break;
                fi;
                # Some must be in the socle, so this terminates with break!
            od;
            TriangulizeMat(b);
            fu := function() return RandomElm(ri,"StabChain",true).el; end;
            opt := rec( Projective := true, RandomElmFunc := fu );
            if Length(b) = 1 then
                opt.Cand := rec( points := [b[1]], ops := [OnLines] );
            else
                opt.Cand := rec( points := [b], 
                                 ops := [OnSubspacesByCanonicalBasis] );
            fi;
            gm := GroupWithGenerators(stdgens);
            opt.Size := hint.size;
            Info(InfoRecog,2,"Computing hinted stabilizer chain for ",
                 hint.name," ...");
            S := StabilizerChain(gm,opt);
            # Verify correctness by sifting original gens:
            # Actually, genss does not terminate if no group of this
            # size is found!
            ri!.stabilizerchain := S;
            Setslptonice(ri,SLPOfElms(StrongGenerators(S)));
            SetSize(ri,hint.size);
            ForgetMemory(S);
            Unbind(S!.opt.RandomElmFunc);
            Setslpforelement(ri,SLPforElementFuncsProjective.StabilizerChain);
            SetFilterObj(ri,IsLeaf);
            if IsBound(hint.issimple) then
                SetIsSimpleGroup(ri,hint.issimple);
            fi;
            SetIsAlmostSimpleGroup(ri,true);
            ri!.comment := Concatenation("_",hint.name);
            return true;
        od;
    fi;
    Info( InfoRecog, 2, "Got stab chain hint, not yet implemented!" );
    return fail;
  end );

InstallGlobalFunction( DoHintedLowIndex, function(ri,G,hint)
  local bas,d,fld,gens,hm,hom,i,numberrandgens,orb,orblenlimit,s,
        tries,triesinner,triesinnerlimit,trieslimit,x,y;

  Info(InfoRecog,2,"Got hint for group, trying LowIndex...");

  fld := ri!.field;
  d := ri!.dimension;
  if IsBound(hint.elordersstart) then
      i := 0;
      repeat
          i := i + 1;
          if i > 10000 then
              Error("possible infinite loop in DoHintedLowIndex, wrong hints?");
          fi;
          x := PseudoRandom(G);
      until Order(x) in hint.elordersstart;
      x := [x];
  else
      x := [];
  fi;

  tries := 0;
  numberrandgens := RECOG.ParseNumber(hint.numberrandgens,d,2);
  triesinnerlimit := RECOG.ParseNumber(hint.triesforgens,d,"1d");
  trieslimit := RECOG.ParseNumber(hint.tries,d,10);
  orblenlimit := RECOG.ParseNumber(hint.orblenlimit,d,"4d");
  Info(InfoRecog,3,"Using numberrandgens=",numberrandgens,
       " triesinnerlimit=",triesinnerlimit," trieslimit=",trieslimit,
       " orblenlimit=",orblenlimit);
  
  repeat
      gens := ShallowCopy(x);
      triesinner := 0;
      if numberrandgens = Length(gens) then   # we have to make the hm module
          hm := GModuleByMats(gens,fld);
          if MTX.IsIrreducible(hm) then
              tries := tries + 1;
              continue;
          fi;
      else
          while Length(gens) < numberrandgens and 
                triesinner < triesinnerlimit do
              y := PseudoRandom(G);
              Add(gens,y);
              triesinner := triesinner + 1;
              hm := GModuleByMats(gens,fld);
              if MTX.IsIrreducible(hm) then
                  Unbind(gens[Length(gens)]);
              fi;
          od;
      fi;
      if Length(gens) = numberrandgens then
          # We hope to have the maximal subgroup!
          bas := [MTX.ProperSubmoduleBasis(hm)];
          s := bas[1];
          while s <> fail do
              hm := MTX.InducedActionSubmodule(hm,s);
              s := MTX.ProperSubmoduleBasis(hm);
              Add(bas,s);
          od;
          Unbind(bas[Length(bas)]);
          s := bas[Length(bas)];
          for i in [Length(bas)-1,Length(bas)-2..1] do
              s := s * bas[i];
          od;
          # Now s is the basis of a minimal submodule, permute that:
          s := MutableCopyMat(s);
          TriangulizeMat(s);
          # FIXME: this will be unnecessary:
          ConvertToMatrixRep(s);
          Info(InfoRecog,2,"Found invariant subspace of dimension ",
               Length(s),", enumerating orbit...");
          if not IsBound(hint.subspacedims) or 
             Length(s) in hint.subspacedims then
              #orb := RECOG.OrbitSubspaceWithLimit(G,s,orblenlimit);
              orb := Orb(G,s,OnSubspacesByCanonicalBasis,
                         rec(storenumbers := true, 
                             hashlen := NextPrimeInt(2*orblenlimit)));
              Enumerate(orb,orblenlimit);
              if IsClosed(orb) then
                  hom := OrbActionHomomorphism(G,orb);
                  if Length(s) * Length(orb) = d then
                      # A block system!
                      forkernel(ri).t := Concatenation(orb);
                      forkernel(ri).blocksize := Length(s);
                      Add(forkernel(ri).hints,
                  rec(method:=FindHomMethodsProjective.DoBaseChangeForBlocks, 
                            rank := 2000, stamp := "DoBaseChangeForBlocks"),1);
                      Setimmediateverification(ri,true);
                      findgensNmeth(ri).args[1] := Length(orb)+3;
                      findgensNmeth(ri).args[2] := 5;
                      Info(InfoRecog,2,"Found block system with ",
                           Length(orb)," blocks.");
                  else
                      Info(InfoRecog,2,"Found orbit of length ",
                           Length(orb)," - not a block system.");
                  fi;
                  SetHomom(ri,hom);
                  Setmethodsforfactor(ri,FindHomDbPerm);
                  return true;
              fi;
          else
              Info(InfoRecog,2,"Subspace dimension not as expected, ",
                   "not enumerating orbit.");
          fi;
      fi;
      tries := tries + 1;
  until tries > trieslimit;
  return fail;
end );
  
# We start a database of hints, whenever we discover a certain group, we
# can ask this database what to do:

RECOG.AlmostSimpleHints := rec();

InstallGlobalFunction( InstallAlmostSimpleHint,
  function( name, type, re )
    if not(IsBound(RECOG.AlmostSimpleHints.(name))) then
        RECOG.AlmostSimpleHints.(name) := [];
    fi;
    re.type := type;
    Add( RECOG.AlmostSimpleHints.(name),re );
  end );

# FIXME: unused?
RECOG.ProduceTrivialStabChainHint := function(name,reps,maxes)
  local bad,f,g,gens,hint,list,m,o,prevdim,prevfield,r,range,res,ri,
        size,success,t,values,x;
  PrintTo(Concatenation("NEWHINTS.",name),"# Hints for ",name,":\n");
  prevdim := fail;
  prevfield := fail;
  for r in reps do
      Print("\nDoing representation #",r,"\n");
      gens := AtlasGenerators(name,r);
      g := Group(gens.generators);
      f := gens.ring;
      values := [];
      success := false;
      size := Size(CharacterTable(name));
      for m in [1..Length(maxes)] do
          Print("Doing maximal subgroup #",m,"\n");
          hint := rec( name := name, size := size, usemax := [m] );
          ri := EmptyRecognitionInfoRecord(rec(),g,true);
          t := Runtime();
          res := DoHintedStabChain(ri,g,hint);
          t := Runtime() - t;
          if res = true then
              o := ri!.stabilizerchain!.orb;
              x := o[1];
              if IsMatrix(x) then
                  Add(values,[Length(x)*QuoInt(Length(o)+99,100),Length(o)]);
              else
                  Add(values,[QuoInt(Length(o)+99,100),Length(o)]);
              fi;
              Print("value=",values[Length(values)]," time=",t," orblen=",
                    Length(o)," subspace=");
              ViewObj(x);
              Print("\n");
              success := true;
          else
              Add(values,[infinity,infinity]);
              Print("failure\n");
          fi;
      od;
      if success then
          if Size(f) = prevfield and Length(gens.generators[1]) = prevdim then
              AppendTo(Concatenation("NEWHINTS.",name),
                       ">>>SAME FIELD AND DIM\n");
          fi;
          list := ShallowCopy(maxes);
          SortParallel(values,list);
          bad := First([1..Length(values)],i->values[i][1] = infinity);
          if bad = fail or bad > 3 then
              if Length(values) > 3 then
                  range := [1..3];
              else
                  range := [1..Length(values)];
              fi;
          else
              range := [1..bad-1];
          fi;
          AppendTo(Concatenation("NEWHINTS.",name),
                "InstallAlmostSimpleHint( \"",name,"\", \"StabChainHint\",\n",
                "  rec( name := \"",name,"\", fields := [",
                Size(f),"], dimensions := [",Length(gens.generators[1]),
                "], \n       usemax := ",list{range},
                ", \n       size := ", size, 
                ", atlasrepnrs := [",r,"], \n       values := ",
                values{range},"\n  ));\n");
      fi;
      prevfield := Size(f);
      prevdim := Length(gens.generators[1]);
  od;
end;

# FIXME: unused?
RECOG.DistinguishAtlasReps := function(name,rep1,rep2)
  local br1,br2,classes,gens1,gens2,guck1,guck2,l,lens,slps;
  classes := AtlasProgram(name,"cyclic").program;
  gens1 := GeneratorsWithMemory(AtlasGenerators(name,rep1).generators);
  gens2 := AtlasGenerators(name,rep2).generators;
  guck1 := ResultOfStraightLineProgram(classes,gens1);
  guck2 := ResultOfStraightLineProgram(classes,gens2);
  br1 := List(guck1,x->BrauerCharacterValue(x!.el));
  br2 := List(guck2,BrauerCharacterValue);
  l := Filtered([1..Length(br1)],i->br1[i]<>br2[i]);
  slps := List(guck1,SLPOfElm);
  lens := List(l,x->Length(LinesOfStraightLineProgram(slps[x])));
  SortParallel(lens,l);
  Print("brauercharelm := ",slps[l[1]],", brauercharvals := ",
        [br1[l[1]],br2[l[1]]],",\n");
end;


# This is for the released AtlasRep package:
if not(IsBound(AGR_TablesOfContents)) then
    AGR_TablesOfContents := fail;
    AGR_InfoForName := fail;
fi;

# FIXME: unused?
RECOG.PrintGenericStabChainHint := function ( n )
    local S,g,gens,nn,toc,tocs;
    tocs := AGR_TablesOfContents( "all" );
    nn := AGR_InfoForName( n )[2];
    toc := tocs[1].(nn);
    gens := AtlasGenerators( n, 1 ).generators;
    g := Group( gens );
    S := StabilizerChain( g );
    Print( "InstallAlmostSimpleHint( \"", n, "\", \"StabChainHint\",\n" );
    Print( "  rec( name := \"", n, "\", usemax := " );
    Print( Set( List( toc.maxes, x->x[2] ) ) );
    Print( ",\n       size := ", Size( S ), ",\n  ));\n" );
end;

# dimensions optionally
# subspacedims there or not
# elordersstart unbound ==> start with empty generator list
# if numberrandgens = "logd" then it will use LogInt(d,2)
# if triesforgens = "Xd" then it will use X * d (X a number as a string)
# if orblenlimit = "Xd" then it will use X * d (X a number as a string)
# L2 hint with doing the decision on the fly
#   depending on the ppd-Properties of L2(p)
# This means:
#   rec( numberrandgens := "logd", tries := 10, triesforgens := "1d",
#        orblenlimit := "4d" )
# is the standard low index.

# BUG: The following hint was added a long time ago, but it
# can lead to an infinite loop in DoHintedLowIndex, because
# elordersstart suggests searching for elements of order 31,
#  but no such elements are found.
# See also https://github.com/gap-system/recog/issues/6
# InstallAlmostSimpleHint( "L2(31)", "LowIndexHint",
#   rec( characteristics := [31], dimensions := [1,2,3],
#        elordersstart := [31], numberrandgens := 2, tries := 1,
#        triesforgens := 100, orblenlimit := 32, issimple := true ) );

InstallGlobalFunction( LookupHintForSimple, 
  function(ri,G,name)
    local dim,f,hi,j,p,q;
    Info(InfoRecog,2,"Looking up hints for ",name,"...");
    if IsBound(RECOG.AlmostSimpleHints.(name)) then
        j := 1;
        hi := RECOG.AlmostSimpleHints.(name);
        f := ri!.field;
        p := Characteristic(f);
        q := Size(f);
        dim := ri!.dimension;
        while j <= Length(hi) do
            if (not(IsBound(hi[j].characteristics)) or 
                p in hi[j].characteristics) and 
               (not(IsBound(hi[j].fields)) or
                q in hi[j].fields) and
               (not(IsBound(hi[j].dimensiondivs)) or 
                ForAny(hi[j].dimensiondivs,d->dim mod d = 0)) and
               (not(IsBound(hi[j].dimensions)) or
                dim in hi[j].dimensions) then
                # This hint is applicable!
                if hi[j].type = "LowIndexHint" then
                    return DoHintedLowIndex(ri,G,hi[j]);
                elif hi[j].type = "StabChainHint" then
                    return DoHintedStabChain(ri,G,hi[j]);
                # Put other hint types here!
                fi;
            fi;
            j := j + 1;
        od;
    fi;
    Info(InfoRecog,2,"No hint worked, giving up.");
    return fail;
  end );


#checks whether the orbit of <vec> under g is not longer than bound
RECOG.shortorbit:=function(vec,g,bound)
local short, v, i, pos;

v:=StructuralCopy(vec);
short:=false;
i:=0;
pos:=First([1..Length(vec)],x->vec[x]<>0*vec[1]);
repeat 
  i:=i+1;
  v:=v*g;
  if v=(v[pos]/vec[pos])*vec then
     short:=true;
  fi;
until short or i=bound;

return i;

end;


# Under the assumption that G is an almost simple group,
# attempt to guess the "natural" characteristic of the
# group based on the two maximal orders of group elements.
RECOG.findchar:=function(ri,G,randelfunc)
    # randelfunc must be a function taking ri as one argument and returning
    # uniformly distributed random elements in G together with its
    # projective order (as for example below), or fail.
    local mat,vs,vec,bound,count,m1,m2,m3,g,order,list,last,r,p,d,pr;

    if randelfunc = fail then
        pr := ProductReplacer(GeneratorsOfGroup(G));
        randelfunc := function(ri)
          local el;
          el := Next(pr);
          return rec( el := el, order := ProjectiveOrder(el)[1] );
        end;
    fi;

    p := Characteristic(ri!.field);
    d := ri!.dimension;
    mat:=One(G);
    vs:=VectorSpace(GF(p),mat);
    repeat
        vec:=Random(vs);
    until not(IsZero(vec));

    if RECOG.shortorbit(vec,Product(GeneratorsOfGroup(G)), 3*d) = 3*d then 
        return p;
    fi;

    #find three largest element orders m1, m2, m3
    bound:=32*(LogInt(d,2))^2*6*4;
    count:=0;
    m1:=0;
    m2:=0;
    m3:=0;
    last:=0;
    repeat
        count:=count+1;
        r := randelfunc(ri);
        g := r.el;
        order:=r.order;
        if order >= 3*d then 
            return p;
        elif order > m1 then
            m3:=m2;
            m2:=m1;
            m1:=order;
            last:=count;
        elif order<m1 and order>m2 then 
            m3:=m2;
            m2:=order;
            last:=count;
        elif order<m2 and order>m3 then
            m3:=order;
            last:=count;
        fi;
    until count=bound or count>=2*last+50;

    #handle ambiguous cases
    if [m1,m2,m3] = [13,7,5] then 
        return [[13,7, ["2B2",8]]];
    elif [m1,m2] = [13,8] then
        return [[13,8, ["l",3,3]]];
    elif [m1,m2,m3] = [13,7,6] then
        return [[13,7, ["l",2,13]]];
    elif [m1,m2,m3] = [13,12,6] then
        return [[13,12,["l",2,5]]];
    elif [m1,m2,m3] = [13,12,9] then 
        return [[13,12,["G2",3]]];
    elif [m1,m2,m3] = [12,9,6] then 
        return [[12,9,["u",4,2]]];
    elif [m1,m2,m3] = [12,9,8] then 
        return [[12,9,["u",4,3]]];
    elif [m1,m2] = [5,3] then
        return [[ 5,3,["l",2,4]]];
    elif [m1,m2] = [5,4] then
        return [[5,4,["l",2,9]]];
    elif [m1,m2] = [7,4] then
        return [[7,4,["l",2,7]]];
    elif [m1,m2] = [15,13] then
        return [[15,13,["u",3,4]]];
    elif [m1,m2] = [30,20] then
        return [[30,20,["s",4,5]]];
    elif [m1,m2] = [30,24] then
        return [[30,24,["s",8,2]]];
    elif [m1,m2] = [63,60] then 
        return [[63,60,["u",4,5]]];
    elif [m1,m2] = [91,85] then
        return [[91,85,["l",3,16]]];
    fi;

    list:=Filtered(RECOG.grouplist, x->x[1]=m1 and x[2]=m2);
    #one more ambiguous case
    if  Length(list) >=2 and (
        (list[1][3]{[1,2]}=["l",2] and list[2][3][1]="G2") or 
        (list[2][3]{[1,2]}=["l",2] and list[1][3][1]="G2")) then
       if m3>m1/2 then
           return Filtered(list,x->x[3][1]="G2");
       else 
           return Filtered(list,x->x[3][1]="l");
       fi;
    else
        return list;
    fi;

end;


RECOG.MakePSL2Hint := function( name, G )
  local d,defchar,f,p,q;
  f := DefaultFieldOfMatrixGroup(G);
  q := Size(f);
  p := Characteristic(f);
  d := DimensionOfMatrixGroup(G);
  defchar := Factors(name[3])[1];
  if p = defchar then return fail; fi;
  Info(InfoRecog,2,"Making hint for group ",name,"...");
  # we are in cross characteristic.
  # to be made better...
  return rec( elordersstart := [defchar], numberrandgens := 1, tries := 10,
              triesforgens := 3*(name[3]+1), 
              orblenlimit := 3*(name[3]+1) );
end;

RECOG.simplesocle := function(ri,g)
  local x,y,comm,comm2,comm3,gensH;

  repeat
    x:=RandomElm(ri,"simplesocle",true).el;
  until not ri!.isone(x);

  repeat
    y:=RandomElm(ri,"simplesocle",true).el;
    comm:=Comm(x,y);
  until not ri!.isone(comm);

  repeat
    y:=RandomElm(ri,"simplesocle",true).el;
    comm2:=Comm(comm,comm^y);
  until not ri!.isone(comm2);

  repeat
    y:=RandomElm(ri,"simplesocle",true).el;
    comm3:=Comm(comm2,comm2^y);
  until not ri!.isone(comm3);

  gensH:=FastNormalClosure(GeneratorsOfGroup(g),[comm3],20);

  return gensH;
end;

FindHomMethodsProjective.ComputeSimpleSocle := function(ri,G)
  # This simply computes the simple socle, stores it and returns false
  # such that it is never called again for this node.
  local x;
  RECOG.SetPseudoRandomStamp(G,"ComputeSimpleSocle");
  ri!.simplesocle := Group(RECOG.simplesocle(ri,G));
  ri!.simplesoclepr := ProductReplacer(ri!.simplesocle);
  ri!.simplesoclerand := EmptyPlist(100);
  Append(ri!.simplesoclerand,GeneratorsOfGroup(ri!.simplesocle));
  ri!.simplesoclerando := EmptyPlist(100);
  for x in ri!.simplesoclerand do
      Add(ri!.simplesoclerando,ProjectiveOrder(x)[1]);
  od;
  ri!.simplesoclerandp := 0;
  ri!.simplesocle!.pseudorandomfunc := 
       [rec( func := Next, args := [ri!.simplesoclepr] )];
  return false;
end;

RECOG.RandElFuncSimpleSocle := function(ri)
  local el,ord;
  ri!.simplesoclerandp := ri!.simplesoclerandp + 1;
  if not(IsBound(ri!.simplesoclerand[ri!.simplesoclerandp])) then
      el := Next(ri!.simplesoclepr);
      ri!.simplesoclerand[ri!.simplesoclerandp] := el;
      ord := ProjectiveOrder(el)[1];
      ri!.simplesoclerando[ri!.simplesoclerandp] := ord;
  else
      el := ri!.simplesoclerand[ri!.simplesoclerandp];
      ord := ri!.simplesoclerando[ri!.simplesoclerandp];
  fi;
  return rec( el := el, order := ord );
end;

FindHomMethodsProjective.ThreeLargeElOrders := function(ri,G)
  local hint,name,namecat,p,res;
  RECOG.SetPseudoRandomStamp(G,"ThreeLargeElOrders");
  ri!.simplesoclerandp := 0;
  p := RECOG.findchar(ri,ri!.simplesocle,RECOG.RandElFuncSimpleSocle);
  if p = Characteristic(ri!.field) then
      Info(InfoRecog,2,"ThreeLargeElOrders: defining characteristic p=",p);
      return false;
  fi;
  # Try all possibilities:
  Info(InfoRecog,2,"ThreeLargeElOrders: found ",p);
  for hint in p do
      Info(InfoRecog,2,"Trying ",hint);
      name := hint[3];
      if name[1] = "l" then  # Handle PSL specially
          if name[2] = 2 then
              hint := RECOG.MakePSL2Hint(name,G);
              if hint <> fail then
                  res := DoHintedLowIndex(ri,G,hint);
              else   # we use Pete Brooksbank's methods
                  return SLCR.FindHom(ri,G,2,name[3]);
              fi;
          else
              return SLCR.FindHom(ri,G,name[2],name[3]);
          fi;
      else
          if Length(name) = 3 then
              namecat := Concatenation(UppercaseString(name[1]),
                                       String(name[2]),
                                       "(",String(name[3]),")");
          else
              namecat := name[1];
          fi;
          res := LookupHintForSimple(ri,G,namecat);
      fi;
      if res = true then return true; fi;
  od;
  Info(InfoRecog,2,"Did not succeed with hints, giving up...");
  return fail;
end;

RECOG.DegreeAlternating := function (orders)
    local   degs,  prims,  m,  f,  n;
    degs := []; 
    prims := [];
    for m in orders do 
        if m > 1 then
            f := Collected(Factors(m));
            Sort(f);
            n := Sum(f, x->x[1]^x[2]);
            if f[1][1] = 2 then n := n+2; fi;
            AddSet(degs,n);
            UniteSet(prims,Set(f,x->x[1]));
        fi; 
    od;
    return [degs, prims];
end;    #  DegreeAlternating

RECOG.RecognizeAlternating := function (orders)
    local   tmp,  degs,  prims,  mindeg,  p1,  p2,  i;
   tmp := RECOG.DegreeAlternating (orders);
   degs := tmp[1];
   prims := tmp[2];
   if Length(degs) = 0 then 
       return "Unknown"; 
   fi;
   mindeg := Maximum (degs);  # minimal possible degree
   
   p1 := PrevPrimeInt (mindeg + 1);
   p2 := PrevPrimeInt (p1);
   if not p1 in prims or not p2 in prims then
       return 0;
   fi;
   if mindeg mod 2 = 1 then
       if not (mindeg in orders and  mindeg - 2 in orders) then 
           return 0;
       fi;
   else
       if not mindeg - 1 in orders then 
           return 0;
       fi;
   fi;
  
   for i in [3..Minimum (QuoInt(mindeg,2) - 1, 6)] do
       if IsPrime (i) and IsPrime (mindeg - i) then
           if not i * (mindeg - i) in orders then
               return 0;
           fi;
       elif IsPrime (i) and IsPrime (mindeg - i -1) then
           if not i * (mindeg - i - 1) in orders then
               return 0;
           fi;
       fi;
   od;
   return  mindeg;
end;   # RecognizeAlternating

SLPforElementFuncsProjective.Alternating := function(ri,x)
  local y,slp;
  RecSnAnIsOne := IsOneProjective;
  RecSnAnEq := IsEqualProjective;
  y := FindImageAn(ri!.recogSnAnDeg,x,
                   ri!.recogSnAnRec[2][1], ri!.recogSnAnRec[2][2],
                   ri!.recogSnAnRec[3][1], ri!.recogSnAnRec[3][2]);
  RecSnAnIsOne := IsOne;
  RecSnAnEq := EQ;
  if y = fail then return fail; fi;
  slp := SLPforAn(ri!.recogSnAnDeg,y);
  return slp;
end;

SLPforElementFuncsProjective.Symmetric := function(ri,x)
  local y,slp;
  RecSnAnIsOne := IsOneProjective;
  RecSnAnEq := IsEqualProjective;
  y := FindImageSn(ri!.recogSnAnDeg,x,
                   ri!.recogSnAnRec[2][1], ri!.recogSnAnRec[2][2],
                   ri!.recogSnAnRec[3][1], ri!.recogSnAnRec[3][2]);
  RecSnAnIsOne := IsOne;
  RecSnAnEq := EQ;
  if y = fail then return fail; fi;
  slp := SLPforSn(ri!.recogSnAnDeg,y);
  return slp;
end;

# FIXME: unused?
FindHomMethodsProjective.AlternatingBBByOrders := function(ri,G)
  local Gm,RecSnAnEq,RecSnAnIsOne,deg,limit,ordersseen,r;
  if IsBound(ri!.projordersseen) then
      ordersseen := ri!.projordersseen;
  else
      ordersseen := [];
  fi;
  limit := QuoInt(3*ri!.dimension,2);
  while Length(ordersseen) <= limit do
      Add(ordersseen,RECOG.ProjectiveOrder(PseudoRandom(G)));
      if Length(ordersseen) mod 20 = 0 or
         Length(ordersseen) = limit then
          deg := RECOG.RecognizeAlternating(ordersseen);
          Info(InfoRecog,2,ordersseen);
          if deg > 0 then  # we strongly suspect Alt(deg):
              # Switch blackbox recognition to projective:
              Info(InfoRecog,2,"Suspect alternating or symmetric group of ",
                   "degree ",deg,"...");
              RecSnAnIsOne := IsOneProjective;
              RecSnAnEq := IsEqualProjective;
              Gm := GroupWithMemory(G);
              r := RecogniseSnAn(deg,Gm,1/100);
              RecSnAnIsOne := IsOne;
              RecSnAnEq := EQ;
              if r = fail or r[1] <> "An" then 
                  Info(InfoRecog,2,"AltByOrders: Did not find generators.");
                  continue; 
              fi;
              Info(InfoRecog,2,"Found Alt(",deg,")!");
              ri!.recogSnAnRec := r;
              ri!.recogSnAnDeg := deg;
              SetSize(ri,Factorial(deg)/2);
              Setslpforelement(ri,SLPforElementFuncsProjective.Alternating);
              Setslptonice(ri,SLPOfElms(Reversed(r[2])));
              ForgetMemory(r[2]);
              ForgetMemory(r[3][1]);
              SetFilterObj(ri,IsLeaf);
              SetIsSimpleGroup(ri,true);
              return true;
          fi;
      fi;
  od;
  return fail;
end;

RECOG.HomFDPM := function(data,x)
  local r;
  r := RECOG.FindPermutation(data.cob*x*data.cobi,data.fdpm);
  if r = fail then return fail; fi;
  return r[2];
end;

FindHomMethodsProjective.AltSymBBByDegree := function(ri,G)
  local GG,Gm,RecSnAnEq,RecSnAnIsOne,d,deg,f,fact,hom,newgens,o,orders,p,primes,
        r,totry;
  RECOG.SetPseudoRandomStamp(G,"AltSymBBByDegree");
  d := ri!.dimension;
  orders := RandomOrdersSeen(ri);
  if Length(orders) = 0 then
      orders := [RandomElmOrd(ri,"AltSym",false).order];
  fi;
  primes := Filtered(Primes,x->x <= d+2);
  for o in orders do
      fact := FactorsTD(o,primes);
      if Length(fact[2]) <> 0 then
          Info(InfoRecog,2,"AltSym: prime factor of order excludes A_n");
          return false;
      fi;
  od;
  f := ri!.field;
  # We first try the deleted permutation module method:
  if d >= 6 then
      Info(InfoRecog,3,"Trying deleted permutation module method...");
      r := RECOG.RecogniseFDPM(G,f,1/10);
      if r <> fail and IsRecord(r) then
          # Now make a homomorphism object:
          newgens := List(GeneratorsOfGroup(G),
                          x->RECOG.HomFDPM(r,x));
          if not(fail in newgens) then
              GG := GroupWithGenerators(newgens);
              hom := GroupHomByFuncWithData(G,GG,RECOG.HomFDPM,r);

              SetHomom(ri,hom);
              Setmethodsforfactor(ri,FindHomDbPerm);

              ri!.comment := "_FDPM";
              return true;
          fi;
      fi;
      Info(InfoRecog,3,"Deleted permutation module method failed.");
  fi;
  p := Characteristic(f);
  totry := EmptyPlist(2);
  if (d+1) mod p <> 0 and d+1 > 10 then
      Add(totry,d+1);
  fi;
  if (d+2) mod p = 0 and d+2 > 10 then
      Add(totry,d+2);
  fi;
  return fail;    # do not try any more now
  for deg in totry do
      Info(InfoRecog,3,"Looking for Alt/Sym(",deg,")...");
      RecSnAnIsOne := IsOneProjective;
      RecSnAnEq := IsEqualProjective;
      Gm := GroupWithMemory(G);
      r := RecogniseSnAn(deg,Gm,1/100);
      RecSnAnIsOne := IsOne;
      RecSnAnEq := EQ;
      if r = fail then 
          Info(InfoRecog,2,"AltSym: deg=",deg,": did not find generators.");
          continue; 
      fi;
      if r[1] = "An" then
          Info(InfoRecog,2,"Found Alt(",deg,")!");
          ri!.recogSnAnRec := r;
          ri!.recogSnAnDeg := deg;
          SetSize(ri,Factorial(deg)/2);
          Setslpforelement(ri,SLPforElementFuncsProjective.Alternating);
          Setslptonice(ri,SLPOfElms(Reversed(r[2])));
          ForgetMemory(r[2]);
          ForgetMemory(r[3][1]);
          SetFilterObj(ri,IsLeaf);
          SetIsSimpleGroup(ri,true);
          ri!.comment := "_Alt";
          return true;
      else   # r[1] = "Sn" 
          Info(InfoRecog,2,"Found Sym(",deg,")!");
          ri!.recogSnAnRec := r;
          ri!.recogSnAnDeg := deg;
          SetSize(ri,Factorial(deg));
          Setslpforelement(ri,SLPforElementFuncsProjective.Symmetric);
          Setslptonice(ri,SLPOfElms(Reversed(r[2])));
          ForgetMemory(r[2]);
          ForgetMemory(r[3][1]);
          SetFilterObj(ri,IsLeaf);
          SetIsAlmostSimpleGroup(ri,true);
          ri!.comment := "_Sym";
          return true;
      fi;
  od;
  return fail;
end;

# Looking at element orders to determine which sporadic it could be:

RECOG.SporadicsElementOrders :=
[ [ 1,2,3,5,6,7,10,11,15,19 ],[ 1,2,3,4,5,6,8,11 ],
  [ 1,2,3,4,5,6,8,10,11 ],
  [ 1,2,3,4,5,6,8,9,10,12,15,17,19 ],
  [ 1,2,3,4,5,6,7,8,11,14,15,23 ],[ 1,2,3,4,5,6,7,8,11 ],
  [ 1,2,3,4,5,6,7,8,10,12,15 ],
  [ 1,2,3,4,5,6,7,8,10,12,14,15,17,21,28 ],
  [ 1,2,3,4,5,6,7,8,10,12,13,14,15,16,20,24,26,29 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,15,20 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,21,23 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,16,20,21,22,23,24,28,
      29,30,31,33,35,37,40,42,43,44,66 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,16,19,20,28,31 ],
  [ 1,2,3,4,5,6,7,8,9,10,12,13,14,15,18,19,20,21,24,27,
      28,30,31,36,39 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,19,20,21,22,25,30, 35,40 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,18,20,21,22,24,25,
      28,30,31,33,37,40,42,67 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,18,20,21,22,23,24,30 
     ],[ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,18,20,23,24,28,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,18,20,21,24 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,24,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,
      23,24,26,28,30,33,35,36,39,40,42,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,
      22,23,24,26,27,28,30,35,36,39,42,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,
      22,23,24,26,27,28,29,30,33,35,36,39,42,45,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
      21,22,23,24,25,26,27,28,30,31,32,33,34,35,36,38,39,40,
      42,44,46,47,48,52,55,56,60,66,70 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
      21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,38,39,
      40,41,42,44,45,46,47,48,50,51,52,54,55,56,57,59,60,62,
      66,68,69,70,71,78,84,87,88,92,93,94,95,104,105,110,119 ]
    ,[ 1,2,3,4,5,6,8,10,11,12 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,20,30 ],
  [ 1,2,3,4,5,6,7,8,10,12,14,15,24 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,20,22,24,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,24,28,30,40 ],
  [ 1,2,3,4,5,6,7,8,10,12,14,15,16,17,20,21,24,28,30,42 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,18,19,20,21,22,24,
      25,28,30,35,40,42,44,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,24,30,36,42 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,
      22,23,24,26,27,28,29,30,33,34,35,36,39,40,42,45,46,54,60,66,70,78,84 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,16,19,20,22,24,28,30,
      31,38,56 ],[ 1,2,3,4,5,6,8,9,10,12,15,17,18,19,24,34 ]
    ,[ 1,2,3,4,5,6,8,10,12,13,16 ],
  [ 1,2,3,4,5,6,8,10,12,13,16,20 ] ];
RECOG.SporadicsProbabilities :=
[ [ 1/175560,1/120,1/30,1/15,1/6,1/7,1/5,1/11,2/15,3/19 ],
  [ 1/7920,1/48,1/18,1/8,1/5,1/6,1/4,2/11 ],
  [ 1/95040,3/320,5/108,1/16,1/10,1/4,1/4,1/10,2/11 ],
  [ 1/50232960,1/1920,49/9720,1/96,1/15,1/24,1/8,1/9,1/5,1/12,2/15,
      2/17,2/19 ],
  [ 1/10200960,1/2688,1/180,1/32,1/15,1/12,1/7,1/8,2/11,1/7,2/15,
      2/23 ],[ 1/443520,1/384,1/36,3/32,1/5,1/12,2/7,1/8,2/11 ],
  [ 1/604800,3/640,31/1080,1/96,7/150,1/8,1/7,1/8,3/10,1/12,2/15 ],
  [ 1/4030387200,17/322560,2/945,1/84,1/300,1/18,95/4116,1/16,1/20,
      1/6,5/28,1/15,2/17,4/21,1/14 ],
  [ 1/145926144000,283/22364160,1/2160,17/5120,13/3000,1/48,1/28,
      11/192,3/40,1/8,1/52,3/28,1/15,1/8,3/20,1/12,3/52,2/29 ],
  [ 1/44352000,11/23040,1/360,19/960,17/375,5/72,1/7,3/16,1/10,2/11,
      1/12,1/15,1/10 ],
  [ 1/244823040,19/107520,11/3780,1/48,1/60,1/12,1/21,1/16,1/20,
      1/11,1/6,1/7,2/15,2/21,2/23 ],
  [ 1/86775571046077562880,13/21799895040,1/2661120,53/1576960,1/6720,
      2311/2661120,1/420,31/7680,13/960,133/31944,1/32,5/84,1/30,
      1/32,1/80,1/21,13/264,1/23,1/24,1/14,1/29,1/30,3/31,1/33,
      2/35,3/37,1/20,1/21,3/43,1/44,1/33 ],
  [ 1/460815505920,1/161280,1/3240,79/20160,1/180,1/72,29/1372,1/16,
      1/20,1/11,1/36,1/28,2/45,1/4,3/19,1/10,1/14,2/31 ],
  [ 1/90745943887872000,1/92897280,13603/1719506880,257/1935360,1/3000,
      67/25920,1/1176,5/384,5/648,1/120,25/432,1/39,1/56,1/15,5/72,
      1/19,1/20,1/21,1/6,1/9,1/28,1/15,2/31,1/12,2/39 ],
  [ 1/898128000,1/40320,31/29160,1/96,31/750,11/360,1/7,1/8,2/27,
      1/30,2/11,1/12,1/7,1/15,1/15 ],
  [ 1/273030912000000,131/473088000,59/1632960,23/46080,16913/31500000,
      1/192,1/420,9/320,1/27,431/12000,1/22,17/144,1/28,13/180,2/19,
      3/20,1/21,1/22,2/25,1/12,2/35,1/20 ],
  [ 1/51765179004000000,1/39916800,15401/2694384000,1/20160,601/2250000,
      1291/362880,1/168,1/80,1/54,73/3600,1/33,5/288,1/168,28/1125,
      1/18,1/40,1/21,1/11,1/8,1/25,1/28,1/45,5/31,2/33,2/37,1/20,
      1/21,3/67 ],
  [ 1/495766656000,179/31933440,631/2449440,1/1440,1/250,373/12960,
      1/42,1/24,1/54,1/15,1/11,1/18,1/14,1/10,1/18,1/10,1/21,1/11,
      2/23,1/12,1/30 ],
  [ 1/42305421312000,523/743178240,1/116640,139/120960,1/500,79/12960,
      1/56,5/192,1/54,1/20,1/11,2/27,5/56,1/10,1/16,1/18,1/10,
      2/23,1/12,1/28,1/10 ],
  [ 1/448345497600,151/23224320,661/1959552,103/23040,7/1800,187/10368,
      1/84,5/96,1/27,3/40,1/11,31/288,2/13,1/28,1/9,1/9,1/20,2/21,
      1/24 ],
  [ 1/64561751654400,4297/7357464576,11419/176359680,181/276480,1/600,
      9121/933120,1/42,17/384,5/108,1/24,1/11,79/864,2/13,1/14,1/30,
      1/16,7/108,1/20,1/21,1/11,1/24,1/30 ],
  [ 1/4157776806543360000,39239/12752938598400,7802083/4035109478400,
      1061/11612160,1433/15120000,198391/69672960,2/2205,79/23040,1/216,
      109/9600,1/66,10949/207360,1/156,1/42,277/5400,1/32,1/24,
      37/480,17/252,1/22,2/23,25/288,1/52,1/14,13/120,1/33,1/35,
      1/36,2/39,1/40,1/84,1/60 ],
  [ 1/4089470473293004800,407161/129123503308800,161281/148565394432,
      239/5806080,1/25200,1036823/705438720,1/840,1/128,127/17496,
      11/1200,1/44,529/12960,1/39,5/168,1/72,1/16,1/17,13/216,1/30,
      1/42,3/44,2/23,1/16,1/13,1/27,1/28,7/120,1/35,1/18,2/39,
      1/42,1/60 ],
  [ 1/1255205709190661721292800,6439/1032988026470400,144613199/
        4412392214630400,25/6967296,1/907200,159797/564350976,67/123480,
      11/4608,1189/1049760,7/4800,1/132,4741/311040,1/234,5/168,
      103/16200,1/32,1/17,11/288,1/48,17/252,1/44,2/23,7/72,1/26,
      1/27,1/28,2/29,1/24,2/33,1/35,1/24,4/117,5/84,2/45,1/60 ],
  [ 1/4154781481226426191177580544000000,
      34727139371/281639525236291462496256000,160187/10459003768012800,
      56445211/3060705263616000,1873/11088000000,7216687/1418939596800,
      1/564480,18983/123863040,5/34992,667/2688000,1/1320,12629/3732480,
      1/312,871/564480,31/3600,1/96,1/68,7/432,1/38,323/12000,1/252,
      5/264,1/23,19/432,1/25,3/104,1/27,5/224,67/1200,2/31,1/32,
      1/66,3/68,1/70,5/108,1/38,1/39,1/20,1/36,1/44,1/23,2/47,
      1/48,1/52,1/55,1/56,1/30,1/66,1/70 ],
  [ 1/808017424794512875886459904961710757005754368000000000,
      952987291/132953007399245638117682577408000000,
      1309301528411/299423045898886400305790976000,
      228177889/1608412858851262464000,361177/34128864000000000,
      352968797/83672030144102400,16369/1382422809600,80467/177124147200,
      7/18895680,1270627/532224000000,1/1045440,20669/313528320,
      31/949104,9/250880,8611/40824000,1/3072,1/2856,91/139968,1/1140,
      2323/1152000,907/370440,3/3520,1/276,167/13824,1/250,1/208,
      1/162,3/392,1/87,529/43200,1/93,1/64,5/1188,1/136,31/2100,
      1/48,1/76,25/702,49/1600,1/41,1/56,1/176,1/135,3/92,1/47,
      1/96,1/50,1/51,3/104,1/54,1/110,5/112,1/57,2/59,41/720,1/31,
      1/44,1/68,2/69,3/140,2/71,1/26,1/28,2/87,1/44,1/46,2/93,
      1/47,2/95,1/52,1/105,1/110,2/119 ],
  [ 1/190080,17/1920,5/216,3/32,1/20,5/24,1/8,3/20,1/11,1/4 ],
  [ 1/887040,29/8960,1/72,7/96,1/10,1/8,1/7,1/8,1/10,1/11,1/12,1/7 
     ],[ 1/88704000,11/21504,1/720,7/240,17/750,17/240,1/14,1/8,1/6,
      1/11,1/12,1/14,1/30,1/5,1/30 ],
  [ 1/1209600,103/26880,31/2160,11/192,7/300,7/48,1/14,5/48,3/20,
      5/24,1/14,1/15,1/12 ],
  [ 1/1796256000,67/887040,31/58320,17/2880,31/1500,31/720,1/14,5/48,
      1/27,7/60,1/11,7/72,1/14,1/30,1/10,1/11,1/12,1/30 ],
  [ 1/896690995200,16081/2554675200,661/3919104,1031/322560,7/3600,
      2879/103680,1/168,53/1440,1/54,89/1200,1/22,65/576,1/13,3/56,
      1/18,1/16,1/18,1/40,1/21,1/22,19/144,1/28,1/30,1/20 ],
  [ 1/8060774400,23/387072,1/945,9/1120,1/600,473/7560,95/8232,7/96,
      1/24,1/8,19/168,1/30,1/8,1/17,1/20,2/21,1/12,1/28,1/30,1/21 ]
    ,[ 1/546061824000000,7057/25546752000,59/3265920,119351/177408000,
      16913/63000000,2497/362880,1/840,21/640,1/54,691/24000,1/44,
      101/1440,5/168,13/360,1/18,1/19,743/6000,1/42,1/44,1/8,1/25,
      1/28,7/120,1/35,1/10,1/42,1/22,1/60 ],
  [ 1/129123503308800,10781/17517772800,11419/352719360,329/414720,
      1/1200,46757/4354560,1/84,1/32,5/216,17/400,1/22,295/2592,1/13,
      1/12,1/60,1/16,29/216,1/20,1/42,1/22,1/8,1/20,1/36,1/42 ],
  [ 1/2510411418381323442585600,352149857/65431527572688076800,
      144613199/8824784429260800,12091/4180377600,1/1814400,
      20115929623/65368773550080,67/246960,13/7680,1189/2099520,97/67200,
      1/264,282547/13063680,1/468,31/1680,103/32400,1/32,1/34,
      4153/139968,41/2400,17/504,7/264,1/23,7/96,5/156,1/54,2/21,
      1/29,11/240,1/33,1/34,1/70,31/432,2/117,1/40,11/168,1/45,
      1/23,1/54,1/60,1/33,1/70,1/39,1/84 ],
  [ 1/921631011840,401/67415040,1/6480,79/40320,1/360,17/720,29/2744,
      43/672,7/120,1/22,1/72,5/56,1/45,1/8,3/38,1/20,1/22,1/12,
      1/28,1/15,1/31,3/38,1/14 ],
  [ 1/100465920,91/195840,49/19440,1/64,1/30,11/144,5/48,1/18,1/10,
      1/8,1/15,1/17,1/6,1/19,1/12,1/17 ],
  [ 1/17971200,23/30720,1/108,11/384,1/50,1/12,3/16,1/10,1/6,2/13,
      1/4 ],[ 1/35942400,23/61440,1/216,37/1280,1/100,1/24,3/16,1/20,
      1/4,1/13,1/4,1/10 ] ];
RECOG.SporadicsNames :=
[ "J1","M11","M12","J3","M23","M22","J2","He","Ru","HS","M24",
  "J4","ON","Th","McL","HN","Ly","Co3","Co2","Suz","Fi22","Co1",
  "Fi23","Fi24'","B","M","M12.2","M22.2","HS.2","J2.2","McL.2","Suz.2",
  "He.2","HN.2","Fi22.2","Fi24'.2","ON.2","J3.2","2F4(2)'","2F4(2)'.2"];
RECOG.SporadicsSizes :=
[ 175560,7920,95040,50232960,10200960,443520,604800,4030387200,
  145926144000,44352000,244823040,86775571046077562880,460815505920,
  90745943887872000,898128000,273030912000000,51765179004000000,
  495766656000,42305421312000,448345497600,64561751654400,
  4157776806543360000,4089470473293004800,1255205709190661721292800,
  4154781481226426191177580544000000,
  808017424794512875886459904961710757005754368000000000,190080,887040,
  88704000,1209600,1796256000,896690995200,8060774400,546061824000000,
  129123503308800,2510411418381323442585600,921631011840,100465920,
  17971200,35942400 ];
RECOG.SporadicsKillers :=
[ [[ 5,7 ]],[[ 5,7 ]],[[ 6,7 ]],[[ 11,9 ]],[[ 10,9 ]],[[ 5,7 ]],[[ 7,9 ]],
  [[ 11,14 ]],[[ 14,15 ]],[[ 10,8 ]],[[ 12,11 ]],[[ 29,20,26,23 ]],
  [[ 15,14 ]],[[ 20,19 ]],[[ 13,11 ]],[[ 12,16 ]],[[ 19,23 ]],[[ 11,14,16 ]],
  [[ 17,14,21 ]],[[ 15,13 ]],[ [ 18 .. 22 ] ],
  [ [ 26 .. 32 ],[ 25 .. 32 ] ],[ [ 28 .. 32 ],[ 27 .. 32 ] ],
  [ [ 27 .. 35 ],[ 29 .. 35 ],[ 27,29,34 ] ],  # the latter is for Fi23
  [ [ 31 .. 49 ],[ 40,41,42,43,44,45,46,48,49 ] ], # the latter is agains Fi23
  [ [ 32 .. 73 ],[ 61 .. 73 ] ],[[ 6,10 ]],[[ 7,12 ]],[[ 9,14 ]],[[ 9,10 ]],
  [[ 15,8,10 ]],[[ 13,12,21 ]],[[ 11,13,10 ]],[[ 25,17,20 ]],
  [[ 21,17 ],[23,24]],   # the latter is to distinguish Fi22.2 and Fi22
  [[ 35,32,23,26 ],[ 36,37,38,40,41,42,43 ]], # the latter is for Fi23
  [[ 18,12,14 ]],[[ 10,13 ]],[[ 7,11 ]],[[ 9,11 ]] ];
RECOG.SporadicsWorkers := [];
# Removed to avoid dependency on unpublished package gensift:
#RECOG.SporadicsWorkers[2] := SporadicsWorkerGenSift;   # M11
# and same for: M12, M22, J2, HS, Ly, Co3, Co2

# FIXME: unused?
RECOG.MakeSporadicsInfo := function(name)
  local ct,i,index,killers,o,orders,p,pos,prob,probs,probscopy,sum;
  ct := CharacterTable(name);
  orders := Set(OrdersClassRepresentatives(ct));
  probs := [];
  for o in orders do
      prob := 0;
      pos := Positions(OrdersClassRepresentatives(ct),o);
      for p in pos do
          prob := prob + 1/SizesCentralizers(ct)[p];
      od;
      Add(probs,prob);
  od;
  index := [1..Length(orders)];
  probscopy := ShallowCopy(probs);
  SortParallel(probscopy,index);
  sum := probscopy[Length(orders)];
  i := Length(orders);
  repeat
      i := i - 1;
      sum := sum + probscopy[i];
  until sum > 1/4;
  killers := index{[i..Length(orders)]};
  return rec( size := Size(ct), orders := orders,
              probabilities := probs, killers := killers, name := name );
end;

RECOG.RuleOutSmallProjOrder := function(m)
  local l,o,v;
  if IsPerm(m) then
      o := Order(m);
      if o > 119 then return fail; fi;
      return o;
  fi;
  v := ShallowCopy(m[1]);
  Randomize(v);
  ORB_NormalizeVector(v);
  o := Orb([m],v,OnLines,rec( hashlen := 300, report := 0 ));
  Enumerate(o,121);
  if not(IsClosed(o)) then return fail; fi;
  l := Length(o);
  Randomize(v);
  ORB_NormalizeVector(v);
  o := Orb([m],v,OnLines,rec( hashlen := 300, report := 0 ));
  Enumerate(o,121);
  if not(IsClosed(o)) then return fail; fi;
  l := Lcm(l,Length(o));
  if l > 119 then return fail; fi;
  return l;
end;

FindHomMethodsProjective.SporadicsByOrders := function(ri,G)
  local count,gens,i,j,jj,k,killers,l,limit,o,ordersseen,pp,r,raus,res,x;

  RECOG.SetPseudoRandomStamp(G,"SporadicsByOrders");

  l := [1..Length(RECOG.SporadicsNames)];
  pp := 0*l;
  ordersseen := [];
  count := 0;
  gens := GeneratorsOfGroup(G);
  limit := 120+Length(gens);
  for i in [1..limit] do
      if i <= Length(gens) then
          r := rec( el := gens[i] );
      else
          r := RandomElm(ri,"SporadicsByOrders",false);
      fi;
      o := RECOG.RuleOutSmallProjOrder(r.el);
      if o = fail then
          Info(InfoRecog,2,"Ruled out all sporadic groups.");
          return false;
      fi;
      if i <= Length(gens) then
          if ri!.projective then
              r.order := ProjectiveOrder(r.el)[1];
          else
              r.order := Order(r.el);
          fi;
      else
          GetElmOrd(ri,r);
      fi;
      o := r.order;
      x := r.el;
      AddSet(ordersseen,o);
      Info(InfoRecog,3,"Found order: ",String(o,3)," (element #",i,")");
      l := Filtered(l,i->o in RECOG.SporadicsElementOrders[i]);
      if l = [] then
          Info(InfoRecog,2,"Ruled out all sporadic groups.");
          return false;
      fi;
      # Throw out improbable ones:
      j := 1;
      while j <= Length(l) do
          if Length(l) = 1 then
              limit := 1/1000;
          else
              limit := 1/400;
          fi;
          jj := l[j];
          raus := false;
          for k in [1..Length(RECOG.SporadicsElementOrders[jj])] do
              if not(RECOG.SporadicsElementOrders[jj][k] in ordersseen) and
                 (1-RECOG.SporadicsProbabilities[jj][k])^i < limit then
                  Info(InfoRecog,3,"Have thrown out ",RECOG.SporadicsNames[jj],
                       " (did not see order ",
                       RECOG.SporadicsElementOrders[jj][k],")");
                  raus := true;
                  break;
              fi;
          od;
          if not(raus) and IsBound(RECOG.SporadicsKillers[jj]) then
            for killers in RECOG.SporadicsKillers[jj] do
              if Intersection(ordersseen,
                              RECOG.SporadicsElementOrders[jj]{killers})=[]
                 and (1-Sum(RECOG.SporadicsProbabilities[jj]{killers}))^i 
                     < 10^-3 then
                  raus := true;
                  break;
                  Info(InfoRecog,3,"Have thrown out ",RECOG.SporadicsNames[jj],
                       " (did not see orders in ",
                       RECOG.SporadicsElementOrders[jj]{killers},")");
              fi;
            od;
          fi;
          if raus then
              Remove(l,j);
          else
              j := j + 1;
          fi;
      od;
      if l = [] then
          Info(InfoRecog,2,"Ruled out all sporadic groups.");
          return false;
      fi;
      if Length(l) = 1 then
        count := count + 1;
        if count >= 9 then
          Info(InfoRecog,2,"I guess that this is the sporadic simple group ",
               RECOG.SporadicsNames[l[1]],".");
          break;
        fi;
      fi;
      if Length(l) < 6 then
          Info(InfoRecog,2,"Possible sporadics left: ",
               RECOG.SporadicsNames{l}," i=",i);
      else
          Info(InfoRecog,2,"Possible sporadics left: ",Length(l)," i=",i);
      fi;
  od;
  if ValueOption("DEBUGRECOGSPORADICS") <> fail then
      return RECOG.SporadicsNames{l};
  fi;
  for i in [1..Length(l)] do
      Info(InfoRecog,2,"Trying hint for ",RECOG.SporadicsNames[l[i]],"...");
      res := LookupHintForSimple(ri,G,RECOG.SporadicsNames[l[i]]);
      if res = true then return res; fi;
      if IsBound(RECOG.SporadicsWorkers[l[i]]) then
          Info(InfoRecog,2,"Calling its installed worker...");
          res := RECOG.SporadicsWorkers[l[1]](RECOG.SporadicsNames[l[i]],
                                        RECOG.SporadicsSizes[l[i]],ri,G);
          if res = true then return res; fi;
      fi;
      Info(InfoRecog,2,"This did not work.");
  od;
  return false;
end;

RECOG.LieTypeOrderFunc := RECOG.ProjectiveOrder;
RECOG.LieTypeSampleSize := 250;
RECOG.LieTypeNmrTrials := 10;

RECOG.OMppdset := function(p, o)
    local   primes;
    primes := Set(Factors(o));
    RemoveSet(primes,p);
    return Set(primes, l->OrderMod(p,l));
end;

RECOG.VerifyOrders := function (type, n, q, orders)
    local   p,  allowed,  maxprime,  r,  rq,  ii, LargestPrimeOccurs;
    LargestPrimeOccurs := function(r, orders)
        local   maxp;
        maxp := Maximum(Factors(r));
        return ForAny(orders, i->i mod maxp = 0);
    end;
    p := Factors(q)[1];
    allowed := orders;  
    maxprime := true;
    if type = "L" then
        if n = 2 then
            if p = 2 then
                allowed := Set([2, q-1, q+1]);
            else
                allowed := Set([p, (q-1)/2, (q+1)/2]);
          fi;
      elif n = 3 then
          if (q-1) mod 3 <> 0 then
              allowed := Set([4, p* (q-1), q^2-1, q^2+q+1]);
          else
              allowed := Set([4, p* (q-1)/3, q-1, (q^2-1)/3, (q^2+q+1)/3]);
          fi;
      elif n = 4 then
          if p = 2 then
              allowed := Set([4* (q-1), p* (q^2-1), q^3-1, (q^2+1)* (q-1), 
                              (q^2+1)* (q+1)]);
          elif p = 3 then
              allowed := Set([9, p* (q^2-1), q^3-1, (q^2+1)* (q-1), 
                              (q^2+1)* (q+1)]);
          elif (q-1) mod 2 <> 0 then
              allowed := Set([p*(q^2-1),q^3-1,(q^2+1)* (q-1), (q^2+1)* (q+1)]);
          elif (q-1) mod 4 = 2 then
              allowed := Set([p* (q^2-1), (q^3-1)/2, (q^2+1)* (q-1)/2,
                              (q^2+1)* (q+1)/2 ]);
          else
              allowed := Set([p* (q^2-1), (q^3-1)/4, (q^2+1)* (q-1)/4,
                              (q^2+1)* (q+1)/4 ]);
          fi;
      elif n = 5 and q = 2 then
          allowed := Set([8, 12, 14, 15, 21, 31]);
      elif n = 6 and q = 3 then
          allowed := Set([36, 78, 80, 104, 120, 121, 182]);
          maxprime := 91 in orders or 121 in orders;
      else
          maxprime := LargestPrimeOccurs (q^n-1, orders)
                      and LargestPrimeOccurs (q^(n-1)-1, orders)
                      and Maximum (orders) <= (q^n-1)/ (q-1)/Gcd (n,q-1);
          if n = 8 and q = 2 then
              maxprime := maxprime and LargestPrimeOccurs (7, orders);
              #/Set([ i : i in orders | i mod 21 = 0]) <> Set([]);
          fi;
      fi;
  elif type = "U" then
      if n = 3 then
          if (q+1) mod 3 <> 0 then
              allowed := Set([4, p* (q+1), q^2-1, q^2-q+1]);
          else
              allowed := Set([4, p* (q+1)/3, q+1, (q^2-1)/3, (q^2-q+1)/3]);
          fi;
      elif n = 4 then
          if p = 2 then
              allowed := Set([8, 4* (q+1), p* (q^2-1), q^3+1, (q^2+1)* (q-1), 
                              (q^2+1)* (q+1)]);
          elif p = 3 then
              allowed := Set([9, p* (q^2-1), q^3+1, (q^2+1)* (q-1), 
                              (q^2+1)* (q+1)]);
              if q = 3 then
                  maxprime := 8 in orders and 9 in orders;
              fi;
          elif (q+1) mod 2 <> 0 then
              allowed := Set([p*(q^2-1),q^3+1,(q^2+1)* (q-1), (q^2+1)* (q+1)]);
          elif (q+1) mod 4 = 2 then
              allowed := Set([p* (q^2-1), (q^3+1)/2, (q^2+1)* (q-1)/2,
                              (q^2+1)* (q+1)/2 ]);
              if q = 5 then
                  maxprime := Maximum (orders) > 21;
              fi;
          else
              allowed := Set([p* (q^2-1), (q^3+1)/4, (q^2+1)* (q-1)/4,
                              (q^2+1)* (q+1)/4 ]);
          fi;
      else
          r := 2 * ((n-1)/2)+1;
          maxprime := LargestPrimeOccurs (q^r+1, orders)
                      and Maximum (orders) <= (q^(r+1)-1)/ (q-1);
          if n = 6 and q = 2 then
              maxprime := maxprime and 18 in orders;
          fi;
      fi;
  elif type = "S" then
      if n = 4 then
          if q mod 2 = 0 then
              allowed := Set([4, p * (q-1), p * (q+1), q^2-1, q^2+1]);
          elif q mod 3 = 0 then
              allowed := Set([9, p * (q-1), p * (q+1), (q^2-1)/2, (q^2+1)/2]);
          else
              allowed := Set([p * (q-1), p * (q+1), (q^2-1)/2, (q^2+1)/2]);
          fi;
      elif n = 6 and q = 2 then
          allowed := Set([ 7, 8, 9, 10, 12, 15 ]);
          maxprime := 8 in orders and 15 in orders;
      else
          maxprime := LargestPrimeOccurs (q^(n/2)+1, orders) and
                      LargestPrimeOccurs (q^(n/2)-1, orders);
      fi;
  elif type = "O^+" and n = 8 and q = 2 then
      allowed := Set([ 7, 8, 9, 10, 12, 15 ]);
      maxprime := 8 in orders and 15 in orders;
  elif type = "O^+" and n = 10 and q = 2 then
      allowed := Set([ 18, 24, 31, 42, 45, 51, 60]);
  elif type = "O^-" then
      maxprime := LargestPrimeOccurs (q^(n/2)+1, orders) and
                  LargestPrimeOccurs (q^(n/2 -1)-1, orders);
  elif type = "2B" then
      rq := RootInt(2*q);
      allowed := Set([4, q-1, q-rq+1, q+rq+1]);
  elif type = "2G" then
      rq := RootInt(3*q);
      allowed := Set([9, 3* (q-1), q+1, q-rq+1, q+rq+1]);
  elif type = "G" then
      if p = 2 then
          allowed := Set([8, 4 * (q-1), 4 * (q+1), q^2-1, q^2-q+1, q^2+q+1]);
      elif p <= 5 then
          allowed := Set([p^2, p * (q-1), p * (q+1), q^2-1, q^2-q+1, q^2+q+1]);
      else
          allowed := Set([p * (q-1), p * (q+1), q^2-1, q^2-q+1, q^2+q+1]);
      fi;
  elif type = "2F" and q = 2 then
      allowed := Set([10, 12, 13, 16 ]);
  elif type = "2F" and q = 8 then
      allowed := Set([ 12, 16, 18, 20, 28, 35, 37, 52, 57, 63, 65, 91, 109 ]);
      maxprime := Maximum (orders) > 37;
  elif type = "3D" and q = 2 then
      allowed := Set([ 8, 12, 13, 18, 21, 28 ]);
      maxprime := Maximum (orders) > 13;
  elif type = "F" and q = 2 then
      allowed := Set([ 13, 16, 17, 18, 20, 21, 24, 28, 30 ]);
  elif type = "2E" and q = 2 then
      allowed := Set([ 13, 16, 17, 18, 19, 20, 21, 22, 24, 28, 30, 33, 35 ]);
  elif type = "E" and n = 7 and q = 2 then
      maxprime := Maximum (orders) <= 255;
  fi;
  
  if not maxprime then
      return "RO_CONTRADICTION";
  fi;
  for ii in allowed do
      orders := Filtered( orders, o-> ii mod o <> 0 );
  od;
  if orders = [] then
      return Concatenation(type,String(n), "(", String(q), ")");
  else
      return  "RO_CONTRADICTION";
  fi;
end;  #  VerifyOrders

#/*  P random process for group; 
#    distinguish PSp (2n, p^e) from Omega (2n + 1, p^e);
#    orders are orders of elements */
#

RECOG.DistinguishSpO := function (G, n, p, e, orders)
    local   twopart,   q,  goodtorus,  t1,  tp,  t2,  
            found,  tf,  ttf,  g,  o,  mp,  i,  x,  z,  po,  h;
    
    twopart := function (n)
        local k;
        k := 1;
        while n mod 2 = 0 do
            n := n/2; 
            k := k*2;
        od;
        return k;
    end;
    
    q := p^e;
    if n mod 2 = 1 and (q + 1) mod 4 = 0 then
        goodtorus := 2 * n; 
        t1 := q^n + 1;
        tp := twopart ((q^n + 1) / 2);
    else
        goodtorus := n; 
        t1 := q^n - 1;
        tp := twopart ((q^n - 1) / 2);
    fi;
    t2 := q^QuoInt(n , 2) + 1;
    
    found := false;
    tf := 0; ttf := 0;  # counters to deal with wrong char groups
    repeat
        g := PseudoRandom (G);
        o := RECOG.LieTypeOrderFunc (g);
        if o mod p <> 0 then
            ttf := ttf+1;
            mp := RECOG.OMppdset (p, o);
            
            
            if 2*o = t1 then
                tf := tf+1;
                g := g^(o / 2);
                found := n mod 2 = 1; 
                i := 0;
                while not found and i < 8 * n do
                    i := i+1;
                    x := PseudoRandom (G); 
                    z := g * g^x;
                    o := RECOG.LieTypeOrderFunc (z);
                    if o mod 2 = 1 then
                        po := RECOG.LieTypeOrderFunc (z^((o + 1) / 2) / x);
                        mp := RECOG.OMppdset (p, po);
                        if (q - 1) mod 4 = 0 and (n - 1) * e in mp or
                           (q + 1) mod 4 = 0 and 2 * (n - 1) * e in mp or
                           (q - 1) mod 4 = 0 and 2 * (n - 1) * e in mp or
                           (q + 1) mod 4 = 0 and 2 * n * e in mp
#		      or (n = 4 and 6 in mp)
                           then
                            found := true;
                  #printf"mp= %o, o (z)= %o\n", mp, Factorization (oo);
                        fi;
                    fi;
                od;
            fi;
        fi;
    until found or (tf > 15) or (ttf > 80);
    if ttf > 80 then 
        return "RO_NO_LUCK"; 
    fi;
    
    for i in [1..6 * n] do
        h := PseudoRandom (G); 
        o := Order (g * g^h);
        if (q * (q + 1) mod o <> 0) and (q * (q - 1) mod o <> 0) 
           then
            return RECOG.VerifyOrders ("S", 2 * n, q, orders);
        fi;
    od;
    
    return RECOG.VerifyOrders ("O", 2 * n + 1, q, orders);
    
end;   # DistinguishSpO

#
#/* compute Artin invariants for element of order o; 
#   p is characteristic */

RECOG.ComputeArtin := function (o, p)
    local   IsFermat,  IsMersenne,  primes,  orders;
    IsFermat := n-> IsPrime(n) and Set(Factors(n-1)) = [2];
    IsMersenne := n->IsPrime(n) and Set(Factors(n+1)) = [2];
    primes := Set(Factors(o));
    RemoveSet(primes,p);
    RemoveSet(primes,2);
    orders := Set(primes, x-> OrderMod(p, x));

    if IsFermat (p) and o mod 4 = 0 then 
        AddSet(orders,1);
    fi;
    if IsMersenne (p) and o mod 4 = 0 then 
        AddSet(orders,2);
    fi;
    if p = 2 and o mod 9 = 0 then
        AddSet(orders, 6);
    fi;
    return orders;
end;

#/* partition at most Nmr elements according to their 
#   projective orders listed in values; we consider
#   at most NmrTries elements; P is a random process */ 

RECOG.ppdSample := function (G, ppd, p, values, SampleSize) 
    local   Bins,  x,  j,  original,  NmrTries,  g,  o,  list;

    Bins := ListWithIdenticalEntries(Length(values),0);

   for x in ppd do
       for j in [1..Length(values)] do
           if values[j] in x then
               Bins[j] := Bins[j] + 1;
           fi;
       od;
   od;
   original := Length(ppd);
            
   ppd := [];

   NmrTries := 0;
   while NmrTries <= SampleSize do 
       NmrTries := NmrTries + 1;
       g := PseudoRandom (G);
       o := Order (g);
       list := RECOG.ComputeArtin (o, p);
       Add (ppd, list);
       for j in [1..Length(values)] do
           if values[j] in list then
               Bins[j] := Bins[j]+1;
           fi;
       od;
   od;
   

   return [Bins/(original + SampleSize), ppd, Bins];

end;

RECOG.OrderSample := function (G, p, orders, values, SampleSize)
    local    Bins,  i,  j,  original,  NmrTries,  g,  o,  
            Total;

    Bins := ListWithIdenticalEntries(Length(values),0);

   for i in orders do
      for j in [1..Length(values)] do
         if i mod values[j] = 0 then
            Bins[j] := Bins[j] + 1;
         fi;
      od;
   od;
   original := Length(orders);
            
   NmrTries := 0;
   while NmrTries <= SampleSize do 
      NmrTries := NmrTries + 1;
      g := PseudoRandom (G);
      o := RECOG.LieTypeOrderFunc (g);
      Add (orders, o);
      for j in [1..Length(values)] do
         if o mod values[j] = 0 then
            Bins[j] := Bins[j]+1;
         fi;
      od;
      Total := Sum(Bins);
   od;

   return [ Bins/ (SampleSize + original), orders, Bins] ;

end;

# PSL (2, p^k) vs PSp (4, p^(k / 2)) 
RECOG.PSLvsPSP := function (G, ppd, q, SampleSize, NmrTrials, orders)
    local   p,  g,  o,  v1,  values,  temp,  prob;
   p := Factors (q)[1];
   if q = 2 then
      repeat 
         SampleSize := SampleSize - 1;
         g := PseudoRandom (G);
         o := RECOG.LieTypeOrderFunc (g);
         if o = 4 then 
            return RECOG.VerifyOrders ("L",2,9, orders);
         fi;
      until SampleSize = 0;
      return RECOG.VerifyOrders ("L",2,4, orders);
   fi;

   v1 := Maximum (ppd);
   ppd := [];
   values := [v1];
   repeat 
       temp := RECOG.ppdSample (G, ppd, p, values, SampleSize);
       prob := temp[1];
       ppd  := temp[2];
       prob := prob[1];
       if prob >= 1/3 and prob < 1/2 then
           return RECOG.VerifyOrders ("L",2, q^2, orders);
       elif prob >= 1/5 and prob < 1/4 then
           return RECOG.VerifyOrders ("S",4, q, orders);
       fi;
       NmrTrials := NmrTrials + 1;
   until NmrTrials = 0;

   if NmrTrials = 0 then 
#      return "Have not settled this recognition"; 
      return "RO_NO_LUCK"; 
   fi;

end;


RECOG.OPlus82vsS62 := function (G, orders, SampleSize)
    local   values,  temp,  prob;
    values := [15];
    temp := RECOG.OrderSample (G, 2, [], values, SampleSize);
    prob := temp[1]; 
    orders := temp[2];
    prob := prob[1];
#"prob is ", prob;
    if AbsoluteValue (1/5 - prob) < AbsoluteValue (1/15 - prob) then 
        return RECOG.VerifyOrders ("O^+",8, 2, orders );
    else 
        return RECOG.VerifyOrders ("S",6, 2, orders );
    fi;
end;

RECOG.OPlus83vsO73vsSP63 := function (G, orders, SampleSize)
    local   values,  temp,  prob;
    values := [20];
    temp := RECOG.OrderSample (G, 3, [], values, SampleSize);
    prob := temp[1];
    orders := temp[2];
    prob := prob[1];
    if AbsoluteValue (3/20 - prob) < AbsoluteValue (1/20 - prob) then 
        return "O^+_8(3)";
    else 
        return RECOG.DistinguishSpO (G, 3, 3, 1, orders);
    fi;
end;


RECOG.OPlus8vsO7vsSP6 := function (G, orders, p, e, SampleSize)
    local   i,  g,  o,  list;

   for i in [1..SampleSize] do
       g := PseudoRandom (G);
       o := RECOG.LieTypeOrderFunc (g);
       list := RECOG.ComputeArtin (o, p);
       if IsSubset(list, [e, 2 * e, 4 * e]) then
           return RECOG.VerifyOrders ("O^+",8, p^e , orders);    
       fi;
   od;
   if p = 2 then
       return RECOG.VerifyOrders ("S",6, 2^e, orders);
   else
       return RECOG.DistinguishSpO (G, 3, p, e, orders);
   fi;
end;


#// O- (8, p^e) vs S (8, p^e) vs O (9, p^e) 
RECOG.OMinus8vsSPvsO := function (G, v1, p, e, orders, SampleSize, NmrTrials)
    local   ppd,  values,  epsilon,  temp,  prob;
    ppd := [];
    values := [v1];
    epsilon := 1/50;
    repeat 
        temp := RECOG.ppdSample (G, ppd, p, values, SampleSize);
        prob := temp[1]; 
        ppd := temp[2];
#"prob is ", prob;
        prob := prob[1];
        if prob >= 1/5 - epsilon and prob < 1/4 + epsilon then
            return RECOG.VerifyOrders ("O^-",8, p^(v1/8), orders);
        elif prob >= 1/10 - epsilon and prob < 1/8 + epsilon then
            if p = 2 then
                return RECOG.VerifyOrders ("S",8, 2^e, orders);
            else
                return RECOG.DistinguishSpO (G, 4, p, e, orders);
            fi;
        fi;
        NmrTrials := NmrTrials - 1;
    until NmrTrials = 0;
    
    if NmrTrials = 0 then 
#      return "Have not settled this recognition"; 
        return "RO_NO_LUCK"; 
    fi;
    
end;

RECOG.ArtinInvariants := function (G, p, Nmr)
    local   orders,  combs,  invariants,  newv1,  v1,  i,  g,  o,  
            ppds;

    orders := []; 
    combs := [];
    if p > 2 then 
        invariants := [0, 1, 2];
    else 
        invariants := [0, 1];
    fi;
    newv1 := Maximum (invariants);
    repeat
        v1 := newv1;
        for i in [1..Nmr] do
            g := PseudoRandom (G);
            o := RECOG.LieTypeOrderFunc (g);
            AddSet (orders, o);
            if o mod 3 = 0 then 
                AddSet(orders,3);
            fi;
            if o mod 4 = 0 then 
                AddSet (orders, 4); 
            fi;
            ppds := RECOG.OMppdset (p, o);
            if p = 2 and o mod 9 = 0 then 
                AddSet (ppds, 6);
                AddSet (orders, 9);
            fi;
            UniteSet(invariants,ppds);
            UniteSet(combs, Combinations (ppds, 2));
        od;
        newv1 := Maximum (invariants);
    until newv1 = v1;
    return [invariants, combs, orders];
end; # ArtinInvariants


RECOG.LieType := function (G, p, orders, Nmr)
    local   temp,  invar,  combs,  orders2,  v1,  v2,  w,  v3,  e,  m,  
            bound,  combs2;

    #   P := RandomProcess ( G );
    temp := RECOG.ArtinInvariants (G, p, Nmr);
    invar := temp[1];
    combs := temp[2];
    orders2 := temp[3];
   UniteSet(orders, orders2);
   
   v1 := Maximum (invar);
   RemoveSet(invar, v1);

   if v1 = 2 then
      return RECOG.VerifyOrders ("L",2, p, orders);
   fi;

   if v1 = 3 then
      if p > 2 then
         return RECOG.VerifyOrders ("L",3, p, orders);
      elif 8 in orders then
         return RECOG.VerifyOrders ("U",3, 3, orders);
      else
         return RECOG.VerifyOrders ("L",3, 2, orders);
      fi; 
   fi;


   if v1 = 4 then
      if 3 in invar then
         if p > 2 then
            return RECOG.VerifyOrders ("L",4, p, orders);
         elif 15 in orders then
	    return RECOG.VerifyOrders ("L",4, 2, orders);
         else
            return RECOG.VerifyOrders ("L",3, 4, orders);
         fi; 
      else
         return RECOG.PSLvsPSP (G, [1, 2, 4], p, RECOG.LieTypeSampleSize, 
                   RECOG.LieTypeNmrTrials, orders);
      fi;
   fi;  # v1 = 4

   v2 := Maximum (invar);
   w := v1 / (v1 - v2);

#v1; v2; w; invar; orders;
   if v1 = 12 and v2 = 4 and p = 2 then
      if 21 in orders then
         return RECOG.VerifyOrders ("G",2, 4, orders);
      elif 16 in orders then
         return RECOG.VerifyOrders ("2F",4, 2, orders);
      elif 7 in orders then
         return RECOG.VerifyOrders ("2B",2, 8, orders);
      elif 15 in orders then
         return RECOG.VerifyOrders ("U",3, 4, orders);
      else 
          return "RO_CONTRADICTION";
      fi; 
   fi;  # v2 = 4

   RemoveSet(invar,v2);
   if Length(invar)  = 0 then 
       return "RO_Unknown"; 
   fi;
   v3 := Maximum (invar);

#printf"p, v1, v2, v3: %o %o %o %o;",p,v1,v2,v3; invar; combs; orders;
   if v1 mod 2 = 1 then
      e := v1 - v2;
      if v1 mod e <> 0 then
         return "RO_CONTRADICTION";
      fi;
      m := v1/e;
      if v3 <> e* (m-2) then
          return "RO_CONTRADICTION";
      fi;
      return RECOG.VerifyOrders ("L", m, p^e, orders);
   fi;

   if w = 3/2 then
      if p = 2 and not 3 in orders then
      	 if v1 mod 8 <> 4 then
	    return "RO_CONTRADICTION";
	 fi;
	 return RECOG.VerifyOrders ("2B",2,2^(v1 / 4), orders);
      fi;
      if v1 mod 6 <> 0 then
         return "RO_CONTRADICTION";
      fi;
      if p = 3 and not 4 in orders then
         if v1 > 6 then
            if v1 mod 12 <> 6 then
	       return "RO_CONTRADICTION";
	    fi;
	    return RECOG.VerifyOrders ("2G",2, 3^(v1 / 6), orders);
         else
	    return RECOG.VerifyOrders ("L",2, 8, orders);
         fi;
      fi;
      return RECOG.VerifyOrders ("U",3, p^(v1 / 6), orders);
   fi; 

   if w = 4/3 then
      if p = 2 and v1 mod 8 = 4 then
	 return RECOG.VerifyOrders ("2B",2, 2^(v1 / 4), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;

   if w = 2 then  # exceptional groups
      if v1 mod 12 = 0 and not ([v1 / 3, v1] in combs) then
         if 4 * v3 = v1 then
            return RECOG.VerifyOrders ("3D",4, p^(v1 / 12), orders);
         elif (v1 / 4) in invar or (p = 2 and v1 = 24) then
            return RECOG.VerifyOrders ("G",2, p^(v1 / 6), orders);
         else
	    if p = 2 and v1 mod 24 = 12 and 12*v3 = 4*v1 then
               return RECOG.VerifyOrders ("2F",4,2^(v1 / 12), orders); 
	    else return "RO_CONTRADICTION";
	    fi;
         fi; 

  #    /* next clause is replacement for error in draft of paper */
      elif v1 mod 12 = 6 and Maximum (orders) <= p^(v1/3) + p^(v1/6) + 1 then
         return RECOG.VerifyOrders ("G",2, p^(v1 / 6), orders);
      fi; 

      if v1 mod 4 = 2 then
	 return RECOG.VerifyOrders ("L",2,p^(v1 / 2), orders);
      else
         return RECOG.PSLvsPSP (G, Union(invar,[v1, v2]),p^(v1 / 4),
                  RECOG.LieTypeSampleSize, RECOG.LieTypeNmrTrials, orders);
      fi;
   fi;  # w = 2

#printf"p, v1, v2, v3: %o %o %o %o;",p,v1,v2,v3; invar; combs; orders;
   if w = 3 then
      if v1 mod 18 = 0 and 18 * v3 = 10 * v1 then
         if 8* (v1 / 18) in invar then
            return RECOG.VerifyOrders ("2E",6, p^(v1 / 18), orders);
	 else return "RO_OTHER";
	 fi;
      elif v1 mod 12 = 0 then
         if v1 > 12 or p > 2 then
            if v1 = 2 * v3 and not ([v1 / 2, v1] in combs)
               and not ([v1 / 3, v1] in combs) then
               return RECOG.VerifyOrders ("F",4, p^(v1 / 12), orders);
            fi;
         elif 9 in orders and not ([4, 12] in combs) then
            return RECOG.VerifyOrders ("F",4, 2, orders);
         fi;  
      fi; 
   fi;  # w = 3

   if w = 4 and 8 * v1 = 12 * v3 then
      if v1 mod 12 = 0 then
         return RECOG.VerifyOrders ("E",6, p^(v1 / 12), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;

   if w = 9/2 and 12 * v1 = 18 * v3 then
      if v1 mod 18 = 0 then
         return RECOG.VerifyOrders ("E",7, p^(v1 / 18), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;

   if w = 5 and 20 * v1 = 30 * v3 then
      if v1 mod 30 = 0 then
         return RECOG.VerifyOrders ("E",8, p^(v1 / 30), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;   # exceptional groups

   if v1 mod (v1 - v2) <> 0 then   # unitary groups
      if (v1-v2) mod 4 <> 0  or  2 * v1 mod (v1 - v2) <> 0 then 
          return "RO_OTHER";
      fi;
      e := (v1-v2) / 4;
      m := (2 * v1) / (v1 - v2);
      if ((m + 1) mod 4 = 0 and e * (m + 1) in invar) or
        ((m + 1) mod 4 <> 0 and e * (m + 1) / 2 in invar) then
	    if (m > 7 and v2-v3 = 4*e) or (m <= 7 and v2-v3 = 2*e) then
               return RECOG.VerifyOrders ("U", m + 1, p^e, orders);
	    fi;
      else
         if (m > 5 and v2-v3 = 4*e) or (m = 5 and v2-v3 = 2*e) then
            return RECOG.VerifyOrders ("U", m, p^e, orders);
	 fi;
      fi;
      return "RO_OTHER";
   fi;   # unitary groups
   
#printf"1: v1 v2 v3 = %o %o %o;;",v1, v2, v3; invar;
   if (v1 - v2) mod 2 <> 0 then
      e := v1 - v2;  m := v1 / (v1 - v2);
      if v3 = e* (m-2) or (p = 2 and e* (m-2) = 6) or (m <= 3) then
         return RECOG.VerifyOrders ("L", m, p^e, orders);
      else
         return "RO_OTHER";
      fi;
   fi;
   
   e := (v1 - v2) / 2; m := v1 / (v1 - v2);  # only classical grps remain

   if p = 2 and e * m = 6 and e <= 2 and 91 in orders then
      if v3 = 10-2*e  or  m = 3 then
         return RECOG.VerifyOrders ("L", m, 2^(2 * e), orders);
      else
         return "RO_OTHER";
      fi;
   fi;

   if Set([m * e, v1]) in combs then
      if v3 = 2*e* (m-2) or m <= 3 then
         return RECOG.VerifyOrders ("L", m, p^(2 * e), orders);
      else
         return "RO_OTHER";
      fi;
   fi;

   if m = 3 then
      if 3 * v3 = v1 then
         return RECOG.VerifyOrders ("U",4, p^(v1 / 6), orders);
      else
         if p^e = 2 then
            return RECOG.OPlus82vsS62 (G, orders, RECOG.LieTypeSampleSize);
         fi;
         if p^e = 3 then
            return RECOG.OPlus83vsO73vsSP63 (G,orders,RECOG.LieTypeSampleSize);
         else
            return RECOG.OPlus8vsO7vsSP6 (G,orders,p,e,RECOG.LieTypeSampleSize);
         fi; 
      fi;
   fi;

   if v3 <> 2*e* (m-2) and (m > 4 or v3 <> 5*e) then   # wrong characteristic
      return "RO_OTHER";
   fi;
   
   if IsMatrixGroup(G) then
       bound := 5*DimensionOfMatrixGroup(G);
   else
       bound := 100;
   fi;
   temp := RECOG.ArtinInvariants (G, p, bound);
   invar := temp[1]; combs2 := temp[2]; orders2 := temp[3];
   combs := Union(combs, combs2);
   orders := Union(orders, orders2);
   if m mod 2 = 0 then
      if [m * e, (m + 2) * e] in combs then
          return RECOG.VerifyOrders ("O^+", 2 * m + 2, p^e, orders);
      elif m = 4 then 
         return RECOG.OMinus8vsSPvsO(G,v1,p,e,orders,RECOG.LieTypeSampleSize,
                                     RECOG.LieTypeNmrTrials);
      else #/* m >= 6 */
         if [ (m - 2) * e, (m + 2) * e] in combs then
            if p = 2 then 
               return RECOG.VerifyOrders ("S", 2 * m, 2^e, orders);
            else 
               return RECOG.DistinguishSpO (G, m, p, e, orders);
            fi;
         else
            return RECOG.VerifyOrders ("O^-", 2*m, p^e, orders);
         fi; 
      fi;  # m even
   elif [(m - 1) * e, (m + 3) * e] in combs then
      return RECOG.VerifyOrders ("O^+", 2 * m + 2, p^e, orders);
   elif [(m - 1) * e, (m + 1) * e] in combs then
      if p = 2 then 
         return RECOG.VerifyOrders ("S", 2 * m, 2^e, orders);
      fi;
      # p <> 2 case 
      return RECOG.DistinguishSpO (G, m, p, e, orders);
   else
      return RECOG.VerifyOrders ("O^-", 2 * m, p^e, orders);
   fi; 

   return "RO_undecided";
end;

FindHomMethodsProjective.LieTypeNonConstr := function(ri,G)
    local count,dim,f,i,ords,p,q,r,res;
    RECOG.SetPseudoRandomStamp(G,"LieTypeNonConstr");
    dim := ri!.dimension;
    f := ri!.field;
    q := Size(f);
    p := Characteristic(f);

    count := 0;
    ords := Set(ri!.simplesoclerando);
    while true do   # will be left by return
        r := RECOG.LieType(ri!.simplesocle,p,ords,30+10*dim);
        if not(IsString(r)) or r{[1..3]} <> "RO_" then
            # We found something:
            Info(InfoRecog,2,"LieTypeNonConstr: found ",r,
                 ", lookup up hints...");
            ri!.comment := Concatenation("_",r);
            res := LookupHintForSimple(ri,G,r);
            if res = true then return true; fi;
            Info(InfoRecog,2,"LieTypeNonConstr: giving up.");
            return fail;
        fi;
        count := count + 1;
        if count > 3 then
            Info(InfoRecog,2,"LieTypeNonConstr: giving up...");
            return fail;
        fi;
        Info(InfoRecog,2,"LieTypeNonConstr: need more element orders...");
        for i in [1..dim] do
            AddSet(ords,RandomElmOrd(ri,"LieTypeNonConstr",false).order);
        od;
    od;
end;

##
##  This program is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program.  If not, see <http://www.gnu.org/licenses/>.
##

