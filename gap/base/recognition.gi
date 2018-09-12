#############################################################################
##
##  recognition.gi        recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors
##  This file is free software, see license information at the end.
##
##  The generic code for recognition, implementation part.
##
#############################################################################


# First some technical preparations:

# The type:

InstallValue( RecognitionInfoType,
  NewType(RecognitionInfoFamily, IsRecognitionInfo and IsAttributeStoringRep));


# one can now create objects by doing:
# r := rec( ... )
# Objectify(RecognitionInfoType,r);


# a nice view method:
RECOG_ViewObj := function( level, ri )
    local ms;
    if IsReady(ri) then
        Print("<recoginfo ");
    else
        Print("<failed recoginfo ");
    fi;
    if IsBound(ri!.projective) and ri!.projective then
        Print("(projective) ");
    fi;
    if Hasfhmethsel(ri) then
        ms := fhmethsel(ri);
        if IsRecord(ms) then
            if IsBound(ms.successMethod) then
                Print(ms.successMethod);
            else
                Print("NO STAMP");
            fi;
        elif IsString(ms) then
            Print(ms);
        fi;
        if IsBound(ri!.comment) then
            Print(ri!.comment);
        fi;
    fi;
    if HasIsSimpleGroup(ri) and IsSimpleGroup(ri) then
        Print(" Simple");
    elif HasIsAlmostSimpleGroup(ri) and IsAlmostSimpleGroup(ri) then
        Print(" AlmostSimple");
    fi;
    if HasSize(ri) then
        Print(" Size=",Size(ri));
    fi;
    if HasGrp(ri) and IsMatrixGroup(Grp(ri)) then
        Print(" Dim=",ri!.dimension);
        Print(" Field=",Size(ri!.field));
    fi;
    if not(IsLeaf(ri)) then
        Print("\n",String("",level)," F:");
        if HasRIFac(ri) then
            RECOG_ViewObj(level+3, RIFac(ri));
        else
            Print("has no factor");
        fi;
        Print("\n",String("",level), " K:");
        if HasRIKer(ri) then
            if RIKer(ri) = fail then
                Print("<trivial kernel");
            else
                RECOG_ViewObj(level+3, RIKer(ri));
            fi;
        else
            Print("has no kernel");
        fi;
    fi;
    Print(">");
  end;

InstallMethod( ViewObj, "for recognition infos", [IsRecognitionInfo],
  function(ri)
    RECOG_ViewObj(0, ri);
  end);


#############################################################################
# The main recursive function:
#############################################################################

InstallGlobalFunction( RecognisePermGroup,
  function(G)
    return RecogniseGeneric(G,FindHomDbPerm,"");
  end);

InstallGlobalFunction( RecogniseMatrixGroup,
  function(G)
    return RecogniseGeneric(G,FindHomDbMatrix,"");
  end);

InstallGlobalFunction( RecogniseProjectiveGroup,
  function(G)
    return RecogniseGeneric(G,FindHomDbProjective,"");
  end);

InstallGlobalFunction( RecogniseBBGroup,
  function(G)
    return RecogniseGeneric(G,FindHomDbBB,"");
  end);

InstallGlobalFunction( RecogniseGroup,
  function(G)
    if IsPermGroup(G) then
        return RecogniseGeneric(G,FindHomDbPerm,"");
    elif IsMatrixGroup(G) then
        return RecogniseGeneric(G,FindHomDbMatrix,"");
    else
        return RecogniseGeneric(G,FindHomDbBB,"");
    fi;

# TODO: perhaps check if the result does not have IsReady set;
# in that case print a warning or error or ...?

    # Note: one cannot use "RecogniseGroup" to recognise projective groups
    #       as of now since "Projective groups" do not yet exist as GAP
    #       objects here!
  end);

# TODO: TryFindHomMethod is never called by anything
# in recog.
# Seems to be for user intervention and/or debugging?
# If so, document it accordingly. Otherwise remove it!
InstallGlobalFunction( TryFindHomMethod,
  function( g, method, projective )
    local result,ri;
    ri := EmptyRecognitionInfoRecord(rec(),g,projective);
    Unbind(g!.pseudorandomfunc);
    result := method(ri,g);
    if result in [TemporaryFailure, NeverApplicable] then
        return result;
    else
        SetFilterObj(ri,IsReady);
        Setfhmethsel(ri,"User");
        return ri;
    fi;
  end );

InstallGlobalFunction( EmptyRecognitionInfoRecord,
  function(r,H,projective)
    local ri;
    ri := ShallowCopy(r);
    Objectify( RecognitionInfoType, ri );
    ri!.nrgensH := Length(GeneratorsOfGroup(H));
    SetGrp(ri,H);
    Setslpforelement(ri,SLPforElementGeneric);
    SetgensN(ri,[]);       # this will grow over time
    Setimmediateverification(ri,false);
    Setforkernel(ri,rec(hints := []));
          # this is eventually handed down to the kernel
    Setforfactor(ri,rec(hints := []));
          # this is eventually handed down to the factor
    if projective then
        Setisone(ri,IsOneProjective);
        Setisequal(ri,IsEqualProjective);
    else
        Setisone(ri,IsOne);
        Setisequal(ri,\=);
    fi;
    ri!.projective := projective;
    # FIXME: perhaps DON'T set a default for findgensNmeth, to ensure
    # people always set a value? Or at least find some way so that
    # methods must explicitly acknowledge that they want the default...
    SetfindgensNmeth(ri,rec(method := FindKernelFastNormalClosure,
                            args := [6,3]));
    if IsMatrixGroup(H) then
        ri!.field := FieldOfMatrixGroup(H);
        ri!.dimension := DimensionOfMatrixGroup(H);
    fi;
    ri!.pr := ProductReplacer(GeneratorsOfGroup(H));
    ri!.gensHmem := GeneratorsWithMemory(GeneratorsOfGroup(H));
    ri!.prodrep := ProductReplacer(ri!.gensHmem, rec( maxdepth := 400 ));
    ri!.randr := EmptyPlist(100);
    ri!.rando := EmptyPlist(100);
    ri!.randp := EmptyPlist(100);
    ri!.randrpt := rec();
    ri!.randopt := rec();
    ri!.randppt := rec();
    ri!.randstore := true;  # TODO: try what happens if we change this to false in terms of performance
    H!.pseudorandomfunc := [rec(func := function(ri,name,bool)
                                          return RandomElm(ri,name,bool).el;
                                        end,
                                args := [ri,"PseudoRandom",false])];
    return ri;
  end );

RECOG.SetPseudoRandomStamp := function(g,st)
  if IsBound(g!.pseudorandomfunc) then
      g!.pseudorandomfunc[Length(g!.pseudorandomfunc)].args[2] := st;
  fi;
end;

InstallMethod( RandomElm, "for a recognition info record, a string and a bool",
  [ IsRecognitionInfo, IsString, IsBool ],
  function(ri, s, mem)
    local pos,el;
    if ri!.randstore then
        if not(IsBound(ri!.randrpt.(s))) then
            ri!.randrpt.(s) := 1;
            pos := 1;
        else
            ri!.randrpt.(s) := ri!.randrpt.(s) + 1;
            pos := ri!.randrpt.(s);
        fi;
        if not(IsBound(ri!.randr[pos])) then
            ri!.randr[pos] := Next(ri!.prodrep);
        fi;
        el := ri!.randr[pos];
    else
        el := Next(ri!.prodrep);
    fi;
    if mem then
        return rec( el := el, nr := pos );
    else
        return rec( el := el!.el, nr := pos );
    fi;
  end );

InstallMethod( RandomElmOrd,
  "for a recognition info record, a string and a bool",
  [ IsRecognitionInfo, IsString, IsBool ],
  function(ri, s, mem)
    local pos,res;
    if ri!.randstore then
        if not(IsBound(ri!.randopt.(s))) then
            ri!.randopt.(s) := 1;
            pos := 1;
        else
            ri!.randopt.(s) := ri!.randopt.(s) + 1;
            pos := ri!.randopt.(s);
        fi;
        if not(IsBound(ri!.rando[pos])) then
            if not(IsBound(ri!.randr[pos])) then
                ri!.randr[pos] := Next(ri!.prodrep);
            fi;
            if ri!.projective then
                ri!.rando[pos] := ProjectiveOrder(ri!.randr[pos]!.el)[1];
            else
                ri!.rando[pos] := Order(ri!.randr[pos]!.el);
            fi;
        fi;
        res := rec( order := ri!.rando[pos], projective := ri!.projective,
                    el := ri!.randr[pos] );
    else
        res := rec( el := Next(ri!.prodrep) );
        if ri!.projective then
            res.order := ProjectiveOrder(res.el!.el)[1];
        else
            res.order := Order(res.el!.el);
        fi;
        res.projective := ri!.projective;
        Add(ri!.rando,res.order);
    fi;
    if not(mem) then
        res.el := res.el!.el;
    fi;
    return res;
  end );

InstallMethod( GetElmOrd, "for a recognition info record and a record",
  [ IsRecognitionInfo, IsRecord ],
  function( ri, r )
    local x;
    if ri!.randstore and r.nr > 0 then
        if not( IsBound(ri!.rando[r.nr]) ) then
            if ri!.projective then
                ri!.rando[r.nr] := ProjectiveOrder(ri!.randr[r.nr]!.el)[1];
            else
                ri!.rando[r.nr] := Order(ri!.randr[r.nr]!.el);
            fi;
            r.order := ri!.rando[r.nr];
        else
            r.order := ri!.rando[r.nr];
        fi;
    else
        if IsObjWithMemory(r.el) then
            x := r.el!.el;
        else
            x := r.el;
        fi;
        if ri!.projective then
            r.order := ProjectiveOrder(x)[1];
        else
            r.order := Order(x);
        fi;
    fi;
  end );

InstallMethod( RandomElmPpd,
  "for a recognition info record, a string and a bool",
  [ IsRecognitionInfo, IsString, IsBool ],
  function(ri, s, mem)
    local pos,res;
    if ri!.randstore then
        if not(IsBound(ri!.randppt.(s))) then
            ri!.randppt.(s) := 1;
            pos := 1;
        else
            ri!.randppt.(s) := ri!.randppt.(s) + 1;
            pos := ri!.randppt.(s);
        fi;
        if not(IsBound(ri!.randp[pos])) then
            if not(IsBound(ri!.randr[pos])) then
                ri!.randr[pos] := Next(ri!.prodrep);
            fi;
            if not(IsMatrix(ri!.randr[pos])) then
                Error("ppd elements only make sense for matrices");
            fi;
            res := rec( el := ri!.randr[pos] );
            res.charpoly := CharacteristicPolynomial(ri!.field,ri!.field,
                                                     res.el!.el,1);
            res.factors := Factors(PolynomialRing(ri!.field), res.charpoly);
            res.degrees := List(res.factors,Degree);
            res.degset := Set(res.degrees);
            ri!.randp[pos] := ShallowCopy(res);
            Unbind(ri!.randp[pos].el);
        else
            res := ShallowCopy(ri!.randp[pos]);
            res.el := ri!.randr[pos];
        fi;
    else
        res := rec( el := Next(ri!.prodrep) );
        res.charpoly := CharacteristicPolynomial(ri!.field,ri!.field,
                                                 res.el!.el,1);
        res.factors := Factors(PolynomialRing(ri!.field), res.charpoly);
        res.degrees := List(res.factors,Degree);
        res.degset := Set(res.degrees);
    fi;
    if not(mem) then
        res.el := res.el!.el;
    fi;
    return res;
  end );

InstallMethod( GetElmPpd, "for a recognition info record and a record",
  [ IsRecognitionInfo, IsRecord ],
  function( ri, r )
    local x;
    if IsObjWithMemory(r.el) then
        x := r.el!.el;
    else
        x := r.el;
    fi;
    if ri!.randstore and r.nr > 0 then
        if not( IsBound(ri!.randp[r.nr]) ) then
            r.charpoly := CharacteristicPolynomial(ri!.field,ri!.field,x,1);
            r.factors := Factors(PolynomialRing(ri!.field), r.charpoly);
            r.degrees := List(r.factors,Degree);
            r.degset := Set(r.degrees);
            ri!.randp[r.nr] := ShallowCopy(r);
            Unbind(ri!.randp[r.nr].el);
            Unbind(ri!.randp[r.nr].nr);
        else
            r.charpoly := ri!.randp[r.nr].charpoly;
            r.factors := ri!.randp[r.nr].factors;
            r.degrees := ri!.randp[r.nr].degrees;
            r.degset := ri!.randp[r.nr].degset;
        fi;
    else
        r.charpoly := CharacteristicPolynomial(ri!.field,ri!.field,x,1);
        r.factors := Factors(PolynomialRing(ri!.field), r.charpoly);
        r.degrees := List(r.factors,Degree);
        r.degset := Set(r.degrees);
    fi;
  end );


InstallMethod( RandomOrdersSeen, "for a recognition info record",
  [ IsRecognitionInfo ],
  function(ri)
    return Compacted(ri!.rando);
  end );

InstallMethod( StopStoringRandEls, "for a recognition info record",
  [ IsRecognitionInfo ],
  function(ri)
    ri!.randstore := false;
    Unbind(ri!.randr);
    Unbind(ri!.randp);
    Unbind(ri!.randrpt);
    Unbind(ri!.randopt);
    Unbind(ri!.randppt);
    ri!.rando := Compacted(ri!.rando);
    # Note that we keep the random element orders seen!
  end );

InstallGlobalFunction( PrintTreePos,
  function(mark,depth,H)
    if InfoLevel(InfoRecog) = 1 then
        if IsMatrixGroup(H) then
            Print(mark," dim=",String(DimensionOfMatrixGroup(H),4),
                  " field=",Size(FieldOfMatrixGroup(H))," ",
                  String(Length(depth),2)," ",depth,"   \r");
        elif IsPermGroup(H) then
            Print(mark," pts=",String(LargestMovedPoint(H),6)," ",
                  String(Length(depth),2)," ",depth,"   \r");
        else
            Print(mark," ",String(Length(depth),2)," ",depth,"   \r");
        fi;
    fi;
  end );

InstallGlobalFunction( RecogniseGeneric,
  function(arg)
    # Assume all the generators have no memory!
    local H,N,depth,done,i,knowledge,l,ll,methgensN,methoddb,allmethods,
          proj1,proj2,ri,rifac,riker,s,x,y,z,succ,counter;

    # Look after arguments:
    H := arg[1];
    methoddb := arg[2];
    depth := arg[3];    # FIXME: why is this a string? perhaps rename to depthString? or indentString...
    if Length(arg) = 4 then
        knowledge := arg[4];
    else
        knowledge := rec();
    fi;

    PrintTreePos("E",depth,H);
    Info(InfoRecog,4,"Recognising: ",H);

    if Length(GeneratorsOfGroup(H)) = 0 then
        H := Group([One(H)]);
    fi;

    # Set up the record and the group object:
    if IsIdenticalObj( methoddb, FindHomDbProjective ) then
        ri := EmptyRecognitionInfoRecord(knowledge,H,true);
    else
        ri := EmptyRecognitionInfoRecord(knowledge,H,false);
    fi;
    ri!.depth := Length(depth);
    ri!.depthst := depth;   # FIXME: rename depthst to depthString or so?
    # was here earlier: Setcalcnicegens(ri,CalcNiceGensGeneric);
    Setmethodsforfactor(ri,methoddb);

    # Find a possible homomorphism (or recognise this group as leaf)
    if IsBound(knowledge.hints) and Length(knowledge.hints) > 0 then
        allmethods := Concatenation(knowledge.hints,methoddb);
        Sort(allmethods,function(a,b) return a.rank > b.rank; end);
        Setfhmethsel(ri,CallMethods( allmethods, 10, ri, H));
    else
        Setfhmethsel(ri,CallMethods( methoddb, 10, ri, H ));
        # TODO: extract the value 10 into a named constant, and / or make it
        #       an option parameter to the func
    fi;
    # Reset the pseudo random stamp:
    RECOG.SetPseudoRandomStamp(Grp(ri),"PseudoRandom");
    if fhmethsel(ri).result = TemporaryFailure then
        # FIXME: shouldn't we print an error here? at least if the user called us...
        # Perhaps yes: this is an ri which does NOT have IsReady set, and may be useful for debugging...
        SetFilterObj(ri,IsLeaf);
        if InfoLevel(InfoRecog) = 1 and depth = "" then Print("\n"); fi;
        return ri;
    fi;

    # Handle the leaf case:
    if IsLeaf(ri) then
        # If nobody has set how we produce preimages of the nicegens:
        if not(Hascalcnicegens(ri)) then
            Setcalcnicegens(ri,CalcNiceGensGeneric);
        fi;
        if Hasslptonice(ri) then
            SlotUsagePattern(slptonice(ri));
        fi;
        # Handle the case that nobody set nice generators:
        if not(HasNiceGens(ri)) then
            if Hasslptonice(ri) then
                SetNiceGens(ri,ResultOfStraightLineProgram(slptonice(ri),
                                            GeneratorsOfGroup(H)));
            else
                # FIXME: is this a good idea???
                # maybe an error would be better for debugging
                SetNiceGens(ri,GeneratorsOfGroup(H));
            fi;
        fi;
        # these two were set correctly by FindHomomorphism
        if IsLeaf(ri) then SetFilterObj(ri,IsReady); fi;
        # FIXME: settle what IsReady means *exactly*;
        # if it means that the leaf is "guaranteed" to be mathematically correct,
        # then we need to verify that this is really always the case (for some
        # methods, one might doubt this...)
        if InfoLevel(InfoRecog) = 1 and depth = "" then Print("\n"); fi;
        # StopStoringRandEls(ri);
        return ri;
    fi;

    # The non-leaf case:
    # In that case we know that ri now knows: homom plus additional data.

    # Try to recognise the factor a few times, then give up:
    counter := 0;
    repeat
        counter := counter + 1;
        if counter > 10 then
            Info(InfoRecog,1,"Giving up desperately...");
            if InfoLevel(InfoRecog) = 1 and depth = "" then Print("\n"); fi;
            return ri;
        fi;

        if IsMatrixGroup(Image(Homom(ri))) then
            Info(InfoRecog,2,"Going to the factor (depth=",
              Length(depth),", try=",
              counter,", dim=",DimensionOfMatrixGroup(Image(Homom(ri))),
              ", field=",Size(FieldOfMatrixGroup(Image(Homom(ri)))),").");
        else
            Info(InfoRecog,2,"Going to the factor (depth=",
              Length(depth),", try=",
              counter,").");
        fi;
        Add(depth,'F');
        rifac := RecogniseGeneric(
                  Group(List(GeneratorsOfGroup(H), x->ImageElm(Homom(ri),x))),
                  methodsforfactor(ri), depth, forfactor(ri) ); # TODO: change forfactor to hintsForFactor??)
        Remove(depth);
        PrintTreePos("F",depth,H);
        SetRIFac(ri,rifac);
        SetRIParent(rifac,ri);

        if IsMatrixGroup(H) then
            Info(InfoRecog,2,"Back from factor (depth=",Length(depth),
                 ", dim=",ri!.dimension,", field=",
                 Size(ri!.field),").");
        else
            Info(InfoRecog,2,"Back from factor (depth=",Length(depth),").");
        fi;

        if not(IsReady(rifac)) then
            # the recognition of the factor failed, also give up here:
            if InfoLevel(InfoRecog) = 1 and depth = "" then Print("\n"); fi;
            return ri;
        fi;

        # Now we want to have preimages of the new generators in the factor:
        Info(InfoRecog,2,"Calculating preimages of nice generators.");
        Setpregensfac( ri, CalcNiceGens(rifac,ri!.gensHmem) );
        ri!.genswithmem := Concatenation(ri!.gensHmem,pregensfac(ri));  # FIXME: what is genswithmem? document it?
        # TODO: somehow here is the hidden assumption that pregensfac()
        # contains (at least initially) generators with memory; and then
        # we strip this memory away. That's bad design
        # TODO: rewrite this code to not need ForgetMemory at all

        # replace the entries of the list pregensfac(ri) with
        # generators without memory
        ForgetMemory(pregensfac(ri));   # TODO: get rid of ForgetMemory here!

        # Now create the kernel generators with the stored method:
        methgensN := findgensNmeth(ri);
        succ := CallFuncList(methgensN.method,
                             Concatenation([ri],methgensN.args));
    until succ;

    # If nobody has set how we produce preimages of the nicegens:
    if not(Hascalcnicegens(ri)) then
        Setcalcnicegens(ri,CalcNiceGensHomNode);
    fi;

    # Do a little bit of preparation for the generators of N:
    l := gensN(ri);
    if not(IsBound(ri!.leavegensNuntouched)) then
        Sort(l,SortFunctionWithMemory);   # this favours "shorter" memories!
        # FIXME: For projective groups different matrices might stand
        #        for the same element, we might overlook this here!
        # remove duplicates:
        ll := [];
        for i in [1..Length(l)] do
            if not(isone(ri)(l[i])) and
               (i = 1 or not(isequal(ri)(l[i],l[i-1]))) then
                Add(ll,l[i]);
            fi;
        od;
        SetgensN(ri,ll);
    fi;
    if Length(gensN(ri)) = 0 then
        # We found out that N is the trivial group!
        # In this case we do nothing, kernel is fail indicating this.
        Info(InfoRecog,2,"Found trivial kernel (depth=",Length(depth),").");
        SetRIKer(ri,fail);
        # We have to learn from the factor, what our nice generators are:
        SetNiceGens(ri,pregensfac(ri));
        SetFilterObj(ri,IsReady);
        if InfoLevel(InfoRecog) = 1 and depth = "" then Print("\n"); fi;
        # StopStoringRandEls(ri);
        return ri;
    fi;

    Info(InfoRecog,2,"Going to the kernel (depth=",Length(depth),").");
    repeat
        # Now we go on as usual:
        SetgensNslp(ri,SLPOfElms(gensN(ri)));
        SlotUsagePattern(gensNslp(ri));

        # This is now in terms of the generators of H!
        N := Group(StripMemory(gensN(ri)));

        Add(depth,'K');
        riker := RecogniseGeneric( N, methoddb, depth, forkernel(ri) );
        Remove(depth);
        PrintTreePos("K",depth,H);
        SetRIKer(ri,riker);
        SetRIParent(riker,ri);
        Info(InfoRecog,2,"Back from kernel (depth=",Length(depth),").");

        done := true;
        if IsReady(riker) and immediateverification(ri) then
            # Do an immediate verification:
            Info(InfoRecog,2,"Doing immediate verification.");
            for i in [1..5] do
                # We must use different random elements than the kernel
                # finding routines!
                x := RandomElm(ri,"KERNELANDVERIFY",true).el;
                s := SLPforElement(rifac,ImageElm( Homom(ri), x!.el ));
                if s = fail then
                    Error("Very bad: factor was wrongly recognised and we ",
                          "found out too late");
                fi;
                y := ResultOfStraightLineProgram(s,
                   ri!.genswithmem{[ri!.nrgensH+1..Length(ri!.genswithmem)]});
                z := x*y^-1;
                s := SLPforElement(riker,z!.el);
                if InfoLevel(InfoRecog) >= 2 then Print(".\c"); fi;
                if s = fail then
                    # We missed something!
                    done := false;
                    Add(gensN(ri),z);
                    Info(InfoRecog,2,
                         "Alarm: Found unexpected kernel element! (depth=",
                         Length(depth),")");
                fi;
            od;
            if InfoLevel(InfoRecog) >= 2 then Print("\n"); fi;
            if not(done) then
                succ := FindKernelFastNormalClosure(ri,5,5);
                Info(InfoRecog,2,"Have now ",Length(gensN(ri)),
                     " generators for kernel, recognising...");
                if succ = false then
                    Error("Very bad: factor was wrongly recognised and we ",
                          "found out too late");
                fi;
            fi;
        fi;
    until done;

    if IsReady(riker) then    # we are only ready when the kernel is
        # Now make the two projection slps:
        SetNiceGens(ri,Concatenation(pregensfac(ri), NiceGens(riker)));
        #ll := List([1..Length(NiceGens(rifac))],i->[i,1]);
        #ri!.proj1 := StraightLineProgramNC([ll],Length(NiceGens(ri)));
        #ll := List([1..Length(NiceGens(riker))],
        #           i->[i+Length(NiceGens(rifac)),1]);
        #ri!.proj2 := StraightLineProgramNC([ll],Length(NiceGens(ri)));
        SetFilterObj(ri,IsReady);
    fi;
    if InfoLevel(InfoRecog) = 1 and depth = "" then Print("\n"); fi;
    # StopStoringRandEls(ri);
    return ri;
  end);

InstallGlobalFunction( CalcNiceGens,
  function(ri,origgens)
    return calcnicegens(ri)(ri,origgens);
  end );

InstallGlobalFunction( CalcNiceGensGeneric,
  # generic function using an slp:
  function(ri,origgens)
    if not(Hasslptonice(ri)) then
        return origgens;
    else
        return ResultOfStraightLineProgram(slptonice(ri),origgens);
    fi;
  end );

InstallGlobalFunction( CalcNiceGensHomNode,
  # function for the situation on a homomorphism node (non-Leaf):
  function(ri,origgens)
    local origkergens,rifac,riker,pregensfactor;
    # Is there a non-trivial kernel?
    rifac := RIFac(ri);
    if HasRIKer(ri) and RIKer(ri) <> fail then
        pregensfactor := CalcNiceGens(rifac,origgens);
        riker := RIKer(ri);
        origkergens := ResultOfStraightLineProgram( gensNslp(ri), origgens );
        return Concatenation( pregensfactor,
                              CalcNiceGens(riker,origkergens) );
    else
        return CalcNiceGens(rifac,origgens);
    fi;
  end );

InstallGlobalFunction( SLPforElement,
  function(ri,x)
    local slp;
    slp := slpforelement(ri)(ri,x);
    if slp <> fail then
        SlotUsagePattern(slp);
    fi;
    return slp;
  end );

InstallGlobalFunction( SLPforElementGeneric,
  # generic method for a non-leaf node
  function(ri,g)
    local gg,n,rifac,riker,s,s1,s2,y,nr1,nr2;
    rifac := RIFac(ri);
    riker := RIKer(ri);   # note: might be fail
    gg := ImageElm(Homom(ri),g);
    if gg = fail then
        return fail;
    fi;
    s1 := SLPforElement(rifac,gg);
    if s1 = fail then
        return fail;
    fi;
    # if the kernel is trivial, we are done:
    if riker = fail then
        # was: return CompositionOfStraightLinePrograms(s1,gensQslp(ri));
        return s1;
    fi;
    # Otherwise work in the kernel:
    y := ResultOfStraightLineProgram(s1,pregensfac(ri));
    n := g*y^-1;
    s2 := SLPforElement(riker,n);
    if s2 = fail then
        return fail;
    fi;
    nr2 := NrInputsOfStraightLineProgram(s2);
    nr1 := NrInputsOfStraightLineProgram(s1);
    s := NewProductOfStraightLinePrograms(s2,[nr1+1..nr1+nr2],
                                          s1,[1..nr1],
                                          nr1+nr2);
    #s := ProductOfStraightLinePrograms(
    #       CompositionOfStraightLinePrograms(s2,ri!.proj2),
    #       CompositionOfStraightLinePrograms(s1,ri!.proj1));
    return s;
  end);

# Some helper functions for generic code:

InstallGlobalFunction( FindKernelRandom,
  function(ri,n)
    local i,l,rifac,s,x,y;
    Info(InfoRecog,2,"Creating ",n," random generators for kernel.");
    l := gensN(ri);
    rifac := RIFac(ri);
    for i in [1..n] do
        x := RandomElm(ri,"KERNELANDVERIFY",true).el;
        s := SLPforElement(rifac,ImageElm( Homom(ri), x!.el ));
        if s = fail then
            return false;
        fi;
        y := ResultOfStraightLineProgram(s,
                 ri!.genswithmem{[ri!.nrgensH+1..Length(ri!.genswithmem)]});
        Add(l,x^-1*y);
        if InfoLevel(InfoRecog) >= 2 then
            Print(".\c");
        fi;
    od;
    if InfoLevel(InfoRecog) >= 2 then
        Print("\n");
    fi;
    return true;
  end );

InstallGlobalFunction( FindKernelDoNothing,
  function(ri,n1,n2)
    return true;
  end );

InstallGlobalFunction( RandomSubproduct, function(a)
    local prod, list, g;

    if IsGroup(a) then
        prod := One(a);
        list := GeneratorsOfGroup(a);
    elif IsList(a) then
        if Length(a) = 0 or
            not IsMultiplicativeElementWithInverse(a[1]) then
            Error("<a> must be a nonempty list of group elements");
        fi;
        prod := One(a[1]);
        list := a;
    else
        Error("<a> must be a group or a nonempty list of group elements");
    fi;

    for g in list do
        if Random( [ true, false ] )  then
            prod := prod * g;
        fi;
    od;
    return prod;
end );

InstallGlobalFunction( FastNormalClosure , function( grpgens, list, n )
  local i,list2,randgens,randlist;
  list2:=ShallowCopy(list);
  if Length(grpgens) > 3 then
    for i in [1..6*n] do
      if Length(list2)=1 then
        randlist:=list2[1];
      else
        randlist:=RandomSubproduct(list2);
      fi;
      if not(IsOne(randlist)) then
        randgens:=RandomSubproduct(grpgens);
        if not(IsOne(randgens)) then
          Add(list2,randlist^randgens);
        fi;
      fi;
    od;
  else # for short generator lists, conjugate with all generators
    for i in [1..3*n] do
      if Length(list2)=1 then
        randlist:=list2[1];
      else
        randlist:=RandomSubproduct(list2);
      fi;
      if not(IsOne(randlist)) then
         for randgens in grpgens do
             Add(list2, randlist^randgens);
         od;
      fi;
    od;
  fi;
  return list2;
end );

# FIXME: rename FindKernelFastNormalClosure to indicate that it *also* computes random generators
InstallGlobalFunction( FindKernelFastNormalClosure,
  # Used in the generic recursive routine.
  function(ri,n1,n2)
    local succ;

    succ := FindKernelRandom(ri,n1);
    if succ = false then
        return false;
    fi;

    SetgensN(ri,FastNormalClosure(ri!.genswithmem,gensN(ri),n2));

    return true;
  end);

InstallOtherMethod( Size, "for a recognition info record",
  [IsRecognitionInfo and IsReady],
  function(ri)
    local size;
    if IsLeaf(ri) then
        # Note: A leaf in projective recognition *has* to set the size
        #       of the recognition info record!
        return Size(Grp(ri));
    else
        size := Size(RIFac(ri));
        if RIKer(ri) <> fail then
            return Size(RIKer(ri)) * size;
        else
            return size;   # trivial kernel
        fi;
    fi;
  end);

InstallOtherMethod( Size, "for a failed recognition info record",
  [IsRecognitionInfo],
  function(ri)
    Error("the recognition described by this info record has failed!");
  end);

InstallOtherMethod( \in, "for a group element and a recognition info record",
  [IsObject, IsRecognitionInfo and IsReady],
  function( el, ri )
    local gens,slp;
    slp := SLPforElement(ri,el);
    if slp = fail then
        return false;
    else
        gens := NiceGens(ri);
        if IsObjWithMemory(gens[1]) then
            gens := StripMemory(gens);
        fi;
        return isequal(ri)(el,ResultOfStraightLineProgram(slp,gens));
    fi;
  end);

InstallOtherMethod( \in, "for a group element and a recognition info record",
  [IsObject, IsRecognitionInfo],
  function( el, ri )
    Error("the recognition described by this info record has failed!");
  end);

InstallGlobalFunction( "DisplayCompositionFactors", function(arg)
  local c,depth,f,i,j,ri,homs,ksize;
  if Length(arg) = 1 then
      ri := arg[1];
      depth := 0;
      homs := 0;
      ksize := 1;
  else
      ri := arg[1];
      depth := arg[2];
      homs := arg[3];
      ksize := arg[4];
  fi;
  if not(IsReady(ri)) then
      for j in [1..homs] do Print("-> "); od;
      Print("Recognition failed\n");
      return;
  fi;
  if IsLeaf(ri) then
      c := CompositionSeries(Grp(ri));
      for i in [1..Length(c)-1] do
          if homs > 0 then
              Print("Group with Size ",ksize*Size(c[i]));
              for j in [1..homs] do Print(" ->"); od;
              Print(" ");
          fi;
          Print("Group ",GroupString(c[i],""),"\n | ");
          f := Image( NaturalHomomorphismByNormalSubgroup( c[i], c[i+1] ) );
          Print(IsomorphismTypeInfoFiniteSimpleGroup( f ).name, "\n" );
      od;
  else
      if HasRIKer(ri) and RIKer(ri) <> fail then
          DisplayCompositionFactors(RIFac(ri),depth+1,homs+1,
                                    ksize*Size(RIKer(ri)));
          DisplayCompositionFactors(RIKer(ri),depth+1,homs,ksize);
      else
          DisplayCompositionFactors(RIFac(ri),depth+1,homs+1,ksize);
      fi;
  fi;
  if depth = 0 then
      Print("1\n");
  fi;
end );

BindGlobal( "SLPforNiceGens", function(ri)
  local l,ll,s;
  l := List( [1..Length(GeneratorsOfGroup(Grp(ri)))], x->() );
  l := GeneratorsWithMemory(l);
  ll := CalcNiceGens(ri,l);
  s := SLPOfElms(ll);
  if s <> fail then
      SlotUsagePattern(s);
  fi;
  return s;
end );

InstallGlobalFunction( "GetCompositionTreeNode",
  function( ri, what )
    local r,c;
    r := ri;
    for c in what do
      if c in "fF" then r := RIFac(r);
      elif c in "kK" then r := RIKer(r); fi;
    od;
    return r;
  end );

# Testing:

RECOG.TestGroup := function(g,proj,size)
  local l,r,ri,s,x,count,lvl,seedMT,seedRS;
  count := 0;
  lvl:=InfoLevel(InfoRecog);
  SetInfoLevel(InfoRecog, 0);
  repeat
      count := count + 1;
      #r := Runtime();
      seedMT := State(GlobalMersenneTwister);
      seedRS := State(GlobalRandomSource);
      if proj then
          ri := RecogniseProjectiveGroup(g);
      else
          ri := RecogniseGroup(g);
      fi;
      #Print("Time for recognition: ",Runtime()-r,"\n");
      if Size(ri) <> size then
          Print("ALARM: set count to -1 to skip test!\n");
          Print("seedMT := ", seedMT, ";\n");
          Print("seedRS := ", seedRS, ";\n");
          Error("Alarm: Size not correct!\n");
          if count = -1 then return fail; fi;
      else
          #Print("Test was OK!\n");
          count := 3;   # worked!
      fi;
  until count >= 3;
  #View(ri);
  #Print("\n");
  count := 0;
  l := CalcNiceGens(ri,GeneratorsOfGroup(g));
  repeat
      count := count + 1;
      #Print(".\c");
      x := PseudoRandom(g);
      s := SLPforElement(ri,x);
      if s = fail or not(isequal(ri)(ResultOfStraightLineProgram(s,l),x)) then
          Print("ALARM: set count to -1 to skip test!\n");
          Error("Alarm: SLPforElement did not work!\n");
          if count = -1 then return fail; fi;
      fi;
  until count >= 30;
  #Print("\n30 random elements successfully sifted!\n");
  SetInfoLevel(InfoRecog, lvl);
  return ri;
end;

RECOG.TestRecognitionNode := function(ri,stop,recurse)
  local err, grp, x, slp, y, ef, ek, i;
  err := 0;
  grp := Grp(ri);
  for i in [1..100] do
      x := PseudoRandom(grp);
      slp := SLPforElement(ri,x);
      if slp <> fail then
          y := ResultOfStraightLineProgram(slp,NiceGens(ri));
      fi;
      if slp = fail or not(ri!.isone(x/y)) then
          if stop then Error("Error found, look at x, slp and y"); fi;
          err := err + 1;
          Print("X\c");
      else
          Print(".\c");
      fi;
  od;
  Print("\n");
  if err > 0 and recurse then
      if IsLeaf(ri) then
          return rec(err := err, badnode := ri);
      fi;
      ef := RECOG.TestRecognitionNode(RIFac(ri),stop,recurse);
      if IsRecord(ef) then return ef; fi;
      if RIKer(ri) <> fail then
          ek := RECOG.TestRecognitionNode(RIKer(ri),stop,recurse);
          if IsRecord(ek) then return ek; fi;
      fi;
      return rec( err := err, badnode := ri, factorkernelok := true );
  fi;
  return err;
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

