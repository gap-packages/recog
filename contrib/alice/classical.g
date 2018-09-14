########################################
# Classical Group Recognition in GAP4  #
#                                      #
########################################


#global record that will keep track of info
recognise := rec();


SetReturnNPFlags := function( grp, case )

   # first we check whether we found some evidence that the case was wrong
   if case = "symplectic"  and
       PositionProperty(recognise.E, x ->(x mod 2 <> 0)) <> false then
           #InfoRecog1("#I  The group does not preserve a symplectic form\n");
           recognise.type := "unknown";
           recognise.isGeneric := false;
           recognise.possibleOverLargerField := true;
           recognise.possibleNearlySimple := Set([]);
           return false;
   fi;
   if case = "unitary"  and
      PositionProperty(recognise.E, x ->(x mod 2 = 0)) <> false then
           #InfoRecog1("#I  The group does not preserve a unitary form\n");
           recognise.type := "unknown";
           recognise.isGeneric := false;
           recognise.possibleOverLargerField := true;
           recognise.possibleNearlySimple := Set([]);
           return false;
   fi;
  if case in ["orthogonalminus","orthogonalplus","orthogonalcircle"] and
        PositionProperty(recognise.E, x ->(x mod 2 <> 0)) <> false then
           #InfoRecog1("#I  The group does not preserve a quadratic form\n");
           recognise.type := "unknown";
           recognise.isGeneric := false;
           recognise.possibleOverLargerField := true;
           recognise.possibleNearlySimple := Set([]);
           return false;
   fi;

   #SetIsSymplecticGroupFlag( recognise, false );
   recognise.isSymplecticGroup := false;
   #SetIsOrthogonalGroupFlag( recognise, false );
   recognise.isOrthogonalGroup := false;
   #SetIsUnitaryGroupFlag( recognise, false );
   recognise.isUnitaryGroup := false;
   #SetIsSLContainedFlag( recognise, false );
   recognise.isSLContained := false;
   if case = "linear"  then
       #SetIsSLContainedFlag( recognise, true  );
       recognise.isSLContained := true;
   elif case = "symplectic"  then
       #SetIsSymplecticGroupFlag( recognise, true  );
       recognise.isSymplecticGroup := true;
   elif case = "unitary"  then
       #SetIsUnitaryGroupFlag( recognise, true  );
       recognise.isUnitaryGroup := true;
   elif case in ["orthogonalminus","orthogonalplus","orthogonalcircle"] then
       #SetIsOrthogonalGroupFlag( recognise, true  );
       recognise.isOrthogonalGroup := true;
   fi;
   #set the group type
   recognise.type := case;
   Unbind (recognise.dimsReducible);
   Unbind (recognise.possibleOverLargerField);
   Unbind (recognise.possibleNearlySimple);
   return true;

end;


#Initialise the record based on group  structure
InitRecog := function (grp,case)
   local f;

   f := FieldOfMatrixGroup(grp);

   recognise := rec( d := DegreeOfMatrixGroup(grp),
                     p := Characteristic(f),
                     a := DegreeOverPrimeField(f),
                     q := Characteristic(f)^DegreeOverPrimeField(f),
                     E := Set([]), LE := Set([]), basic := false,
                     n := 0,
                     isReducible := "unknown",
                     isGeneric := false,
                     type := case,
                     possibleOverLargerField := true,
                     possibleNearlySimple := Set([]),
                     dimsReducible := [],
                     orders := Set([]),
                     isSLContained := "unknown",
                     isSymplecticGroup := "unknown",
                     isOrthogonalGroup := "unknown",
                     isUnitaryGroup := "unknown",
                    );
 end;

# Compute the degrees of the irreducible factors of
# the characteristic polynomial <cpol>
IsReducible := function(grp,cpol)
  local deg, dims,g;

  #reducible groups still possible?
  if recognise.isReducible = false then
     return false;
  fi;

  #compute the degrees of the irreducible factors
  deg := List(Factors(cpol));

  #compute all possible dimensions
  dims := [0];
  for g in deg do
     UniteSet(dims,dims+g);
  od;

  #intersect it with recognise.dimsReducible
  if IsEmpty(recognise.dimsReducible) then
      recognise.dimsReducible := dims;
  else
      IntersectSet(recognise.dimsReducible,dims);
  fi;

  # G acts irreducibly if only 0 and d are possible
  if Length(recognise.dimsReducible = 2) then
      recognise.isReducible := false;
      #TODO: INFORECOG2?
     return false;
  fi;

  return true;
end;


#Test a random element Re: implementation paper. See GAP3 for better
#comment for now. TODO: Update comments to something reasonable
TestRandomElement := function (grp,g)
    local ppd, bppd, d, cpol;

    d := recognise.d;

    # Compute the characteristic polynomial
    cpol := CharacteristicPolynomial(g);
    IsReducible(grp,cpol);
    ppd := IsPpdElement (FieldOfMatrixGroup(grp), cpol, d, recognise.q, 1);
    if ppd = false then
        return false;
    fi;

    AddSet(recognise.E,ppd[1]);
    if ppd[2] = true then
        AddSet(recognise.LE,ppd[1]);
    fi;
    if recognise.basic = false then
        #We only need one basic ppd-element
        #Also, each basic ppd element is a ppd-element
        bppd := IsPpdElement (FieldOfMatrixGroup(grp), cpol, d, recognise.p, recognise.a);
        if bppd <> false then
            recognise.basic := bppd[1];
        fi;
    fi;

    return ppd[1];
end;

#Test to check whether the group contains both a large ppd element and a basic
#ppd element TODO: Better comments...
GenericParameters := function(grp,case)
    local fact,d,q;

    if not IsBound(recognise) then
        InitRecog(grp,case);
    fi;

    d := recognise.d;
    q := recognise.q;

    if case = "linear" and d <= 2 then
        return false;

    elif case = "linear" and d = 3 then
        #q = 2^s-1
        fact := Collected(Factors(q+1));
        if Length(fact) = 1 and fact[1][1] = 2 then
            return false;
        fi;
        return true;

    elif case = "symplectic" and
      (d < 6 or (d mod 2 <> 0) or
       [d,q] in [[6,2],[6,3],[8,2]]) then
        return false;

    elif case = "unitary" and
      (d < 5 or d = 6 or [d,q] = [5,4]) then
        return false;

    elif case = "orthogonalplus" and
      (d mod 2 <> 0 or d < 10
       or (d = 10 and q = 2)) then
        return false;

    elif case = "orthogonalminus" and
      (d mod 2 <> 0 or d < 6
       or [d,q] in [[6,2],[6,3],[8,2]]) then
        return false;

    elif case = "orthogonalcircle" then
        if d < 7 or [d,q] = [7,3] then
            return false;
        fi;
        if d mod 2 = 0 then
            return false;
        fi;
        if q mod 2 = 0 then
            #TODO: INFORECOG1 ... not irreducible
            #TODO: INFORECOG2 ... d odd --> q odd
            return false;
        fi;
    fi;

    return true;
end;


#Generate elements until we find the required ppd type elements...monte  yes
#TODO: Better comments

IsGeneric := function (grp, N_gen)
    local b, N, g;

    if not IsBound(recognise) then
        InitRecog(grp,"unknown");
    fi;

    if recognise.isGeneric then
        #TODO: INFORECOG2 ... group is generic
        return true;
    fi;

    b := recognise.d;

    for N in [1..N_gen] do
        g := PseudoRandom(grp);
        recognise.n := recognise.n + 1;
        TestRandomElement(grp,g);
        if Length(recognise.E) >= 2 and
           Length(recognise.LE) >= 1 and
           recognise.basic <> false then
            recognise.isGeneric := true;
            #TODO: INFORECOG2: group is geenric in n sections...
            return true;
        fi;
    od;

    return false;
end;


#enough info to rule out extension field groups...?
#TODO: comments...
RuledOutExtFieldParamaters := function (grp,case)

    local differmodfour, d, q, E;

    d := recognise.d;
    q := recognise.q;
    E := recognise.E;

    differmodfour := function(E)
        local e;
        for e in E do
            if E[1] mod 4 <> e mod 4 then
                return true;
            fi;
        od;
        return false;
    end;

    if case = "linear" then
        if not IsPrime(d)
           or E <> Set([d-1,d])
           or d-1 in recognise.LE then
            return true;
        fi;

    elif case = "unitary" then
        return true;

    elif case = "symplectic" then
        if d mod 4 = 2 and q mod 2 = 1 then
            return (PositionProperty(E, x -> (x mod 4 = 0)) <> false);
        elif  d mod 4 = 0 and q mod 2 = 0 then
            return (PositionProperty( E, x -> (x mod 4 = 2)) <> false);
        elif d mod 4 = 0 and q mod 2 = 1 then
            return differmodfour(E);
        elif d mod 4 = 2 and q mod 2 = 0 then
            return (Length(E) > 0);
        else
            Error("d cannot be odd in case Sp");
        fi;

    elif case = "orthogonalplus" then
        if d mod 4 = 2  then
            return (PositionProperty (E, x -> (x mod 4 = 0 )) <> false);
        elif d mod 4 = 0  then
            return differmodfour(E);
        else  Error("d cannot be odd in case O+");
     fi;

    elif case = "orthogonalminus" then
        if d mod 4 = 0  then
            return (PositionProperty ( E, x -> (x mod 4 = 2)) <> false);
        elif d mod 4 = 2  then
            return differmodfour(E);
        else  Error("d cannot be odd in case O-");
    fi;

    elif case = "orthogonalcircle" then
        return true;
    fi;

    return false;
end;


#rule out extension field...
#TODO: comments...
IsExtensionField := function (grp, case, N_ext)

    local b, bx, g, ppd, N, testext;

    if not IsBound(recognise) then
        InitRecog(grp,case);
    fi;

    if (recognise.isGeneric and
       (not recognise.possibleOverLargerField)) then
        return false;
    fi;

    b := recognise.d;

    if Length(recognise.E) > 0 then
        b := Gcd (UnionSet(recognise.E,[recognise.d]));
    fi;

    if case in ["linear","unitary","orthogonalcircle"] then
        bx := 1;
    else
        bx := 2;
    fi;

    if b = bx then
        if RuledOutExtFieldParamaters(grp,case) then
            #TODO: INFORECOG2 ... not an extension field group
            recognise.possibleOverLargerField := false;
        fi;
        return 0;
    fi;

    N := 1;

    while N <= N_ext do
        g := PseudoRandom(grp);
        recognise.n := recognise.n + 1;
        ppd := TestRandomElement(grp,g);
        N := N+1;
        if b > bx then
            b := Gcd(b,ppd);
        elif b < bx then
            return false;
        fi;

        if b = bx then
            testext := RuledOutExtFieldParamaters(grp,case);
            if testext then
                #TODO: INFORECOG2...not an extension field group...
                recognise.possibleOverLargerField := false;
                return N;
            fi;
        fi;
    od;

    #INFORECOG1 ... group could preserve an extension field...
    return true;
end;


# Functrions for rulng out nearly simple groups
# TODO: comments...
FindCounterExample := function (grp, prop, N)
    local i,g;

    g := One(grp);
    if prop(g) then
       return true;
    fi;

    for i in [1..N] do
       g := PseudoRandom(grp);
       recognise.n := recognise.n +1;
       TestRandomElement(grp,g);
       if prop(g) or Length (recognise.E) > 2 then
           return true;
       fi;
    od;

    return false;
end;


IsAlternating := function(grp,N)

    local V, P, i,g ,q;

    q := recognise.q;

    if recognise.d <> 4 or q <> recognise.p or (3 <= q and q < 23) then
       #TODO: INFORECOG2...G is not an alternating group
       return false;
    fi;

    if q = 2 then
       V := VectorSpace(IdentityMat(4,GF(2)),GF(2));
       P := Action(grp, Difference (Elements(V),Zero(V)));
       if Size(P) <> 3*4*5*6*7 then
           #TODO: INFORECOG2...G is not an alternating group...
           return false;
       else
           #TODO: INFORECOG2...G might be A_7...
           AddSet(recognise.possibleNearlySimple,"A7");
           return true;
       fi;
    fi;


    if q >= 23 then

       if FindCounterExample(grp,g->2 in recognise.LE,N ) <> false then
         #TODO: INFORECOG2...G is not an alternating group...
         return false;
       fi;

       AddSet (recognise.possibleNearlySimple, "2.A7");
       #TODO: INFORECOG2....G might be 2.A_7
       return true;
   fi;
end;



IsMatthieu := function( grp, N )

   local i, fn, g, d, q, E;

   d := recognise.d;
   q := recognise.q;
   E := recognise.E;

   if not [d, q]  in [ [5, 3], [6,3], [11, 2] ] then
       ##InfoRecog2( "#I  G' is not a Mathieu group;\n");
       return false;
   fi;

   if d  in [5, 6] then
       fn := function(g)
           local ord;
           ord := Order(g);
           return (ord mod 121=0 or (d=5 and ord=13) or (d=6 and ord=7));
       end;
   else
       fn := g -> ForAny([6,7,8,9],m-> m in E);
   fi;

   if FindCounterExample( grp, fn, N ) <> false then
       ##InfoRecog2("#I  G' is not a Mathieu group\n");
       return false;
   fi;

   if d = 5 then
       AddSet(recognise.possibleNearlySimple, "M_11" );
       ##InfoRecog2( "#I  G' might be M_11;\n");
   elif d = 6 then
       AddSet(recognise.possibleNearlySimple, "2M_12" );
       ##InfoRecog2( "#I  G' might be 2M_12;\n");
   else
       AddSet(recognise.possibleNearlySimple, "M_23" );
       AddSet(recognise.possibleNearlySimple, "M_24" );
       ##InfoRecog2( "#I  G' might be M_23 or M_24;\n");
   fi;

   return true;

end;


IsPSL := function ( grp, N )

   local i, E, LE, d, p, a, q,  str, fn;

   E := recognise.E;
   LE := recognise.LE;
   d := recognise.d;
   q := recognise.q;
   a := recognise.a;
   p := recognise.p;

   if d = 3 then
       str := "PSL(2,7)";
       i:= Factors(q+1);
       if i[Length(i)]=3 and (Length(i)=1 or i[Length(i)-1]=2)
           and not ((q^2-1) mod 9 = 0 or Maximum(Factors(q^2-1))>3) then
           # q = 3*2^s-1 and q^2-1 has no large ppd.
           fn := function(g)
               local ord;
               ord := Order(g);
               return (ord mod 8 <> 0 or (p^(2*a)-1) mod ord = 0);
           end;
       else
           if p = 3 or p = 7 then  fn := (g -> true);
           else  fn :=  (g -> 2 in LE);
           fi;
       fi;
   elif [d, q]  = [5,3] then
       str := "PSL(2,11)";
       fn := function(g)
           local ord;
           ord := Order(g);
           return (ord mod 11^2 = 0  or ord mod 20 = 0);
       end;
   elif d = 5  and p <> 5 and p <> 11 then
       str := "PSL(2,11)";
       fn := g -> (3 in LE or 4 in LE) ;
   elif [d, q]  = [6, 3] then
       str := "PSL(2,11)";
       fn :=  g-> (Order(g) mod 11^2=0 or 6 in E);
   elif d = 6 and p <> 5 and p <> 11 then
       str := "PSL(2,11)";
       fn :=  g -> (6 in E or 4 in LE);
   else
       str := "PSL(2,r)";
       fn :=  g->true;
   fi;

   i :=  FindCounterExample( grp, fn, N );
   if not i or E = [] then
       #InfoRecog2("#I  G' might be ", str, "\n");
       return true;
   fi;

   # test whether e_2 = e_1 + 1 and
   # e_1 + 1 and 2* e_2 + 1 are primes
   if i <> false or E[2]-1<>E[1] or
       not IsPrime(E[1]+1) or not IsPrime(2*E[2]+1) then
        #InfoRecog2("#I  G' is not ", str, "\n");
        return false;
   fi;

   str := Concatenation("PSL(2,",Int(2*E[2]+1));
   str := Concatenation(str, ")");
   #InfoRecog2("#I  G' might be ", str, "\n");
   AddSet( recognise.possibleNearlySimple, str );
   return true;
end;


IsGenericNearlySimple := function( grp, case, N )

   local   isal;

   if case <> "linear" then
       return false;
   fi;

   if N < 0 then
       return true;
   fi;

   if not IsBound(grp.recognise) then
       InitRecog(grp, case);
   fi;

   isal := IsAlternating(grp,N) or IsMatthieu(grp,N) or IsPSL(grp,N);

   if not isal then
       recognise.possibleNearlySimple := Set([]);
   fi;
   return isal;

end;

###################################################################
###################################################################
# OLD MAIN FUNCTIONS, PORTED FROM                                ##
# GAP3 CODE                                                      ##
###################################################################
###################################################################

######################################################################
##
#F  RecogniseClassicalNPCase(grp,case,N) . . . . . . .
#F                    . . . .  Does <grp>  contain a classical group?
##
##  Input:
##
##  - a group <grp>, which is a subgroup of  GL(d,q)
##  - a string <case>, one of "linear", "unitary", "symplectic",
##           "orthogonalplus", "orthogonalminus", or "orthogonalcircle"
##  - an optional integer N
##
##  Assumptions about the Input:
##
##  It is assumed that it is known that the only forms preserved by
##  <grp> are the forms of the corresponding case.
##
##  Output:
##
##  Either a boolean, i.e. either 'true' or 'false'
##  or the string "does not apply"
##
##
##  The  algorithm  is designed  to  test  whether <grp>  contains the
##  corresponding classical group Omega (see [1]).
##
##

RecogniseClassicalNPCase := function( arg )

    local   recog, d,  p,  a,  isext,  grp, N, case, n;

    if not Length(arg)  in [2,3] then
        Error("usage: RecogniseClassicalNPCase( <grp>, <case>[, N])" );
    fi;

    grp := arg[1];
    case := arg[2];
    if Length( arg ) = 3 then
        N := arg[3];
    else
        if case = "linear" then
             N := 15;
         else
             N := 25;
         fi;
     fi;

     if IsBound(recognise) then
         if case = "linear"  and recognise.isSLContained <> "unknown" then
             return recognise.isSLContained;
       elif case = "symplectic" and
         recognise.isSymplecticGroup <> "unknown" then
           return recognise.isSymplecticGroup;
       elif case = "unitary" and recognise.isUnitaryGroup <>"unknown" then
           return recognise.isUnitaryGroupFlag;
       elif case in ["orthogonalminus","orthogonalplus","orthogonalcircle"] and
         recognise.isOrthogonalGroup <> "unknown" then
           return recognise.isOrthogonalGroup;
       fi;
   fi;

   if not case in [ "linear", "unitary", "symplectic",
              "orthogonalplus", "orthogonalminus", "orthogonalcircle" ] then
       Error("unknown case\n");
   fi;

   if IsBound( recognise ) and IsBound(recognise.type) and
      recognise.type = "unknown" then
       recognise.type := case;
   fi;

   if not IsBound(recognise) then
       InitRecog( grp, case );
   elif (IsBound(recognise.type) and
         recognise.type <> case) then
       recognise.n := 0;
       recognise.type := case;
       recognise.possibleOverLargerField := true;
       recognise.possibleNearlySimple := Set([]);
   fi;

        # test whether the theory applies for this group and case
   if GenericParameters( grp, case ) = false then
       #InfoRecog1("#I  Either algorithm does not apply in this case\n");
       #InfoRecog1("#I  or the group is not of type ", case, ".\n");
       Unbind( recognise );
       return "does not apply";
   fi;

   n := recognise.n;
   # try to establish whether the group is generic
   if not IsGeneric( grp, N )  then
       #InfoRecog1 ("#I  The group is not generic\n");
       #InfoRecog1("#I  The group probably does not contain");
       #InfoRecog1(" a classical group\n");
       Unbind( recognise.type );
       return false;
   fi;

   isext := IsExtensionField( grp, case, N-recognise.n+n );
   if isext = true then
       return false;
   elif isext = false then
       #InfoRecog1( "#I  The group does not preserve a");
       if case = "symplectic" then
           #InfoRecog1(" symplectic form\n");
   else
       #InfoRecog1(" quadratic form\n");
   fi;
   Unbind(recognise.type);
   return false;
   fi;

   # Now we know that the group preserves no extension field structure on V;
   if  IsGenericNearlySimple( grp, case, N-recognise.n+n ) then
    #InfoRecog1( "#I  The group could be a nearly simple group.\n");
    Unbind(recognise.type);
    return false;
   fi;
   n := recognise.n - n;
   #InfoRecog2( "#I  The group is not nearly simple\n");

   # maybe the number of random elements selected was not sufficient
   # to prove that the group acts irreducibly. In this case we call
   # the meataxe.
   if recognise.isReducible = "unknown" then
       if IsIrreducible(
            GModuleByMats(GeneratorsOfGroup(grp),FieldOfMatrixGroup(grp)) ) then
           recognise.isReducible := false;
       else
           recognise.isReducible := true;
       fi;
   fi;
   # if the group acts reducibly then our algorithm does not apply
   if recognise.isReducible = true then
       # TODO: WHAT HERE? SetNotAbsIrredFlags (grp);
       #InfoRecog1("#I  The group acts reducibly\n");
       return "does not apply";
   fi;
   #InfoRecog2("#I  The group acts irreducibly\n");


   ##ALICE: returnNPFlags?
#   if SetReturnNPFlags( grp, case ) = true then
       #InfoRecog1("#I  Proved that the group contains a classical" );
       #InfoRecog1(" group of type ", case, "\n#I  in " );
       #InfoRecog1( StringInt(recognise.n)," random selections.\n");
       return true;
 #  else
 #      Unbind(recognise.type);
 #      return false;
 #  fi;

end;



######################################/
#
#  NonGenericLinear (grp, N) . . . . . . . . . . . . non-generic linear case
#
#  Recognise non-generic linear matrix groups over finite fields:
#  In order to prove that a group G <= GL( 3, 2^s-1) contains SL, we need to
#  find an element of order a multiple of 4 and a large and basic ppd(3,q;3)-
#  element
#
NonGenericLinear := function( grp, N )
    local order4, d,ord, g;

    if not IsBound(recognise) then
        InitRecog(grp,"linear");
    fi;

    if not IsBound(recognise.orders) then
        recognise.orders := Set([]);
    fi;


    order4 := false;
    d := recognise.d;
    while  N >= 0  do
        N := N - 1;
        g := Random(grp);
        recognise.n := recognise.n + 1;
        if order4 = false then
            ord := Order(g);
            if ord mod 4 = 0 then
                order4 := true;
            fi;
        fi;

        if Length(recognise.LE) = 0 then
            TestRandomElement( grp, g);
        fi;

        #ALICE: basic is a list in magma, boolean here?
        if Length(recognise.LE) >= 1 and 3 in recognise.LE and
           3 = recognise.basic and order4 = true  then
               return true;
        fi;
    od;


    return false;

end;


