#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Daniel Rademacher.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################

##############################################################################
# Naming Algorithms
##############################################################################

# Test to check whether the group contains both a large ppd element
# and a basic ppd element 
# TODO: Better comments... 

###
## Test whether n is a power of the prime p
##
IsPowerOfPrime := function( n, p )

    local x;

    if n <= 0 then return false; fi;

    repeat
        x := QuotientRemainder( n, p );
        if x[2] <> 0 then return false; fi;
        n := x[1];
    until n = 1;

    return true;

end;



RECOG.IsGenericParameters := function( recognise, grp )
    
    local fact, d, q, hint;
    
    hint := recognise.hint;

    d := recognise.d;
    q := recognise.q;

    if hint = "unknown"  then 
        return NeverApplicable; 

    elif hint = "linear" and d <= 2 then
        recognise.isGeneric := false;
        return NeverApplicable;
        
    elif hint = "linear" and d = 3 then
        #q = 2^s-1
        if IsPowerOfPrime( q+1, 2 ) then 
            recognise.isGeneric := false;
        fi;
        return NeverApplicable;
        
    elif hint = "symplectic" and 
      (d < 6 or (d mod 2 <> 0) or
       [d,q] in [[6,2],[6,3],[8,2]]) then
        recognise.isGeneric := false;
        return NeverApplicable;
        
    elif hint = "unitary" and
      (d < 5 or d = 6 or [d,q] = [5,4]) then
        recognise.isGeneric := false;
        return NeverApplicable;
        
    elif hint = "orthogonalplus" and 
      (d mod 2 <> 0 or d < 10
       or (d = 10 and q = 2)) then
        recognise.isGeneric := false;
        return NeverApplicable;
        
    elif hint = "orthogonalminus" and
      (d mod 2 <> 0 or d < 6 
       or [d,q] in [[6,2],[6,3],[8,2]]) then
        recognise.isGeneric := false;
        return NeverApplicable;
        
    elif hint = "orthogonalcircle" then
        if d < 7 or [d,q] = [7,3] then
            recognise.isGeneric := false;
            return NeverApplicable;
        fi;
        if d mod 2 = 0 then
            recognise.isGeneric := false;
            return NeverApplicable;
        fi;
        if q mod 2 = 0 then
            #TODO: INFORECOG1 ... not irreducible
            #TODO: INFORECOG2 ... d odd --> q odd
            recognise.isReducible := true;
            recognise.isGeneric := false;
            return NeverApplicable;
        fi;
    fi;
    
    return NeverApplicable;
end;


# Generate elements until we find the required ppd type
# elements...monte  yes 
# TODO: Better comments

RECOG.IsGeneric := function (recognise, grp)

    if recognise.isGeneric = false then
        return NeverApplicable;
    fi;

#sg
    if recognise.d = 2 then
	recognise.isGeneric := false;
	return NeverApplicable;
    fi;
#sg

    if Length(recognise.E) < 2 then return TemporaryFailure; fi;
    if Length(recognise.LE) < 1 then return TemporaryFailure; fi;
    if Length(recognise.BE) < 1 then return TemporaryFailure; fi;

    recognise.isGeneric := true;
    
    return NeverApplicable;
end;

#enough info to rule out extension field groups...?
#TODO: comments...
RECOG.RuledOutExtField := function (recognise, grp)
    
    local differmodfour, d, q, E, b, bx, hint;
    
    hint := recognise.hint;
    d := recognise.d;
    q := recognise.q;
    E := recognise.E;

#sg
    if recognise.d = 2 then return NeverApplicable; fi;
#sg

    differmodfour := function(E)
        local e;
        for e in E do
            if E[1] mod 4 <> e mod 4 then
                return Success;
            fi;
        od;
        return NeverApplicable;
    end;
    
    b := recognise.currentgcd;
    
    if hint in ["linear","unitary","orthogonalcircle"] then
        bx := 1;
    else
        bx := 2;
    fi;
    

    if b < bx then 
        if hint <> "unknown" then
           recognise.hintIsWrong := true;
           # raeume auf + komme nie wieder
           return Success;
        fi;
        recognise.isNotExt := true; 
        return NeverApplicable; 
    fi;
    if b > bx then return TemporaryFailure; fi;

    if hint = "linear" then
        if not IsPrime(d)
           or E <> [d-1,d]
           or d-1 in recognise.LE then
            recognise.isNotExt  := true;
            return NeverApplicable;
        fi;
        
    elif hint = "unitary" then
        recognise.isNotExt  := true;
        return NeverApplicable;
        
    elif hint = "symplectic" then
        if d mod 4 = 2 and q mod 2 = 1 then
             recognise.isNotExt := 
            (PositionProperty(E, x -> (x mod 4 = 0)) <> fail);
        elif  d mod 4 = 0 and q mod 2 = 0 then
             recognise.isNotExt := 
             (PositionProperty( E, x -> (x mod 4 = 2)) <> fail);
        elif d mod 4 = 0 and q mod 2 = 1 then
             recognise.isNotExt := differmodfour(E);
        elif d mod 4 = 2 and q mod 2 = 0 then
            recognise.isNotExt :=  (Length(E) > 0);
        else
           Info( InfoClassical, 2, "d cannot be odd in hint Sp");
           recognise.hintIsWrong := true;
           # raeume auf + komme nie wieder
           return Success;
        fi;
        
    elif hint = "orthogonalplus" then
        if d mod 4 = 2  then
            recognise.isNotExt  := 
           (PositionProperty (E, x -> (x mod 4 = 0 )) <> fail);
        elif d mod 4 = 0  then
            recognise.isNotExt  := differmodfour(E);
        else  
           Info( InfoClassical, 2, "d cannot be odd in hint O+");
           recognise.hintIsWrong := true;
           # raeume auf + komme nie wieder
           return Success;
        fi;

     
    elif hint = "orthogonalminus" then
        if d mod 4 = 0  then
            recognise.isNotExt  := 
            (PositionProperty ( E, x -> (x mod 4 = 2)) <> fail);
        elif d mod 4 = 2  then
            recognise.isNotExt  := differmodfour(E);
        else 
           Info( InfoClassical, 2, "d cannot be odd in hint O-");
           recognise.hintIsWrong := true;
           # raeume auf + komme nie wieder
           return Success;
        fi;
    
    elif hint = "orthogonalcircle" then
        recognise.isNotExt  := true;
        return NeverApplicable;
    fi;
    
    if recognise.isNotExt = true then return NeverApplicable; 
    else return TemporaryFailure;
    fi;
end;

RECOG.IsNotAlternating := function( recognise, grp )

    local V, P, i, g ,q, o;

    q := recognise.q;
    
#sg
    if recognise.d = 2 then return NeverApplicable; fi;
#sg

#   if recognise.hint <> "unknown" and recognise.hint <> "linear" then
#       Info( InfoClassical, 2, "G' not an AlternatingGroup;"); 
#       recognise.isNotAlternating := true;
#       return NeverApplicable;
#   fi;

    if Length(recognise.ClassicalForms) > 0 and not "linear" in 
        recognise.ClassicalForms then 
       recognise.isNotAlternating := true;
       return NeverApplicable;
    fi;

    if recognise.d <> 4 or q <> recognise.p or (3 <= q and q < 23) then
       Info( InfoClassical, 2, "G is not an alternating group" );
       recognise.isNotAlternating := true;
       return NeverApplicable;
    fi;

    if q = 2 then
       if Size(grp) <> 3*4*5*6*7 then
           Info( InfoClassical, 2, "G is not an alternating group" );
           recognise.isNotAlternating := true;
           return NeverApplicable;
       else 
           Info( InfoClassical, 2, "G' might be A7;");
           AddSet(recognise.possibleNearlySimple,"A7");
           return Success;
       fi;
    fi;

    
    if q >= 23 then
        # TODO Check Magma Code
       o := Order( recognise.g );
       if o mod 25 = 0 then
           Info( InfoClassical, 2, "G' not alternating;");
           recognise.isNotAlternating := true;
           return NeverApplicable;
       fi;
       o := Collected( Factors (o) );
       for i in o do
           if i[1] >= 11 then
               Info( InfoClassical, 2, "G' not alternating;");
               recognise.isNotAlternating := true;
               return NeverApplicable;
           fi;
       od;
  
       if recognise.n > 15 then     
           AddSet (recognise.possibleNearlySimple, "2.A7");
           Info( InfoClassical, 2, "G' might be 2.A7;");
           return  TemporaryFailure;
       fi;
   fi;

   return TemporaryFailure;
   
end;


RECOG.IsNotMathieu := function( recognise, grp )

   local i, fn, g, d, q, E, ord;

   d := recognise.d;
   q := recognise.q;
   E := recognise.E;
   g := recognise.g;

#sg
    if d = 2 then return NeverApplicable; fi;
#sg

#   if recognise.hint <> "unknown" and recognise.hint <> "linear" then
#       Info( InfoClassical, 2, "G' not a Mathieu Group;");
#       recognise.isNotMathieu := true;
#       return NeverApplicable;
#   fi;

    if Length(recognise.ClassicalForms) > 0 and not "linear" in 
        recognise.ClassicalForms then 
       recognise.isNotMathieu := true;
       return NeverApplicable;
    fi;

   if not [d, q]  in [ [5, 3], [6,3], [11, 2] ] then
       Info( InfoClassical, 2, "G' is not a Mathieu group;\n");
       recognise.isNotMathieu := true;
       return NeverApplicable;
   fi;

   if d  in [5, 6] then
       ord := Order(g);
       if (ord mod 121=0 or (d=5 and ord=13) or (d=6 and ord=7)) then
          Info( InfoClassical, 2, "G' is not a Mathieu group;\n");
          recognise.isNotMathieu := true; 
          return NeverApplicable;
       fi;
   else
       if ForAny([6,7,8,9],m-> m in E) then
          Info( InfoClassical, 2, "G' is not a Mathieu group;\n");
           recognise.isNotMathieu := true; 
           return NeverApplicable;
       fi;
   fi;

 
# TODO Check how big n should be
    if d = 5 then
        if recognise.n > 15 then
            AddSet(recognise.possibleNearlySimple, "M_11" );
            Info( InfoClassical, 2, "G' might be M_11;");
            return TemporaryFailure;
        fi;
    elif d = 6 then
        if recognise.n > 15 then
            AddSet(recognise.possibleNearlySimple, "2M_12" );
            Info( InfoClassical, 2, "G' might be 2M_12;");
            return TemporaryFailure;
        fi;
    else
        if recognise.n > 15 then
            AddSet(recognise.possibleNearlySimple, "M_23" );
            AddSet(recognise.possibleNearlySimple, "M_24" );
            Info( InfoClassical, 2, "G' might be M_23 or M_24;");
            return TemporaryFailure;
        fi;
    fi;
 
   return TemporaryFailure;

end;


RECOG.IsNotPSL := function (recognise, grp)

   local i, E, LE, d, p, a, q,  str, fn, ord;

    E := recognise.E;
    LE := recognise.LE;
    d := recognise.d;
    q := recognise.q;
    a := recognise.a;
    p := recognise.p;

#sg
     if d = 2 then return NeverApplicable; fi;
#sg

#    if recognise.hint <> "unknown" and recognise.hint <> "linear" then
#        Info( InfoClassical, 2, "G' not PSL(2,r);");
#        recognise.isNotPSL := true;
#        return NeverApplicable;
#    fi;
    if Length(recognise.ClassicalForms) > 0 and not "linear" in 
        recognise.ClassicalForms  then 
       recognise.isNotPSL := true;
       return NeverApplicable;
    fi;

    if d = 3 and (q = 5 or q = 2) then
        Info( InfoClassical, 2,  "G' is not PSL(2,7)");
        recognise.isNotPSL := true;
        return NeverApplicable;
    fi;

    if d = 6 and q = 2 then
        Info( InfoClassical, 2,  "G' is not PSL(2,11)");
        recognise.isNotPSL := true;
        return NeverApplicable;
    fi;

    # test whether e_2 = e_1 + 1 and
    # e_1 + 1 and 2* e_2 + 1 are primes
    if  Length(E) >= 2 then
        if E[2]-1<>E[1] or 
            not IsPrimeInt(E[1]+1) or not IsPrimeInt(2*E[2]+1) then
            Info(InfoClassical, 2, " G' is not PSL(2,r)");
            recognise.isNotPSL := true;
            return NeverApplicable;
        fi;
    fi;
   
   if d = 3 then
       # q = 3*2^s-1 and q^2-1 has no large ppd.
       # TODO recheck this 
       if (q = 2 or ((q+1) mod 3 = 0 and IsPowerOfPrime((q+1)/3,2))) then
            ord := Order(recognise.g);
            if (ord mod 8 <> 0 or (p^(2*a)-1) mod ord = 0) then
                Info( InfoClassical, 2, "G' not PSL(2,7);");
                recognise.isNotPSL := true;
                return NeverApplicable;
           fi;
       else
           if p = 3 or p = 7 or 2 in LE then  
                Info( InfoClassical, 2, "G' not PSL(2,7);");
                recognise.isNotPSL := true;
                return NeverApplicable;
           fi;
       fi;
   elif [d, q]  = [5,3] then
       ord := Order(recognise.g);
       if (ord mod 11^2 = 0  or ord mod 20 = 0) then
           Info( InfoClassical, 2, "G' not PSL(2,11);");
           recognise.isNotPSL := true;
           return NeverApplicable;
       fi;
   elif d = 5  and p <> 5 and p <> 11 then
       if (3 in LE or 4 in LE) then
           Info( InfoClassical, 2, "G' not PSL(2,11);");
           recognise.isNotPSL := true;
           return NeverApplicable;
       fi;
   elif [d, q]  = [6, 3] then
       ord := Order(recognise.g);
       if (ord mod (11^2)=0 or 6 in E) then
           Info( InfoClassical, 2, "G' not PSL(2,11);");
           recognise.isNotPSL := true;
           return NeverApplicable;
       fi;
   elif d = 6 and p <> 5 and p <> 11 then
       if  (6 in E or 4 in LE) then
           Info( InfoClassical, 2, "G' not PSL(2,11);");
           recognise.isNotPSL := true;
           return NeverApplicable;
       fi;
   else
       Info( InfoClassical, 2, "G' not PSL(2,r);");
       recognise.isNotPSL := true;
       return NeverApplicable;
   fi;


   if recognise.n > 15  and Length(recognise.E) > 2 then
       str := Concatenation("PSL(2,",Int(2*E[2]+1));
       str := Concatenation(str, ")");
       Info( InfoClassical, 2, "G' might be ", str);
       AddSet( recognise.possibleNearlySimple, str );
       return TemporaryFailure;
   fi;
   return TemporaryFailure;
end;


# generate the next random element and its char polynomial
RECOG.TestRandomElement := function (recognise, grp)

    local g, ppd, bppd, d, q, cpol, f, deg, facs, r, s, h, gmod, str,
    ord, bc, phi, kf, o1, o2;

#sg
    if recognise.d = 2 then
	return NeverApplicable;
    fi;
#sg

    recognise.g := PseudoRandom(grp);
    recognise.cpol := CharacteristicPolynomial(recognise.g); 
    recognise.n := recognise.n + 1;

    d := recognise.d;
    q := recognise.q;
    f := recognise.field;
    g := recognise.g;
    cpol := recognise.cpol;

    if recognise.needOrders then
        ord := Order(g);
        recognise.ord := ord;
        AddSet( recognise.orders, ord );
    fi;
    if recognise.needPOrders then
        ord := ProjectiveOrder(g);
        AddSet( recognise.porders, ord );
    fi;
        
    ppd := IsPpdElement (f, cpol, d, recognise.q, 1); 
    # if the element is no ppd we get out
    if ppd = false then 
        recognise.isppd := false;
    else    
        AddSet(recognise.E,ppd[1]);
        recognise.currentgcd := Gcd( recognise.currentgcd, ppd[1] );
        if ppd[2] = true then
            AddSet(recognise.LE,ppd[1]);
        fi;
        recognise.ppd := [ ppd[1], ppd[2], "unknown" ];
        if Length(recognise.BE) < 1 or recognise.needLB then
            #We only need one basic ppd-element
            #Also, each basic ppd element is a ppd-element
            bppd := IsPpdElement (f, cpol, d, recognise.p, recognise.a);
            if bppd <> false then
                AddSet(recognise.BE, bppd[1]);
                if ppd[2] = true and ppd[1] = bppd[1] then
                    AddSet( recognise.LB, ppd[1] );
                    recognise.ppd[3] := true;
                fi;
            fi;
        fi;
    fi;
    if recognise.needE2 = true then
        ppd := IsPpdElementD2(f, cpol, d, recognise.q, 1); 
        if ppd <> false then 
            AddSet( recognise.E2, ppd[1] );
            if ppd[2] = true then
        
            ## first we test whether the characteristic polynomial has
            ## two factors of degree d/2. 
            facs := Factors( cpol );
            deg := List(facs, EuclideanDegree );
            if Length(deg) = 2 and deg[1] = deg[2] and deg[1] = d/2 then

            ## Now we compute the r-part h of g
            r := ppd[3];
            s := Order(g);
            while s mod r = 0 do s := Int (s/r); od;
            str := "  Found a large and special ppd(";
            str := Concatenation(str, String(recognise.d));
            str := Concatenation(str, ", " );
            str := Concatenation(str, String(recognise.q));
            str := Concatenation(str, "; " );
            str := Concatenation(str, String(ppd[1]));
            str := Concatenation(str,  ")-element");
	    if s = 1 and Length(facs) = 2 then 
                Info(InfoClassical,2, str );
                AddSet(recognise.LS, ppd[1] );
            else
                h := g^s;
                gmod := GModuleByMats([h], recognise.field);
	        if Length(MTX.CollectedFactors(gmod ))  = 2 then
                    Info(InfoClassical,2, str );
                    AddSet(recognise.LS, ppd[1] );
                fi;
            fi;
            fi;
          fi;
        fi;
    fi;


    if PositionProperty(recognise.E, x->(x mod 2 <> 0)) <> fail then
        recognise.IsSpContained := false;
        recognise.IsSOContained := false;
    fi;
    if PositionProperty(recognise.E, x ->(x mod 2 = 0)) <> fail then
        recognise.IsSUContained := false;
    fi;

    if recognise.needBaseChange = true and recognise.bc = "unknown" then     
        if Length(recognise.ClassicalForms) = 0 then    
            recognise.needForms := true;
            return NeverApplicable;
        fi;
        if "orthogonalplus" in recognise.ClassicalForms then
            phi := recognise.InvariantDualForm;
            if IsOddInt (q) then 
                Info(InfoClassical, 2,"Performing base change");
                bc := FindBase (d, q, phi);
                Info(InfoClassical, 2,"Computed base change matrix");
                bc := bc^-1;
                recognise.bc := bc;
            else 
                bc := FindBaseC2 (d, q, recognise.QuadraticForm);
                Info(InfoClassical,2,
                     "Computed base change matrix for char 2\n");
                bc := bc^-1;
                recognise.bc := bc;
            fi;
        else
            Info(InfoClassical, 2, "need basechange only in O+");
            return TemporaryFailure;
         fi;
     fi;

     if recognise.needKF  = true  then
            if recognise.bc = "unknown" then
                recognise.needBaseChange := true;
            else
                kf := KroneckerFactors( g^recognise.bc );
                if kf = false then 
                    kf := KroneckerFactors( (g^2)^recognise.bc );
                fi;
                recognise.kf  := kf;
            fi;
      fi;

      if recognise.needPlusMinus = true then
            if recognise.kf = "unknown" then  
                recognise.needKF := true;
                return TemporaryFailure;
            fi;
            if recognise.kf = false then  
                return TemporaryFailure;
            fi;
            kf := recognise.kf;
            o1 := Order( kf[1] );
            o2 := Order( kf[2] );
            Info(InfoClassical,2,o1, " ", o2, "\n");
            if ( (q+1) mod o1 = 0 and (q+1) mod o2 = 0) then 
                Add( recognise.plusminus, [1,1] );
            fi;
            if ( (q+1) mod o1 = 0 and (q-1) mod o2 = 0) then 
                Add( recognise.plusminus, [1,-1] );
            fi;
            if ( (q-1) mod o1 = 0 and (q+1) mod o2 = 0) then 
                Add( recognise.plusminus, [1,-1] );
            fi;
            if ( (q-1) mod o1 = 0 and (q-1) mod o2 = 0) then 
                Add( recognise.plusminus, [-1,-1] );
            fi;
        fi;

        if recognise.needDecompose = true then        
            if recognise.kf = "unknown" then  
                recognise.needKF := true;
                return TemporaryFailure;
            fi;
            if recognise.kf = false then  
                return TemporaryFailure;
            fi;
            kf := recognise.kf;     
                
            if not kf[1] in Group(recognise.sq1) then
                AddSet(recognise.sq1,kf[1]);
            fi;
            if not kf[2] in Group(recognise.sq2) then
                AddSet(recognise.sq2,kf[2]);
            fi;
       fi;

    return TemporaryFailure;

end;



# Compute the degrees of the irreducible factors of
# the characteristic polynomial <cpol>
RECOG.IsReducible := function( recognise, grp )
    
    local deg, dims, g;

    # compute the degrees of the irreducible factors
    deg := List(Factors(recognise.cpol), i-> Degree(i));

    # compute all possible dimensions
    dims := [0];
    for g in deg do
        UniteSet(dims,dims+g);
    od;

    # intersect it with recognise.dimsReducible
    if IsEmpty(recognise.dimsReducible) then
        recognise.dimsReducible := dims;
    else
        IntersectSet(recognise.dimsReducible,dims);
    fi;

    # G acts irreducibly if only 0 and d are possible
    if Length(recognise.dimsReducible)=2 then
        recognise.isReducible := false;
        return NeverApplicable;
    fi;
  
    return TemporaryFailure;
end;



RECOG.NoClassicalForms := function( recognise, grp )

#sg
    if recognise.d = 2 then return NeverApplicable; fi;
#sg

    PossibleClassicalForms( grp, recognise.g, recognise );

    if recognise.maybeDual = false and 
        recognise.maybeFrobenius = false then  
        recognise.ClassicalForms := ["linear"];
        return NeverApplicable;
    fi;

    return TemporaryFailure;

end;



RECOG.ClassicalForms := function( recognise, grp)
    local   field,  z,  d,  i,  qq,  A,  c,  I,  t,  i0,  
            a,  l,  g,  module,  forms,  dmodule,  fmodule,  form;

#sg
    if recognise.d = 2 then return NeverApplicable; fi;
#sg

    if recognise.n > 15 then recognise.needForms := true; fi;
    if recognise.needForms <> true then return NeverApplicable; fi;

    # the group has to be absolutely irreducible
    if recognise.isReducible = "unknown"  then
        recognise.needMeataxe := true;
        return TemporaryFailure;
    fi;
     
    # set up the field and other information
    field := recognise.field;
    d := recognise.d;
    z := Zero(field);
    module := recognise.module;

    if recognise.maybeFrobenius  = true then
        qq := Characteristic(field) ^ (LogInt( Size(field),
              Characteristic(field))/2 );
    fi;

    # try to find generators without scalars
    if recognise.maybeDual = true then
        dmodule := ClassicalForms_GeneratorsWithoutScalarsDual(grp);
        if dmodule = false  then
            Add( recognise.ClassicalForms,  "unknown"  );
            recognise.maybeDual := false;
        fi;
    fi;
    if recognise.maybeFrobenius = true then
        fmodule := ClassicalForms_GeneratorsWithoutScalarsFrobenius(grp);
        if fmodule = false  then
            Add( recognise.ClassicalForms,  "unknown" );
            recognise.maybeFrobenius := false;
        fi;
    fi;

    # now try to find an invariant form
    if recognise.maybeDual  = true then
        form := ClassicalForms_InvariantFormDual(module,dmodule);
        if form <> false  then
            Add( recognise.ClassicalForms, form[1] );
            recognise.InvariantDualForm := form[2];
            if Length(form) = 4 then
                recognise.QuadraticForm := form[4];
            fi;
        else
            Add( recognise.ClassicalForms, "dual"  );
        fi;
    fi;

    if recognise.maybeFrobenius = true then
        form := ClassicalForms_InvariantFormFrobenius(module,fmodule);
        if form <> false  then
            Add( recognise.ClassicalForms, form[1] );
            recognise.InvariantFrobeniusForm := form[2];
        else
            Add( recognise.ClassicalForms, "frobenius"  );
        fi;
    fi;
    return NeverApplicable;

end;


RECOG.MeatAxe := function( recognise, grp )

    if recognise.n > 15 then recognise.needMeataxe := true; fi;
    if recognise.needMeataxe <> true then return NeverApplicable; fi;
    
    if MTX.IsIrreducible(recognise.module) then
        recognise.isReducible := false;
        return NeverApplicable;
    else
        Info( InfoClassical, 2, 
        "The group acts reducibly and thus doesn't contain a classical group");
        recognise.isReducible := true;
        recognise.IsSLContained := false;
        recognise.IsSpContained := false;
        recognise.IsSUContained := false;
        recognise.IsSOContained := false;
        return Success;
    fi;
end;


## Main function to test whether group contains SL
RECOG.IsSLContained := function( recognise, grp )

#sg
    if recognise.d = 2 then return NeverApplicable; fi;
#sg

    if recognise.isGeneric <> true or
       recognise.isNotExt <> true or
       recognise.isNotPSL <> true  or
       recognise.isReducible = true or
       recognise.isNotMathieu <> true or 
       recognise.isNotAlternating <> true  then
          return TemporaryFailure;
    fi;

    if recognise.isReducible = "unknown" then 
        recognise.needMeataxe := true;
        return NeverApplicable; 
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NeverApplicable;
    fi;

    if "linear" in recognise.ClassicalForms then
        recognise.IsSLContained := true;
        Info(InfoClassical,2,"The group contains SL(", recognise.d, ", ",
        recognise.q, ");");
        return Success;
    else
        recognise.IsSLContained := false;
        Info(InfoClassical,2,"The group does not contain SL(", 
        recognise.d, ", ", recognise.q, ");");
        return NeverApplicable;
    fi;

end;

## Main function to test whether group contains Sp
RECOG.IsSpContained := function( recognise, grp )

#sg
    if recognise.d = 2 then return NeverApplicable; fi;
#sg

    # if the dimension is not even, the group cannot be symplectic
    if recognise.d mod 2 <> 0 then
        recognise.IsSpContained := false;
        return NeverApplicable;
    fi;

    if recognise.IsSpContained = false then return NeverApplicable; fi;

    if recognise.isGeneric <> true or
       recognise.isReducible = true or
       recognise.currentgcd <> 2 or
       recognise.isNotPSL <> true  or
       recognise.isNotMathieu <> true or 
       recognise.isNotAlternating <> true  then
          return TemporaryFailure;
    fi;

    if recognise.isReducible = "unknown" then 
        recognise.needMeataxe := true;
        return NeverApplicable; 
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NeverApplicable;
    fi;

    if "symplectic" in recognise.ClassicalForms then
        recognise.IsSpContained := true;
        recognise.isNotExt := true;
        Info(InfoClassical,2,"The group contains Sp(", recognise.d, ", ",
        recognise.q, ");");
        return Success;
    else
        recognise.IsSpContained := false;
        Info(InfoClassical,2,"The group does not contain Sp(", 
        recognise.d, ", ", recognise.q, ");");
        return NeverApplicable;
    fi;
end;


## Main function to test whether group contains SU
RECOG.IsSUContained := function( recognise, grp )

    local f;

    f := recognise.field;

#sg
    if recognise.d = 2 then return NeverApplicable; fi;
#sg

    # if size of field not a square, the group cannot be unitary
    if LogInt(Size(f),Characteristic(f))  mod 2 <> 0 then
        recognise.IsSUContained := false;
        return NeverApplicable;
    fi;
 
    if recognise.IsSUContained = false then return NeverApplicable; fi;

    if recognise.isGeneric <> true or
       recognise.isReducible = true or
       recognise.isNotExt <> true or
       recognise.isNotPSL <> true  or
       recognise.isNotMathieu <> true or 
       recognise.isNotAlternating <> true  then
          return TemporaryFailure;
    fi;

    if recognise.isReducible = "unknown" then 
        recognise.needMeataxe := true;
        return NeverApplicable; 
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NeverApplicable;
    fi;
        
    if "unitary" in recognise.ClassicalForms then
        recognise.IsSUContained := true;
        Info(InfoClassical,2,"The group contains SU(", recognise.d, ", ",
        recognise.q, ");");
        return Success;
    else
        recognise.IsSUContained := false;
        Info(InfoClassical,2,"The group does not contain SU(", 
        recognise.d, ", ", recognise.q, ");");
        return NeverApplicable;
    fi;
end;



## Main function to test whether group contains SO
RECOG.IsSOContained := function( recognise, grp )

    local f;

#sg
    if recognise.d = 2 then return NeverApplicable; fi;
#sg

    if recognise.IsSOContained = false then return NeverApplicable; fi;

    if IsOddInt(recognise.d) and not IsOddInt(recognise.q) then 
        return NeverApplicable; 
    fi;

    if recognise.isGeneric <> true or
       not recognise.currentgcd in [1,2] or
       recognise.isNotPSL <> true  or
       recognise.isReducible = true or
       recognise.isNotMathieu <> true or 
       recognise.isNotAlternating <> true  then
          return TemporaryFailure;
    fi;

    if recognise.isReducible = "unknown" then 
        recognise.needMeataxe := true;
        return NeverApplicable; 
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NeverApplicable;
    fi;

    if "orthogonalcircle" in recognise.ClassicalForms then
        if recognise.d mod 2 = 0 then return NeverApplicable; fi;
        if recognise.currentgcd <> 1 then return TemporaryFailure; fi;
        recognise.isNotExt := true;
        recognise.IsSOContained := true;
        Info(InfoClassical,2,"The group contains SO^o(", recognise.d, ", ",
        recognise.q, ");");
        return Success;

    elif "orthogonalplus" in recognise.ClassicalForms then
        if recognise.d mod 2 <> 0 then return NeverApplicable; fi;
        if recognise.currentgcd <> 2 then return TemporaryFailure; fi;
        recognise.isNotExt := true;
        recognise.IsSOContained := true;
        Info(InfoClassical,2,"The group contains SO+(", recognise.d, ", ",
        recognise.q, ");");
        return Success;

    elif "orthogonalminus" in recognise.ClassicalForms then
        if recognise.d mod 2 <> 0 then return NeverApplicable; fi;
        if recognise.currentgcd <> 2 then return TemporaryFailure; fi;
        recognise.isNotExt := true;
        recognise.IsSOContained := true;
        Info(InfoClassical,2,"The group contains SO-(", recognise.d, ", ",
        recognise.q, ");");
        return Success;
    else
        recognise.IsSOContained := false;
        Info(InfoClassical,2,"The group does not contain SO(", 
        recognise.d, ", ", recognise.q, ");");
        return NeverApplicable;
    fi;
end;


HasElementsMultipleOf := function(orders, ord )

    local o;

    for o in ord do
       if PositionProperty(orders, i->(i mod o = 0 )) = fail then
           return NeverApplicable;
       fi;
    od;

    return Success;

end;

############################################################################/
##
##  The following functions deal with the Non-generic cases. See [3].
##

############################################################################/
##
##  NonGenericLinear (recognise, grp)  . . . . . . . non-generic linear case
##
##  Recognise non-generic linear matrix groups over finite fields:
##  In order to prove that a group G <= GL( 3, 2^s-1) contains SL, we need to
##  find an element of order a multiple of 4 and a large and basic ppd(3,q;3)-
##  element
##
RECOG.NonGenericLinear := function( recognise, grp )

    local CheckFlag;

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return TemporaryFailure;
        fi;
        Info(InfoClassical,2,"The group is not generic");
        Info(InfoClassical,2,"and contains SL(", recognise.d, ", ",
        recognise.q, ");");
        recognise.IsSLContained := true;
        return Success;
    end;

    if recognise.isReducible = true then return NeverApplicable; fi;

#sg
    if recognise.d = 2 then 
	recognise.needPOrders := true;
	return NeverApplicable;
    fi;
#sg

    if recognise.d > 3 then return NeverApplicable; fi;

    if Length( recognise.ClassicalForms ) > 0 and 
       not "linear" in recognise.ClassicalForms then
       return NeverApplicable;
    fi;

    if recognise.n <= 5 then
        return TemporaryFailure;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return TemporaryFailure;
    fi;

    if 3 in recognise.LE and 3 in recognise.BE 
       and HasElementsMultipleOf(recognise.orders, [4]) then
           return CheckFlag();
    fi;

    return TemporaryFailure;
end;

############################################################################/
##
##  Recognise non-generic symplectic matrix groups over finite fields
##
RECOG.NonGenericSymplectic := function(recognise, grp)

    local d, q, CheckFlag;

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return TemporaryFailure;
        fi;
        Info(InfoClassical,2,"The group is not generic");
        Info(InfoClassical,2,"and contains Sp(", recognise.d, ", ",
        recognise.q, ");");
        recognise.IsSpContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

#sg
    if d = 2 then return NeverApplicable; fi;
#sg

    if not IsEvenInt(recognise.d) then return NeverApplicable; fi;
    if recognise.isReducible = true then return NeverApplicable; fi;

    if Length( recognise.ClassicalForms ) > 0 and 
       not "symplectic" in recognise.ClassicalForms then
       return NeverApplicable;
    fi;

    if d > 8 then return NeverApplicable; fi;

    if recognise.n <= 5 then
        return NeverApplicable;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        if d = 4 then
            recognise.needLB := true;
            recognise.needE2 := true;
        fi;
        return TemporaryFailure;
    fi;


    if d = 8 and q = 2 then
        if not HasElementsMultipleOf(recognise.orders, [5,9,17]) then
            return TemporaryFailure; 
        fi;
    elif d = 6 and q = 2 then
        if not HasElementsMultipleOf(recognise.orders, [5,7,9]) then
            return TemporaryFailure; 
        fi;
    elif d = 6 and q = 3 then
        if not HasElementsMultipleOf(recognise.orders, [5,7]) then
            return TemporaryFailure; 
        fi;
    elif d = 4 and q = 3 then
        if not HasElementsMultipleOf(recognise.orders, [5,9]) then
            return TemporaryFailure; 
        fi;
    elif d = 4 and q = 2 then
        if Size(grp) mod (3*4*5*6) <> 0 then
            Info(InfoClassical,2,"group does not contain Sp(", 
                 recognise.d, ", ", recognise.q, ");");
           recognise.isSpContained := false;
           return NeverApplicable;
        fi;
    elif d = 4 and q = 5 then
        if not HasElementsMultipleOf(recognise.orders, [13,15]) then
            return TemporaryFailure; 
        fi;
    elif d = 4 and not IsPowerOfPrime(q+1,2) and not ((q+1) mod 3 = 0 and
                   IsPowerOfPrime((q+1)/3, 2)) and q<>2 then
        if not 4 in recognise.LB then 
            return TemporaryFailure; 
        fi;
        if not 2 in  recognise.LS then return TemporaryFailure; fi;
    elif d = 4  and q >= 7 and IsPowerOfPrime(q+1,2) then
        if not 4 in recognise.LB then return TemporaryFailure; fi;
        if not HasElementsMultipleOf(recognise.orders, [4]) then
            return TemporaryFailure; 
        fi;

    elif d = 4 and q >= 11 and IsPowerOfPrime((q+1)/3, 2) then
        if not HasElementsMultipleOf(recognise.orders, [3,4]) then
            return TemporaryFailure; 
        fi;
        if not 4 in recognise.LB then return TemporaryFailure; fi;
    else
        Info(InfoClassical,2,
             "NonGenericSymplectic: d and q must have been be generic");
        return NeverApplicable;
    fi;

    return CheckFlag();

end;

############################################################################/
##
##  Recognise non-generic unitary matrix groups over finite fields
##
RECOG.NonGenericUnitary := function(recognise, grp)

    local d, q, q0, g, f1, f2, o, CheckFlag;

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return TemporaryFailure;
        fi;
         Info(InfoClassical,2,"group contains SU(", 
          recognise.d, ", ", recognise.q, ");");
        recognise.isSpContained := true;

        recognise.IsSUContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

#sg
    if d = 2 then return NeverApplicable; fi;
#sg
    if d > 6 then  return NeverApplicable; fi;
    if recognise.isReducible = true then return NeverApplicable; fi;

    if Length( recognise.ClassicalForms ) > 0 and 
       not "unitary" in recognise.ClassicalForms then
       return NeverApplicable;
    fi;

    if recognise.n <= 5 then
        return NeverApplicable;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        if d = 6 or d = 4 then
            recognise.needLB := true;
            recognise.needE2 := true;
        fi;
        if d = 3 then
            recognise.needPOrders := true;
            if q >= 49 then
               recognise.needLB := true;
            fi;
        fi;
        return TemporaryFailure;
    fi;

    if d = 6 and q = 4 then
        if not HasElementsMultipleOf(recognise.orders, [7,10,11]) then
            return TemporaryFailure; 
        fi;
    elif d = 6 and q >= 9 then
        if not 3 in recognise.E2 then return TemporaryFailure; fi;
        if not 5 in recognise.LB then return TemporaryFailure; fi;
    elif d = 5 and q = 4 then 
        if not HasElementsMultipleOf(recognise.orders, [11,12]) then
            return TemporaryFailure; 
        fi;
    elif d = 4 and q = 4 then 
        #TO DO : check this is same in Magma
        if not HasElementsMultipleOf(recognise.orders, [5,9]) then
            return TemporaryFailure; 
        fi;
    elif d = 4 and q = 9 then 
        if not HasElementsMultipleOf(recognise.orders, [5,7,9]) then
            return TemporaryFailure; 
        fi;
    elif d = 4 and q > 9 then 
        if not 3 in recognise.LB then 
            return TemporaryFailure; 
        fi;
        if not 2 in recognise.E2  then return TemporaryFailure; fi;
        f1 := Collected(Factors( q^3-1 ));
        f2 := Collected(Factors( q^2-1 ));
        # check if we have a prime at least 11
        if PositionProperty( f1, i-> (i[1] >= 11)) <> fail then
            return CheckFlag();
        fi;
        if PositionProperty( f2, i-> (i[1] >= 11)) <> fail then
            return CheckFlag();
        fi;
        # Now we know that q^3-1 and q^2-1 only contain primes
        # at most 7
        if not q^3 mod 7 = 1 or q^2 mod 7 = 1 or q mod 7 = 1 then
            # 7 is not ppd of q^3-1
            return CheckFlag();
        fi;
        # Now we know 7 is ppd of q^3 -1 
        if not q^2 mod 5 = 1 or q mod 5 = 1 then
            # 5 is not ppd of q^2-1
            return CheckFlag();
        fi;
        if PositionProperty( recognise.orders, i -> 
        (i mod 7 = 0 and     # order divisible by 7
         i <> 7 and          # but not equal to 7
         q^3 mod i = 1 and   # order divides q^3-1
        (7*(q-1)) mod i <> 0 # order does not divide 7*(q-1)
         )) <> fail then 
            # 5 is not ppd of q^2-1
            return CheckFlag();
        fi;
    elif d = 3 and q = 4 then
        if Order(grp) mod 216 = 0 then 
            return CheckFlag();
        else
            recognise.IsSUContained := false;
            return NeverApplicable;
        fi;
    elif d = 3 and q = 9 then 
        if not HasElementsMultipleOf(recognise.orders, [7]) then
            return TemporaryFailure; 
        fi;
        if recognise.hasSpecialEle = false then
            if not Order( recognise.g ) mod 6 = 0 then return TemporaryFailure; fi;
            if PositionProperty( GeneratorsOfGroup(grp), 
                h-> (Comm(h,recognise.g^3) <> One(grp))) <> fail then
                Info( InfoClassical,2, 
            "Cube of element of order div by 6 is not central" );
                 recognise.hasSpecialEle := true;
                return CheckFlag();
             fi;
        else return CheckFlag();
        fi;
    elif d = 3 and q = 16 then 
        if not HasElementsMultipleOf(recognise.orders, [5,13]) then
            return TemporaryFailure; 
        fi;
        if recognise.hasSpecialEle = false then
            if not Order(recognise.g) mod 5  = 0 then return TemporaryFailure; fi;
            if PositionProperty( GeneratorsOfGroup(grp), 
            h-> (Comm(h,recognise.g) <> One(grp))) <> fail then
                Info( InfoClassical,2, 
                "The element of order 5 is not central" );
                 recognise.hasSpecialEle := true;
                 return CheckFlag();
            fi;
        else return CheckFlag();
        fi;
    elif d = 3 and q = 25 then 
        if not HasElementsMultipleOf(recognise.orders, [5,7,8]) then
            return TemporaryFailure; 
        fi;
        if recognise.hasSpecialEle = false then
            if Order(recognise.g) mod 8 <> 0 then return TemporaryFailure; fi;
            g := recognise.g^(Order(recognise.g)/2);
            if PositionProperty( GeneratorsOfGroup(grp), 
                h-> (Comm(h,g) <> One(grp))) <> fail then
                Info( InfoClassical,2, 
                "involution in cyclic subgroup  of order 8 is not central" );
                recognise.hasSpecialEle := true;
                return CheckFlag();
             fi;
        else return CheckFlag();
        fi;        
    elif d = 3 and q >= 49  then 
        if not 3 in recognise.LE or not 3 in recognise.BE then
           return TemporaryFailure;
        fi;
        if not recognise.ppd[1] = 3 or not recognise.ppd[2]=true
           or not recognise.ppd[3]=true then 
            return TemporaryFailure; 
        fi;
        if recognise.hasSpecialEle = false then
            g := recognise.g;
            o := Order(g);
            q0 := Characteristic(recognise.field)^
             (LogInt(q,Characteristic(recognise.field))/2);
            if not ((q0^2 - q0 + 1)/Gcd(3,q0+1)) mod o = 0 then
                return TemporaryFailure;
            fi;
            if not o > 7* Gcd(3,q0+1) then
                return TemporaryFailure;
            fi;
            if PositionProperty(recognise.porders,
               i->(i[1]>3 and q mod i[1]=1))=fail then
                return TemporaryFailure;
            fi;
            recognise.hasSpeccialEle := true;
            return CheckFlag();
         else 
            return CheckFlag();
         fi;
    else
        Info(InfoClassical,2, 
            "NonGenericUnitary: d and q must have been be generic");
        return NeverApplicable;
    fi;

    return CheckFlag();
end;


RECOG.NonGenericOrthogonalPlus := function(recognise,grp)

    local d, q, gp1, gp2, CheckFlag, pgrp, orbs;

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return TemporaryFailure;
        fi;
        Info(InfoClassical,2,"group contains SO+(", 
        recognise.d, ", ", recognise.q, ");");

        recognise.IsSOContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

    if not d in [4,6,8,10] then return NeverApplicable; fi;

    if d = 10 and q <> 2 then return NeverApplicable; fi;
    if recognise.isReducible = true then return NeverApplicable; fi;

    if Length( recognise.ClassicalForms ) > 0 and 
       not "orthogonalplus" in recognise.ClassicalForms then
       return NeverApplicable;
    fi;

    if recognise.n <= 5 then
        return NeverApplicable;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        if d = 8 then
           recognise.needE2 := true;
        fi;
        return TemporaryFailure;
    fi;

    if d = 10 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [17,31])  then
            return TemporaryFailure; 
        fi;
    elif d = 8 and q = 2 then
        if not IsSubset(recognise.orders,[7, 9, 10, 15]) then 
            return TemporaryFailure;
        fi;
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        orbs := Orbits( pgrp, MovedPointsPerms( GeneratorsOfGroup(pgrp)));   

        if Set(List(orbs,Length)) <> [ 120, 135 ] then 	
           recognise.isSOContained := false;
           return NeverApplicable; 
        fi;
	if Size(pgrp) mod  174182400 = 0 then
           return CheckFlag();
           recognise.isSOContained := true;
        else
           recognise.isSOContained := false;
           return NeverApplicable; 
         fi;
    elif d = 8 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [7,13])  then
            return TemporaryFailure; 
        fi;
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        orbs := Orbits( pgrp, MovedPointsPerms( GeneratorsOfGroup(pgrp)));   
	if Set(List(orbs, Length)) <> [ 1080, 1120] then
             recognise.isSOContained := false;
             return NeverApplicable; 
        fi;
        if Size(pgrp) mod 4952179814400 = 0 then 
             return CheckFlag();
        else
             recognise.isSOContained := false;
             return NeverApplicable;
        fi;
    elif d = 8 and  q =  5 then 
        if not HasElementsMultipleOf( recognise.orders, [7,13])  then
            return TemporaryFailure; 
        fi;
    elif d = 8 and (q = 4 or q > 5) then 
        if not 6 in recognise.LB then return TemporaryFailure; fi;
        if not 4 in recognise.LS then return TemporaryFailure; fi;
    elif d = 6 and q = 2 then
        if not IsSubset( recognise.orders, [7,15] ) then return TemporaryFailure; fi;
    elif d = 6 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5])  then
            return TemporaryFailure; 
        fi;
        if not 13 in recognise.orders then return TemporaryFailure; fi;
    elif d = 6 and q >= 4 then
        if not 4 in recognise.LB then return TemporaryFailure; fi;
        if not 3 in recognise.E2 then return TemporaryFailure; fi;
    elif d = 4 and (q = 8 or q >= 11) then
        if recognise.needPlusMinus = false then 
            recognise.needPlusMinus := true;
            return NeverApplicable;
        fi;
        if not IsSubset(recognise.plusminus,[[1,1],[1,-1],[-1,-1]]) then
            return TemporaryFailure;
        fi;
    elif d = 4 and q = 2 then
        if Size(grp) mod 36 <> 0 then 
            recognise.isSOContained := false;
            return NeverApplicable; 
        fi;
        if recognise.needDecompose = false then 
           recognise.needDecompose := true;
           return TemporaryFailure;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoClassical,2,"Group projects to group of order ",
        Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars),"\n");
        if Size(gp1/recognise.scalars) mod 6 = 0 and
           Size(gp2/recognise.scalars) mod 6 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q = 3 then
        if Size(grp) mod 288 <> 0 then 
            recognise.isSOContained := false;
            return NeverApplicable; 
        fi;
        if recognise.needDecompose = false then 
           recognise.needDecompose := true;
           return TemporaryFailure;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoClassical,2,"Group projects to group of order ",
        Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars),"\n");
        if Size(gp1/recognise.scalars) mod 12 = 0 and
           Size(gp2/recognise.scalars) mod 12 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q =  4 then
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        orbs := Orbits( pgrp, MovedPointsPerms(
           GeneratorsOfGroup(pgrp)));   
        # TODO Check this in MAGMA
        if Size(pgrp) mod 3600 <> 0 then 
             recognise.isSOContained := false;
             return NeverApplicable; 
        fi;
        if recognise.needDecompose = false then 
           recognise.needDecompose := true;
           return TemporaryFailure;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoClassical,2,"Group projects to group of order ",
        Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars),"\n");
        if Size(gp1/recognise.scalars) mod 3 = 0 and
           Size(gp2/recognise.scalars) mod 3 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q = 5 then
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        if Size(pgrp) mod 7200 <> 0 then 
            recognise.isSOContained := false;
            return NeverApplicable;
        else
            return CheckFlag();
        fi;
    elif d = 4 and q = 7 then
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        if Size(pgrp) mod 56448  <> 0 then 
            recognise.isSOContained := false;
            return NeverApplicable;
        fi;
        if recognise.needDecompose = false then 
           recognise.needDecompose := true;
           return TemporaryFailure;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoClassical,2,"Group projects to group of order ",
        Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars),"\n");
        if Size(gp1/recognise.scalars) mod 168 = 0 and
           Size(gp2/recognise.scalars) mod 168 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q = 9 then
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        if Size(pgrp) mod 259200 <> 0 then 
            recognise.isSOContained := false;
            return NeverApplicable;
        else
            return CheckFlag();
        fi;
    else
        Info(InfoClassical, 2,
           "NonGenericO+: d and q must have  been be generic");  
        return NeverApplicable;
    fi;
     
     return CheckFlag();

end;

RECOG.NonGenericOrthogonalMinus := function(recognise, grp)

    local d, q, orbs, pgrp, h,  g, ppd,  CheckFlag;

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return TemporaryFailure;
        fi;
        Info(InfoClassical,2,"group contains SO-(", 
        recognise.d, ", ", recognise.q, ");");
        recognise.IsSOContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

    if not d in [4,6,8] then return NeverApplicable; fi;
    if d = 8 and q <> 2 then return NeverApplicable; fi;
    if d = 6 and q > 3 then return NeverApplicable; fi;

    if recognise.isReducible = true then return NeverApplicable; fi;

    if Length( recognise.ClassicalForms ) > 0 and 
       not "orthogonalminus" in recognise.ClassicalForms then
       return NeverApplicable;
    fi;

    if recognise.n <= 5 then
        return NeverApplicable;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return TemporaryFailure;
    fi;

    if d = 8 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [9,17])  then
            return TemporaryFailure; 
        fi;
    elif d = 6 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5,7,9])  then
            return TemporaryFailure; 
        fi;
    elif d = 6 and q = 2 then 
        if not HasElementsMultipleOf( recognise.orders, [5,9])  then
            return TemporaryFailure; 
        fi;
    elif d = 4 and q = 2 then 
        if not HasElementsMultipleOf( recognise.orders, [3,5])  then
            return TemporaryFailure; 
        fi;
    elif d = 4 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5])  then
            return TemporaryFailure; 
        fi;
        pgrp := ProjectiveActionOnFullSpace( grp, GF(3), 4 );       
        orbs := Orbits( pgrp, MovedPointsPerms( GeneratorsOfGroup(pgrp)));
        if Length(orbs) <>  3 then
            recognise.isSOContained := false;
            return NeverApplicable;
         fi;
    elif d = 4 and q >=  4 then
         # TODO check this in Magma
        ppd := IsPpdElement( recognise.field, recognise.cpol, d, q, 1 );
        if ppd = false or ppd[1] <> 4 then return TemporaryFailure; fi;
        # found a ppd( 4, q; 4)-element
        g := recognise.g;
        for h in GeneratorsOfGroup(grp) do
            if Comm(h,g) <> One(grp) or Comm(Comm(h,g),g) <> One(grp) then
                        return CheckFlag();
            fi;
        od;
        Info(InfoClassical, 2, "grp contained in O-(2,", q,  "^2)\n" );
        recognise.isNotExt := false;
        recognise.isSOContained := false;
        return NeverApplicable;
    else
      Info(InfoClassical, 2, "NonGenericO-: d and q must be generic\n" );
        return NeverApplicable;
    fi;

     return CheckFlag();

end;


RECOG.NonGenericOrthogonalCircle := function( recognise, grp )

    local d, q, g, s, CheckFlag;

    if not IsOddInt(recognise.d) then return NeverApplicable; fi;
    if not IsOddInt(recognise.q) then return NeverApplicable; fi;

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return TemporaryFailure;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return TemporaryFailure;
        fi;
        Info(InfoClassical,2,"group contains SOo(", 
        recognise.d, ", ", recognise.q, ");");
        recognise.IsSOContained := true;
        return Success;
    end;

    d := recognise.d;
    q := recognise.q;

    if recognise.isReducible = true then return NeverApplicable; fi;

    if Length( recognise.ClassicalForms ) > 0 and 
       not "orthogonalcircle" in recognise.ClassicalForms then
       return NeverApplicable;
    fi;

    if recognise.n <= 5 then
        return NeverApplicable;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return TemporaryFailure;
    fi;


    if d = 7 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5,7,13])  then
            return TemporaryFailure; 
        fi;
    elif d = 5 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5,9])  then
            return TemporaryFailure; 
        fi;
    elif d = 5 and q >= 5 then 
        if not 4 in recognise.LE then return TemporaryFailure; fi;
    elif d = 3 and q = 3 then 
        if not HasElementsMultipleOf( recognise.orders, [3])  then
            return TemporaryFailure; 
        fi;
    elif d = 3 and q = 5 then 
        if not HasElementsMultipleOf( recognise.orders, [3,5])  then
            return TemporaryFailure; 
        fi;
    elif d = 3 and q = 7 then 
        if not HasElementsMultipleOf( recognise.orders, [4,7])  then
            return TemporaryFailure; 
        fi;
    elif d = 3 and q = 9 then 
        if not HasElementsMultipleOf( recognise.orders, [3,5])  then
            return TemporaryFailure; 
        fi; 
        if recognise.hasSpecialEle = false then
            if not Order(recognise.g) in [4,8] then return TemporaryFailure; fi;
            g := recognise.g^2;
            if PositionProperty(GeneratorsOfGroup(grp), 
               h->(Comm(h,g)<>One(grp))) <> fail then 
               recognise.hasSpecialEle := true;
               return CheckFlag();
            fi;
        else
               return CheckFlag();
        fi; 
        recognise.IsSOContained := false;
        return NeverApplicable;
    elif d = 3 and q = 11 then 
        if not HasElementsMultipleOf( recognise.orders, [3,11])  then
            return TemporaryFailure; 
        fi; 
    elif d = 3 and q = 19 then 
        if not HasElementsMultipleOf( recognise.orders, [5,9,19])  then
            return TemporaryFailure; 
        fi; 
    elif d = 3 and q >=31 and IsPowerOfPrime(q+1,2) then 
        s := LogInt(q+1,2);
        if PositionProperty(recognise.orders,
            i->(i > 2 and (q-1) mod i = 0))=fail then 
            return TemporaryFailure; 
        fi; 
        if PositionProperty(recognise.orders, 
            i-> i mod 2^(s-1) = 0 ) = fail then
            return TemporaryFailure; 
        fi; 
    elif d = 3 and q>11 and ((q+1) mod 3=0 and
        IsPowerOfPrime((q+1)/3,2)) then 
        # TO DO Check this in Magma
        s := LogInt( (q+1)/3, 2);
        if PositionProperty(recognise.orders, 
            i-> i mod (3*2^(s-1)) = 0 ) = fail then
            return TemporaryFailure; 
        fi; 
        if PositionProperty(recognise.orders,
            i->(i > 2 and (q-1) mod i = 0))=fail then 
            return TemporaryFailure; 
        fi; 
    elif d = 3 and ((q+1) mod 3 <> 0 or not IsPowerOfPrime((q+1)/3,2)) and
                   not IsPowerOfPrime(q+1,2) then 
        if not 2 in recognise.LB then return TemporaryFailure; fi;
        if PositionProperty(recognise.orders,
            i->(i > 2 and (q-1) mod i = 0))=fail then 
            return TemporaryFailure; 
        fi; 
    else
       Info(InfoClassical, 2, "NonGenericOo: d and q must be generic\n" );
        return NeverApplicable;
    fi;

     return CheckFlag();
end;





##############################
##                          ##
## sg (functions for d = 2) ##
##                          ##
##############################

# generates the next random element and its char polynomial
RECOG.TestRandomElementCase2 := function ( recognise, grp )

    local g, porder;

    if recognise.d <> 2 then return NeverApplicable; fi;

    recognise.g := PseudoRandom(grp);
    recognise.cpol := CharacteristicPolynomial(recognise.g); 
    recognise.n := recognise.n + 1;

    g := recognise.g;

    if recognise.needPOrders then
        porder := ProjectiveOrder(g);
        AddSet( recognise.porders, porder );

	# for further calculations find h in G s.t. h^2 is not in Z(G)
        if porder[1] > 2 then
	    recognise.h := g;
	    recognise.hasExp2 := false;
	    recognise.needPOrders := false;
	fi;
    fi;

    return TemporaryFailure;
end;


# tests whether group is abelian
RECOG.IsAbelian := function ( recognise, grp )

    if recognise.d <> 2 then return NeverApplicable; fi;

    if IsAbelian( grp ) then
	recognise.isAbelian := true;
        # an abelian group does not contain SL(2,q)
        Info( InfoClassical, 2, 
        "The group is abelian and thus doesn't contain a classical group");
	recognise.IsSLContained := false;
	return Success;
    fi;

    recognise.isAbelian := false;
    return NeverApplicable;
end;


# tests whether group modulo scalars has exp = 2
RECOG.HasExp2 := function ( recognise, grp )

    local generators, gen, porder;

    if recognise.d <> 2 then return NeverApplicable; fi;
    if recognise.hasExp2 <> "unknown" then return NeverApplicable; fi;

    generators := recognise.generators;

    # if testing random elements did not rule out
    # the case exp(G/Z) = 2 then test generators
    if recognise.n > 15 then
	# find projective order of generators and - if possible -
	# set h such that h^2 is not in Z(G)
	for gen in generators do
	    porder := ProjectiveOrder( gen );
	    if porder[1] > 2 then
	        recognise.h := gen;
	        recognise.hasExp2 := false;
	        return NeverApplicable;
	    fi;
	od;
	# if all generators have projective order <= 2 then 
	# g^2 in Z for all g in G and thus (gZ)^2 = Z
	# hence ord(gZ) = 2 for all gZ in G/Z, i.e. exp(G/Z) = 2
	recognise.hasExp2 := true;
        # a group with exp(G/Z) = 2 does not contain SL(2,q)
	Info( InfoClassical, 2,
        "The group modulo scalars has exponent 2 and thus doesn't contain a classical group");
	recognise.IsSLContained := false;
	return Success;
    fi;

    return TemporaryFailure;
end;


# tests whether G is a subgroup of GammaL(1,q^2)
RECOG.IsSubgroupOfGammaL := function ( recognise, grp )

    local h, q, gen, generators, x, x2, charPol;

    if recognise.d <> 2 then return NeverApplicable; fi;

    # in case we haven't found h yet try again later
    if recognise.h  = fail then return TemporaryFailure; fi;

    h := recognise.h;
    q := recognise.q;
    charPol := CharacteristicPolynomial(h^2);
    x := h^4;
    generators := recognise.generators;

    # if h^2 is reducible then G is not conjugate to a subgroup of GammaL
    if not IsIrreducible(charPol) then
	recognise.isSubgroupOfGammaL := false;
	return NeverApplicable;
    fi;

    # if h^2 is not 'primitive', i.e a ppd(2,q;2)-element, then find a new h
    if ( Order( h^2 ) in Factors( q^2-1 ) ) = false or
     Order( h^2 ) in Factors( q-1 ) then
        recognise.needPOrders := true;
        return TemporaryFailure;
    fi;

    for gen in generators do
	x2 := x^gen;
	if (x2 * x <> x * x2) then
	    recognise.isSubgroupOfGammaL := false;
            return NeverApplicable;
      	fi;
    od;

    recognise.isSubgroupOfGammaL := true;
    # a subgroup of GammaL does not contain SL(2,q)
    Info( InfoClassical, 2, 
    "The group is conjugate to a subgroup of GammaL(1,", q, ") and thus doesn't contain a classical group");
    recognise.IsSLContained := false;
    return Success;
end;


# tests whether G is imprimitive
RECOG.IsImprimitive := function ( recognise, grp )

  local h, f, gen, genNew, generators, eigenvectors;

    if recognise.d <> 2 then return NeverApplicable; fi;

    # in case we haven't found h yet try again later
    if recognise.h = fail then return TemporaryFailure; fi;
 
    h := recognise.h;
    f := recognise.field;
    generators := recognise.generators;
    eigenvectors := Eigenvectors( f, h^2 );

    # if there are not two distict eigenspaces then G is primitive
    if Length(eigenvectors) <> 2 then
	recognise.isImprimitive := false;
	return NeverApplicable;
    fi;

    # consider the list of eigenvectors as a matrix
    for gen in generators do
    genNew := gen^eigenvectors;
	# if genNew is not monomial, then G is primitive
        if not IsMonomialMatrix( genNew ) then
	    recognise.isImprimitive := false;
	    return NeverApplicable;
        fi;

    od;
    recognise.isImprimitive := true;
    # an imprimitive group does not contain SL(2,q)
    Info( InfoClassical, 2, 
    "The group is imprimitive and thus doesn't contain a classical group");
    recognise.IsSLContained := false;
    return Success;
end;


# tests if group is isomorphic to Alt(5), Alt(4), Sym(4)
RECOG.IsAlt5Alt4Sym4 := function ( recognise, grp )

    local pgrp, q;
 
    if recognise.d <> 2 then return NeverApplicable; fi;

    pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, 2 );
    recognise.pgrp := pgrp;
    q := recognise.q;

    if NrMovedPoints( pgrp ) <= 5 then
      # check if G/Z is isomorphic to Alt4, Alt5 or Sym4
      # and is not one of the exceptions ( GL(2,3), SL(2,3),
      # GL(2,4), SL(2,4), SL(2,5), <SL(2,3), Z(GL(2,5))> )
      # if so, then G does not contain SL(2,q)
      if (Size( pgrp ) = 12 and q <> 3) or 
         (Size( pgrp ) = 24 and q <> 3) or
         (Size( pgrp ) = 60 and q <> 4 and q <> 5) then
        if IsAlternatingGroup(pgrp) or IsSymmetricGroup(pgrp) then
          recognise.isAlt5Alt4Sym4 := true;
	  Info( InfoClassical, 2,
          "The group modulo scalars is isomorphic to Alt5, ALt4 or Sym4 and is not one of the exceptions thus doesn't contain a classical group");
     	  recognise.IsSLContained := false;
    	  return Success;
        fi;
      fi;
    fi;

    recognise.isAlt5Alt4Sym4 := false;
    return NeverApplicable;
end;


# tests whether a subgroup of GL(2,q) contains SL(2,q)
RECOG.IsSL2Contained := function( recognise, grp )

    if recognise.d <> 2 then return NeverApplicable; fi;
    if recognise.isReducible = true then return NeverApplicable; fi;

    # if G has passed all the tests so far then it is either representable
    # over a proper subfield modulo scalars or it contains SL(2,q)
    if (recognise.isReducible = false and
        recognise.isAbelian = false and
        recognise.hasExp2 = false and
        recognise.isSubgroupOfGammaL = false and
        recognise.isImprimitive = false and
        recognise.isAlt5Alt4Sym4 = false) then

       # if G is transitive on the q+1 1-dim subspaces of the underlying
       # vector space then it is not realizable over a proper subfield
       if IsTransitive( recognise.pgrp ) then
          recognise.isRepresentableOverSubfield := false;
          Info(InfoClassical,2,"The group is not generic");
          Info(InfoClassical,2,"and contains SL(", 2, ", ", recognise.q, ");");
          recognise.IsSLContained := true;
          return Success;
       fi;

       recognise.isRepresentableOverSubfield := true;
       Info( InfoClassical, 2, 
       "The group is representable over a proper subfield and thus doesn't contain a classical group");
       recognise.IsSLContained := false;
       return Success;
    fi;

    return TemporaryFailure;
end;
