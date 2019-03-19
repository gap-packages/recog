#############################################################################
##
##  AnBB.gi
##                              recog package
##                                                            Martin Leuner
##                                                         Sebastian Jambor
##                                                      & Alice C. Niemeyer
##
##
##  Copyright (C) 2012 by the authors.
##  Lehrstuhl B f"ur Mathematik, RWTH Aachen and
##  the University of Western Australia.
##
##  This file is free software, see license information at the end.
##
##
##  This file provides code for recognising whether a black box group
##  with degree n \le N for given N is isomorphic to A_n or S_n.
##
##  Most of the code is based upon the algorithm presented in the paper
##  "Fast recognition of alternating groups of unknown degree" by
##  Sebastian Jambor, Martin Leuner, Alice C. Niemeyer and Wilhelm Plesken.
##
##  Several functions, namely AnBB_AnPresentationSatisfied, AnBB_SnPresentationSatisfied,
##  AnBB_SLPForAn, AnBB_SLPForSn and AnBB_ComputeIsomorphism are based upon
##  algorithms presented in the paper "A black-box group algorithm for
##  recognizing finite symmetric and alternating groups. I." by Robert Beals,
##  Charles R. Leedham-Green, Alice C. Niemeyer, Cheryl E. Praeger and
##  'Akos Seress.
##
##
##  This file is generated automatically.
##
SetInfoLevel( InfoRecAnBB, 0 );



# Function used to check whether a group element is trivial:
if not IsBound( AnBB_IsOne ) then
 AnBB_IsOne := IsOne;
fi;

# Function used to check whether two group elements equal each other:
if not IsBound( AnBB_Equals ) then
 AnBB_Equals := EQ;
fi;



########################################################################
##
## The function AnBB_InitialList initializes the data structure used by the algorithm.
##
AnBB_InitialList := function( G, N )
 local AnBB_Vars;
 AnBB_Vars := [];
 AnBB_Vars[23] := []; # allocate memory
 AnBB_Vars[23][8] := 0; # allocate memory
 AnBB_Vars[15] := [];
 AnBB_Vars[15][8] := 0; # allocate memory
 AnBB_Vars[1] := G;
 AnBB_Vars[2] := N;
 AnBB_Vars[9] := One( G );
 AnBB_Vars[4] := Product( List( Filtered( [ 3 .. AnBB_Vars[2] ], IsPrimeInt ), p -> p^LogInt(AnBB_Vars[2],p) ) );
 AnBB_Vars[7] := Int( 14441/5000*( Log2Int( AnBB_Vars[2] ) + 1 ) ) + 1;	
 return AnBB_Vars;
end;	# function AnBB_InitialList



########################################################################
##
## The function AnBB_NextSmallSupportInvolution tries to find an involution in G.
## It may find that G cannot be isomorphic to A_n or S_n for any n \le N, in this case it returns false.
## If it gives up, it returns fail.
## If it succeeds, it returns true and writes the involution to AnBB_Vars[8].
##
AnBB_NextSmallSupportInvolution := function( AnBB_Vars )
 local TempElement, SquareBound;
 AnBB_Vars[8] := One( AnBB_Vars[1] );

# Randomly search for a new involution:
 while AnBB_Vars[7] > 0 and AnBB_IsOne( AnBB_Vars[8] ) do
  AnBB_Vars[7] := AnBB_Vars[7] - 1;
  AnBB_Vars[8] := PseudoRandom( AnBB_Vars[1] ) ^ AnBB_Vars[4];
 od;

 if AnBB_Vars[7] <= 0 and AnBB_IsOne( AnBB_Vars[8] ) then
# Found no involution, giving up.
  return fail;
 fi;

# Repeatedly square new element to obtain an involution:
 SquareBound := Log2Int( AnBB_Vars[2] );
 TempElement := AnBB_Vars[8];
 while not AnBB_IsOne( TempElement ) and SquareBound > 0 do
  SquareBound := SquareBound - 1;
  AnBB_Vars[8] := TempElement;
  TempElement := TempElement ^ 2;
 od;

 if not AnBB_IsOne( TempElement ) then
# G is *certainly* not isomorphic to A_n or S_n for any n \le N.
  return false;
 fi;

# Found new involution.
# Reset bounds to generate a 3-cycle from it:
 AnBB_Vars[5] := 6;					
 AnBB_Vars[6] := Int( 18/5 * AnBB_Vars[2] ) + 1;
 return true;
end;	# function AnBB_NextSmallSupportInvolution



########################################################################
##
## The function AnBB_IsProbableThreeCycle heuristically checks whether an element is a 3-cycle.
## If it finds that the element cannot be a 3-cycle, it returns false.
## Otherwise it returns true.
##
AnBB_IsProbableThreeCycle := function( AnBB_Vars )
 local RndElement, ConjProducts, Powers, PowCounter, LogN, BuildingPower, TempElement, i;
 LogN := Log2Int( AnBB_Vars[2] );

 if AnBB_IsOne( AnBB_Vars[9] ) or not AnBB_IsOne( AnBB_Vars[9]^3 ) then
# Candidate has order <> 3
  return false;
 fi;

 for i in [ 1 .. 4 ] do
# Find non-commuting conjugate of candidate:
  RndElement := PseudoRandom( AnBB_Vars[1] );
 
  ConjProducts := [ AnBB_Vars[9] ^ RndElement ];
  ConjProducts[LogN] := One( AnBB_Vars[1] );	# allocate memory for whole list
 
  Powers := [ RndElement ];
  Powers[LogN] := ConjProducts[LogN];	# allocate memory for whole list
 
  PowCounter := 1;
 
  while AnBB_Equals( ConjProducts[PowCounter]*AnBB_Vars[9], AnBB_Vars[9]*ConjProducts[PowCounter] ) do
   PowCounter := PowCounter + 1;
   if PowCounter = LogN then
# Random element did not generate non-commuting element, giving up.
    return false;
   fi;
 
   ConjProducts[PowCounter] := ConjProducts[PowCounter-1] * ( ConjProducts[PowCounter-1] ^ Powers[PowCounter-1] );
   Powers[PowCounter] := Powers[PowCounter-1]^2;
  od;	# while commuting

  if PowCounter = 1 then
   BuildingPower := ConjProducts[LogN];
  else
   PowCounter := PowCounter - 1;
   BuildingPower := Powers[PowCounter];
  fi;
 
  while PowCounter > 1 do
   PowCounter := PowCounter - 1;
 
   TempElement := ConjProducts[PowCounter] ^ BuildingPower;
   if AnBB_Equals( AnBB_Vars[9] * TempElement, TempElement * AnBB_Vars[9] ) then
 
# Contribution of Powers[PowCounter] is necessary to reach non-commuting conjugate.
    BuildingPower := BuildingPower * Powers[PowCounter];
 
   fi;
 
  od;	# while PowCounter > 1
 
  BuildingPower := BuildingPower * RndElement;	# smallest power of RndElement s.t. [TC,TC^BP] \neq 1
  TempElement := AnBB_Vars[9] * AnBB_Vars[9] ^ BuildingPower;
 
  BuildingPower := TempElement^2;
  if not AnBB_IsOne( BuildingPower ) and not AnBB_IsOne( BuildingPower^2 * TempElement ) then
# Product of TC and TC^BP does not have order 2 or 5.
   return false;
  fi;

 od;	# for oracle checks

# All tests passed.
 return true;
end;	# function AnBB_IsProbableThreeCycle



########################################################################
##
## The function AnBB_NextThreeCycle tries to generate a 3-cycle out of a small support involution.
## If it gives up, it returns false.
## If it succeeds, it returns true and writes the probable 3-cycle to AnBB_Vars[9].
##
AnBB_NextThreeCycle := function( AnBB_Vars )
 local TempConjugate;

# Search for conjugates of SSI not commuting with SSI:
 while AnBB_Vars[6] > 0 and AnBB_Vars[5] > 0 do
  AnBB_Vars[6] := AnBB_Vars[6] - 1;
  TempConjugate := AnBB_Vars[8] ^ PseudoRandom( AnBB_Vars[1] );

  if not AnBB_Equals( TempConjugate*AnBB_Vars[8], AnBB_Vars[8]*TempConjugate ) then
# Found non-commuting conjugate, may obtain 3-cycle:
   AnBB_Vars[5] := AnBB_Vars[5] - 1;
   AnBB_Vars[9] := ( AnBB_Vars[8] * TempConjugate )^2;

# Test the 3-cycle candidate:
   if AnBB_IsProbableThreeCycle( AnBB_Vars ) then
# Probably found a 3-cycle.
    AnBB_Vars[10] := AnBB_Vars[9] ^ 2;
    return true;
   fi;

  fi; # if non-commuting

 od;
# Found no 3-cycle, giving up.
 return false;
end;	# function AnBB_NextThreeCycle



########################################################################
##
## The function AnBB_NextBolsteringElement tries to find a new bolstering element w.r.t. AnBB_Vars[9].
## If it gives up, it returns false.
## If it succeeds, it returns true and writes the element to AnBB_Vars[13].
##
AnBB_NextBolsteringElement := function( AnBB_Vars )
 local Candidate, Tmp1, Tmp2, Tmp3;

 while AnBB_Vars[14] > 0 do
  Candidate := PseudoRandom( AnBB_Vars[1] );
  AnBB_Vars[14] := AnBB_Vars[14] - 1;

# Check whether Candidate is pre-bolstering:
  Tmp1 := AnBB_Vars[9] ^ Candidate;
  if AnBB_Equals( Tmp1 * AnBB_Vars[9], AnBB_Vars[9] * Tmp1 ) then continue; fi;
  Tmp2 := Tmp1 ^ Candidate;
  if AnBB_Equals( Tmp2, AnBB_Vars[9] )
	or AnBB_Equals( Tmp2, AnBB_Vars[10] )
	or not AnBB_Equals( AnBB_Vars[9] * Tmp2, Tmp2 * AnBB_Vars[9] ) then
   continue;
  fi;

# Candidate is pre-bolstering. Make it bolstering:
  Tmp3 := AnBB_Vars[9] * Candidate;
  if AnBB_IsOne( ( Tmp1 ^ Tmp3 * Tmp1 ^ ( Tmp2 * AnBB_Vars[9] ) )^3 ) then
   AnBB_Vars[13] := AnBB_Vars[9] * Tmp3;
  else
   AnBB_Vars[13] := Tmp3;
  fi;

  return true;
 od; # while PBETries

# Found no pre-bolstering element, giving up.
 return false;
end;	# function AnBB_NextBolsteringElement



########################################################################
##
## The function AnBB_MatchingLongCycle tries to construct a cycle matching AnBB_Vars[9].
## If it gives up, it returns false.
## If it succeeds, it returns true, writes the cycle to AnBB_Vars[11] and its length to AnBB_Vars[12].
##
AnBB_MatchingLongCycle := function( AnBB_Vars )
 local RemainingBolsteringElements, GreatestElement, CurrentLength, CurrentConjugate, PointsBeforeFailure,
	PointsBeforeFailureLong, Tmp1, Tmp2, i, PointOfFailure, BESquared;

# Reset bounds for bolstering elements:
 RemainingBolsteringElements := 5;
 AnBB_Vars[14] := 35 * AnBB_Vars[2];
 AnBB_Vars[12] := 0;

# Find bolstering element of maximal length:
 while RemainingBolsteringElements > 0 do
  if not AnBB_NextBolsteringElement( AnBB_Vars ) then
# Failed to find enough bolstering elements, giving up.
   return false;
  fi;

  RemainingBolsteringElements := RemainingBolsteringElements - 1;

# Determine length of new bolstering element:
  CurrentConjugate := AnBB_Vars[9] ^ AnBB_Vars[13];
  CurrentLength := 3;

  Tmp1 := CurrentConjugate * AnBB_Vars[9];
# Go through bolstering element until first point of failure is reached:
  while not AnBB_IsOne( Tmp1^6 ) do	# criterion for first point of failure
   CurrentLength := CurrentLength + 2;

   if CurrentLength > AnBB_Vars[2] then
# AnBB_Vars[9] cannot be a 3-cycle, give up.
    return false;
   fi;

   CurrentConjugate := CurrentConjugate ^ AnBB_Vars[13];
   Tmp1 := CurrentConjugate * AnBB_Vars[9];
  od;	# first point of failure reached, now edit cycle and continue w/ BE^2
  PointsBeforeFailure := CurrentLength;

  if not AnBB_IsOne( Tmp1 ) and not AnBB_Equals( CurrentConjugate, AnBB_Vars[9] ) then # at least one point unused
   PointOfFailure := CurrentConjugate;
   CurrentConjugate := CurrentConjugate ^ AnBB_Vars[13];
   if not AnBB_IsOne( ( CurrentConjugate * AnBB_Vars[9] )^6 ) then # at least two points unused

# Decide form and length of components of the bolstering element, edit accordingly:
    Tmp2 := PointOfFailure ^ AnBB_Vars[9];
    if AnBB_Equals( CurrentConjugate * Tmp2, Tmp2 * CurrentConjugate ) then		# 1 in supp( PointOfFailure )
     if AnBB_IsOne( Tmp1^2 ) then			# PointOfFailure "=" (1,x,3)
      CurrentConjugate := PointOfFailure ^ ( ( CurrentConjugate ^ AnBB_Vars[9] ) ^ 2 );
     else					# PointOfFailure "=" (x,1,3)
      CurrentConjugate := PointOfFailure ^ ( CurrentConjugate ^ AnBB_Vars[9] );
     fi;
    else									# 2 in supp( PointOfFailure )
     if AnBB_IsOne( Tmp1^2 ) then			# PointOfFailure "=" (x,2,3)
      CurrentConjugate := PointOfFailure ^ ( CurrentConjugate ^ AnBB_Vars[10] );
     else					# PointOfFailure "=" (2,x,3)
      CurrentConjugate := PointOfFailure ^ ( ( CurrentConjugate ^ AnBB_Vars[10] ) ^ 2 );
     fi;
    fi;	# finished editing CurrentConjugate
    BESquared := AnBB_Vars[13] ^ 2;

# Go through bolstering element until second point of failure is reached:
    while not AnBB_IsOne( ( CurrentConjugate * AnBB_Vars[9] )^6 ) do
     CurrentLength := CurrentLength + 2;

     if CurrentLength > AnBB_Vars[2] then
# AnBB_Vars[9] cannot be a 3-cycle, give up.
      return false;
     fi;

     CurrentConjugate := CurrentConjugate ^ BESquared;
    od; # used all points in relevant cycles

   fi;
  fi; # if at least one point unused


# If bolstering element generates a cycle of greater length, save it:
  if CurrentLength > AnBB_Vars[12] then
   AnBB_Vars[12] := CurrentLength;
   PointsBeforeFailureLong := PointsBeforeFailure;
   GreatestElement := AnBB_Vars[13];
  fi;

 od; # while RemainingBolsteringElements 


 if AnBB_Vars[12] < 7 then
# Matching cycle would be too short, give up.
  return false;
 fi;


# Build cycle:
 i := (PointsBeforeFailureLong-1)/2;
 Tmp1 := GreatestElement ^ (i-1);
# First part:
 AnBB_Vars[11] := ( AnBB_Vars[9] * GreatestElement^-1 )^(i-1) * AnBB_Vars[9] * Tmp1;
 CurrentConjugate := AnBB_Vars[9] ^ ( Tmp1 * GreatestElement );

# Edit for second part if necessary:
 if PointsBeforeFailureLong < AnBB_Vars[12] then # at least two points unused
  PointOfFailure := CurrentConjugate;
  Tmp1 := CurrentConjugate * AnBB_Vars[9];
  CurrentConjugate := CurrentConjugate ^ GreatestElement;

  Tmp2 := PointOfFailure ^ AnBB_Vars[9];
  if AnBB_Equals( CurrentConjugate * Tmp2, Tmp2 * CurrentConjugate ) then	# 1 in supp PointOfFailure
   if AnBB_IsOne( Tmp1^2 ) then		# PointOfFailure "=" (1,x,3)
    CurrentConjugate := PointOfFailure ^ ( ( CurrentConjugate ^ AnBB_Vars[9] ) ^ 2 );
   else					# PointOfFailure "=" (x,1,3)
    CurrentConjugate := PointOfFailure ^ ( CurrentConjugate ^ AnBB_Vars[9] );
   fi;
  else										# 2 in supp PointOfFailure
   if AnBB_IsOne( Tmp1^2 ) then		# PointOfFailure "=" (x,2,3)
    CurrentConjugate := PointOfFailure ^ ( CurrentConjugate ^ AnBB_Vars[10] );
   else					# PointOfFailure "=" (2,x,3)
    CurrentConjugate := PointOfFailure ^ ( ( CurrentConjugate ^ AnBB_Vars[10] ) ^ 2 );
   fi;
  fi;

# Second part:
  BESquared := GreatestElement ^ 2;
  i := (AnBB_Vars[12]-1)/2 - (PointsBeforeFailureLong+3)/2 + 1;
  AnBB_Vars[11] := AnBB_Vars[11] * ( CurrentConjugate * BESquared^-1 )^i * CurrentConjugate * BESquared^i;
 fi;	# if PointsBeforeFailureLong < AnBB_Vars[12]

# Found enough elements and built cycle of maximal length.
 return true;
end;	# function AnBB_MatchingLongCycle



########################################################################
##
## The function AnBB_IsFixedPoint decides whether the element ActingElement
## fixes the unique point contained in the intersection of
## supp( CyclesAndConjs[1] ) and supp( CyclesAndConjs[3] ).
##
## In comparison with the Algorithm in [1], ActingElement corresponds to
## the element r, CyclesAndConjs[1] corresponds to c and CyclesAndConjs[3] corresponds
## to c^(g^2).
##
AnBB_IsFixedPoint := function( ActingElement, LargeSuppGenerator, NumberOfPoints, CyclesAndConjs )
 local CheckList, CheckConjugate, ShiftCycle, CommCtr, Comms11, Comms12, Comms13;

 if NumberOfPoints < 11 then
# Must use expensive method on few points:

# Check commutation with first list:
  CheckList := [ CyclesAndConjs[1], CyclesAndConjs[1] ^ CyclesAndConjs[2], , , ]; # allocate memory all at once

# First conjugate:
  CommCtr := 0;
  CheckConjugate := CyclesAndConjs[6];

  Comms11 := AnBB_Equals( CheckConjugate * CheckList[1], CheckList[1] * CheckConjugate );
  if Comms11 then CommCtr := CommCtr + 1; fi;

  if AnBB_Equals( CheckConjugate * CheckList[2], CheckList[2] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  CheckList[3] := CheckList[2] ^ CyclesAndConjs[4];
  if AnBB_Equals( CheckConjugate * CheckList[3], CheckList[3] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  CheckList[4] := CheckList[3] ^ CyclesAndConjs[4];
  if AnBB_Equals( CheckConjugate * CheckList[4], CheckList[4] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if CommCtr = 1 then
   CheckList[5] := CheckList[4] ^ CyclesAndConjs[5];
   if AnBB_Equals( CheckConjugate * CheckList[5], CheckList[5] * CheckConjugate ) then return false; fi; # Point must be moved
  fi;

# Second conjugate:
  CommCtr := 0;
  CheckConjugate := CyclesAndConjs[8];

  Comms12 := AnBB_Equals( CheckConjugate * CheckList[1], CheckList[1] * CheckConjugate );
  if Comms12 then CommCtr := CommCtr + 1; fi;

  if AnBB_Equals( CheckConjugate * CheckList[2], CheckList[2] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CheckConjugate * CheckList[3], CheckList[3] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CheckConjugate * CheckList[4], CheckList[4] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if CommCtr = 1 then
   if not IsBound( CheckList[5] ) then CheckList[5] := CheckList[4] ^ CyclesAndConjs[5]; fi;
   if AnBB_Equals( CheckConjugate * CheckList[5], CheckList[5] * CheckConjugate ) then return false; fi; # Point must be moved
  fi;

# Third conjugate:
  CommCtr := 0;
  CheckConjugate := CyclesAndConjs[3] ^ ( CyclesAndConjs[4] * CyclesAndConjs[5] * ActingElement );

  Comms13 := AnBB_Equals( CheckConjugate * CheckList[1], CheckList[1] * CheckConjugate );
  if Comms13 then CommCtr := CommCtr + 1; fi;

  if AnBB_Equals( CheckConjugate * CheckList[2], CheckList[2] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CheckConjugate * CheckList[3], CheckList[3] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CheckConjugate * CheckList[4], CheckList[4] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if CommCtr = 1 then
   if not IsBound( CheckList[5] ) then CheckList[5] := CheckList[4] ^ CyclesAndConjs[5]; fi;
   if AnBB_Equals( CheckConjugate * CheckList[5], CheckList[5] * CheckConjugate ) then return false; fi; # Point must be moved
  fi;

# Check commutation with second list:
  CheckList := [ CyclesAndConjs[1], CyclesAndConjs[2], , , ]; # allocate memory for whole list

# First conjugate:
  CommCtr := 0;

  if Comms11 then CommCtr := CommCtr + 1; fi;

  if AnBB_Equals( CyclesAndConjs[6] * CheckList[2], CheckList[2] * CyclesAndConjs[6] ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  CheckList[3] := CheckList[2] ^ CyclesAndConjs[4];
  if AnBB_Equals( CyclesAndConjs[6] * CheckList[3], CheckList[3] * CyclesAndConjs[6] ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  CheckList[4] := CheckList[3] ^ CyclesAndConjs[4];
  if AnBB_Equals( CyclesAndConjs[6] * CheckList[4], CheckList[4] * CyclesAndConjs[6] ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if CommCtr = 1 then
   CheckList[5] := CheckList[4] ^ CyclesAndConjs[5];
   if AnBB_Equals( CyclesAndConjs[6] * CheckList[5], CheckList[5] * CyclesAndConjs[6] ) then return false; fi; # Point must be moved
  fi;

# Second conjugate:
  CommCtr := 0;

  if Comms12 then CommCtr := CommCtr + 1; fi;

  if AnBB_Equals( CyclesAndConjs[8] * CheckList[2], CheckList[2] * CyclesAndConjs[8] ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CyclesAndConjs[8] * CheckList[3], CheckList[3] * CyclesAndConjs[8] ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CyclesAndConjs[8] * CheckList[4], CheckList[4] * CyclesAndConjs[8] ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if CommCtr = 1 then
   if not IsBound( CheckList[5] ) then CheckList[5] := CheckList[4] ^ CyclesAndConjs[5]; fi;
   if AnBB_Equals( CyclesAndConjs[8] * CheckList[5], CheckList[5] * CyclesAndConjs[8] ) then return false; fi; # Point must be moved
  fi;

# Third conjugate:
  CommCtr := 0;

  if Comms13 then CommCtr := CommCtr + 1; fi;

  if AnBB_Equals( CheckConjugate * CheckList[2], CheckList[2] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CheckConjugate * CheckList[3], CheckList[3] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CheckConjugate * CheckList[4], CheckList[4] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if CommCtr = 1 then
   if not IsBound( CheckList[5] ) then CheckList[5] := CheckList[4] ^ CyclesAndConjs[5]; fi;
   if AnBB_Equals( CheckConjugate * CheckList[5], CheckList[5] * CheckConjugate ) then return false; fi; # Point must be moved
  fi;

# No combination had at least two commuting pairs of elements, point must be fixed.
  return true;

 else
# Eleven or more points known, use cheaper method:

  CheckList := [ CyclesAndConjs[1], CyclesAndConjs[3], , , ]; # allocate memory for whole list

# First conjugate:
  CommCtr := 0;
  CheckConjugate := CyclesAndConjs[6];

  if AnBB_Equals( CheckConjugate * CheckList[1], CheckList[1] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;

  if AnBB_Equals( CheckConjugate * CheckList[2], CheckList[2] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  ShiftCycle := ( CyclesAndConjs[1] ^ 2 * LargeSuppGenerator ) ^ 2;
  CheckList[3] := CheckList[2] ^ ShiftCycle;
  if AnBB_Equals( CheckConjugate * CheckList[3], CheckList[3] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  CheckList[4] := CheckList[3] ^ ShiftCycle;
  if AnBB_Equals( CheckConjugate * CheckList[4], CheckList[4] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if CommCtr = 1 then
   CheckList[5] := CheckList[4] ^ ShiftCycle;
   if AnBB_Equals( CheckConjugate * CheckList[5], CheckList[5] * CheckConjugate ) then return false; fi; # Point must be moved
  fi;

# Second conjugate:
  CommCtr := 0;
  CheckConjugate := CyclesAndConjs[8];

  if AnBB_Equals( CheckConjugate * CheckList[1], CheckList[1] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;

  if AnBB_Equals( CheckConjugate * CheckList[2], CheckList[2] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CheckConjugate * CheckList[3], CheckList[3] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if AnBB_Equals( CheckConjugate * CheckList[4], CheckList[4] * CheckConjugate ) then CommCtr := CommCtr + 1; fi;
  if CommCtr = 2 then return false; fi; # Point must be moved

  if CommCtr = 1 then
   if not IsBound( CheckList[5] ) then CheckList[5] := CheckList[4] ^ ShiftCycle; fi;
   if AnBB_Equals( CheckConjugate * CheckList[5], CheckList[5] * CheckConjugate ) then return false; fi; # Point must be moved
  fi;

# No combination had at least two commuting pairs of elements, point must be fixed.
  return true;

 fi; # if too few points

end;	# function AnBB_IsFixedPoint



########################################################################
##
## The function AnBB_NextPoint shifts the cycles used by AnBB_IsFixedPoint
## by one point.
##
AnBB_NextPoint := function( AnBB_Vars )
 AnBB_Vars[15][1] := AnBB_Vars[15][2];
 AnBB_Vars[15][2] := AnBB_Vars[15][3];
 AnBB_Vars[15][3] := AnBB_Vars[15][4];
 AnBB_Vars[15][4] := AnBB_Vars[15][5];
 AnBB_Vars[15][5] := AnBB_Vars[15][5] ^ AnBB_Vars[16];
 AnBB_Vars[15][6] := AnBB_Vars[15][7];
 AnBB_Vars[15][7] := AnBB_Vars[15][8];
 AnBB_Vars[15][8] := AnBB_Vars[15][3] ^ AnBB_Vars[20];
end;	# function AnBB_NextPoint



########################################################################
##
## The function AnBB_AdjustCycle tries to find a conjugate of AnBB_Vars[20]
## which fixes two points and moves one point of supp( AnBB_Vars[9] ).
## If it fails, it returns false.
## If it succeeds, it returns true and replaces AnBB_Vars[20] by said conjugate.
##
AnBB_AdjustCycle := function( AnBB_Vars )
 local FoundFixed, i, InvGenCyc, Point1, Point2, FirstPointsFixed, ExchangingElement, TempElement;

 FirstPointsFixed := [,,]; # allocate memory
 InvGenCyc := AnBB_Vars[16]^-1;
 Point1 := 0;
 Point2 := 0;
# Initialise cycles used by AnBB_IsFixedPoint:
 AnBB_Vars[15][3] := AnBB_Vars[9];			# (1,2,3)
 AnBB_Vars[15][2] := AnBB_Vars[15][3] ^ ( InvGenCyc );	# (k,1,2)
 AnBB_Vars[15][1] := AnBB_Vars[15][2] ^ ( InvGenCyc );	# (k-1,k,1)
 AnBB_Vars[15][4] := AnBB_Vars[21];			# (2,3,4)
 AnBB_Vars[15][5] := AnBB_Vars[22];			# (3,4,5)
 AnBB_Vars[15][6] := AnBB_Vars[15][1] ^ AnBB_Vars[20];
 AnBB_Vars[15][7] := AnBB_Vars[15][2] ^ AnBB_Vars[20];
 AnBB_Vars[15][8] := AnBB_Vars[15][3] ^ AnBB_Vars[20];

# Check first three points:
 FirstPointsFixed[1] := AnBB_IsFixedPoint( AnBB_Vars[20], AnBB_Vars[16], AnBB_Vars[17], AnBB_Vars[15] );
 for i in [ 2, 3 ] do
  AnBB_NextPoint( AnBB_Vars );
  FirstPointsFixed[i] := AnBB_IsFixedPoint( AnBB_Vars[20], AnBB_Vars[16], AnBB_Vars[17], AnBB_Vars[15] );
 od;

 FoundFixed := Number( FirstPointsFixed, b->b );

 if FoundFixed <> 2 then
# Need to find more points.
 
  for i in [ 4 .. AnBB_Vars[17] ] do
   AnBB_NextPoint( AnBB_Vars );

   if AnBB_IsFixedPoint( AnBB_Vars[20], AnBB_Vars[16], AnBB_Vars[17], AnBB_Vars[15] ) then

    if FoundFixed < 2 then
     if Point1 = 0 then
      Point1 := i;
      if FoundFixed = 1 then
# Found fixed and moved points.
       break;
      fi;
     else
      Point2 := i;
# Found fixed and moved points.
      break;
     fi;
    fi;	# if FoundFixed < 2

   else	# if i is fixed point

    if FoundFixed > 2 then
     Point1 := i;
# Found fixed and moved points.
     break;
    fi;	# if FoundMoved < 1

   fi;	# if i is fixed point
  od;	# checked all points

  if Point1 = 0 or ( FoundFixed = 0 and Point2 = 0 ) then
   return false;
  fi;

 fi; # if FoundFixed <> 2

# We now know two fixed points and a moved point.
# Compute the exponent to adjust AnBB_Vars[20]:

 if FirstPointsFixed[1] then
  if FirstPointsFixed[2] then
   if FirstPointsFixed[3] then	# 1,2,3 fixed
    ExchangingElement := AnBB_Vars[9] ^ (
       AnBB_Vars[19]^(Point1-3) * AnBB_Vars[9]
       ) * AnBB_Vars[9];		# (2,3,p1)(1,2,3) = (1,2)(3,p1)
   else				# 1,2 fixed, 3 moved
    ExchangingElement := One( AnBB_Vars[1] );
   fi;
  else
   if FirstPointsFixed[3] then	# 1,3 fixed, 2 moved
    AnBB_NextPoint( AnBB_Vars );
    if AnBB_IsFixedPoint( AnBB_Vars[20], AnBB_Vars[16], AnBB_Vars[17], AnBB_Vars[15] ) then
     ExchangingElement := AnBB_Vars[21];	# (2,3,4)
    else
     ExchangingElement := AnBB_Vars[21]^2;	# (2,4,3)
    fi;
   else				# 1 fixed, 2,3 moved
    ExchangingElement := AnBB_Vars[9] ^ (
       AnBB_Vars[19]^(Point1-3) * AnBB_Vars[9] );	# (2,3,p1)
   fi;
  fi;
 else
  if FirstPointsFixed[2] then
   if FirstPointsFixed[3] then	# 2,3 fixed, 1 moved
    AnBB_NextPoint( AnBB_Vars );
    if AnBB_IsFixedPoint( AnBB_Vars[20], AnBB_Vars[16], AnBB_Vars[17], AnBB_Vars[15] ) then
     ExchangingElement := AnBB_Vars[9] ^ (AnBB_Vars[21]);	# (1,3,4)
    else
     ExchangingElement := AnBB_Vars[10] ^ (AnBB_Vars[21]);	# (1,4,3)
    fi;
   else				# 2 fixed, 1,3 moved
    if Point1 = 4 then
     ExchangingElement := AnBB_Vars[9] ^ (AnBB_Vars[21]);	# (1,3,4)
    else
     ExchangingElement := AnBB_Vars[9] ^ (
       AnBB_Vars[19]^(Point1-3) * AnBB_Vars[21] );	# (1,3,p1)
    fi;
   fi;
  else
   if FirstPointsFixed[3] then	# 3 fixed, 1,2 moved
    ExchangingElement := AnBB_Vars[10] ^ ( AnBB_Vars[19]^(Point1-3) )
       * AnBB_Vars[10];	# (1,p1,2)(1,3,2) = (1,p1)(2,3)
   else				# 1,2,3 moved
    TempElement := AnBB_Vars[9] ^ ( AnBB_Vars[19]^(Point1-3) );	# (1,2,p1)
    ExchangingElement := TempElement ^ ( AnBB_Vars[19]^(Point2-Point1) ) * TempElement;	# (1,2,p2)(1,2,p1) = (1,p1)(1,p2)
   fi;
  fi;
 fi;

# Conjugate new long cycle such that it fixes the points 1 and 2 and moves the point 3:
 AnBB_Vars[20] := AnBB_Vars[20] ^ ExchangingElement;

 return true;
end;	# function AnBB_AdjustCycle



########################################################################
##
## The function AnBB_AppendPoints finds new points in supp( AnBB_Vars[20] )
## and appends them to AnBB_Vars[16] or stores them in AnBB_Vars[18].
##
AnBB_AppendPoints := function( AnBB_Vars )
 local i, CurrentConjugate;

 CurrentConjugate := AnBB_Vars[10];
# Consider each point in support of adjusted long cycle:
 for i in [ 1 .. AnBB_Vars[12]-1 ] do
  CurrentConjugate := CurrentConjugate ^ AnBB_Vars[20];

  if AnBB_Equals( CurrentConjugate * AnBB_Vars[19], AnBB_Vars[19] * CurrentConjugate ) then
# CurrentConjugate contains a new point.

   if AnBB_Vars[3] then
# Two new points are known now.

    if not AnBB_Equals( AnBB_Vars[18], CurrentConjugate ) then
# New point is not the stored point.
# Append the new point:

     AnBB_Vars[18] := AnBB_Vars[18] ^ CurrentConjugate;	# SCy ^ CCo^2 "=" (1,z,2) ^ (1,x,2) = (1,x,z)
     AnBB_Vars[16] := AnBB_Vars[16] * AnBB_Vars[18];
     AnBB_Vars[17] := AnBB_Vars[17] + 2;
     AnBB_Vars[19] := AnBB_Vars[16] * AnBB_Vars[10];

     AnBB_Vars[3] := false;

    fi;	# if new point equals stored point

   else # if point pending
# No point stored, store new point in storage cycle:

    AnBB_Vars[18] := CurrentConjugate;
    AnBB_Vars[3] := true;

   fi; # if point pending

  fi; # if new point

 od;	# for i=1..InitLength-1
# Used all points in support of adjusted cycle.

end;	# function AnBB_AppendPoints



########################################################################
##
## The function AnBB_NiceGenerators tries to construct an element g such that
## g and AnBB_Vars[9] are standard generators for AnBB_Vars[1].
## If it gives up, it returns false.
## If it succeeds, it returns true and writes the element g to AnBB_Vars[16].
##
AnBB_NiceGenerators := function( AnBB_Vars )
 local NumberOfConjugates;

# Initialise variables for construction of the generating cycle:
 AnBB_Vars[18] := One( AnBB_Vars[1] );
 AnBB_Vars[3] := false;
 AnBB_Vars[16] := AnBB_Vars[11];
 AnBB_Vars[17] := AnBB_Vars[12];
 AnBB_Vars[19] := AnBB_Vars[16] * AnBB_Vars[10];
 AnBB_Vars[21] := AnBB_Vars[9] ^ AnBB_Vars[16];
 AnBB_Vars[22] := AnBB_Vars[21] ^ AnBB_Vars[16];
 NumberOfConjugates := Int( ( 4153*( Log2Int( AnBB_Vars[2] ) + 1 ) + 8492 )/5000 ) + 1;

# If there are enough points, shorten cycle to ensure that the support of the generating cycle
# contains at least two points fixed by conjugates of the initial long cycle.
 if AnBB_Vars[12] >= 9 then
  AnBB_Vars[12] := AnBB_Vars[12] - 2;
  AnBB_Vars[11] := AnBB_Vars[19];
 fi;

# Choose random conjugates and check them for new points:
 while NumberOfConjugates > 0 do

  AnBB_Vars[20] := AnBB_Vars[11] ^ PseudoRandom( AnBB_Vars[1] );
  NumberOfConjugates := NumberOfConjugates - 1;

  if not AnBB_AdjustCycle( AnBB_Vars ) then
# Something went wrong, this cannot happen on correct input. Giving up.
   return false;
  fi;
  AnBB_AppendPoints( AnBB_Vars );

  if AnBB_Vars[17] > AnBB_Vars[2] then
# Something went wrong, this cannot happen on correct input. Giving up.
   return false;
  fi;

 od; # while NumberOfConjugates > 0

# We should have all points now, compute standard generators: 
 if AnBB_Vars[3] then
# Degree is even.
  AnBB_Vars[17] := AnBB_Vars[17] + 1;
  AnBB_Vars[9] := AnBB_Vars[18]^2;
  AnBB_Vars[10] := AnBB_Vars[18];
  AnBB_Vars[16] := AnBB_Vars[16] * AnBB_Vars[9];
 else
# Degree is odd.
  AnBB_Vars[16] := AnBB_Vars[10] * AnBB_Vars[16];
 fi;

 return true;
end;	# function AnBB_NiceGenerators



########################################################################
##
## The function AnBB_SnPresentationSatisfied checks whether the tuple (AnBB_Vars[16], AnBB_Vars[9])
## satisfies a certain presentation for a symmetric group of degree AnBB_Vars[17].
## For the presentation cf. Coxeter/Moser: Generators and relations for discrete groups,
## Ergeb. Math. Grenzgeb. 19, 1957.
##
AnBB_SnPresentationSatisfied := function( AnBB_Vars )
 local j, GenPower;

# Basic order checks:
 if not AnBB_IsOne( AnBB_Vars[9]^2 )
	or not AnBB_IsOne( AnBB_Vars[16]^AnBB_Vars[17] )
	or not AnBB_IsOne( ( AnBB_Vars[16] * AnBB_Vars[9] )^(AnBB_Vars[17]-1) ) then
  return false;
 fi;

# Now try [t,s^j]^2 for all 2 \le j \le n/2:
 j := 4;
 GenPower := AnBB_Vars[16];

 while j <= AnBB_Vars[17] do
  GenPower := GenPower * AnBB_Vars[16];

  if not AnBB_IsOne( Comm( AnBB_Vars[9], GenPower )^2 ) then
   return false;
  fi;

  j := j + 2;
 od;

# Presentation is satisfied.
 return true;
end;	# function AnBB_SnPresentationSatisfied



########################################################################
##
## The function AnBB_AnPresentationSatisfied checks whether the tuple (AnBB_Vars[16], AnBB_Vars[9])
## satisfies a certain presentation for an alternating group of degree AnBB_Vars[17].
## For the presentation cf. Carmichael: Abstract definitions of the symmetric and
## alternating groups and certain other permutation groups, Quart. J. of Math. 49, 1923.
##
AnBB_AnPresentationSatisfied := function( AnBB_Vars )
 local k, Bnd, TCConj;

# Common order checks independent from parity of degree:
 if not AnBB_IsOne( AnBB_Vars[9]^3 ) or not AnBB_IsOne( AnBB_Vars[16]^(AnBB_Vars[17]-2) ) then
  return false;
 fi;

 if IsEvenInt( AnBB_Vars[17] ) then
# Even degree:

  if not AnBB_IsOne( ( AnBB_Vars[16] * AnBB_Vars[9] )^(AnBB_Vars[17]-1) ) then
   return false;
  fi;

# For 1 \le k \le (n-2)/2, try (ts^-kts^k)^2, k even, (t^-1s^-kts^k), k odd:
  k := 1;
  Bnd := (AnBB_Vars[17]-2)/2;
  TCConj := AnBB_Vars[9];

  while k <= Bnd do
   TCConj := TCConj ^ AnBB_Vars[16];

   if IsEvenInt(k) then
    if not AnBB_IsOne( ( AnBB_Vars[9] * TCConj )^2 ) then return false; fi;
   else
    if not AnBB_IsOne( ( AnBB_Vars[10] * TCConj )^2 ) then return false; fi;
   fi;

   k := k + 1;
  od;

 else
# Odd degree:

  if not AnBB_IsOne( ( AnBB_Vars[16] * AnBB_Vars[9] )^AnBB_Vars[17] ) then
   return false;
  fi;

# Try (ts^-kts^k)^2 for all 1 \le k \le (n-3)/2:
  k := 1;
  Bnd := (AnBB_Vars[17]-3)/2;
  TCConj := AnBB_Vars[9];

  while k <= Bnd do
   TCConj := TCConj ^ AnBB_Vars[16];

   if not AnBB_IsOne( ( AnBB_Vars[9] * TCConj )^2 ) then return false; fi;

   k := k + 1;
  od;

 fi;

# Presentation is satisfied.
 return true;
end;	# function AnBB_AnPresentationSatisfied



########################################################################
##
## The function AnBB_InitialiseIso computes certain group elements used
## to evaluate the homomorphism defined by the standard generators on
## arbitrary elements.
## It stores these elements in the list AnBB_Vars[23].
##
AnBB_InitialiseIso := function( AnBB_Vars )
 local i, SumOfPowers, CurrPower, CurrShift;

 AnBB_Vars[23][8] := 0; # allocate memory

 if IsEvenInt( AnBB_Vars[17] ) then
# We can only build an (n-1)-cycle, so adjust constants:
  AnBB_Vars[23][5] := AnBB_Vars[17] - 1;
 else
# We can build an n-cycle.
  AnBB_Vars[23][5] := AnBB_Vars[17];
 fi;

 AnBB_Vars[23][1] := Log2Int( QuoInt( AnBB_Vars[23][5], 3 ) ) + 1;

# If n is even, compute (1,3,...,n)^3.
# If n is odd, compute (1,2,3,...,n)^3.
 AnBB_Vars[23][7] := ( AnBB_Vars[16] * AnBB_Vars[9] );
 AnBB_Vars[23][8] := AnBB_Vars[23][7]^-1;
 AnBB_Vars[23][2] := [ AnBB_Vars[23][7]^3 ];
 AnBB_Vars[23][2][ AnBB_Vars[23][1] ] := AnBB_Vars[9]; # allocate memory

 if IsEvenInt( AnBB_Vars[17] ) then
# Start with (1,3,4):
  AnBB_Vars[23][3] := [ AnBB_Vars[9] ^ ( AnBB_Vars[16] * AnBB_Vars[10] ) ];
 else
# Start with (1,2,3):
  AnBB_Vars[23][3] := [ AnBB_Vars[9] ];
 fi;
 AnBB_Vars[23][3][ AnBB_Vars[23][1] ] := AnBB_Vars[9]; # allocate memory

# Compute powers and 3-cycle products:
 i := 1;
 while i < AnBB_Vars[23][1] do
  AnBB_Vars[23][2][ i + 1 ] := AnBB_Vars[23][2][ i ]^2;
  AnBB_Vars[23][3][ i + 1 ] := AnBB_Vars[23][3][ i ] * ( AnBB_Vars[23][3][ i ] ^ AnBB_Vars[23][2][ i ] );
  i := i + 1;
 od;

# Determine correct checks in the case that a cycle commutes with all 3-cycle products:
 CurrPower := 2 ^ ( i - 1 );
 SumOfPowers := 3*CurrPower;
 AnBB_Vars[23][4] := [];
 AnBB_Vars[23][6] := AnBB_Vars[23][3][ i ];
 CurrShift := AnBB_Vars[23][2][ i ];
 i := i - 1;
 while i > 0 and SumOfPowers < AnBB_Vars[23][5] do
  CurrPower := CurrPower/2;
  AnBB_Vars[23][4][i] := SumOfPowers + ( 3 * CurrPower ) <= AnBB_Vars[23][5];
  if AnBB_Vars[23][4][i] then
   SumOfPowers := SumOfPowers + ( 3 * CurrPower );
   AnBB_Vars[23][6] := AnBB_Vars[23][6] * ( AnBB_Vars[23][3][ i ] ^ CurrShift );
   CurrShift := CurrShift * AnBB_Vars[23][2][ i ];
  fi;
  i := i - 1;
 od;

end;	# function AnBB_InitialiseIso



########################################################################
##
## The function AnBB_NonCommThreeCycle returns a 3-cycle not commuting with ConjTC.
##
AnBB_NonCommThreeCycle := function( IsoData, ConjTC, CancelData )
 local Lv, TempElement, Expo, CollisionUp, CollisionsDown, Override;

 if CancelData[1] or CancelData[2] then
  Lv := CancelData[3];
 else
  Lv := 1;
 fi;

# Find first non-commuting product:
 while Lv <= IsoData[1] do
  TempElement := IsoData[3][Lv];
  if CancelData[1] or CancelData[2] then TempElement := CancelData[5] * TempElement; fi;
  if not AnBB_Equals( TempElement * ConjTC, ConjTC * TempElement ) then break; fi;
  Lv := Lv + 1;
 od;

 CollisionUp := Lv;
 CollisionsDown := [];

 if ( CancelData[1] or CancelData[2] ) and CollisionUp > CancelData[3] then
# Collision was on a further level than the previous collision. Don't need to cancel elements.
  CancelData[1] := false;
  CancelData[2] := false;
 fi;

# Binary search to find non-commuting 3-cycle:
 if Lv > IsoData[1] then

# ConjTC commuted with all check elements. Consider remaining points:
  Override := false;
  Lv := Lv - 2;
  Expo := IsoData[2][ CollisionUp - 1 ];

  while Lv > 0 do
   if IsoData[4][Lv] or Override then
# This level may contribute. Check whether it does.

# First check how much we know already:
    if CancelData[1] then

     if not CancelData[4][Lv] then

# There was no collision on this level during the first try, so there can't be one now either.
      CollisionsDown[Lv] := false;

     elif CancelData[2] then

      if not CancelData[6][Lv] then # CancelDown1 true, CancelDown2 false

# There was no collision on this level after cancellation of first non-commuting 3-cycle, so there can't be one now either.
       CancelData[1] := false;
       CollisionsDown[Lv] := false;

      else # CancelDown1 true, CancelDown2 true

# Collisions on this level in both previous tries, cancel corresponding cycles. Then check whether there still is a collision.
       TempElement := IsoData[3][Lv] ^ Expo * CancelData[5];
       CollisionsDown[Lv] := not AnBB_Equals( TempElement * ConjTC, ConjTC * TempElement );
       if not CollisionsDown[Lv] then
        CancelData[1] := false;
        CancelData[2] := false;
       fi;

      fi;

     else # CancelDown1 true, CancelSwitch2 false

# Collision on this level during first try, cancel corresponding cycle. Then check whether there still is a collision.
      TempElement := IsoData[3][Lv] ^ Expo * CancelData[5];
      CollisionsDown[Lv] := not AnBB_Equals( TempElement * ConjTC, ConjTC * TempElement );
      if not CollisionsDown[Lv] then
       CancelData[1] := false;
      fi;

     fi;

    elif CancelData[2] then # only second try is relevant

     if not CancelData[6][Lv] then

# No collision in second try on this level, so there can't be one now either.
      CollisionsDown[Lv] := false;

     else

# Collision on this level during second try, cancel corresponding cycle. Then check whether there still is a collision.
      TempElement := IsoData[3][Lv] ^ Expo * CancelData[7];
      CollisionsDown[Lv] := not AnBB_Equals( TempElement * ConjTC, ConjTC * TempElement );
      if not CollisionsDown[Lv] then
       CancelData[2] := false;
      fi;

     fi;

    else # both switches are off

     TempElement := IsoData[3][Lv] ^ Expo;
     CollisionsDown[Lv] := not AnBB_Equals( TempElement * ConjTC, ConjTC * TempElement );

    fi;

    if not CollisionsDown[Lv] then
# Need the corresponding power to reach non-commuting 3-cycle.
     Expo := Expo * IsoData[2][Lv];
    else
     Override := true;
    fi;

   fi;
   Lv := Lv - 1;
  od; # while Lv > 0

  if not IsoData[4][1] then TempElement := IsoData[3][1] ^ Expo; fi;

 else # if Lv > IsoPowerNum

# Check which powers we need to reach non-commuting 3-cycle:
  Lv := Lv - 1;

# Catch a first level hit to avoid a bad index:
  if Lv = 0 then return [ IsoData[3][1], 1, [ ] ]; fi;

  Expo := IsoData[2][Lv];
  Lv := Lv - 1;

  while Lv > 0 do

# First check how much we know already:
   if CancelData[1] then

    if not CancelData[4][Lv] then

# There was no collision on this level during the first try, so there can't be one now either.
     CollisionsDown[Lv] := false;

    elif CancelData[2] then

     if not CancelData[6][Lv] then # CancelDown1 true, CancelDown2 false

# There was no collision on this level after cancellation of first non-commuting 3-cycle, so there can't be one now either.
      CancelData[1] := false;
      CollisionsDown[Lv] := false;

     else # CancelDown1 true, CancelDown2 true

# Collisions on this level in both previous tries, cancel corresponding cycles. Then check whether there still is a collision.
      TempElement := IsoData[3][Lv] ^ Expo * CancelData[5];
      CollisionsDown[Lv] := not AnBB_Equals( TempElement * ConjTC, ConjTC * TempElement );
      if not CollisionsDown[Lv] then
       CancelData[1] := false;
       CancelData[2] := false;
      fi;

     fi;

    else # CancelDown1 true, CancelSwitch2 false

# Collision on this level during first try, cancel corresponding cycle. Then check whether there still is a collision.
     TempElement := IsoData[3][Lv] ^ Expo * CancelData[5];
     CollisionsDown[Lv] := not AnBB_Equals( TempElement * ConjTC, ConjTC * TempElement );
     if not CollisionsDown[Lv] then
      CancelData[1] := false;
     fi;

    fi;

   elif CancelData[2] then # only second try is relevant

    if not CancelData[6][Lv] then

# No collision in second try on this level, so there can't be one now either.
     CollisionsDown[Lv] := false;

    else

# Collision on this level during second try, cancel corresponding cycle. Then check whether there still is a collision.
     TempElement := IsoData[3][Lv] ^ Expo * CancelData[7];
     CollisionsDown[Lv] := not AnBB_Equals( TempElement * ConjTC, ConjTC * TempElement );
     if not CollisionsDown[Lv] then
      CancelData[2] := false;
     fi;

    fi;

   else # both switches are off

    TempElement := IsoData[3][Lv] ^ Expo;
    CollisionsDown[Lv] := not AnBB_Equals( TempElement * ConjTC, ConjTC * TempElement );

   fi;

   if not CollisionsDown[Lv] then
# Need the corresponding power to reach non-commuting 3-cycle.
    Expo := Expo * IsoData[2][Lv];
   fi;

   Lv := Lv - 1;

  od; # while Lv > 0

 fi; # if Lv > IsoPowerNum

# First non-commuting, non-cancelled 3-cycle is the base cycle conjugated by ( Expo * triple shift element ):
 return [ IsoData[3][1] ^ Expo, CollisionUp, CollisionsDown ];

end;	# function AnBB_NonCommThreeCycle



########################################################################
##
## The function AnBB_NonCommTCPoints returns the number of common moved
## points of two non-commuting 3-cycles.
##
AnBB_NonCommTCPoints := function( TC1, TC2 )
 local TCProd, Square;

 TCProd := TC1 * TC2;
 Square := TCProd^2;
 if AnBB_IsOne( Square ) or AnBB_IsOne( Square * TCProd ) then return 2; fi;
 return 1;
end;	# function AnBB_NonCommTCPoints



########################################################################
##
## The function AnBB_CycleNumber returns the number of the 3-cycle found by
## AnBB_NonCommThreeCycle with collisions indicated by Lv and CommList.
##
AnBB_CycleNumber := function( IsoData, Lv, CommList )
 local CurrLv, TCNum, CurrPow, Override;

 if Lv > IsoData[1] then

# Collision at maximum level, only take certain levels into account:
  Override := false;
  CurrLv := Lv - 2;
  TCNum := 2^CurrLv;
  CurrPow := TCNum;
  while CurrLv > 0 do
   CurrPow := CurrPow/2;
   if Override or IsoData[4][CurrLv] then
    if not CommList[CurrLv] then
     TCNum := TCNum + CurrPow;
    else
     Override := true;
    fi;
   fi;
   CurrLv := CurrLv - 1;
  od;
  return TCNum + 1;

 else

# Collision at lower level, go through every single one:
  TCNum := 1;
  CurrLv := 1;
  CurrPow := 1;
  if Lv = 1 then return 1; fi;
  while CurrLv < Lv-1 do
   if not CommList[CurrLv] then TCNum := TCNum + CurrPow; fi;
   CurrPow := 2 * CurrPow;
   CurrLv := CurrLv + 1;
  od;
  return TCNum + CurrPow;
 fi;

end;	# function AnBB_CycleNumber



########################################################################
##
## The function AnBB_FindSinglePoint identifies the single point moved
## by both ImageData[1]^EvalElement and ImageData[3]^EvalElement.
##
AnBB_FindSinglePoint := function( ImageData, IsoData, ImTCNum, EvalElement, SingleShift, MapElement, InvCurrTC )
 local FPData, FPTestElement, i;
 FPData := [];
 FPData[8] := 0; # allocate memory

 if ImageData[9][ ImTCNum ] = 1 then

  return 3*ImTCNum - 3 + Position( ImageData[10][ImTCNum], true );

 else

  i := 1;
  while i < 6 do
  FPData[i] := ImageData[i];
   i := i + 1;
  od;

  if ImTCNum = ImageData[7] then

   if ImageData[10][ ImTCNum ][1] then
# Check first point:
    FPData[8] := ImageData[3] ^ EvalElement;
    FPData[7] := ImageData[2] ^ EvalElement;
    FPData[6] := ImageData[1] ^ EvalElement;
    if AnBB_IsFixedPoint( EvalElement, IsoData[7], IsoData[5], FPData ) then
     ImageData[10][ ImTCNum ][1] := false;
     return 3*ImTCNum - 2;
    elif not ImageData[10][ ImTCNum ][2] then
     ImageData[10][ ImTCNum ][3] := false;
     return 3*ImTCNum;
    elif not ImageData[10][ ImTCNum ][3] then
     ImageData[10][ ImTCNum ][2] := false;
     return 3*ImTCNum - 1;
    else
# Check second point:
     FPTestElement := EvalElement * InvCurrTC;
     FPData[8] := ImageData[3] ^ FPTestElement;
     FPData[7] := ImageData[2] ^ FPTestElement;
     FPData[6] := ImageData[1] ^ FPTestElement;
     if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
      ImageData[10][ ImTCNum ][2] := false;
      return 3*ImTCNum - 1;
     else
      ImageData[10][ ImTCNum ][3] := false;
      return 3*ImTCNum;
     fi;
    fi;
   else
# First point is already image of another point. Check second point:
    FPTestElement := EvalElement * InvCurrTC;
    FPData[8] := ImageData[3] ^ FPTestElement;
    FPData[7] := ImageData[2] ^ FPTestElement;
    FPData[6] := ImageData[1] ^ FPTestElement;
    if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
     ImageData[10][ ImTCNum ][2] := false;
     return 3*ImTCNum - 1;
    else
     ImageData[10][ ImTCNum ][3] := false;
     return 3*ImTCNum;
    fi;
   fi;

  elif ImTCNum > ImageData[7] then

   if ImageData[10][ ImTCNum ][3] then
# Check third point:
    FPTestElement := EvalElement * MapElement;
    FPData[8] := ImageData[3] ^ FPTestElement;
    FPData[7] := ImageData[2] ^ FPTestElement;
    FPData[6] := ImageData[1] ^ FPTestElement;
    if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
     ImageData[10][ ImTCNum ][3] := false;
     return 3*ImTCNum;
    elif not ImageData[10][ ImTCNum ][2] then
     ImageData[10][ ImTCNum ][1] := false;
     return 3*ImTCNum - 2;
    elif not ImageData[10][ ImTCNum ][1] then
     ImageData[10][ ImTCNum ][2] := false;
     return 3*ImTCNum - 1;
    else
# Check second point:
     FPTestElement := FPTestElement * SingleShift;
     FPData[8] := ImageData[3] ^ FPTestElement;
     FPData[7] := ImageData[2] ^ FPTestElement;
     FPData[6] := ImageData[1] ^ FPTestElement;
     if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
      ImageData[10][ ImTCNum ][2] := false;
      return 3*ImTCNum - 1;
     else
      ImageData[10][ ImTCNum ][1] := false;
      return 3*ImTCNum - 2;
     fi;
    fi;
   else
# Third point is already image of another point. Check second point:
    FPTestElement := EvalElement * MapElement * SingleShift;
    FPData[8] := ImageData[3] ^ FPTestElement;
    FPData[7] := ImageData[2] ^ FPTestElement;
    FPData[6] := ImageData[1] ^ FPTestElement;
    if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
     ImageData[10][ ImTCNum ][2] := false;
     return 3*ImTCNum - 1;
    else
     ImageData[10][ ImTCNum ][1] := false;
     return 3*ImTCNum - 2;
    fi;
   fi;

  else # ImTCNum[1] < ImageData[7]

   if ImageData[10][ ImTCNum ][1] then
# Check first point:
    FPTestElement := EvalElement * MapElement;
    FPData[8] := ImageData[3] ^ FPTestElement;
    FPData[7] := ImageData[2] ^ FPTestElement;
    FPData[6] := ImageData[1] ^ FPTestElement;
    if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
     ImageData[10][ ImTCNum ][1] := false;
     return 3*ImTCNum - 2;
    elif not ImageData[10][ ImTCNum ][2] then
     ImageData[10][ ImTCNum ][3] := false;
     return 3*ImTCNum;
    elif not ImageData[10][ ImTCNum ][1] then
     ImageData[10][ ImTCNum ][2] := false;
     return 3*ImTCNum - 1;
    else
# Check second point:
     FPTestElement := FPTestElement * SingleShift;
     FPData[8] := ImageData[3] ^ FPTestElement;
     FPData[7] := ImageData[2] ^ FPTestElement;
     FPData[6] := ImageData[1] ^ FPTestElement;
     if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
      ImageData[10][ ImTCNum ][2] := false;
      return 3*ImTCNum - 1;
     else
      ImageData[10][ ImTCNum ][3] := false;
      return 3*ImTCNum;
     fi;
    fi;
   else
# First point is already image of another point. Check second point:
    FPTestElement := EvalElement * MapElement * SingleShift;
    FPData[8] := ImageData[3] ^ FPTestElement;
    FPData[7] := ImageData[2] ^ FPTestElement;
    FPData[6] := ImageData[1] ^ FPTestElement;
    if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
     ImageData[10][ ImTCNum ][2] := false;
     return 3*ImTCNum - 1;
    else
     ImageData[10][ ImTCNum ][3] := false;
     return 3*ImTCNum;
    fi;
   fi;

  fi; # ImTCNum =, >, < ImageData[7] cases

 fi; # if more than one possible image point

end;	# function AnBB_FindSinglePoint



########################################################################
##
## The function AnBB_PartialImageAn tries to find the images of the points
## in supp( CurrTC ) under the homomorphism defined by the standard generators.
##
AnBB_PartialImageAn := function( ImageData, IsoData, EvalElement, Degree, InvThreeCycle )
 local	NCRet1, NCRet2, NCRet3, CancelData, FirstCommonPoints, SecondCommonPoints, ImTCNum,
	SingleOnePointShift, SingleOnePointBackShift, TripleOnePointBackShift, i, Missing,
	Tries, MapElement, ImagePoint, ShiftedIMCycles, FPData, FPTestElement, TmpElement,
	PrevImTC, NextImTC, EditImTC, FirstPoint, SecondPoint, ThirdPoint, InvCurrTC, SecCheck;

 ShiftedIMCycles := 0;
 ImagePoint := [0,0,0];
 MapElement := [0,0,0];
 ImTCNum := [0,0,0];
 FPData := [0,0,0,0,0,0,0,0];
 InvCurrTC := ImageData[8]^2;
 

# Compute shifting cycles:
 SingleOnePointShift := InvCurrTC * IsoData[7];
 SingleOnePointBackShift := SingleOnePointShift^-1;
 TripleOnePointBackShift := SingleOnePointBackShift^3;

# Initialise behavioural variables for non-comm alg:
 CancelData := [];
 CancelData[7] := 0; # allocate memory
 CancelData[1] := false;
 CancelData[2] := false;

# Check whether current 3-cycle coincides with one of the cycles used to search for collisions in IsoData:
 if AnBB_Equals( IsoData[6] * ImageData[6], ImageData[6] * IsoData[6] ) then

# Check against backshifted cycles.
# Find first non-commuting 3-cycle:
  NCRet1 := AnBB_NonCommThreeCycle( IsoData, ImageData[6] ^ IsoData[7], CancelData );
  ImTCNum[1] := AnBB_CycleNumber( IsoData, NCRet1[2], NCRet1[3] );

# If image of current 3-cycle equals the last cycle used to search for collisions, we incorrectly find
# a collision with the first cycle due to shifting. Catch this:
  if ImTCNum[1] = 1 and not AnBB_Equals( ImageData[6], IsoData[3][1] )
	and not AnBB_IsOne( ImageData[6] * IsoData[3][1] ) then
   ImTCNum[1] := QuoInt( Degree, 3 );
  fi;
# Check whether image 3-cycle moves the missing point:
  if IsEvenInt( Degree ) and Degree mod 3 = 0 and ImTCNum[1] = QuoInt( Degree, 3 ) then
   TmpElement := NCRet1[1] ^ ( IsoData[2][1] ^ -1 );
   Missing := not AnBB_Equals( TmpElement, ImageData[6] ) and not AnBB_IsOne( TmpElement * ImageData[6] );
  else
   Missing := false;
  fi;

# Check and set information about available image points:
  if ImageData[9][ ImTCNum[1] ] < 3 then return fail; fi;
  ImageData[9][ ImTCNum[1] ] := 0;

# Initialise data for fixed point algorithm:
  if ImTCNum[1] <> ImageData[7] then
   MapElement[1] := TripleOnePointBackShift ^ ( ImTCNum[1] - ImageData[7] );
   FPTestElement := EvalElement * MapElement[1];
  else
   FPTestElement := EvalElement;
  fi;
  FPData[8] := ImageData[3] ^ FPTestElement;
  FPData[7] := ImageData[2] ^ FPTestElement;
  FPData[6] := ImageData[1] ^ FPTestElement;
  i := 1;
  while i < 6 do
   FPData[i] := ImageData[i];
   i := i + 1;
  od;
  if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then

# We know the first image point:
   if ImTCNum[1] > ImageData[7] then
    ImagePoint[1] := 3*ImTCNum[1];
   else
    ImagePoint[1] := 3*ImTCNum[1] - 2;
   fi;
   Tries := 1;

  else # if fixed point
# Check second point of image 3-cycle:

   if ImTCNum[1] > ImageData[7] then
    FPTestElement := FPTestElement * SingleOnePointShift;
   elif ImTCNum[1] < ImageData[7] then
    FPTestElement := FPTestElement * SingleOnePointBackShift;
   else
    FPTestElement := FPTestElement * InvCurrTC;
   fi;
   FPData[8] := ImageData[3] ^ FPTestElement;
   FPData[7] := ImageData[2] ^ FPTestElement;
   FPData[6] := ImageData[1] ^ FPTestElement;

   if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
# We know the first image point:
    ImagePoint[1] := 3*ImTCNum[1] - 1;
    Tries := 2;
   else
# We know the first image point unless the image cycle moves the missing point:
    if not Missing then
     if ImTCNum[1] > ImageData[7] then
      ImagePoint[1] := 3*ImTCNum[1] - 2;
     else
      ImagePoint[1] := 3*ImTCNum[1];
     fi;
     Tries := 3;
    else
# Check the third point:

     FPTestElement := FPTestElement * SingleOnePointShift;
     FPData[8] := ImageData[3] ^ FPTestElement;
     FPData[7] := ImageData[2] ^ FPTestElement;
     FPData[6] := ImageData[1] ^ FPTestElement;

     if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
# We know the first image point:
      ImagePoint[1] := 3*ImTCNum[1] - 2;
      Tries := 3;
     else
# We know the first image point:
      ImagePoint[1] := Degree;
      Tries := 1;
     fi;
    fi;
   fi;

  fi; # if fixed point

# Now check second image point. Get next cycles:
  ImageData[1] := ImageData[2];
  ImageData[2] := ImageData[3];
  ImageData[3] := ImageData[4];
  ImageData[4] := ImageData[5];
  ImageData[5] := ImageData[5] ^ IsoData[7];
  ShiftedIMCycles := ShiftedIMCycles + 1;
  i := 1;
  while i < 6 do
   FPData[i] := ImageData[i];
   i := i + 1;
  od;

  if Tries = 1 then
# Check second point of image 3-cycle:

   if ImTCNum[1] > ImageData[7] then
    FPTestElement := EvalElement * ( MapElement[1] * SingleOnePointShift ) ^ ImageData[8];
   elif ImTCNum[1] < ImageData[7] then
    FPTestElement := EvalElement * ( MapElement[1] * SingleOnePointBackShift ) ^ ImageData[8];
   else
    FPTestElement := EvalElement;
   fi;
   FPData[8] := ImageData[3] ^ FPTestElement;
   FPData[7] := ImageData[2] ^ FPTestElement;
   FPData[6] := ImageData[1] ^ FPTestElement;

   if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then

# We know all image points:
    ImagePoint[2] := 3*ImTCNum[1] - 1;
    if ImTCNum[1] > ImageData[7] then
     ImagePoint[3] := 3*ImTCNum[1] - 2;
    else
     ImagePoint[3] := 3*ImTCNum[1];
    fi;

   else # if fixed point

# We know all image points unless the image cycle moves the missing point:
    if not Missing then
     ImagePoint[3] := 3*ImTCNum[1] - 1;
     if ImTCNum[1] > ImageData[7] then
      ImagePoint[2] := 3*ImTCNum[1] - 2;
     else
      ImagePoint[2] := 3*ImTCNum[1];
     fi;
    else
# Check third point of image 3-cycle:

     FPTestElement := FPTestElement * SingleOnePointShift ^ ImageData[8];
     FPData[8] := ImageData[3] ^ FPTestElement;
     FPData[7] := ImageData[2] ^ FPTestElement;
     FPData[6] := ImageData[1] ^ FPTestElement;

     if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
      ImagePoint[2] := 3*ImTCNum[1] - 2;
      ImagePoint[3] := 3*ImTCNum[1] - 1;
     else
      ImagePoint[2] := 3*ImTCNum[1] - 1;
      ImagePoint[3] := 3*ImTCNum[1] - 2;
     fi;

    fi;

   fi; # if fixed point

  else # if Tries = 1

   if ImTCNum[1] <> ImageData[7] then
    FPTestElement := EvalElement * MapElement[1] ^ ImageData[8];
   else
    FPTestElement := EvalElement * ImageData[8];
   fi;
   FPData[8] := ImageData[3] ^ FPTestElement;
   FPData[7] := ImageData[2] ^ FPTestElement;
   FPData[6] := ImageData[1] ^ FPTestElement;

   if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then

# We know all image points:
    if ImTCNum[1] > ImageData[7] then
     ImagePoint[2] := 3*ImTCNum[1];
     if Tries = 2 then
      ImagePoint[3] := 3*ImTCNum[1] - 2;
     else
      ImagePoint[3] := 3*ImTCNum[1] - 1;
     fi;
    else
     ImagePoint[2] := 3*ImTCNum[1] - 2;
     if Tries = 2 then
      ImagePoint[3] := 3*ImTCNum[1];
     else
      ImagePoint[3] := 3*ImTCNum[1] - 1;
     fi;
    fi;

   else # if fixed point

# We know all image points unless the image cycle moves the missing point:
    if not Missing then
     if ImTCNum[1] > ImageData[7] then
      ImagePoint[3] := 3*ImTCNum[1];
      if Tries = 2 then
       ImagePoint[2] := 3*ImTCNum[1] - 2;
      else
       ImagePoint[2] := 3*ImTCNum[1] - 1;
      fi;
     else
      ImagePoint[3] := 3*ImTCNum[1] - 2;
      if Tries = 2 then
       ImagePoint[2] := 3*ImTCNum[1];
      else
       ImagePoint[2] := 3*ImTCNum[1] - 1;
      fi;
     fi;
    elif Tries = 2 then
# Check third point.

     FPTestElement := EvalElement * ( MapElement[1] * SingleOnePointShift^2 ) ^ ImageData[8];
     FPData[8] := ImageData[3] ^ FPTestElement;
     FPData[7] := ImageData[2] ^ FPTestElement;
     FPData[6] := ImageData[1] ^ FPTestElement;

     if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
      ImagePoint[2] := 3*ImTCNum[1] - 2;
      ImagePoint[3] := Degree;
     else
      ImagePoint[2] := Degree;
      ImagePoint[3] := 3*ImTCNum[1] - 2;
     fi;

    else
# Check second point.

     FPTestElement := EvalElement * ( MapElement[1] * SingleOnePointShift ) ^ ImageData[8];
     FPData[8] := ImageData[3] ^ FPTestElement;
     FPData[7] := ImageData[2] ^ FPTestElement;
     FPData[6] := ImageData[1] ^ FPTestElement;

     if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
      ImagePoint[2] := 3*ImTCNum[1] - 1;
      ImagePoint[3] := Degree;
     else
      ImagePoint[2] := Degree;
      ImagePoint[3] := 3*ImTCNum[1] - 1;
     fi;

    fi;

   fi; # if fixed point

  fi; # if Tries = 1

 else # if commuting with check cycle

# There are unshifted cycles not commuting with current 3-cycle.
# Find non-commuting 3-cycle and determine intersection of supports:
  NCRet1 := AnBB_NonCommThreeCycle( IsoData, ImageData[6], CancelData );
  FirstCommonPoints := AnBB_NonCommTCPoints( ImageData[6], NCRet1[1] );
  ImTCNum[1] := AnBB_CycleNumber( IsoData, NCRet1[2], NCRet1[3] );

# Set behavioural variables for non-comm alg:
  CancelData[1] := true;
  CancelData[3] := NCRet1[2];
  CancelData[4] := NCRet1[3];
  CancelData[5] := NCRet1[1]^2;

# Find second non-commuting 3-cycle:
  NCRet2 := AnBB_NonCommThreeCycle( IsoData, ImageData[6], CancelData );
  SecondCommonPoints := AnBB_NonCommTCPoints( ImageData[6], NCRet2[1] );
  ImTCNum[2] := AnBB_CycleNumber( IsoData, NCRet2[2], NCRet2[3] );

  if FirstCommonPoints = 1 and SecondCommonPoints = 1 then
# Need a third non-commuting 3-cycle, set behavioural variables:
   CancelData[7] := NCRet2[1]^2;
   CancelData[2] := true;
   CancelData[6] := NCRet2[3];
   CancelData[5] := CancelData[7] * CancelData[5];
   if NCRet2[2] > CancelData[3] then
    CancelData[1] := false;
    CancelData[3] := NCRet2[2];
   else
    CancelData[1] := true;
   fi;

# Find cycle:
   NCRet3 := AnBB_NonCommThreeCycle( IsoData, ImageData[6], CancelData );
   ImTCNum[3] := AnBB_CycleNumber( IsoData, NCRet3[2], NCRet3[3] );

# 1-1-1 case.
   if ImageData[9][ ImTCNum[1] ] = 0 or ImageData[9][ ImTCNum[2] ] = 0 then return fail; fi;

  elif FirstCommonPoints = 2 then

# 2-1 or 2-missing case.
   if ImageData[9][ ImTCNum[1] ] < 2 then return fail; fi;

  else

# 1-2 or 1-1-missing case.
   if ImageData[9][ ImTCNum[1] ] = 0 then return fail; fi;

  fi;

# In case of even degree, check whether image 3-cycle moves missing point:
  Missing := false;
  if IsEvenInt( Degree ) and (
	( FirstCommonPoints = 1 and SecondCommonPoints = 1 and 3*ImTCNum[3] > IsoData[5] ) or
	3*ImTCNum[2] > IsoData[5] ) then
   FPTestElement := EvalElement * InvThreeCycle * IsoData[2][1] ^ ( ImageData[7] - 1 );
   FPData[8] := ImageData[3] ^ FPTestElement;
   FPData[7] := ImageData[2] ^ FPTestElement;
   FPData[6] := ImageData[1] ^ FPTestElement;
   i := 1;
   while i < 6 do
    FPData[i] := ImageData[i];
    i := i + 1;
   od;
   if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
# First point of image 3-cycle mapped to missing point.
    Missing := true;
    FirstPoint := 3;
    ImagePoint[1] := Degree;
   else
    FPTestElement := IsoData[7] * FPTestElement;
    FPData[8] := FPData[3] ^ FPTestElement;
    FPData[7] := FPData[2] ^ FPTestElement;
    FPData[6] := FPData[1] ^ FPTestElement;
    if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
# Second point of image 3-cycle mapped to missing point.
     Missing := true;
     SecondPoint := 3;
     ImagePoint[2] := Degree;
    else
     FPTestElement := IsoData[7] * FPTestElement;
     FPData[8] := FPData[3] ^ FPTestElement;
     FPData[7] := FPData[2] ^ FPTestElement;
     FPData[6] := FPData[1] ^ FPTestElement;
     if AnBB_IsFixedPoint( FPTestElement, IsoData[7], IsoData[5], FPData ) then
# Third point of image 3-cycle mapped to missing point.
      Missing := true;
      ThirdPoint := 3;
      ImagePoint[3] := Degree;
     fi;
    fi;
   fi;
  fi;

  if Missing then ImTCNum[3] := QuoInt(IsoData[5],3)+2; fi;

  if FirstCommonPoints = 1 and SecondCommonPoints = 1 then
# 1-1-1 case.
   if not Missing and ImageData[9][ ImTCNum[3] ] = 0 then return fail; fi;

# If overlap is possible, edit last non-commuting 3-cycle:
   if not Missing and ImTCNum[1] = 1 and 3*ImTCNum[3] > IsoData[5] then
    if IsoData[5] mod 3 = 0 then
     TmpElement := NCRet3[1];
    elif IsoData[5] mod 3 = 2 then
     if ImTCNum[2] = ImTCNum[3] - 1 then
      TmpElement := NCRet3[1] ^ ( NCRet1[1] ^ 2 * NCRet1[1] ^ IsoData[7] );
     else
      TmpElement := NCRet3[1] ^ IsoData[8];
     fi;
    else
     if ImTCNum[2] = ImTCNum[3] - 1 then
      TmpElement := NCRet1[1] ^ ( IsoData[2][1] * NCRet1[1] ^ IsoData[7] * NCRet3[1] );
     else
      TmpElement := NCRet3[1] ^ ( IsoData[8] ^ 2 );
     fi;
    fi;
   else
    TmpElement := NCRet3[1];
   fi;
   if Missing and ImTCNum[1] = 1 and 3*ImTCNum[2] > IsoData[5] then
    if IsoData[5] mod 3 = 0 then
     SecCheck := NCRet2[1];
    elif IsoData[5] mod 3 = 2 then
     SecCheck := NCRet2[1] ^ IsoData[8];
    else
     SecCheck := NCRet2[1] ^ ( IsoData[8] ^ 2 );
    fi;
   else
    SecCheck := NCRet2[1];
   fi;


# Identify which point collides with which cycle in the generic case:
   PrevImTC := ImageData[2] ^ EvalElement;
   NextImTC := PrevImTC ^ ImageData[6];
   if not Missing or not IsBound( FirstPoint ) then
    if AnBB_Equals( NextImTC * NCRet1[1], NCRet1[1] * NextImTC ) then
# First point of image 3-cycle moved by first non-comm 3-cycle.
     FirstPoint := 1;
    elif AnBB_Equals( NextImTC * SecCheck, SecCheck * NextImTC ) then
# First point of image 3-cycle moved by second non-comm 3-cycle.
     FirstPoint := 2;
    elif not Missing and AnBB_Equals( NextImTC * TmpElement, TmpElement * NextImTC ) then
# First point of image 3-cycle moved by third non-comm 3-cycle.
     FirstPoint := 3;
    else
# We don't know anything about the first point.
     FirstPoint := 0;
    fi;
   fi;

   if not Missing or not IsBound( ThirdPoint ) then
    if FirstPoint <> 1 and AnBB_Equals( PrevImTC * NCRet1[1], NCRet1[1] * PrevImTC ) then
# Third point of image 3-cycle moved by first non-comm 3-cycle.
     ThirdPoint := 1;
    elif FirstPoint <> 2 and AnBB_Equals( PrevImTC * SecCheck, SecCheck * PrevImTC ) then
# Third point of image 3-cycle moved by second non-comm 3-cycle.
     ThirdPoint := 2;
    elif not Missing and FirstPoint <> 3 and AnBB_Equals( PrevImTC * TmpElement, TmpElement * PrevImTC ) then
# Third point of image 3-cycle moved by third non-comm 3-cycle.
     ThirdPoint := 3;
    else
# We don't know anything about the third point.
     ThirdPoint := 0;
    fi;
   fi;

   if FirstPoint <> 0 and ThirdPoint <> 0 then
# We know everything!
    SecondPoint := Difference( [1,2,3], [FirstPoint,ThirdPoint] )[1];
   elif not Missing or not IsBound( SecondPoint ) then
    EditImTC := NextImTC ^ ImageData[6];
    if FirstPoint <> 1 and ThirdPoint <> 1 and AnBB_Equals( EditImTC * NCRet1[1], NCRet1[1] * EditImTC ) then
# Second point of image 3-cycle moved by first non-comm 3-cycle.
     SecondPoint := 1;
    elif FirstPoint <> 2 and ThirdPoint <> 2 and AnBB_Equals( EditImTC * SecCheck, SecCheck * EditImTC ) then
# Second point of image 3-cycle moved by second non-comm 3-cycle.
     SecondPoint := 2;
    elif FirstPoint <> 3 and ThirdPoint <> 3 and AnBB_Equals( EditImTC * TmpElement, TmpElement * EditImTC ) then
# Second point of image 3-cycle moved by third non-comm 3-cycle.
     SecondPoint := 3;
    else
# We don't know anything about the second point, this is not supposed to happen on correct input.
     return fail;
    fi;
   fi;

# If necessary, set remaining point:
   if FirstPoint = 0 then
    FirstPoint := Difference( [1,2,3], [ThirdPoint,SecondPoint] )[1];
   elif ThirdPoint = 0 then
    ThirdPoint := Difference( [1,2,3], [FirstPoint,SecondPoint] )[1];
   fi;

# Compute necessary mapping elements:
   if ImTCNum[1] <> ImageData[7] and ImageData[9][ ImTCNum[1] ] > 1 then
    MapElement[1] := TripleOnePointBackShift ^ ( ImTCNum[1] - ImageData[7] );
   fi;
   if ImTCNum[2] <> ImageData[7] and ImageData[9][ ImTCNum[2] ] > 1 then
    MapElement[2] := TripleOnePointBackShift ^ ( ImTCNum[2] - ImageData[7] );
   fi;
   if not Missing and ImTCNum[3] <> ImageData[7] and ImageData[9][ ImTCNum[3] ] > 1 then
    MapElement[3] := TripleOnePointBackShift ^ ( ImTCNum[3] - ImageData[7] );
   fi;

  else # if 1-1-1 case

# 2-1 / 1-2 case.
# Find cycles containing points:
   if FirstCommonPoints = 2 then
# 2-1 case.
    if Missing then
     if not IsBound( FirstPoint ) then FirstPoint := 1; fi;
     if not IsBound( SecondPoint ) then SecondPoint := 1; fi;
     if not IsBound( ThirdPoint ) then ThirdPoint := 1; fi;
    else
     if ImageData[9][ ImTCNum[2] ] = 0 then return fail; fi;
     PrevImTC := ImageData[1] ^ EvalElement;
     if AnBB_Equals( PrevImTC * NCRet1[1], NCRet1[1] * PrevImTC ) then
      SecondPoint := 1;
      ThirdPoint := 1;
      FirstPoint := 2;
     else
      EditImTC := PrevImTC ^ ImageData[6];
      if AnBB_Equals( EditImTC * NCRet1[1], NCRet1[1] * EditImTC ) then
       FirstPoint := 1;
       ThirdPoint := 1;
       SecondPoint := 2;
      else
       EditImTC := EditImTC ^ ImageData[6];
       if AnBB_Equals( EditImTC * NCRet1[1], NCRet1[1] * EditImTC ) then
        FirstPoint := 1;
        SecondPoint := 1;
        ThirdPoint := 2;
       else
        NextImTC := ImageData[5] ^ EvalElement;
        if AnBB_Equals( NextImTC * NCRet1[1], NCRet1[1] * NextImTC ) then
         FirstPoint := 1;
         SecondPoint := 1;
         ThirdPoint := 2;
        else
         EditImTC := NextImTC ^ ImageData[6];
         if AnBB_Equals( EditImTC * NCRet1[1], NCRet1[1] * EditImTC ) then
          SecondPoint := 1;
          ThirdPoint := 1;
          FirstPoint := 2;
         else
          FirstPoint := 1;
          ThirdPoint := 1;
          SecondPoint := 2;
         fi;
        fi;
       fi;
      fi;
     fi;
    fi;
   else
# 1-2 or 1-1-missing case.
    if Missing and ImageData[9][ ImTCNum[2] ] = 0 then return fail; fi;
    if not Missing and ImageData[9][ ImTCNum[2] ] < 2 then return fail; fi;
    PrevImTC := ImageData[2] ^ EvalElement;
    if AnBB_Equals( PrevImTC * NCRet1[1], NCRet1[1] * PrevImTC ) then
     ThirdPoint := 1;
    else
     EditImTC := PrevImTC ^ ImageData[6];
     if AnBB_Equals( EditImTC * NCRet1[1], NCRet1[1] * EditImTC ) then
      FirstPoint := 1;
     else
      EditImTC := EditImTC ^ ImageData[6];
      if AnBB_Equals( EditImTC * NCRet1[1], NCRet1[1] * EditImTC ) then
       SecondPoint := 1;
      else
       NextImTC := ImageData[4] ^ EvalElement;
       if AnBB_Equals( NextImTC * NCRet1[1], NCRet1[1] * NextImTC ) then
        FirstPoint := 1;
       else
        NextImTC := NextImTC ^ ImageData[6];
        if AnBB_Equals( NextImTC * NCRet1[1], NCRet1[1] * NextImTC ) then
         SecondPoint := 1;
        else
         EditImTC := NextImTC ^ ImageData[6];
         if AnBB_Equals( EditImTC * NCRet1[1], NCRet1[1] * EditImTC ) then
          ThirdPoint := 1;
         else
          EditImTC := ImageData[5] ^ ( EvalElement * NextImTC );
          if AnBB_Equals( EditImTC * NCRet1[1], NCRet1[1] * EditImTC ) then
           SecondPoint := 1;
          else
           EditImTC := EditImTC ^ ImageData[6];
           if AnBB_Equals( EditImTC * NCRet1[1], NCRet1[1] * EditImTC ) then
            ThirdPoint := 1;
           else
            FirstPoint := 1;
           fi;
          fi;
         fi;
        fi;
       fi;
      fi;
     fi;
    fi;
    if not IsBound( FirstPoint ) then FirstPoint := 2; fi;
    if not IsBound( SecondPoint ) then SecondPoint := 2; fi;
    if not IsBound( ThirdPoint ) then ThirdPoint := 2; fi;
   fi;

# Compute mapping elements:
   if ImTCNum[1] <> ImageData[7] and ImageData[9][ ImTCNum[1] ] > 1 then
    MapElement[1] := TripleOnePointBackShift ^ ( ImTCNum[1] - ImageData[7] );
   fi;
   if ( not Missing or FirstCommonPoints = 1 ) and ImTCNum[2] <> ImageData[7] and ImageData[9][ ImTCNum[2] ] > 1 then
    MapElement[2] := TripleOnePointBackShift ^ ( ImTCNum[2] - ImageData[7] );
   fi;

  fi; # if 1-1-1 case

# Determine image of first point:

   if Missing and FirstPoint = 3 then
# Image point already set.
# Generic case:
   elif ImTCNum[FirstPoint] > ImageData[7] then
    ImagePoint[1] := AnBB_FindSinglePoint( ImageData, IsoData, ImTCNum[FirstPoint], EvalElement, SingleOnePointShift, MapElement[FirstPoint], InvCurrTC );
   else
    ImagePoint[1] := AnBB_FindSinglePoint( ImageData, IsoData, ImTCNum[FirstPoint], EvalElement, SingleOnePointBackShift, MapElement[FirstPoint], InvCurrTC );
   fi;

   ImageData[9][ ImTCNum[FirstPoint] ] := ImageData[9][ ImTCNum[FirstPoint] ] - 1;
# First image point known.
# Determine image of second point:

   if Missing and SecondPoint = 3 then
# Image point already set.
# Generic case:
   elif ImTCNum[SecondPoint] > ImageData[7] then
    ImagePoint[2] := AnBB_FindSinglePoint( ImageData, IsoData, ImTCNum[SecondPoint], ImageData[8]*EvalElement, SingleOnePointShift, MapElement[SecondPoint], InvCurrTC );
   else
    ImagePoint[2] := AnBB_FindSinglePoint( ImageData, IsoData, ImTCNum[SecondPoint], ImageData[8]*EvalElement, SingleOnePointBackShift, MapElement[SecondPoint], InvCurrTC );
   fi;

   ImageData[9][ ImTCNum[SecondPoint] ] := ImageData[9][ ImTCNum[SecondPoint] ] - 1;
# Second image point known.
# Determine image of third point:

   if Missing and ThirdPoint = 3 then
# Image point already set.
# Generic case:
   elif ImTCNum[ThirdPoint] > ImageData[7] then
    ImagePoint[3] := AnBB_FindSinglePoint( ImageData, IsoData, ImTCNum[ThirdPoint], InvCurrTC*EvalElement, SingleOnePointShift, MapElement[ThirdPoint], InvCurrTC );
   else
    ImagePoint[3] := AnBB_FindSinglePoint( ImageData, IsoData, ImTCNum[ThirdPoint], InvCurrTC*EvalElement, SingleOnePointBackShift, MapElement[ThirdPoint], InvCurrTC );
   fi;

   ImageData[9][ ImTCNum[ThirdPoint] ] := ImageData[9][ ImTCNum[ThirdPoint] ] - 1;
# Third image point known.

 fi; # if current 3-cycle commutes with check cycle

 while ShiftedIMCycles < 3 do
  ImageData[1] := ImageData[2];
  ImageData[2] := ImageData[3];
  ImageData[3] := ImageData[4];
  ImageData[4] := ImageData[5];
  ImageData[5] := ImageData[5] ^ IsoData[7];
  ShiftedIMCycles := ShiftedIMCycles + 1;
 od;

 return ImagePoint;
end;	# function AnBB_PartialImageAn



########################################################################
##
## The function AnBB_EvaluateIso finds the image of GpElt under the
## homomorphism defined by the standard generators.
##
AnBB_EvaluateIso := function( GpElt, IsoData, Degree, InvThreeCycle )
 local ImagePointList, ImageData, Tmp, FullTCNum, Ret, FPData, RemPts, FPTestElt, MapElt;

# Initialise variables:
 FullTCNum := QuoInt(Degree,3);
 ImagePointList := [];
 ImagePointList[Degree] := 0; # allocate memory
 ImageData := [];
 ImageData[10] := []; # allocate memory
 ImageData[9] := List( [1..FullTCNum], i -> 3 );
 Tmp := Degree mod 3;
 if Tmp > 0 then
  Add( ImageData[9], Tmp );
 fi;
 if IsEvenInt(Degree) then ImageData[9][QuoInt(IsoData[5],3)+2] := 1;; fi;
 ImageData[10] := List( [1..FullTCNum], i -> [true,true,true] );;
 if Tmp = 1 then
  Add( ImageData[10], [true,false,false] );
 elif Tmp = 2 then
  Add( ImageData[10], [true,true,false] );
 fi;

 ImageData[3] := IsoData[3][1];
 ImageData[2] := ImageData[3] ^ IsoData[8];
 ImageData[1] := ImageData[2] ^ IsoData[8];
 ImageData[4] := ImageData[3] ^ IsoData[7];
 ImageData[5] := ImageData[4] ^ IsoData[7];

# Go through 3-cycles and determine images of their moved points:
 FullTCNum := QuoInt( IsoData[5], 3 );
 ImageData[7] := 1;

 while ImageData[7] <= FullTCNum do
 
  ImageData[8] := ImageData[3];
  ImageData[6] := ImageData[3] ^ GpElt;

  Ret := AnBB_PartialImageAn( ImageData, IsoData, GpElt, Degree, InvThreeCycle );
  if Ret = fail then return fail; fi;

  if IsOddInt( Degree ) then
   ImagePointList[3*ImageData[7]-2] := Ret[1];
   ImagePointList[3*ImageData[7]-1] := Ret[2];
   ImagePointList[3*ImageData[7]] := Ret[3];
  else
   ImagePointList[3*ImageData[7]-1] := Ret[1];
   ImagePointList[3*ImageData[7]] := Ret[2];
   ImagePointList[3*ImageData[7]+1] := Ret[3];
  fi;

  ImageData[7] := ImageData[7] + 1;
 od;

# Find images of the last few points:
 Tmp := Degree mod 6;
 FPData := List( [1..5], i -> ImageData[i] );
 RemPts := Difference( [1..Degree], ImagePointList );

 if Tmp = 0 then
# Three points left over.

  MapElt := IsoData[7] ^ ( Degree - 2 - RemPts[1] );
  FPTestElt := GpElt * MapElt;
  FPData[8] := FPData[3] ^ FPTestElt;
  FPData[7] := FPData[2] ^ FPTestElt;
  FPData[6] := FPData[1] ^ FPTestElt;
  if AnBB_IsFixedPoint( FPTestElt, IsoData[7], IsoData[5], FPData ) then
   ImagePointList[ Degree - 1 ] := RemPts[1];

   MapElt := IsoData[7] ^ ( Degree - 1 - RemPts[2] );
   FPTestElt := GpElt * MapElt;
   FPData[1] := FPData[2];
   FPData[2] := FPData[3];
   FPData[3] := FPData[4];
   FPData[4] := FPData[5];
   FPData[5] := FPData[5] ^ IsoData[7];
   FPData[8] := FPData[3] ^ FPTestElt;
   FPData[7] := FPData[2] ^ FPTestElt;
   FPData[6] := FPData[1] ^ FPTestElt;
   if AnBB_IsFixedPoint( FPTestElt, IsoData[7], IsoData[5], FPData ) then
    ImagePointList[ Degree ] := RemPts[2];
    ImagePointList[ 1 ] := RemPts[3];
   else
    ImagePointList[ Degree ] := RemPts[3];
    ImagePointList[ 1 ] := RemPts[2];
   fi;

  else

   MapElt := IsoData[7] ^ ( Degree - 2 - RemPts[2] );
   FPTestElt := GpElt * MapElt;
   FPData[8] := FPData[3] ^ FPTestElt;
   FPData[7] := FPData[2] ^ FPTestElt;
   FPData[6] := FPData[1] ^ FPTestElt;
   if AnBB_IsFixedPoint( FPTestElt, IsoData[7], IsoData[5], FPData ) then
    ImagePointList[ Degree - 1 ] := RemPts[2];
   else
    ImagePointList[ Degree - 1 ] := RemPts[3];
   fi;

   MapElt := IsoData[7] ^ ( Degree - 1 - RemPts[1] );
   FPTestElt := GpElt * MapElt;
   FPData[1] := FPData[2];
   FPData[2] := FPData[3];
   FPData[3] := FPData[4];
   FPData[4] := FPData[5];
   FPData[5] := FPData[5] ^ IsoData[7];
   FPData[8] := FPData[3] ^ FPTestElt;
   FPData[7] := FPData[2] ^ FPTestElt;
   FPData[6] := FPData[1] ^ FPTestElt;

   if AnBB_IsFixedPoint( FPTestElt, IsoData[7], IsoData[5], FPData ) then
    ImagePointList[ Degree ] := RemPts[1];
    if ImagePointList[ Degree - 1 ] = RemPts[2] then
     ImagePointList[1] := RemPts[3];
    else
     ImagePointList[1] := RemPts[2];
    fi;
   else
    ImagePointList[1] := RemPts[1];
    if ImagePointList[ Degree - 1 ] = RemPts[2] then
     ImagePointList[ Degree ] := RemPts[3];
    else
     ImagePointList[ Degree ] := RemPts[2];
    fi;
   fi;

  fi;

 elif Tmp = 1 then
# Only one point left over:
  ImagePointList[Degree] := RemPts[1];
 elif Tmp = 2 then
# Two points left over.

  MapElt := IsoData[7] ^ ( Degree - 1 - RemPts[1] );
  FPTestElt := GpElt * MapElt;
  FPData[8] := FPData[3] ^ FPTestElt;
  FPData[7] := FPData[2] ^ FPTestElt;
  FPData[6] := FPData[1] ^ FPTestElt;
  if AnBB_IsFixedPoint( FPTestElt, IsoData[7], IsoData[5], FPData ) then
   ImagePointList[ Degree ] := RemPts[1];
   ImagePointList[ 1 ] := RemPts[2];
  else
   ImagePointList[ Degree ] := RemPts[2];
   ImagePointList[ 1 ] := RemPts[1];
  fi;

 elif Tmp = 3 then
# No point left over.
 elif Tmp = 4 then
# Only one point left over:
  ImagePointList[1] := RemPts[1];
 elif Tmp = 5 then
# Two points left over.

  MapElt := IsoData[7] ^ ( Degree - 1 - RemPts[1] );
  FPTestElt := GpElt * MapElt;
  FPData[8] := FPData[3] ^ FPTestElt;
  FPData[7] := FPData[2] ^ FPTestElt;
  FPData[6] := FPData[1] ^ FPTestElt;
  if AnBB_IsFixedPoint( FPTestElt, IsoData[7], IsoData[5], FPData ) then
   ImagePointList[ Degree - 1 ] := RemPts[1];
   ImagePointList[ Degree ] := RemPts[2];
  else
   ImagePointList[ Degree - 1 ] := RemPts[2];
   ImagePointList[ Degree ] := RemPts[1];
  fi;

 fi;

# In case of even degree, adjust ImagePointList:
 if IsEvenInt( Degree ) then
  Tmp := ImagePointList[1];
  ImagePointList[1] := ImagePointList[2];
  ImagePointList[2] := Tmp;
  ImagePointList := List( ImagePointList, i -> i+1 );
  Tmp := Position( ImagePointList, 2 );
  if Tmp = fail then return fail; fi;
  ImagePointList[Tmp] := 1;
  Tmp := Position( ImagePointList, Degree+1 );
  if Tmp = fail then return fail; fi;
  ImagePointList[Tmp] := 2;
 fi;

 return PermList( ImagePointList );
end;	# function AnBB_EvaluateIso



########################################################################
##
## The function AnBB_SLPForAn computes a straight line program reaching
## the permutation Perm from the standard generators of the alternating
## group of degree Degree.
##
AnBB_SLPForAn := function( Perm, Degree )
 local CyclesOfPerm, CycleInitPts, CurrCycle, NewCyc, Res, InitPt, NextTrsp, CycleSLP, k, j, NextTau, NextSigma;

 if IsOne( Perm ) then return StraightLineProgram( [ [1,0] ], 2 ); fi;

 CyclesOfPerm := Filtered( Cycles( Perm, [ 1 .. Degree ] ), c -> Length(c) > 1 );
 CycleInitPts := List( CyclesOfPerm, Minimum );

# Make *sure* that each cycle begins with its minimal point.
# This should not actually be called.
 if ForAny( CyclesOfPerm, c -> c[1] <> Minimum(c) ) then
  for CurrCycle in CyclesOfPerm do
   InitPt := Minimum( CurrCycle );
   NewCyc := [ InitPt ];
   NewCyc[ Length(CurrCycle) ] := 0; # allocate memory
   for k in [ 2 .. Length(CurrCycle) ] do
    NewCyc[k] := NewCyc[k-1]^Perm;
   od;
   CyclesOfPerm[ Position( CyclesOfPerm, CurrCycle ) ] := NewCyc;
  od;
 fi;

# Res will be a straight line program from tau_1, sigma_1.
# We update cycle product, tau_i+1, sigma_i+1 and then overwrite the updates into positions 1,2,3.
 Res := [ [1,0], [3,1], [1,1], [2,1], [[4,1],1], [[5,1],2], [[6,1],3] ];
 InitPt := 1;

# We keep track of which transposition of Perm we must compute next.
 NextTrsp := 1;

 repeat
  if InitPt in CycleInitPts then

# CurrCycle is the cycle of Perm beginning with InitPt.
   CurrCycle := CyclesOfPerm[ Position( CycleInitPts, InitPt ) ];
# CycleSLP is the SLP for CurrCycle from tau_i and sigma_i.
# We carry forward the cycle product computed so far.
   CycleSLP := [ 1, 1 ];

   for k in [ 2 .. Length(CurrCycle) ] do
    j := CurrCycle[k];  # so (i,j)=(CurrCycle[1],CurrCycle[k])
    if j < Degree - 1 then
# NB: if i < j < n-1 then (i,j)(n-1,n) = (n-1,n)(i,j)
     if j = InitPt + 1 then
      if IsEvenInt( Degree - InitPt ) then
       Append( CycleSLP, [ 3, InitPt + 2 - Degree, 2, 2, 3, 1, 2, 1, 3, -1, 2, 2, 3, Degree - InitPt - 2 ] );
      else
       Append( CycleSLP, [ 3, InitPt + 2 - Degree, 2, 1, 3, 1, 2, 1, 3, -1, 2, 1, 3, Degree - InitPt - 2 ] );
      fi;
     else
      if IsEvenInt( Degree - InitPt ) then
       Append( CycleSLP, [ 3, InitPt + 2 - j, 2, 1, 3, j - Degree, 2, 2, 3, 1, 2, 1, 3, -1, 2, 2, 3, Degree - j, 2, 2, 3, j - InitPt - 2 ] );
      elif IsOddInt( Degree - InitPt ) and IsEvenInt( j - InitPt - 2 ) then
       Append( CycleSLP, [ 3, InitPt + 2 - j, 2, 1, 3, j - Degree, 2, 1, 3, 1, 2, 1, 3, -1, 2, 1, 3, Degree - j, 2, 2, 3, j - InitPt - 2 ] );
      else
       Append( CycleSLP, [ 3, InitPt + 2 - j, 2, 2, 3, j - Degree, 2, 1, 3, 1, 2, 1, 3, -1, 2, 1, 3, Degree - j, 2, 1, 3, j - InitPt - 2 ] );
      fi;
     fi;
    elif ( j = Degree - 1 or j = Degree ) and InitPt < Degree - 1 then
     if ( j = Degree - 1 and IsOddInt( NextTrsp ) ) or ( j = Degree and IsEvenInt( NextTrsp ) ) then
      if IsEvenInt( Degree - InitPt ) then
       Append( CycleSLP, [ 3, InitPt + 2 - Degree, 2, 2, 3, 1, 2, 1, 3, Degree - InitPt - 3  ] );
      else
       Append( CycleSLP, [ 3, InitPt + 2 - Degree, 2, 1, 3, 1, 2, 1, 3, Degree - InitPt - 3  ] );
      fi;
     elif ( j = Degree and IsOddInt( NextTrsp ) ) or ( j = Degree - 1 and IsEvenInt( NextTrsp ) ) then
      if IsEvenInt( Degree-InitPt ) then
       Append( CycleSLP, [ 3, InitPt + 3 - Degree, 2, 2, 3, - 1, 2, 1, 3, Degree - InitPt - 2  ] );
      else
       Append( CycleSLP, [ 3, InitPt + 3 - Degree, 2, 2, 3, -1, 2, 2, 3, Degree - InitPt - 2  ] );
      fi;
     fi;
    else	# (i,j) = (n-1,n)
     Append( CycleSLP, [ ] );
    fi;

    NextTrsp := NextTrsp + 1;
   od;
    Append( Res, [ [ CycleSLP, 4 ] ] );

  else  # not (InitPt in CycleInitPts)  
# We carry forward cycle product computed so far.
   Append( Res, [ [[1,1],4] ] );
  fi;

# We update tau_i+1 and sigma_i+1.
  if IsEvenInt(Degree-InitPt) then
   NextTau   := [ 2, -1, 3, -1, 2, 1, 3, 1, 2, 1 ];
   NextSigma := [ 3, 1, 5, 1 ];
  else
   NextTau   := [ 2, -1, 3, -1, 2, 2, 3, 1, 2, 1 ];
   NextSigma := [ 3, 1, 2, 2, 5, -1 ];
  fi;

  Append( Res, [ [ NextTau, 5 ], [ NextSigma, 6 ], [[4,1],1], [[5,1],2], [[6,1],3] ]);
  InitPt := InitPt + 1;

 until InitPt > Maximum( CycleInitPts );

 Add( Res,[ [1,1],1 ] );

# Res is a straight line program with 2 input elements.
 Res := StraightLineProgramNC( Res, 2 );

 return Res;
end;	# function AnBB_SLPForAn



########################################################################
##
## The function AnBB_SLPForSn computes a straight line program reaching
## the permutation Perm from the standard generators of the symmetric
## group of degree Degree.
##
AnBB_SLPForSn := function( Perm, Degree )
 local CyclesOfPerm, CycleInitPts, CurrCycle, NewCyc, InitPt, Res, CycleSLP, k, i;

 if AnBB_IsOne( Perm ) then return StraightLineProgram( [ [1,0] ], 2 ); fi;

 CyclesOfPerm := Filtered( Cycles( Perm, [ 1 .. Degree ] ), c -> Length(c) > 1 );
 CycleInitPts := List( CyclesOfPerm, Minimum );

# Make *sure* that each cycle begins with its minimal point.
# This should not actually be called.
 if ForAny( CyclesOfPerm, c -> c[1] <> Minimum(c) ) then
  for CurrCycle in CyclesOfPerm do
   InitPt := Minimum( CurrCycle );
   NewCyc := [ InitPt ];
   NewCyc[ Length(CurrCycle) ] := 0; # allocate memory
   for k in [ 2 .. Length(CurrCycle) ] do
    NewCyc[k] := NewCyc[k-1]^Perm;
   od;
   CyclesOfPerm[ Position( CyclesOfPerm, CurrCycle ) ] := NewCyc;
  od;
 fi;

# Res will be a straight line program from tau_1, sigma_1.
# We update cycle product, tau_i+1, sigma_i+2 and then overwrite the updates into positions 1,2,3.
 Res := [ [1,0], [3,1], [1,1], [2,1,1,1], [[4,1],1], [[5,1],2], [[6,1],3] ];
 InitPt := 1;
 repeat
  if InitPt in CycleInitPts then
# CurrCycle is the cycle of Perm beginning with InitPt.
   CurrCycle := CyclesOfPerm[ Position( CycleInitPts, InitPt ) ];
# CycleSLP is the SLP for CurrCycle from tau_i and sigma_i+1.
   CycleSLP := [ 1, 1, 3, 1 + CurrCycle[1] - CurrCycle[2] ];
   for k in [ 2 .. Length( CurrCycle ) - 1 ] do
    Append( CycleSLP, [ 2, 1, 3, CurrCycle[k] - CurrCycle[k+1] ] );
   od;
   Append( CycleSLP, [ 2, 1, 3, CurrCycle[Length(CurrCycle)] - CurrCycle[1] - 1 ] );
   Add( Res, [ CycleSLP, 4 ] );
  else			# We carry forward cycle product computed so far.
   Add( Res, [ [1,1], 4] );
  fi;
# We update tau_i+1 and sigma_i+2.
  Append( Res, [ [ [2,1,3,-1,2,1,3,1,2,1], 5 ], [ [3,1,2,1,3,-1,2,1,3,1,2,1], 6 ], [ [4,1], 1 ], [ [5,1], 2 ], [ [6,1], 3 ] ] );
  InitPt := InitPt + 1;
 until InitPt > Maximum( CycleInitPts );

 Add( Res, [ [1,1], 1 ] );

# Res is a straight line program with 2 input elements.
 Res := StraightLineProgramNC( Res, 2 );

 return Res;
end;	# function AnBB_SLPForSn



########################################################################
##
## The function AnBB_ComputeIsomorphism tries to build a constructive isomorphism from
## AnBB_Vars[1] to An or Sn where the degree n equals AnBB_Vars[17] and
## AnBB_Vars[9], AnBB_Vars[16] are assumed to be standard generators
## for AnBB_Vars[1].
## If it returns fail, the construction failed.
## Otherwise it returns the constructive isomorphism.
##
AnBB_ComputeIsomorphism := function( AnBB_Vars )
 local OldGenerator, ImageOfGen, SLP, GenPreImage;

# Check An presentation:
 if not AnBB_AnPresentationSatisfied( AnBB_Vars ) then return fail; fi;

# Compute elements to evaluate the isomorphism:
 AnBB_InitialiseIso( AnBB_Vars );
 
# Try to express each old generator in putative standard generators:
 for OldGenerator in GeneratorsOfGroup( AnBB_Vars[1] ) do

  ImageOfGen := AnBB_EvaluateIso( OldGenerator, AnBB_Vars[23], AnBB_Vars[17], AnBB_Vars[10] );
  if ImageOfGen = fail then return fail; fi;

  if SignPerm( ImageOfGen ) = -1 then
# Found an odd permutation, so the group cannot be An.
# Try to replace our generating elements by standard generators for Sn.

   SLP := AnBB_SLPForAn( (1,2) * ImageOfGen, AnBB_Vars[17] );
   GenPreImage := ResultOfStraightLineProgram( SLP, [ AnBB_Vars[9], AnBB_Vars[16] ] );

# Compute a transposition:
   AnBB_Vars[18] := GenPreImage * OldGenerator^-1;

# Compute an n-cycle:
   if IsEvenInt( AnBB_Vars[17] ) then
    AnBB_Vars[16] := AnBB_Vars[18] * AnBB_Vars[16] * AnBB_Vars[9];
   else
    AnBB_Vars[16] := AnBB_Vars[16] * AnBB_Vars[9];
   fi;

   AnBB_Vars[9] := AnBB_Vars[18];

# Now AnBB_Vars[16], AnBB_Vars[9] should be standard generators for Sn. Check this:
   if not AnBB_SnPresentationSatisfied( AnBB_Vars ) then return fail; fi;

# Try to express each old generator in putative standard generators:
   for OldGenerator in GeneratorsOfGroup( AnBB_Vars[1] ) do
    ImageOfGen := AnBB_EvaluateIso( OldGenerator, AnBB_Vars[23], AnBB_Vars[17], AnBB_Vars[10] );
    if ImageOfGen = fail then return fail; fi;
    SLP := AnBB_SLPForSn( ImageOfGen, AnBB_Vars[17] );
    GenPreImage := ResultOfStraightLineProgram( SLP, [ AnBB_Vars[9], AnBB_Vars[16] ] );
    if not AnBB_Equals( OldGenerator, GenPreImage ) then return fail; fi;
   od;

# Could express all old generators in new ones. Return isomorphism:
   return [ "Sn", AnBB_Vars[17], AnBB_Vars[16], AnBB_Vars[9], AnBB_Vars[23] ];

  else # if SignPerm = -1

# Check whether old generator can correctly be expressed in putative standard generators:
   SLP := AnBB_SLPForAn( ImageOfGen, AnBB_Vars[17] );
   GenPreImage := ResultOfStraightLineProgram( SLP, [ AnBB_Vars[9], AnBB_Vars[16] ] );
   if not AnBB_Equals( OldGenerator, GenPreImage ) then return fail; fi;

  fi; # if SignPerm = -1

 od; # for OldGenerator in GeneratorsOfGroup

# Could express all old generators in new ones. Return isomorphism:
 return [ "An", AnBB_Vars[17], AnBB_Vars[16], AnBB_Vars[9], AnBB_Vars[23] ];

end;	# function AnBB_ComputeIsomorphism



########################################################################
##
## The function AnBB_Recognise has as input a group G, a natural number N and
## a real number eps. It tries to recognise symmetric and alternating
## groups of degree n with 9 \le n \le N constructively.
##
## If it returns fail, it has given up. In this case the group G is not
## isomorphic to Sn or An for any n \le N with probability at least 1-eps.
## If it returns false, G is proven not to be isomorphic to Sn or An for any n \le N.
## Otherwise it has found the degree n and recognised the group constructively.
## In this case it returns the constructive isomorphism.
##
AnBB_Recognise := function( G, N, eps )
 local AnBB_Vars, RetVal, try;

 try := Log2Int( Int( 1/eps ) + 1 ) + 1;

 while try > 0 do

  try := try - 1;

# Initialise everything:
  AnBB_Vars := AnBB_InitialList( G, N );

# Search for small support involutions:
  while true do

   RetVal := AnBB_NextSmallSupportInvolution( AnBB_Vars );
   if RetVal = fail then
# Giving up.
    break;
   elif RetVal = false then
# Found that G cannot be isomorphic to Sn or An.
    return false;
   fi;

# Have a new involution, try to generate a 3-cycle:
   while true do

    if not AnBB_NextThreeCycle( AnBB_Vars ) then break; fi;

# Have a putative 3-cycle, construct an initial matching long cycle:
    if not AnBB_MatchingLongCycle( AnBB_Vars ) then continue; fi;

# Have the long cycle, build standard generators:
    if not AnBB_NiceGenerators( AnBB_Vars ) then continue; fi;

# Check whether we have standard generators, build constructive isomorphism if possible:
    RetVal := AnBB_ComputeIsomorphism( AnBB_Vars );
    if RetVal = fail then continue; fi;
    return RetVal;

   od; # while generating 3-cycles from involution

  od; # while looking for small support involutions

 od; # while outer loop ensuring low error probability

 return fail;
end;	# function AnBB_Recognise



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

