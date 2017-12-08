# take an absolutely irreducible matrix group g over k and
# decide if it is (modulo scalars in k)
# conjugate to a group over f
#
# Robert McDougal, Nick Werner,
# Justin Lynd, Niraj Khare

# *********  REQUIRES alg4 *********
alg8 := function ( g , f , k )
  local gPrime, gPrimeGenerators, moduleGenerators,
	s, temp, t, cosets, cosetReps, length, c,
	smallRing, charPoly, j, i, perm, c_jSizes ,
        done , positionInTree , descendNext ,
        chanceOfSuccess , depthInTree , gPrimeGenerators2 ,
        testThreshold , k2 , b , bInverse ,
        success , skew ;

  # check for absolute irreducibility of g first
  if not (MTX.IsAbsolutelyIrreducible (
      GModuleByMats(GeneratorsOfGroup(g) , k))) then
    Print("This algorithm requires an absolutely irreducible group.\n");
    return fail ;
  fi ;

  # check to make sure that f is contained in k
  if not IsSubset(k, f) then
    Print("\nError. f = ", f,
	  " must be contained in of k = ", k, "\n");
    return fail;
  fi;

  # Calculating the derived subgroup in general takes a LONG time
  # Let's not do that if our group is really just conjugate to
  # a matrix group over the smaller field
  # For certain types of testing, you may wish to comment out this
  # section.
  temp := alg4 ( g , f , k ) ;
  if ( temp <> fail and temp <> false ) then
    return temp ;
  fi ;

  # set the threshold for testing (currently arbitrarily)
  testThreshold := 10 ;

  # Step 1:  find a list s of elements of g that together
  #          with g' act absolutely irreducibly.

  gPrime := DerivedSubgroup ( g ) ;
  gPrimeGenerators2 := GeneratorsOfGroup ( gPrime ) ;
  gPrimeGenerators := [ ] ;
  for temp in gPrimeGenerators2 do
    Add ( gPrimeGenerators , temp ) ;
  od ;
  s := [ ] ;
  moduleGenerators := StructuralCopy ( gPrimeGenerators ) ;

  while not (MTX.IsAbsolutelyIrreducible(
	         GModuleByMats(moduleGenerators , k ))) do

    # to avoid redundancy in s, we check each time
    # to make sure that temp is not already in s
    temp := PseudoRandom ( g ) ;
    if Length ( s ) >= 1 then
      while temp in Group ( s ) do
        temp := PseudoRandom(g);
      od ;
    fi ;
    Add ( s , temp ) ;
    Add ( moduleGenerators , temp ) ;
  od ;
  t := Length ( s ) ;
  if t = 0 then
    Print("This algorithm requires that the commutator subgroup\n");
    Print("act absolutely irreducibly.\n");
    return(fail);
  fi ;
  # Step 1 ends here


  # Step 2a:  Find the set c_j of cosets of Units(f) in
  #           Units(k) such that x*s[j] has its char poly
  #           in f, where x is a representative of a coset

  # we require the cosets of the group of units of f in the
  # group of units of k
  cosets := RightCosets(Units(k), Units(f));

  # since we will have a list of cosets and a list of coset
  # representatives running in parallel, we work with the
  # indices of the elements of the lists rather than the
  # actual elements. That is, we use
  # 'for i in [1..Length(cosets]' rather than
  # 'for x in cosets'

  length := Length(cosets);
  cosetReps := [];
  for i in [1..length] do
    Add(cosetReps, Representative(cosets[i]));
  od;

  # c will be the list of lists of cosets c_j for which
  # cosetReps[i]*s[j] has its charPoly in f
  c := [];
  smallRing := PolynomialRing(f);
  for j in [1 .. t] do
    c[j] := [];
    for i in [1..length] do
      charPoly := CharacteristicPolynomial ( cosetReps [ i ] * s [ j ] ) ;
      if charPoly in smallRing then
        Add ( c [ j ] , cosetReps [ i ] ) ;
      fi;
    od;

    if Length ( c [ j ] ) = 0 then
      return false ;
    fi ;
  od ;


####################################
#  Step 2b:  Reorder s (and c) in order of
#            increasing size of c_j
############################################

  SortParallel(c,s, function(v,w) return Length(v) < Length(w) ; end );


  # Step 3:  backtrack search fun
  done := false ;
  depthInTree := 0 ;
  positionInTree := [ ] ;
  descendNext := true ;   # true when next move to descend;
                          # false when next move to advance
  success := false ;
  while not done do

    # move to next position in tree

    if descendNext then
      depthInTree := depthInTree + 1 ;
      positionInTree [ depthInTree ] := 1 ;
    else
      positionInTree [ depthInTree ] := positionInTree [ depthInTree ]+ 1
;
      if positionInTree [ depthInTree ] <= Length ( c [ depthInTree ] )
then
        done := true ;
      fi ;
      # backtrack if we can't advance until we get to a point where we can
      # (and then advance at that point)
      while not done do
        depthInTree := depthInTree - 1 ;
        if depthInTree = 0 then
          done := true ;
        else
          positionInTree [ depthInTree ] := positionInTree [ depthInTree ] + 1 ;
          if positionInTree [ depthInTree ] <= Length ( c [ depthInTree ]
) then
            done := true ;
          fi ;
        fi ;
      od ;
      if depthInTree > 0 then
        done := false ;
      fi ;
    fi ;

    if depthInTree > 0 then
      # is there any chance of this position working?
      # We do this by picking some elements of
      #   F[<g' , s_1*c_1 , ... , s_depthInTree*c_depthInTree>]
      # and checking their characteristic poly
      # To work, the characteristic poly must lie in F[x]...
      # we try testThreshold number of times using elements
      # with testThreshold parts from G' and testThreshold
      # parts from s_i*c_i
      chanceOfSuccess := true ;

      for i in [ 1 .. testThreshold ] do
        if chanceOfSuccess then
          temp := Zero ( f ) ;
          for j in [ 1 .. testThreshold ] do
            k2 := Random ( [ 1 .. depthInTree ] ) ;
            temp := temp + Random ( f ) * PseudoRandom ( gPrime )
                         + Random ( f ) * s [ k2 ] * c [ k2 ] [ positionInTree [ k2 ] ];
          od ;
          if not ( CharacteristicPolynomial ( temp ) in smallRing ) then
            chanceOfSuccess := false ;
          fi ;
        fi ;
      od ;

      # if yes, next time descend;
      # if no, next time advance on same level (or backtrack)
      descendNext := chanceOfSuccess ;  # we use these being independent
                                        # later, so don't try to
                                        # consolidate variables without
                                        # taking that into account

      # are we at depth t?  Be deterministic then (only check of
      # course if there's a chance that this could work)
      if depthInTree = t then
        descendNext := false ;
        if chanceOfSuccess then
          # Can < g' , s_1*c_1 , ... , s_t*c_t > be written over F?
          # sounds like a job for alg4
          temp := ShallowCopy ( gPrimeGenerators ) ;
          for i in [ 1 .. t ] do
            Add ( temp , s [ i ] * c [ i ] [ positionInTree [ i ] ] ) ;
          od ;
          b := alg4 ( Group ( temp ) , f , k ) ;
          if ( b <> fail ) and ( b <> false ) then
            # if we're inside this if loop, then yes it could be.
            # conjugating matrix is b.  So let's check the generators
            # of the original group g to see if when we conjugate them by
            # b, we get a matrix that is a k-scalar multiple of a matrix
            # in f.
            success := true ;
            bInverse := b ^ ( -1 ) ;
            for k2 in GeneratorsOfGroup ( g ) do
              if success then
                temp := bInverse * k2 * b ;
                done := false ;
                # find a nonzero i , j position inside temp
                # must exist since temp <> [ 0 ]
                i := 1 ;
                j := 1 ;
                while not done do
                  if IsZero ( temp [ i ] [ j ] ) then
                    i := i + 1 ;
                    if i > Size ( temp ) then
                      i := 1 ;
                      j := j + 1 ;
                    fi ;
                  else
                    done := true ;
                  fi ;
                od ;
                # all entries of temp must lie in the same coset
                # as temp [ i ] [ j ]... thus if we divide the entries
                # all by this element the result must lie in f
                skew := temp [ i ] [ j ] ;
                 success := ( skew ^ ( -1 ) * temp ) in GL ( Size ( temp ) , f ) ;
              fi ;
            od ;
            # done iff success
            done := success ;
          fi ;
        fi ;
      fi ;

    else
      done := true ;
    fi ;

  od ;

  if success then
    return b ;
  fi ;

  return false ;

  end;
