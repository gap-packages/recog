# add the vector v into nnrbasis
# returns true if v expands the set, false if not
addToNNRBasis := function ( nnrbasis , v )
  local depth , s , i , width , nonzero , temp ;

  s := Size ( nnrbasis . locOfPivots ) ;

  # get a local copy of v
  temp := ShallowCopy ( v ) ;

  # check each of the previous 1s to see if need to clear them in temp
  for i in [ 1 .. s ] do
    if not ( IsZero ( temp [ nnrbasis . locOfPivots [ i ] ] ) ) then
      AddRowVector ( temp , nnrbasis . ans [ i ] , - temp [ nnrbasis . locOfPivots [ i ] ] ) ;
    fi ;
  od ;

  # is temp the zero vector?  if so, nothing to add, so return false
  nonzero := PositionNonZero ( temp ) ;

  if nonzero > Size ( temp ) then
    return false ;
  fi ;

  # At this stage, temp has been cleared out by as much as possible
  # but still has something in the position nonzero
  # We scale that position to 1
  MultRowVector ( temp ,  temp [ nonzero ] ^ ( - 1 ) ) ;

  # Now clear all the old stuff
  for i in nnrbasis . ans do
    AddRowVector ( i , temp , - i [ nonzero ] ) ;
  od ;

  # Finally include temp in our results and exit
  Add ( nnrbasis . ans , temp ) ;
  Add ( nnrbasis . locOfPivots , nonzero ) ;

  return true ;
  end;




# take a group (matrixGroup) over bigField and return
# false if matrixGroup is not conjugate to an algebra over
# smallField, or return the conjugating matrix if it is
#
# Robert McDougal, Nick Werner,
# Justin Lynd, Niraj Khare
#
alg4 := function ( matrixGroup , smallField , bigField )
  local element , a,  smallRing ,
        charPoly , roots , i , j , k ,
        lambda , match , allEigenvectors , v , b , binverse , g ,
        temp , nnrbasis , n, count ;

  if not MTX.IsAbsolutelyIrreducible ( GModuleByMats (
             GeneratorsOfGroup ( matrixGroup ) , bigField ) ) then
    Print ( "This algorithm takes an absolutely irreducible group.\n" ) ;
    return fail ;
  fi ;
  if not IsSubset ( bigField , smallField ) then
    Print ( "Error.  f = " , smallField , " must be contained in k = " ,
            bigField , ".\n" ) ;
    return fail ;
  fi ;
  smallRing := PolynomialRing ( smallField ) ;


  # Step 1:  Find an element that has an eigenvalue with multiplicity 1

  element := false ;
  k := 0 ;
  while ( element = false ) do
    temp := false ;
    k := k + 1 ;
    for i in [ 1 .. k ] do
      if temp then
        a := a + Random ( smallField ) * PseudoRandom ( matrixGroup ) ;
      else
        a := Random ( smallField ) * PseudoRandom ( matrixGroup ) ;
        temp := true ;
      fi ;
    od ;

    if element = false then
      # Check characteristic polynomial of a to make sure it lies in smallField [ x ]
      charPoly := CharacteristicPolynomial ( a ) ;
      if not ( charPoly in smallRing ) then
        return false ;
      fi ;

      # check roots of charPoly... does any have multiplicity 1?
      roots := RootsOfUPol ( charPoly ) ;
      lambda := false ;
      for i in [ 1 .. Length ( roots ) ] do
        if lambda = false and IsBound ( roots [ i ] ) then
          match := false ;
          for j in [ i + 1 .. Length ( roots ) ] do
            if roots [ i ] = roots [ j ] then
              match := true ;
              Unbind ( roots [ j ] ) ;
            fi ;
          od ;
          if not match then
            lambda := roots [ i ] ;   # if none of the other roots are the same
                                      # as the ith one, the that root has multiplicity 1
          fi ;
        fi ;
      od ;
      if lambda <> false and (lambda in smallField) then
        element := a ;
      fi ;
    fi ;
  od ;

  a := element ;
  # step 1 ends here.  We now have an element = a with an eigenvalue
  # lambda of multiplicity 1


  # Step 2: Get an eigenvector v of a corresponding to lambda

  temp := TransposedMat ( a ) - lambda * One ( a ) ;
  v := TriangulizedNullspaceMat( temp ) [1];

  # step 2 ends here.  v is a (non-zero) lambda eigenvector for a


  # step 3: make a basis b out of vectors of the form g * v
  b := [ ] ;
  nnrbasis := rec ( ans := [ ] , locOfPivots := [ ] ) ;


  while not Size(b) = Size(a) do
    g := PseudoRandom(matrixGroup);
    if ( addToNNRBasis ( nnrbasis , g * v ) ) then
      Add(b, g * v);
    fi;
  od;


  # up until now, b is a list of row vectors... we want to transpose it
  b := TransposedMat ( b ) ;

  # step 3 ends here


  # step 4:  conjugate the generators by B & check to see if inside the smaller field
  # somehow we are getting here without (necessarily) having b being n x n
  binverse := b ^ ( -1 ) ;
  for g in GeneratorsOfGroup ( matrixGroup ) do
    temp := binverse * g * b ;
    if not ( temp in GL ( Size ( a ) , smallField ) ) then
      return false ;
    fi ;
  od ;

  return b ;
  end ;

