#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Stephen Howe, Maska Law, Max Neunhöffer,
##  Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  This file contains an implementation of an algorithm for recognising
##  An or Sn acting as matrix groups on their fully deleted permutation
##  modules. The particular algorithm is described in the paper [BLGN+05].
##
#############################################################################

## General utility functions

RECOG.LogRat := function(rat, base)
# LogRat(<rat>, <base>) is an upper bound
# on log <rat> to base <base>.
  return   (LogInt(NumeratorRat(rat), base) + 1)
         - LogInt(DenominatorRat(rat), base);
end;

RECOG.IterateWithRandomElements := function(func, times, group)
# IterateWithRandomElements(<func>, <times>, <group>) randomly
# selects up to <times> random elements (from <group>) to find
# an element such that <func> (with input being this random element)
# does not return 'fail'. The function <func> must take a group
# element as its only argument.

  local itr, # number of random elements selected
        re,  # a random element
        ret; # the result of func(re)

  itr := 1;
  while itr <= times do
    # select random element
    re := PseudoRandom(group);
    # call func with random element
    ret := func(re);
    # if function successful
    if ret <> fail then
      return ret;
    fi;
    # else try again
    itr := itr + 1;
  od;

  return fail;
end;

## Functions for efficient matrix operations

RECOG.Commute := function(g, h);
# Commute(g,h) returns true if and only if
# gh = hg
  ConvertToMatrixRep(g);
  ConvertToMatrixRep(h);
  return g*h = h*g;
end;

RECOG.Conj := function(A, B)
# Conj(A, B) returns the conjugation of
# A by B (where A and B are two matrices)
# That is Conj(A, B) = B^-1*A*B

  ConvertToMatrixRep(B);

  return A^B;
end;

RECOG.ConjInv := function(A, B)
# ConjInv(A, B) returns the conjugation of
# A by B^-1 (where A and B are two matrices)
# That is ConjInv(A, B) = B*A*B^-1

  ConvertToMatrixRep(B);

  return B*A*B^-1;
end;

## Finding a 3-cycle or double transposition

RECOG.LinearFactors := function(poly, field)
# LinearFactors(<poly>, <field>) returns a list with two
# elements when given a univariate polynomial <poly> with
# coefficients from the finite field <field>. The first
# element is a list of field elements [c1,...,cn] where
# t - ci divides <poly> for i = 1,...,n. The second element
# is a function from the multiplicative group of <field> to
# the integers such that: for every non-zero field element c,
# the image of c is the multiplicity of t - c in <poly>.

  local linearFactors, # [c1,...,cn] s.t. t - ci is a factor
        ix,            # list index
        z,             # primitive root of field, i.e., z = Z(q)
        multList,      # a list of multiplicities where t - Z(q)^(i-1)
                       # has multiplicity multList[i]
        Multiplicity;  # function mapping non-zero field elem. c to
                       # mult. of t - c

  # find the linear factors of poly (as polynomials),
  # so linearFactors = [[ai*t + bi, mi]] where ai, bi are
  # field elements and mi are the multiplicities
  linearFactors := Filtered(Collected(Factors(PolynomialRing(field), poly)),
                            f -> DegreeOfLaurentPolynomial(f[1]) = 1);

  # put linearFactors into form [[ci, mi]] where mi is
  # multiplicity of t - ci
  Apply(linearFactors,
        f -> [-Iterated(CoefficientsOfUnivariatePolynomial(f[1]), \/),
              f[2]]);


  # create the function Multiplicity

  z := PrimitiveRoot(field); # find Z(q) where q is size of field
  # create list s.t. the ith entry is the multiplicity
  # of t - Z(q)^(i-1) in poly
  multList := [];
  for ix in [1..Length(linearFactors)] do
    multList[LogFFE(linearFactors[ix][1], z) + 1] := linearFactors[ix][2];
  od;

  Multiplicity := function(ffe)
    local ffeIndex;

    # calc index for ffe
    ffeIndex := LogFFE(ffe, z) + 1;

    # if t - Z(q)^i is not a factor of poly
    # then multList[i] is not bound
    if IsBound(multList[ffeIndex]) then
      return multList[ffeIndex];
    else
      return 0;
    fi;
  end;

  return [List(linearFactors, f -> f[1]), Multiplicity];
end;

RECOG.IsPreDoubleTransposition := function(charPoly, t, linearFactors,
                                     fdpmDim, nAmbig, field)
# IsPreDoubleTransposition(<charPoly>, <t>, <linearFactors>,
#                          <fdpmDim>, <nAmbig>, <field>)
# determines whether some scalar multiple of the matrix described
# by <charPoly> (with indeterminate <t>) represents a
# pre-double-transposition. If so the scalar multiple is returned,
# otherwise 'false' is returned.
#   <linearFactors> - describes the linear factors of <charPoly>
#   <fdpmDim> - the dimension of the matrices described
#   <nAmbig> - true when there are two possible values for n
#   <field> - the field of <charPoly>
# This function works for any field with odd characteristic.
# Note: requires n >= 8 or n = 7 and p <> 7, <=> fdpmDim >= 6

  local b, c,     # field elements
        tpList,   # list of elements c s.t. t^2 - c^2 | charPoly
        r;        # a prime integer

  if Length(linearFactors[1]) < 2 then
    # we must have t + c and t - c as linear factors
    # for some c
    return false;
  else
    tpList := [];
    # we expect tpList to only have two elements
    # at the end of this loop
    for c in linearFactors[1] do
      # we add to tpList in (+/-) pairs
      # so check c is not -d for some d in tpList
      if c in tpList then
        continue;
      elif linearFactors[2](-c) > 0 then
        # t^2 - c^2 divides charPoly
        if not IsEmpty(tpList) then
          # tpList would have more than 2 elements
          return false;
        else
          Add(tpList, c);
          Add(tpList, -c);
        fi;
      fi;
    od;
  fi;

  # determine whether tpList is of the form { c, -c } where
  # t + c has multiplicity 2
  if IsEmpty(tpList) then
    return false;
  elif linearFactors[2](tpList[1]) = 2 then
    # (t - tpList[1]) has multiplicity 2
    c := -tpList[1];
  elif linearFactors[2](tpList[2]) = 2 then
    # (t - tpList[2]) has multiplicity 2
    c := -tpList[2];
  else
    return false;
  fi;

  # determine the scalar b associated with the matrix
  # whose characteristic polynomial we have
  if linearFactors[2](c) <> 2 then
    b := c;
    # some extra cases: Assuming s = 2 and 2 <= r < n/2 in proof,
    # so there may be a (unique) odd prime r >= n/2
    if     IsPrime(fdpmDim - 2)
       and charPoly = (t^2 - b^2)*(t^(fdpmDim - 2) + b^(fdpmDim - 2)) then
      # corresponds to permutation with cycle type 1^1 2^1 (n-3)^1
      return false;
    elif     nAmbig
         and fdpmDim - 4 <> 2 and IsPrime(fdpmDim - 4) # fdpmDim-4 is odd prime
         and charPoly = (t - b)^3*(t+b)*(t^(fdpmDim - 4) + b^(fdpmDim - 4)) then
      # corresponds to permutation with cycle type 2^3 (n-6)^1
      return false;
    fi;
  elif fdpmDim mod 2 = 0 then # also mult (t - c) = 2
    # get coeffs of t^(fdpmDim - 1), t^(fdpmDim - 2), and t^(fdpmDim - 3)
    # in charPoly
    c := CoefficientsOfUnivariatePolynomial(charPoly){
             [fdpmDim - 3 .. fdpmDim - 1] + 1};
    # Check case 3 (ii) and first part of 3 (iii) together (they are
    # identical in terms of fdpmDim = n - delta). That is,
    # check t^2-c[3]^2 | charPoly and
    #  charPoly = (t-c[3])(t+c[3])^2(t^(fdpmDim-3)-c[3]^(fdpmDim - 3))
    if     c[3] in tpList
       and charPoly = (t - c[3]) * (t + c[3])^2 *
                      (t^(fdpmDim - 3) - c[3]^(fdpmDim - 3)) then
      # since we know the form of the characteristic polynomial we don't
      # need to check t^r + b^r does not divide charPoly for r etc.
      return c[3];
    elif nAmbig then # do the rest of 3 (iii) only if delta could be 2
      # expect coeffs of t^(fdpmDim-1) and t^(fdpmDim - 2) are
      # 2b and b^2 respectively with b in tpList
      if c[3]/2 in tpList and c[2] = (c[3]/2)^2 then
        # if c[1] <> 0 then we must have cycle type 2^2 3^1 (n-7)^1
        # if c[1] = 0 then we just set b
        b := c[3]/2;
        if     not IsZero(c[1])
           and charPoly = (t + b)^2 * (t^3 - b^3) *
                          (t^(fdpmDim - 5) - b^(fdpmDim - 5)) then
          # we can return b since we have check the form
          # of charPoly
          return b;
        fi;
      else
        return false; # c[3]/2 is not in tpList
      fi;
    else
      return false; # n not ambiguous
    fi;
  else
    return false; # no special cases for this value of fdpmDim
  fi; # we have now either returned or found a possible scalar b

  # check there is no prime r = 2 or 5 <= r < n/2 with
  # t^r + b^r dividing charPoly
  r := 2;
  while r < QuoInt(fdpmDim + 2, 2) do
    if     r <> Characteristic(field)
       and IsZero(QuotientRemainder(charPoly, t^r + b^r)[2]) then
      return false;
    fi;
    r := NextPrimeInt(r);
  od;

  return b;
end;

RECOG.IsPre3Cycle :=
   function(charPoly, t, linearFactors, fdpmDim, nAmbig, field)
# IsPre3Cycle(<charPoly>, <t>, <linearFactors>, <fdpmDim>, <nAmbig>, <field>)
# determines whether some scalar multiple of the matrix described
# by <charPoly> (with indeterminate <t>) represents a
# pre-3-cycle. If so the scalar multiple is returned,
# otherwise 'false' is returned.
#   <linearFactors> - describes the linear factors of <charPoly>
#   <fdpmDim> - the dimension of the matrices described
#   <nAmbig> - true when there are two possible values for n
#   <field> - the field of <charPoly>
# Note: requires n >= 5 or n = 5 and p <> 5, <=> fdpmDim >= 4

  local tcList, # list of field elems c s.t. t^3 - c^3 | charPoly
        lMult,  # a list of multiplicities
        r,      # a prime
        b, c,   # field elements
        y;      # field element of order 3

  if Size(field) mod 3 = 2 then
    # find all c s.t. t^3 - c^3 | charPoly
    tcList := Filtered(linearFactors[1],
                       c -> IsZero(QuotientRemainder(charPoly,
                                                     t^3 - c^3)[2]));
    if Length(tcList) = 1 then
      # check whether tcList = {c} where t^2+ct+c^2 has mult 1
      if IsZero(QuotientRemainder(charPoly,
                                  (t^2 + tcList[1]*t + tcList[1]^2)^2)[2]) then
        # t^2+ct+c^2 has mult > 1
        return false;
      else
        # set scalar
        b := tcList[1];
      fi;
    elif IsEmpty(tcList) and nAmbig and (fdpmDim + 2) mod 3 <> 0 then
      if Characteristic(field) <> 2 then # if char of field is odd
        # coeff of t^(fdpmDim - 1) in charPoly is 2b
        c := CoefficientsOfUnivariatePolynomial(charPoly)[(fdpmDim - 1)+1]/2;
      else
        # coeff of t^(fdpmDim - 2) in charPoly is b^2
        c := CoefficientsOfUnivariatePolynomial(charPoly)[(fdpmDim - 2)+1];
        c := SquareRoots(field, c)[1];
      fi;
      if charPoly = (t^2 + c*t + c^2)*(t^(fdpmDim-1) - c^(fdpmDim-1))
                    / (t - c) then
        # return the scalar since we know the form of charPoly
        return c;
      else
        return false;
      fi;
    else # Length(tcList) >= 2
      return false;
    fi;
  else # q mod 3 = 1 since we assume q mod 3 <> 0

    # calc field element of order 3
    y := PrimitiveRoot(field)^((Size(field)-1)/3);
    # find all elements c such that t-c | charPoly and t-cy^i | charPoly
    # for i = 1 or 2
    tcList := Filtered(linearFactors[1],
                       c ->    linearFactors[2](c*y)   > 0
                            or linearFactors[2](c*y^2) > 0);

    if    Length(tcList) = 2
      and Order(tcList[1]*tcList[2]^-1) = 3
      and linearFactors[2](tcList[1]) = 1
      and linearFactors[2](tcList[2]) = 1 then
        # set the scalar
        b := tcList[1]^2*tcList[2]^-1;
    elif Length(tcList) = 3 and ForAll(tcList, c -> y*c in tcList) then
      # check whether y*tcList = tcList (setwise)
      # find elements of tcList that have mult > 1
      lMult := Filtered(tcList, c -> linearFactors[2](c) > 1);
      if Length(lMult) = 1 then
        # set the scalar
        b := lMult[1];
      elif IsEmpty(lMult) then
        # get coeffs of t^(fdpmDim-1), t, and t^0
        c := CoefficientsOfUnivariatePolynomial(charPoly){[1,2,(fdpmDim-1)+1]};
        # check for pre-3-cycles with cycle type 3^1 (n-3)^1, if delta = 1,
        # or cycle type 1^1 3^1 (n-4)^1, if delta = 2. The tests are
        # identical when written in terms of n - delta.
        if     (fdpmDim + 1) mod 3 <> 0
           and c[3] in tcList
           and charPoly =  (t^2 + c[3]*t + c[3]^2)
                          *(t^(fdpmDim - 2) - c[3]^(fdpmDim - 2)) then
          # return the scalar since we know the form of charPoly
          return c[3];
        elif     nAmbig # this case only occurs when delta = 2
             and Characteristic(field) >= 5
             and c[3]/2 in tcList
             and c[1] = -(c[3]/2)^fdpmDim            # check coeff of t^0
             and c[2] = -2*(c[3]/2)^(fdpmDim-1) then # check coeff of t
          # set the scalar
          b := c[3]/2;
        else
          return false;
        fi;
      else # Length(lMult) > 1
        return false;
      fi;
    else # Length(tcList) <> 2 or 3
      return false;
    fi;
  fi; # end of q mod 3 = 1 case

  # check there are no primes r (<= n/3, r <> p) such that
  # t^2r + b^r*t^r + b^2r | charPoly
  r := 2;
  while r <= QuoInt(fdpmDim + 2, 3) do
    if    r <> Characteristic(field)
      and IsZero(QuotientRemainder(charPoly,
                                   t^(2*r) + b^r*t^r + b^(2*r))[2]) then
      return false;
    fi;
    r := NextPrimeInt(r);
  od;

  return b;
end;

RECOG.Construct3Cycle := function(mat, fdpm)
# Construct3Cycle(<mat>, <fdpm>) attempts
# to construct a matrix representing a 3-cycle from
# <mat>. If it is successful the new matrix is
# returned in a record, otherwise fail is returned.
# The record has two components; the first is
# 'matrix' and stores the matrix, the second is 'order'
# and stores the order of the matrix i.e. 3.

  local charPoly,      # the characteristic polynomial of mat
        t,             # the indeterminate of charPoly
        linearFactors, # the linear factors of charPoly
        b,             # a field element
        order;         # order of the matrix

  # calculate the characteristic polynomial and its linear factors
  charPoly := CharacteristicPolynomial(mat);
  t := IndeterminateOfLaurentPolynomial(charPoly);
  # calculate the linear factors of charPoly
  linearFactors := RECOG.LinearFactors(charPoly, fdpm.field);

  b := RECOG.IsPre3Cycle(charPoly, t, linearFactors,
                         fdpm.dim, fdpm.nAmbig, fdpm.field);

  if b <> false then
    mat := b^-1*mat;

    # check the order
    order := Order(mat);
    if     order < (fdpm.dim + 2)^(18*RECOG.LogRat(fdpm.dim + 2, 2))
       and order mod 3 = 0 then
      ConvertToMatrixRep(mat);
      mat := mat^(order / 3);
      return rec( matrix := mat, order := 3 );
    fi;
  fi;

  return fail;
end;

RECOG.ConstructDoubleTransposition := function(mat, fdpm)
# ConstructDoubleTransposition(<mat>, <fdpm>)
# attempts to construct a matrix representing a double
# transposition from <mat>. If it is successful the new
# matrix is returned in a record, otherwise 'fail' is
# returned. The record has two components; the first is
# 'matrix' and stores the matrix, the second is 'order'
# and stores the order of the matrix i.e. 2.

  local charPoly,      # the characteristic polynomial of mat
        t,             # the indeterminate of charPoly
        linearFactors, # the linear factors of charPoly
        b,             # a field element
        order;         # order of the matrix

  # calculate the characteristic polynomial and its linear factors
  charPoly := CharacteristicPolynomial(mat);
  t := IndeterminateOfLaurentPolynomial(charPoly);
  # calculate the linear factors of charPoly
  linearFactors := RECOG.LinearFactors(charPoly, fdpm.field);

  b := RECOG.IsPreDoubleTransposition(charPoly, t, linearFactors,
                                fdpm.dim, fdpm.nAmbig, fdpm.field);

  if b <> false then # mat is a pre-double-transposition
    mat := b^-1*mat;

    # check the order
    order := Order(mat);
    if     order < (fdpm.dim + 2)^(18*RECOG.LogRat(fdpm.dim + 2, 2))
       and order mod 2 = 0 then
      ConvertToMatrixRep(mat);
      mat := mat^(order / 2);
      return rec( matrix := mat, order := 2 );
    fi;
  fi;

  return fail;
end;

## Functions for finding the first element of our linked basis

RECOG.DoubleAndShrink := function(g, group, n)
# DoubleAndShrink(<g>, <group>, <n>) returns a conjugate
# h of <g> such that <g> and h have only 1 moved
# point in common where <group> is some matrix representation of
# a finite symmetric group of order <n>, and <g> moves between
# 3 and sqrt(<n>) points.

  local gs,      # list of generated elements
        rs,      # list of random elements, their inverses,
                 # and the conjugations
        ri,      # the current random element
        gi,      # the current generated element
        temp,    # temp storage for some element
        gconjs,  # gs[j-1]^s
        gconjrs, # gs[j-1]^(r[j-1]s) respectively
        i, j,    # counters
        s,       # conjugating element, g^s is returned
        maxItr;  # maximum number of random element selections

  # initialise variables
  maxItr := RECOG.LogRat(n, 2);
  gs := [g];
  gi := g;
  # get random element and calculate its inverse
  # and gi^ri
  ri := PseudoRandom(group);
  ConvertToMatrixRep(ri);
  temp := ri^-1;
  rs := [[ri, temp, temp*gi*ri]];

  i := 1;
  # find elements that do not commute
  while RECOG.Commute(gi, rs[i][3]) do
    if i >= maxItr then
      return fail;
    fi;
    # generate next element
    gi := gi * rs[i][3];
    Add(gs, gi);
    # get next random element
    ri := PseudoRandom(group);
    temp := ri^-1;
    Add(rs, [ri, temp, temp * gi * ri]);

    i := i + 1;
  od;
  # go back through the generated elements to
  # get a conjugating element s such that g
  # and g^s do not commute
  s := rs[i][1];
  for j in [i,i-1..2] do
    # calc gs[j-1]^s
    gconjs := RECOG.Conj(gs[j-1], s);
    # determine new s
    if RECOG.Commute(gs[j-1], gconjs) then
      # calc gs[j-1]^(rs[j-1]*s)
      gconjrs := RECOG.Conj(rs[j-1][3], s);
      if not RECOG.Commute(gs[j-1], gconjrs) then
        s := rs[j-1][1] * s;
      elif not RECOG.Commute(rs[j-1][3], gconjs) then
        s := s * rs[j-1][2];
      else
        # s := s^(rs[j-1][1]^-1)
        s := rs[j-1][1] * s * rs[j-1][2];
      fi;
    # else
      # s stays the same
    fi;
  od;

  return RECOG.Conj(g, s);
end;

RECOG.FixedPointSubspace := function(mat, k)
# FixedPointSubspace(<mat>, <k>) for a matrix <mat> with
# order <k> returns [F, W] where
#    - F is a list of vectors that form a basis
#      for the fixed point subspace of <mat>, and
#    - W is a list of vectors that form a basis for
#      the complement W(<mat>) of F such that for all w
#      in W(<mat>), w+w<mat>+w<mat>^2+...+w<mat>^(k-1) = 0
# This function uses the row echelon form of a matrix in order
# to compute the relevent bases. Requires k mod p <> 0 where
# p is the characteristic of the field.
  local moveLT, trans;

  # linear transformation mapping elements of the
  # vector space to elements of W(<mat>), takes
  # a matrix as its argument
  moveLT := function(v)
    local sum, i;

    # calculate (((v*mat + v)*mat + v)*mat + v)...)*mat + v
    sum := v;
    for i in [1..k-1] do
      sum := sum * mat + v;
    od;

    return k*v - sum;
  end;

  # SemiEchelonMatTransformation(m)
  # returns rec ( heads, vectors, coeffs, relations )
  # where the rank of m is the length of coeffs
  # and coeffs*m are the row vectors of m in row echelon form
  # In particular [ coeffs    ] is the echelonizing matrix
  #               [ relations ]

  # v is a fixed point of mat iff v is in the null space of Xmat
  # compute the transformation taking 'mat - One(mat)' to row echelon form
  trans := SemiEchelonMatTransformation(mat - One(mat));

  return [trans.relations, moveLT(trans.coeffs)];
end;

RECOG.SubspaceIntersection := function(basisA, basisB)
# SubspaceIntersection(basisA, basisB) returns a vector in the intersection
# of the subspaces <basisA[1], basisA[2]> and <basisB[1], basisB[2]>
# We assume that basisA and basisB are both lists of two linearly
# independent vectors.

  local mat,   # matrix formed from rows of basisA and basisB
        row,   # a row vector in the intersection
        nullv; # basis for nullspace of mat

  # check we are given lists of length 2
  if Length(basisA) <> 2 or Length(basisB) <> 2 then
    # this function only works for intersection of subspaces
    # of dimension 2
    return fail;
  fi;

  # create the matrix whose rows are basisA[1], basisA[2],
  # basisB[1], and basisB[2]
  mat := [ShallowCopy(basisA[1]),
          ShallowCopy(basisA[2]),
          ShallowCopy(basisB[1]),
          ShallowCopy(basisB[2])];

  # find the null space of the matrix
  nullv := SemiEchelonMatTransformation(mat).relations;

  if Length(nullv) <> 1 or (    IsZero(nullv[1][1])
                            and IsZero(nullv[1][2])) then
    # the two subspaces don't intersect in a one dimensional
    # subspace
    return fail;
  else
    # calculate vector in subspace intersection
    ConvertToVectorRep(mat[1]);
    MultRowVector(mat[1], nullv[1][1]);
    AddRowVector(mat[1], mat[2], nullv[1][2]);
    return mat[1];
  fi;
end;

RECOG.FindBasisElement := function(g, group, epsilon, fdpm)
# FindBasisElement(<g>, <group>, <epsilon>, <fdpm>) returns,
# with probability 1 - <epsilon>, a vector representing a basis
# element of the fully deleted permutation module, that is,
# a vector representing b(e_i - e_j) + (W \cap E) for some
# non-zero field element b and integers i and j. A matrix
# representing a 3-cycle or a double transposition is passed
# in the record <g>. The record has two components; the first is
# 'matrix' and stores the matrix, the second is 'order' and stores
# the order of the matrix (from which we can determine whether
# the permutation type the matrix represents).

  local itr, h, gh, temp;

  itr := 1;
  # Check the bounds
  while itr < RECOG.LogRat(epsilon^-1, 2)*7 do # 1/log(10/9) < 7
    # get random conjugate
    h := RECOG.DoubleAndShrink(g.matrix, group, fdpm.dim + 2);
    # check if it has exactly one moved point in common
    if h <> fail then
      gh := g.matrix * h;
      if (   (g.order = 2 and Order(gh) = 6)
          or (g.order = 3 and Order(gh) = 5)) then
        # return intersection of the totally moved subspaces
        ConvertToMatrixRep(h);
        temp := h^-1;
        return RECOG.SubspaceIntersection(
                   RECOG.FixedPointSubspace(g.matrix,  g.order)[2],
                   RECOG.FixedPointSubspace(temp * gh, g.order)[2]);
      fi;
    fi;
    itr := itr + 1;
  od;

  return fail;
end;

## Functions for finding a linked sequence of vectors

RECOG.Power := function(xs, k)
# Power(<xs>, <k>) computes <xs>[1]^<k> in
# log k time where <xs> is the list
# a list [x, x^2, x^4, ...., x^(2^m)] for some
# matrix x. If k >= 2^(m+1) then the list will
# be updated
  local q, r, prod, xn;

  q := k;
  xn := 1;            # list index x[xn] = x^(2^(xn-1))
  prod := One(xs[1]); # partial product which will finish as x^k
  while q > 0 do
    # extend the list if we have to
    if xn > Length(xs) then # we have xn = Length(xs) + 1
      ConvertToMatrixRep(xs[xn - 1]);
      Add(xs, xs[xn - 1]^2);
    fi;
    # if this bit in the binary expansion of k is 1
    if RemInt(q, 2) = 1 then
      # update the product
      prod := prod * xs[xn];
    fi;
    xn := xn + 1;
    # move to the next bit
    q := QuoInt(q, 2);
  od;

  return prod;
end;

RECOG.VectorImages := function(v, xs)
# VectorImages(<v>, <xs>) returns the list
#   [<v>, <v>*x, ..., <v>*x^(2^(k+1)-1)]
# where xs = [x,x^2,x^4,...,x^(2^k)].
# The lists are computed in O(logm) time (wrt matrix mult).

  local k,    # counter
        vxs;  # the list [v,vx,...,vx^2logm]

  # calc v,vx,...,vx^2logm
  vxs := [v];
  for k in [1..Length(xs)] do
    Append(vxs, vxs * xs[k]);
  od;

  return vxs;
end;

RECOG.VectorImagesUnder := function(v, h, k)
# VectorImagesUnder(<v>,<h>, <k>) returns
# the list [<v>, <v>*h, ..., <v>*<h>^(2^(LogInt(k,2)+1)-1)]
  local hs, p;

  hs := [h];
  for p in [1..LogInt(k, 2)] do
    ConvertToMatrixRep(hs[p]);
    Add(hs, hs[p]^2);
  od;

  return RECOG.VectorImages(v, hs);
end;

RECOG.MoreBasisVectors := function(x, g, v, fdpm)
# MoreBasisVectors(<x>, <g>, <v>, <fdpm>), where
# <g> is a record and <g>.matrix represents a 3-cycle
# or double transposition, <g>.order is
# the order of <g>.matrix, and <x> is a random group element;
# returns a set of linked basis vectors of prime length r where
# 0.6n+0.4 < r < 0.95n - 0.85

  local i,      # the number of vectors (obtained from v) we consider
        vs,     # the list [vg^i | i = 0, 1, 2, if g reps. a 3 cycle
                #                  i = 0,       if g reps. a dt     ]
        xs,     # the list [x,x^2,x^4,...,x^(2^k)]
                # where 2^k <= n < 2^(k+1)
        vBases, # a list of Basis objects for the vector spaces
                # spanned by the vectors in vs
        vImgs,  # images of vectors in vs under x, ..., x^(n-1)
        rs,     # [r(vg^i,x) | i = 0, 1, 2, if g reps. a 3 cycle
                #              i = 0,       if g reps. a dt     ]
        R,      # returns r(v, x)
        lList,  # { l : 1 <= l < r, vx^l <> vx^lg }
        mat,    # temporary matrix for calc. vImgsG
        vImgsG, # [ vg, vxg, vx^2g, ..., vx^(n-1)g ]
        u,      # a vector
        d,      # u = dv or u = dvg
        h,      # a matrix rep. a (large) prime cycle
        k;      # loop counter

  R := function(vBasis, vxs)
  # R(vBasis, vxs) returns r(v, x) where
  # vBasis is a Basis object for the vector space
  # spanned by v and vxs is the list of images of v
  # under x, ..., x^(n-1)
    local r;

    # find least +ve integer k such that vx^k in
    # the vector space spanned by v
    # Note: opened up the bounds a bit so it works for
    # n < 13
    r := NextPrimeInt(Int(6*(fdpm.dim + 1)/10 + 4/10) - 1);

    # we can just check primes since, if r = r(v, x), and
    # vx^s \in <v> then r divides s. If we are given a
    # scalar multiple of the identity matrix then
    # we will fail when considering the list
    # { l : 1 <= l < r, vx^l <> vx^lg } as v <> vg

    while r < (19*(fdpm.dim + 2) - 17)/20 do
      # check if vx^r = dv for some field element d
      if Coefficients(vBasis, vxs[r+1]) <> fail then
        # check r is prime and in the right range
        return r;
      fi;
      r := NextPrimeInt(r);
    od;

    return fail;
  end;

  # Determine how many vectors (all obtained from v) that
  # we will consider. This number depends on whether we
  # have a 3-cycle or double transposition
  if g.order = 3 then
    i := 3;
  else
    i := 1;
  fi;

  # Calculate the vectors we will consider
  ConvertToMatrixRep(g.matrix);
  vs := [];
  for k in [1..i] do
    Add(vs, v);
    v := v*g.matrix;
  od;

  # Construct the matrices [x,x^2,x^4,...,x^(2^k)]
  # where 2^k <= n < 2^(k+1) in log n time
  xs := [x];
  for k in [1..Int(LogInt(fdpm.dim + 2, 2))] do
    ConvertToMatrixRep(xs[k]);
    Add(xs, xs[k]^2);
  od;

  # Calculate Basis objects for the vector spaces
  # spanned by the vectors of vs. We can use these
  # Basis objects to determine whether a vector lies
  # in the corresponding vector space (which is need
  # for calculating r(x,vg^i)).
  vBases := List(vs, b -> BasisNC(VectorSpace(fdpm.field, [b]), [b]));

  # Construct the images of the vectors in vs under
  # x, ..., x^(n-1) (in log n time). Then we will have
  # the vectors vg^ix, ..., vg^ix^(n-1) for i = 0, 1, 2,
  # if g rep. a 3-cycle and i = 0, otherwise
  ConvertToMatrixRep(vs);
  vImgs := TransposedMat(RECOG.VectorImages(vs, xs));

  # Calculate r(vg^i, x) for i = 0,1,2 if
  # g is a 3-cycle and, i = 0, if g is a double
  # transposition
  rs := ListN(vBases, vImgs, R);

  # for all vg^i such that r(vg^i, x) = r <> fail we check
  # whether the list { l | 1 <= l < r, vx^l <> vx^lg } = 2.
  # If the list does have length two then we can compute
  # a linked sequence of vectors using vg^i
  for k in [1..i] do
    # check that r(vg^k, x) succeeded
    if rs[k] = fail then
      continue;
    fi;
    # calculate vx^lg for l = 1,..., r-1
    mat := vImgs[k]{[1..rs[k]]};
    vImgsG := mat * g.matrix;
    # calculate { l | 1 <= l < r, vx^l <> vx^lg }
    lList := Filtered([1..rs[k]-1], l -> vImgs[k][l+1] <> vImgsG[l+1]);
    if Length(lList) = 2 then
      # try to construct linked sequence of vectors
      u := vImgs[k][lList[1]+1] - vImgsG[lList[1]+1];
      if i = 3 then # if g is a 3-cycle
        # check whether u in span of vs[k]
        d := Coefficients(vBases[k], u);
        if d <> fail then
          h := -d[1]^-1*RECOG.Power(xs, lList[1]);
          return RECOG.VectorImagesUnder(-vs[k], h, rs[k]-1){[1..rs[k]-1]};
        fi;
        # if u not in span of vs[k] then check
        # whether u in span of vs[k]*g = vs[(k + 1) mod 3 + 1]
        d := Coefficients(vBases[k^(1,2,3)], u);
        if d <> fail then
          h := d[1]^-1*RECOG.Power(xs, lList[1]);
          return RECOG.VectorImagesUnder(vs[k], h, rs[k]-1){[1..rs[k]-1]};
        fi;
        # if neither then fail
        return fail;
      else # if g is a double transposition
        # check whether u in span of vs[k]
        d := Coefficients(vBases[k], u);
        if d <> fail then
          h := -d[1]^-1*RECOG.Power(xs, lList[1]);
          return RECOG.VectorImagesUnder(vs[k], h, rs[k]-1){[1..rs[k]-1]};
        fi;
        # otherwise fail
        return fail;
      fi;
    fi;
  od;

  return fail;
end;

## Functions for finding a basis from the linked sequence of
## vectors found by MoreBasisVectors

RECOG.RowSpaceBasis  := function(mat)
# RowSpaceGenerators(<mat>) returns the rows of
# <mat> that form a basis for the row space
# of <mat>. This code borrows from the
# implementation of SemiEchcelonMatDestructive.

  local basis,   # vectors of mat forming a basis
                 # for the row space of mat
        nzheads, # columns with leading 1 in the
                 # row echelon form of mat
        vectors, # vectors spanning subspace of row
                 # space of mat
        row,     # current row of mat
        nrows,   # number of rows of mat
        ncols,   # number of columns of mat
        x,       # a field element
        r, c;    # row and column indexes

  # calc size of matrix
  nrows := Length(mat);
  ncols := Length(mat[1]);

  # list of the non-zero heads, that is, nzheads[i]
  # is the first non-element of vectors[i]
  nzheads := [];
  # vectors contains a linearly independent
  # set of vectors spanning a subset of the row-space
  vectors := [];
  # basis contains vectors that span the same subspace
  # spanned by vectors, but the vectors in basis are
  # from mat
  basis := [];

  for r in [1..nrows] do
    row := ShallowCopy(mat[r]);

    # reduce row using vectors
    for c in [1..Length(nzheads)] do
      x := row[nzheads[c]];
      # if row does not already have a zero in this
      # column
      if not IsZero(x) then
        AddRowVector(row, vectors[c], -x);
      fi;
    od;

    # check row is not the zero row
    c := PositionNonZero(row);
    if c <= ncols then
      # mult row by row[c]^-1 so leading coeff. is 1
      MultRowVector(row, row[c]^-1);
      Add(vectors, row);
      Add(nzheads, c);
      # add mat[r] to basis
      Add(basis, mat[r]);
    fi;
  od;

  return basis;
end;

RECOG.ExtendToBasisEchelon := function(partial, d, field)
# ExtendToBasisEchelon(<partial>, <d>, <field>)
# returns a basis for <field>^<d> such that <partial>
# is a prefix.
  local vectors, v;

  # copy partial
  vectors := ShallowCopy(partial);

  # append identity matrix
  Append(vectors, IdentityMat(d, field));

  # return row space basis
  return RECOG.RowSpaceBasis(vectors);
end;


RECOG.IsIntervalVector := function(v, s)
# IsIntervalVector(<v>, <s>)
# returns [b, supp] if <v> is zero except
# for a uninterrupted sequence of b's within the
# first s positions. If v is not an interval
# vector then fail is returned
  local col, b, i, j;

  # find first non-zero entry in v
  col := 1;
  while col <= s and IsZero(v[col]) do
    col := col + 1;
  od;

  # check first non-zero entry is within first s coords
  if col > s then
    return fail;
  fi;
  # else set i and b
  i := col;
  b := v[i];

  # find first entry not equal to b
  while col <= s and v[col] = b do
    col := col + 1;
  od;

  # set j
  j := col;

  # check the rest of the entries are zero
  while col <= Length(v) do
    if not IsZero(v[col]) then
      return fail;
    fi;
    col := col + 1;
  od;

  return [b, [i, j]];
end;

RECOG.FindBasis := function(x, vs, us, fdpm)
# FindBasis(<x>, <vs>, <us>, <fdpm>) extends the list
# of vectors in <vs> (and in <us>) to a linked basis
# for the fully deleted permutation module, described
# by <fdpm>, when given a random group element <x>.
# The lists are updated as a side effect. If a basis
# is found during the execution of this procedure
# then the basis is returned, otherwise 'fail' is
# returned.

  local s,     # the length of our linked sequence
        P,     # change of basis matrix
        Pinv,  # the inverse of P, if it exists
        vsx,   # the vectors vis*x w.r.t. basis vs
        vsh,   # vs*h
        inti,  # the interval of vi*x
        ints,  # interval of a sum of vi*x
        i, j,  # integers
        ih,    # the image of i under h where x = bh
        vsum,  # sum of vectors
        vsumh, # sum of vectors in vsh
        temp,  # a row vector
        mone,  # -One(field)
        b;     # non-zero field element

  s := Length(vs); # Length(us) should be s + 1

  # calc vi*x w.r.t. basis vi: for finding interval vectors
  P := RECOG.ExtendToBasisEchelon(vs, fdpm.dim, fdpm.field);
  ConvertToMatrixRep(P);
  Pinv := P^-1;
  if Pinv = fail then
    return fail;
  else
    vsx := P * x * Pinv;
    ConvertToMatrixRep(vsx);
  fi;

  # Find scalar b and i,j such that x = bh and j = i^h

  # find i <= s such that vix is an interval vector in <vs>
  i := 1;
  inti := RECOG.IsIntervalVector(vsx[i], s);
  while inti = fail and i < s do
    i := i + 1;
    inti := RECOG.IsIntervalVector(vsx[i], s);
  od;

  # check whether we found an i
  if inti <> fail then # we have; now we find the image of i
    ih := fail; # we have not found the image of i yet

    vsum := ShallowCopy(vsx[i]);
    ConvertToVectorRep(vsum);
    # find j s.t. vi*x + ... + vj*x is an interval vector in
    # span of vs
    for j in [i+1..s] do
      AddRowVector(vsum, vsx[j]);

      # find interval (if any) of vsum
      ints := RECOG.IsIntervalVector(vsum, s);

      if ints <> fail then
        # we can find the image of i under h and
        # the scalar b s.t. x = bh for h in H0
        ih := Intersection(inti[2], ints[2]);
        if Length(ih) <> 1 then
          return fail; # won't happen if input group is Sn or An
        else
          ih := ih[1];
        fi;
        if inti[2][1] = ih then
          b := inti[1];
        else
          b := -inti[1];
        fi;
        break; # leave the for loop
      fi;
    od;
    # if we haven't found i^h try another way
    if ih = fail then
      vsum := ShallowCopy(vsx[i]);
      ConvertToVectorRep(vsum);
      # find j s.t. vj*x + ... + vi*x is an interval vector
      for j in [i-1,i-2..1] do
        AddRowVector(vsum, vsx[j]);
        # find interval (if any) of vsum
        ints := RECOG.IsIntervalVector(vsum, s);
        if ints <> fail then # we can find (i+1)^h and so i^h and b
          ih := Difference(inti[2], ints[2]);
          if Length(ih) <> 1 then
            return fail; # only happens when group not rep. of Sn or An
          else
            ih := ih[1];
          fi;
          if inti[2][1] = ih then
            b := inti[1];
          else
            b := -inti[1];
          fi;
          break; # leave the for loop
        fi;
      od;
      # check we have found ih
      if ih = fail then
        return fail; # if we have found it now we never will
      fi;
    fi;
  else # look for i < s such that vi*x + v(i+1)*x is an interval vector
    i := 1;
    temp := ShallowCopy(vsx[i]);
    ConvertToVectorRep(temp);
    AddRowVector(temp, vsx[i+1]);
    inti := RECOG.IsIntervalVector(temp, s);
    while inti = fail and i < s - 1 do
      i := i + 1;
      temp := ShallowCopy(vsx[i]);
      ConvertToVectorRep(temp);
      AddRowVector(temp, vsx[i+1]);
      inti := RECOG.IsIntervalVector(temp, s);
    od;
    # check whether we found an i
    if inti <> fail then # we have; now we find the image of i
      ih := fail; # we have not found the image of i yet

      # we only try this for i <= s - 2
      if i = s - 1 then
        vsum := ShallowCopy(vsx[i]);
        ConvertToVectorRep(vsum);
        AddRowVector(vsum, vsx[i+1]);
        # find j s.t. vi*x + v(i+1)^x + ... + vj*x is an interval vector
        for j in [i+2..s] do
          AddRowVector(vsum, vsx[j]);
          # find interval (if any) of vsum
          ints := RECOG.IsIntervalVector(vsum, s);
          if ints <> fail then # we can find i^h and b
            ih := Intersection(inti[2], ints[2]);
            if Length(ih) <> 1 then
              return fail; # only when group not rep. of Sn or An
            else
              ih := ih[1];
            fi;
            if inti[2][1] = ih then
              b := inti[1];
            else
              b := -inti[1];
            fi;
            break; # leave the for loop
          fi;
        od;
      fi;

      # if we haven't found ih try another way
      if ih = fail then
        vsum := ShallowCopy(vsx[i]);
        ConvertToVectorRep(vsum);
        AddRowVector(vsum, vsx[i+1]);
        # find j s.t. vj*x + ... + vi*x + v(i+1)*x is an interval vector
        for j in [i-1,i-2..1] do
          AddRowVector(vsum, vsx[j]);
          # find interval (if any) of vsum
          ints := RECOG.IsIntervalVector(vsum, s);
          if ints <> fail then # we can find (i+1)^h and so i^h and b
            ih := Difference(inti[2], ints[2]);
            if Length(ih) <> 1 then
              return fail; # only when group not rep. of Sn or An
            else
              ih := ih[1];
            fi;
            if inti[2][1] = ih then
              b := inti[1];
            else
              b := -inti[1];
            fi;
            break; # leave the for loop
          fi;
        od;
        # check we have found ih
        if ih = fail then
          return fail; # if we have found it now we never will
        fi;
      fi;
    else
      return fail;
    fi;
  fi;
  # found ih and b

  # calc -1 in field, for use with AddRowVector
  mone := -One(fdpm.field);

  # calc vi*h w.r.t. basis vs
  vsx := b^-1 * vsx;
  # calc vi*h not w.r.t. basis vs
  vsh := vs * b^-1*x;
  ConvertToMatrixRep(vsh);

  # extend linked sequence
  vsum := ShallowCopy(vsx[i]);
  ConvertToVectorRep(vsum);
  vsumh := ShallowCopy(vsh[i]);
  ConvertToVectorRep(vsumh);
  for j in [i+1..s] do
    # calc vi*h + v(i+1)*h + ... + vj*h w.r.t to basis vs
    AddRowVector(vsum, vsx[j]);
    # calc vi*h + v(i+1)*h + ... + vj*h w.r.t. to standard basis
    AddRowVector(vsumh, vsh[j]);
    if RECOG.IsIntervalVector(vsum,s) = fail then
      # vsum is not an interval vector so vsumh is an interval
      # vector not in the span of vs
      temp := ShallowCopy(vsumh);
      ConvertToVectorRep(temp);
      AddRowVector(temp, us[ih]);
      Add(us, temp); # us[s+2] := vi*h + ... + vj*h + us[ih]

      temp := ShallowCopy(us[s+2]);
      ConvertToVectorRep(temp);
      AddRowVector(temp, us[s+1], mone);
      Add(vs, temp); # vs[s+1] := us[s+2] - us[s+1]

      s := s + 1;
      # if vs and us span the fully deleted permutation module
      if s = fdpm.dim then
        return [vs, us{[2..s+1]}];
      fi;
    fi;
  od;

  if i <> 1 then
    # vsum = v1*h + ... + v(i-1)*h
    vsum := ShallowCopy(vsx[1]);
    ConvertToVectorRep(vsum);
    for temp in [2..i-1] do
      AddRowVector(vsum, vsx[temp]);
    od;

    vsumh := ShallowCopy(vsh[1]);
    ConvertToVectorRep(vsumh);
    for temp in [2..i-1] do
      AddRowVector(vsumh, vsh[temp]);
    od;

    j := 0;
    repeat
      if RECOG.IsIntervalVector(vsum, s) = fail then
        # vsum is an interval vector not in the span of vs
        temp := ShallowCopy(us[ih]);
        ConvertToVectorRep(temp);
        AddRowVector(temp, vsumh, mone);
        Add(us, temp);

        temp := ShallowCopy(us[s+2]);
        ConvertToVectorRep(temp);
        AddRowVector(temp, us[s+1], mone);
        Add(vs, temp);
        s := s + 1;
        if s = fdpm.dim then
          # return vs and us if they span the fully deleted permutation
          # module. Note: us[1] = u1 = 0
          ConvertToMatrixRep(vs);
          return [vs, us{[2..s+1]}];
        fi;
      fi;
      j := j + 1;
      # calc vj*h + ... + v(i-1)*h
      AddRowVector(vsum, vsx[j], mone);
      AddRowVector(vsumh, vsh[j], mone);
    until j = i - 1;
  fi;

  # we have not found a basis for the fully deleted permutation
  # module yet
  return fail;
end;

## Functions for finding the permutation and scalar represented
## by a matrix given the vectors u_2,...,u_(n-delta+1)

RECOG.PositionsNot := function(list, elem)
# PositionsNot(<list>, <elem>) returns a
# list of all the positions in <list> whose
# value is not <elem>.
  local pos, posList, zero;

  # find position of first element <> elem
  posList := [];
  pos := PositionNot(list, elem);

  # find subsequent positions
  while pos <= Length(list) do
    Add(posList, pos);
    pos := PositionNot(list, elem, pos);
  od;

  return posList;
end;

RECOG.ExpectedForm := function(row, fdpmDim, nAmbig)
# ExpectedForm(<row>, <fdpmDim>, <nAmbig>) checks
# that <row> is of the form b*(u_ix - u_1x)
# for some b and {ix, 1x}; if so either [b, [ix, 1x]] is
# returned or [-b, [1x, ix]] is returned.

  local posNonZero, # the positions of row whose values
                    # are non-zero
        posNotB,    # the positions of row whose values
                    # are not equal to b
        b;          # a (non-zero) field element

  # find the non-zero positions of row
  posNonZero := RECOG.PositionsNot(row, Zero(row[1]));

  if Length(posNonZero) = 1 then
    # if only one position is non-zero then
    # 1x = 1 or ix = 1.
    return [row[posNonZero[1]], [posNonZero[1] + 1, 1]];
  elif Length(posNonZero) = 2 then
    # check row = [..b..-b..] for some b
    if row[posNonZero[1]] = -row[posNonZero[2]] then
      return [row[posNonZero[1]], posNonZero + 1];
    else
      return fail;
    fi;
  elif Length(posNonZero) >= fdpmDim - 1 and nAmbig then # only if delta = 2
    # determine +/- b: find two entries that are the same

    if row[1] = row[2] or row[1] = row[3] then
      b := row[1];
    elif row[2] = row[3] then
      b := row[2];
    else # we have three different field elems when there
         # can be only two
      return fail;
    fi;

    # find positions in row that are not b
    posNotB := RECOG.PositionsNot(row, b);

    if IsEmpty(posNotB) then
      # {ix,1x} = {1,n} so b(u_ix - u_1x) = bu_ix
      return [b, [1, fdpmDim + 2]];
    elif Length(posNotB) = 1 then
      # {ix, 1x} = {j,n} with j <> 1 and
      # row[k] = b for k <> j - 1 and row[j-1] = 2b
      if row[posNotB[1]] = 2*b then
        return [b, [posNotB[1]+1, fdpmDim + 2]];
      fi;
    else # there are three different field elements in row
      return fail;
    fi;
  else # wrong number positions with non-zero entries
    return fail;
  fi;
end;

RECOG.FindPermutation := function(rs, fdpm)
# FindPermutation(<rs>, <fdpmDim>) returns the scalar
# and permutation associated with a given matrix. If
# the matrix is b*x (for some scalar b) then <rs> contains
# the row vectors ui*b*x (where ui = e1 - ei) written
# with respect to the vectors ui. If the matrix is not
# a representation of a permutation then fail is
# returned.

  local perm,     # a permutation
        permList, # the image list of the perm represented
        r,        # a row
        oneIm,    # the image of 1 under the permutation
        imgsA,    # image of ui under bx
        imgsB,    # image of uj under bx
        FindB,    # function to determine b from image of ui
        b,        # the scalar that the matrix represents
        pts;      # a list of images of points under a permutation

  FindB := function(pmb, imgs);
    # input is b, [u_ix, 1x] or
    # -b and [1_x, u_ix]
    if oneIm = imgs[1] then
      return -pmb;
    else
      return pmb;
    fi;
  end;

  # determine +/- b and [1x,2x]
  imgsA := RECOG.ExpectedForm(rs[1], fdpm.dim, fdpm.nAmbig);
  # determine +/- b and [1x,3x]
  imgsB := RECOG.ExpectedForm(rs[2], fdpm.dim, fdpm.nAmbig);

  if imgsA <> fail and imgsB <> fail then
    # determine 1x
    oneIm := Intersection(imgsA[2], imgsB[2]);
    if Length(oneIm) = 1 then
      oneIm := oneIm[1];
    else
      return fail;
    fi;
    permList := [oneIm];
    # determine b
    b := CallFuncList(FindB, imgsA);
  else
    return fail;
  fi;

  # build up permList by looking at rs[i] = u_(i+1)x (w.r.t to basis
  # us) for i = 2,...,n-delta

  for r in rs do
    # check whether rs[i] in is an expected form
    imgsB := RECOG.ExpectedForm(r, fdpm.dim, fdpm.nAmbig);
    if imgsB = fail then
      return fail;
    else # rs[i] is in an expected form so imgsB[2] = [1x, (i+1)x]
      pts := Difference(imgsB[2], [oneIm]);
      # check (i+1)x has been defined uniquely and b is correct
      if Length(pts) = 1 and b = CallFuncList(FindB, imgsB) then
        Append(permList, pts);
      else
        return fail;
      fi;
    fi;
  od;

  # convert permList into permutation
  # if delta = 2 then n will appear in permList but Length(permList) = n - 1
  # so we need to append the missing point to permList
  Append(permList, Difference([1..Maximum(permList)], permList));
  perm := PermListList([1..Length(permList)], permList);
  if perm = fail then
    return fail;
  fi;

  return [b, perm];
end;

## The main function that puts all the above together to
## recognise our matrix group:

RECOG.RecogniseFDPM := function(group, field, eps)
# RecogniseFDPM(<group>, <field>, <eps>) is an example
# of using the algorithm described in ' ' to recognise
# a matrix group representation of An or Sn acting on
# their fully deleted permutation module. It actually computes
# data to apply RECOG.FindPermutation.
  local fdpm,    # a record containing information on
                 # the fully deleted permutation module
        g,       # group element representing 3-cycle or double trans
        v,       # a vector from a linked basis
        k,       # a counter
        vs,      # a linked sequence of vectors
        us,      # the alterate basis
        uvs,     # output of CompleteBasis
        cob,     # change of basis matrix, to the basis u_i
                 # for i = 2,...,n-delta+1
        cobi,    # inverse matrix
        mgens;   # the matrix generators

  # construct matrix group
  mgens := GeneratorsOfGroup(group);

  # information on the fully deleted permutation module
  fdpm := rec( field     := field,
               fieldChar := Characteristic(field),
               dim       := DimensionOfMatrixGroup(group),
               nAmbig    := (DimensionOfMatrixGroup(group) + 2) mod
                              Characteristic(field) = 0
             );

  # check the dimensions allow for the possibility that group is a
  # representation of An or Sn on its fully deleted permutation module
  if (fdpm.dim + 1) mod fdpm.fieldChar = 0 then
    return fail;
  fi;

  Info(InfoFDPM, 2, "Searching for 3-cycle or double-transposition.");

  # find 3-cycle or double transposition
  if fdpm.fieldChar = 3 then
    # check fdpm.dim is largest for IsPreDoubleTransposition to
    # work
    if fdpm.dim < 6 then
      ErrorNoReturn( "This function only works for matrix groups of dimension",
                     " at least 6 over a field of this characteristic.");
      return fail;
    fi;
    # search for double transpositions
    g := RECOG.IterateWithRandomElements(
             m -> RECOG.ConstructDoubleTransposition(m, fdpm),
             RECOG.LogRat(eps^-1, 2)*(RootInt(fdpm.dim + 2) + 1)*41,
                              # 1/0.0249 < 41
             group);
  else
    # check fdpm.dim is largest for IsPre3Cycle to work
    if fdpm.dim < 4 then
      ErrorNoReturn( "This function only works for matrix groups of dimension",
                     " at least 4 over a field of this characteristic.");
      return fail;
    fi;
    # search for a 3-cycle
    g := RECOG.IterateWithRandomElements(
             m -> RECOG.Construct3Cycle(m, fdpm),
             RECOG.LogRat(eps^-1, 2)*(RootInt(fdpm.dim+2,3) + 1)*15,
                              # 1/0.07 < 15
             group);
  fi;
  # Note: when the field characteristic is >= 5 we could search
  # for both 3-cycles and double transpositions. However we would still
  # require about as many random element selections as if we searched
  # only for 3-cycles and, if we found a double transposition, we would
  # require many more random element selections for MoreBasisVectors.
  # This is especially important when group is not a representation of
  # An or Sn.

  # check we found a 3-cycle or double transposition
  if g = fail then
    Info(InfoFDPM, 2, "Could not find 3-cycle or double-transposition.");
    return fail;
  fi;

  if g.order = 3 then
    Info(InfoFDPM, 2, "Found 3-cycle.");
  else
    Info(InfoFDPM, 2, "Found double-transposition.");
  fi;

  # find first basis vector
  v := RECOG.FindBasisElement(g, group, eps, fdpm);
  if v = fail then
    Info(InfoFDPM, 2, "Could not find basis element.");
    return fail;
  fi;

  Info(InfoFDPM, 2, "Found first basis element.");

  # extend basis
  if g.order = 3 then
    vs := RECOG.IterateWithRandomElements(
              m -> RECOG.MoreBasisVectors(m, g, v, fdpm),
              34*RECOG.LogRat(eps^-1, 2)*RECOG.LogRat(fdpm.dim + 2, 2),
                       # 1/0.03 < 34
              group);
  else
    vs := RECOG.IterateWithRandomElements(
              m -> RECOG.MoreBasisVectors(m, g, v, fdpm),
              2000*RECOG.LogRat(eps^-1, 2)*RECOG.LogRat(fdpm.dim + 2, 2),
              group);
  fi;

  if vs = fail then
    Info(InfoFDPM, 2, "Could not find linked sequence of vectors.");
    return fail;
  fi;

  Info(InfoFDPM, 2, "Found linked sequence of vectors.");

  # complete basis

  # compute start of alternate basis
  us := [Zero(vs[1])];
  for k in [1..Length(vs)] do
    Add(us, us[k] + vs[k]);
  od;
  ConvertToMatrixRep(us);

  uvs := RECOG.IterateWithRandomElements(
             m -> RECOG.FindBasis(m, vs, us, fdpm),
             RECOG.LogRat(fdpm.dim + 2, 2)*(  RECOG.LogRat(eps^-1, 2)
                                      + RECOG.LogRat(fdpm.dim + 2, 2)),
             group);

  if uvs = fail then
    Info(InfoFDPM, 2, "Could not complete basis.");
    return fail;
  fi;

  Info(InfoFDPM, 2, "Found change of basis matrix.");

  # determine permutations and scalars: uvs[2] contains the
  # change of basis matrix that takes group elements into
  # our prefered form
  cob := uvs[2];
  ConvertToMatrixRep(cob);
  cobi := cob^-1;
  if cobi = fail then
    return fail;
  fi;
  return rec( cob := cob, cobi := cobi, fdpm := fdpm );
end;
