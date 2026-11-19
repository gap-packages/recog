#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Frank Celler, John Bamberg and Jan De Beule.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##  Computing the sesquilinear form preserved by an absolutely irreducible
##  matrix group, used by the ClassicalForms method in classical.gi.
##
##  Copied from the undocumented ClassicalForms_* functions in lib/recognition.gi
##  and lib/classic.gi of the Forms package 1.3.0 (GPL-2.0-or-later), which
##  Forms keeps only for recog (issue #7).
##
#############################################################################

#############################################################################
##
#F  RECOG.ScalarMultipleFrobenius( <field>, <mat> )
##
RECOG.ScalarMultipleFrobenius := function( F, M )
    local mpol, d, c, I, q, qq, t, a, l, i0, Minv, tM, tMi;

    # compute the characteristic polynomial of <M>
    mpol := CharacteristicPolynomial(M);

    # get the position of the non-zero coefficients
    d := Degree(mpol);
    c := CoefficientsOfUnivariatePolynomial(mpol);

    I := Filtered( [0 .. d],  x -> not IsZero(c[x+1]) );
    q := Size(F);
    qq := Characteristic(F)^(DegreeOverPrimeField(F)/2);

    Minv := M^-1;
    tM := Trace(M); tMi := Trace(Minv)^qq; # Frobenius of trace
    if (IsZero(tM) and not IsZero(tMi)) or
       (not IsZero(tM) and IsZero(tMi)) then
        return false;
    fi;

    # make sure that <d> and <d>-i both occur
    if ForAny( I, x ->  IsZero(c[d-x+1]) )  then
        return false;
    fi;

    Add(I,q-1);
    # we need gcd one in order to get alpha exactly (ignoring +-)
    t := GcdRepresentation(I);
    i0 := I*t;

    if not IsZero(tM) and not IsZero(tMi) then
        return [i0, tM/tMi];
    fi;

    # compute gcd representation
    a:=c[1];
    l:=List([1..Length(I)-1], x ->(a*c[d-I[x]+1]^qq/c[I[x]+1]));

    a:=Product([1..Length(I)-1], x->l[x]^t[x]);
    # Now the scalar $\lambda$ satisfies $\lambda^{i_0}=a$

    # check: $\forall_i: \bar c_{d-i}c_0=c_i\lambda^i$
    if ForAny([1..Length(I)-1],x->l[x]<>a^QuoInt(I[x],i0)) then
        Info( InfoRecog_ClassicalNaming, 2,
              "characteristic polynomial does not reveal scalar" );
        return false;
    fi;

    # compute a square root of <alpha>
    a:=NthRoot(F,a,(qq+1)*i0);
    if a=fail then
        Info( InfoRecog_ClassicalNaming, 2,
              "characteristic polynomial does not reveal scalar" );
        return false;
    fi;
    return [i0,a];
end;


#############################################################################
##
#F  RECOG.GeneratorsWithoutScalarsFrobenius( grp )
##
RECOG.GeneratorsWithoutScalarsFrobenius := function( grp )
    local tries, gens, field, m1, a1, new, i;

    # start with 2 random elements,  at most 10 tries
    tries := 0;
    gens  := [];
    field := FieldOfMatrixGroup(grp);
    while Length(gens) < 2  do
        tries := tries + 1;
        if tries = 11  then return false;  fi;
        m1 := PseudoRandom(grp);
        a1 := RECOG.ScalarMultipleFrobenius(field,m1);
        if IsList(a1) and a1[1]=1 then
            a1:=a1[2];
            Add(gens, m1*a1^-1);
        fi;
    od;
    new := GModuleByMats( gens, field );

    # the module must act absolutely irreducibly
    while not MTX.IsAbsolutelyIrreducible(new)  do
        for i  in [ 1 .. 2 ]  do
            repeat
                tries := tries + 1;
                if tries > 10  then return false;  fi;
                m1 := PseudoRandom(grp);
                a1 := RECOG.ScalarMultipleFrobenius(field,m1);
            until IsList(a1) and a1[1]=1;
            a1:=a1[2];
            Add( gens, m1*a1^-1 );
        od;

        new := GModuleByMats( gens, field );
    od;

    return new;
end;


#############################################################################
##
#F  RECOG.ScalarMultipleDual( <field>, <mat> )
##
RECOG.ScalarMultipleDual := function( F, M )
    local mpol, d, c, z, I, t, a, l, q, i0, Minv;

    # compute the characteristic polynomial of <M>
    mpol := CharacteristicPolynomial(M);

    # get the position of the non-zero coefficients
    d := Degree(mpol);
    c := CoefficientsOfUnivariatePolynomial(mpol);
    z := Zero(F);
    q := Size(F);
    I := Filtered( [ 0 .. d ],  x -> c[x+1] <> z );

    Minv := M^-1;
    if Trace(M) = z and Trace(Minv) <> z or
       Trace(M) <> z and Trace(Minv) = z then
        return false;
    fi;
    # make sure that <d> and <d>-i both occur
    if ForAny( I, x -> not (d-x) in I )  then
        return false;
    fi;

    # we need gcd one in order to get alpha exactly (ignoring +-)
    Add(I,q-1);
    t := GcdRepresentation(I);
    i0 := I*t;

    a:=c[1];
    l:=List([1..Length(I)-1], x ->(a*c[d-I[x]+1]/c[I[x]+1]));

    a:=Product([1..Length(I)-1], x->l[x]^t[x]);
    # Now the scalar $\lambda$ satisfies $\lambda^{i_0}=a$

    # check: $\forall_i: c_{d-i}c_0=c_i\lambda^i
    if ForAny([1..Length(I)-1],x->(l[x]<>a^QuoInt(I[x],i0))) then
        Info( InfoRecog_ClassicalNaming, 2,
              "characteristic polynomial does not reveal scalar" );
        return false;
    fi;

    # compute a square root of <alpha>
    a:=NthRoot(F,a,2*i0);
    if a=fail then
        Info( InfoRecog_ClassicalNaming, 2,
              "characteristic polynomial does not reveal scalar" );
        return false;
    fi;
    return [i0,a];
end;


#############################################################################
##
#F  RECOG.GeneratorsWithoutScalarsDual( grp )
##
RECOG.GeneratorsWithoutScalarsDual := function( grp )
    local tries, gens, field, m1, a1, new, i;

    # start with 2 random elements,  at most 10 tries
    tries := 0;
    gens  := [];
    field := FieldOfMatrixGroup(grp);
    while Length(gens) < 2  do
        tries := tries + 1;
        if tries > 10  then return false;  fi;
        m1 := PseudoRandom(grp);
        a1 := RECOG.ScalarMultipleDual(field,m1);
        if IsList(a1) and a1[1]=1 then
            a1:=a1[2];
            Add(gens, m1*a1^-1);
        fi;
    od;
    new := GModuleByMats( gens, field );

    # the module must act absolutely irreducible
    while not MTX.IsAbsolutelyIrreducible(new)  do
        for i  in [ 1 .. 2 ]  do
            repeat
                tries := tries + 1;
                if tries > 10  then return false;  fi;
                m1 := PseudoRandom(grp);
                a1 := RECOG.ScalarMultipleDual(field,m1);
            until IsList(a1) and a1[1]=1;
            a1:=a1[2];
            Add(gens, m1*a1^-1);
        od;
        new := GModuleByMats( gens, field );
    od;
    return new;
end;


#############################################################################
##
#F  RECOG.Signum2( <field>, <form>, <quad> )
##
##  Computes a base change, seemingly sufficient to see from the changed form
##  what its type is, all for characteristic 2.
##
RECOG.Signum2 := function( field, form, quad )
    local dim, base, avoid, i, d, j, c, k, x, sgn, pol;

    # compute a new basis,  such that the symmetric form is standard
    base :=OneOp(form);
    form:=MutableCopyMat(form);
    avoid := [];
    dim := NrRows(form);
    for i  in [ 1 .. dim-1 ]  do

        # find first non zero entry
        d:=1;
        while d in avoid or IsZero(form[i,d])  do
            d:=d+1;
        od;
        Add(avoid, d);

        # clear all other entries in this row & column
        for j  in [d+1..dim]  do
            c := form[i,j]/form[i,d];
            if c <> Zero(field)  then
                for k  in [ i .. dim ]  do
                    form[k,j] := form[k,j] - c*form[k,d];
                od;
                AddRowVector(form[j],form[d],c);
                AddRowVector(base[j],base[d],c);
            fi;
        od;
    od;

    # reshuffle base
    c := [];
    j := [];
    for i  in [ 1 .. dim ]  do
        if not i in j  then
            k := form[i,avoid[i]];
            Add( c, base[i]/k );
            Add( c, base[avoid[i]] );
            Add( j, avoid[i] );
        fi;
    od;
    base := c;

    # and try to fix the quadratic form (this is not really necessary)
    x   := X(field);
    sgn := 1;
    for i  in [ 1, 3 .. dim-1 ]  do
        c := base[i] * quad * base[i];
        if IsZero(c)  then
            c := base[i+1] * quad * base[i+1];
            if not IsZero(c) then
                AddRowVector(base[i+1],base[i],-c);
            fi;
        else
            j := base[i+1] * quad * base[i+1];
            if IsZero(j)  then
                AddRowVector(base[i],base[i+1],-c);
            else
                pol := Factors(x^2 + x/j + c/j);
                if Length(pol) = 2  then
                    pol:=List(pol,x->-CoefficientsOfUnivariatePolynomial(x)[1]);
                else
                    sgn := -sgn;
                fi;
            fi;
        fi;
    od;
    return sgn;
end;


#############################################################################
##
#F  RECOG.Signum( <field>, <form>, <quad> )
##
RECOG.Signum := function( field, form, quad )
    local sgn, det, sqr;

    # if dimension is odd,  the signum must be 0
    if IsOddInt(NrRows(form))  then
        return [ 0 ];

    # hard case: characteristic is 2
    elif Characteristic(field) = 2  then
        Error( "characteristic must be odd" );
    fi;

    # easy case
    det := DeterminantMat(form);
    sqr := IsEvenInt(LogFFE( det, PrimitiveRoot(field)));
    if IsEvenInt(NrRows(form)*(Size(field)-1)/4)  then
        if sqr  then
            sgn := +1;
        else
            sgn := -1;
        fi;
    else
        if sqr  then
            sgn := -1;
        else
            sgn := +1;
        fi;
    fi;

    return [ sgn, sqr ];
end;


#############################################################################
##
#F  RECOG.QuadraticForm2( <field>, <form>, <gens>, <scalars> )
##
##  <form> is a given bilinear form in characteristic 2, preserved by <gens>
##  modulo <scalars>, this function computes a quadratic form (with <form>
##  as polar form) and preserved by gens (if that is all possible).
##  Note that since the polar form <form> is given, the Gram matrix of
##  the quadratic form is already determined above the diagonal. So only
##  the elements on the diagonal have to be computed.
##
RECOG.QuadraticForm2 := function( field, form, gens, scalars )
    local dim, H, i, j, e, b, y, x, r, l;

    # raise an error if char is not two
    if Characteristic(field) <> 2  then
        Error( "characteristic must be two" );
    fi;

    # construct the upper half of the quadratic form
    H := ZeroOp(form);
    dim := NrRows(form);
    for i  in [ 1 .. dim ]  do
        for j  in [ i+1 .. dim ]  do
            H[i,j] := form[i,j];
        od;
    od;

    # store the linear equations in <e>
    e := [];

    # loop over all generators
    b := [];
    for y  in [ 1 .. Length(gens) ]  do

        # remove scalars
        x := gens[y]*scalars[y]^-1;

        # first the right hand size
        r := x*H*TransposedMat(x)+H;

        # check <r>: it is symmetric if <form> comes from a quadratic form,
        # because H is the upper triangle of <form>
        for i  in [ 1 .. dim ]  do
            for j  in [ i+1 .. dim ]  do
                if not IsZero(r[i,j]+r[j,i]) then
                    Info( InfoRecog_ClassicalNaming, 2,
                          "returning false at symmetry check" );
                    return false;
                fi;
            od;
        od;

        # and now the diagonals
        for i  in [ 1 .. dim  ]  do
            l := [];
            for j  in [ 1 .. dim ]  do
                l[j] := x[i,j]^2;
            od;
            l[i] := l[i]+1;
            Add( b, r[i,i] );
            Add( e, l );
        od;
    od;

    # and return a solution
    e := SolutionMat( TransposedMat(e), b );
    if e <> fail  then
        for i  in [ 1 .. dim ]  do
            H[i,i] := e[i];
        od;
        return ImmutableMatrix(field,H);
    else
        return false;
    fi;
end;


#############################################################################
##
#F  RECOG.QuadraticForm( <field>, <form> )
##
RECOG.QuadraticForm := function( field, form )
    local H, i, j;

    # special case if <p> = 2
    if Characteristic(field) = 2  then
        Error( "characteristic must be odd" );
    fi;

    # use upper half
    H := ZeroOp(form);
    for i  in [ 1 .. NrRows(form) ]  do
        H[i,i] := form[i,i]/2;
        for j  in [ i+1 .. NrRows(form) ]  do
            H[i,j] := form[i,j];
        od;
    od;
    return H;
end;


#############################################################################
##
#F  RECOG.InvariantFormDual( <module>, <dmodule> )
##
RECOG.InvariantFormDual := function( module, dmodule )
    local   hom,  scalars,  form,  iform,  field,  i,  m,  quad,  sgn;

    # <dmodule> acts absolutely irreducible without scalars
    hom := MTX.Homomorphisms( dmodule, DualGModule(dmodule) );
    if 0 = Length(hom)  then
        return false;
    elif 1 < Length(hom)  then
        Error( "module acts absolutely irreducibly but two forms found" );
    fi;
    Info( InfoRecog_ClassicalNaming, 2, "found homomorphism between V and V^*" );

    # make sure that the forms commute with the generators of <module>
    scalars  := [];
    form     := hom[1];
    iform    := form^-1;
    field   :=  MTX.Field(module);
    for i  in MTX.Generators(module)  do
        m := i * form * TransposedMat(i) * iform;
        if not RECOG.IsScalarMat(m)  then
            Info( InfoRecog_ClassicalNaming, 2,
                  "form is not invariant under all generators" );
            return false;
        fi;
        Add( scalars, NthRoot(field,m[1,1],2) );
    od;

    # check the type of form
    if TransposedMat(form) = -form  then
        Info( InfoRecog_ClassicalNaming, 2, "form is symplectic" );
        if Characteristic(field) = 2  then
            quad := RECOG.QuadraticForm2(
                field, form, MTX.Generators(module), scalars );
            if quad = false  then
                return [ "symplectic", form, scalars ];
            elif IsOddInt(MTX.Dimension(module))  then
                Error( "no quadratic form but odd dimension" );
            elif RECOG.Signum2( field, form, quad ) = -1  then
                return [ "orthogonalminus", form, scalars, quad ];
            else
                return [ "orthogonalplus", form, scalars, quad ];
            fi;
        else
            return [ "symplectic", form, scalars ];
        fi;
    elif TransposedMat(form) = form  then
        Info( InfoRecog_ClassicalNaming, 2, "form is symmetric" );
        quad := RECOG.QuadraticForm( field, form );
        if IsOddInt(MTX.Dimension(module))  then
            return [ "orthogonalcircle", form, scalars, quad ];
        else
            sgn := RECOG.Signum( field, form, quad );
            if sgn[1] = -1  then
                return [ "orthogonalminus", form, scalars, quad, sgn[2] ];
            else
                return [ "orthogonalplus", form, scalars, quad, sgn[2] ];
            fi;
        fi;
    else
        Info( InfoRecog_ClassicalNaming, 2, "unknown form" );
        return [ "unknown", "dual", form, scalars ];
    fi;
end;


#############################################################################
##
#F  RECOG.TransposedFrobeniusMat( <mat>, <qq> )
##
RECOG.TransposedFrobeniusMat := function( mat, qq )
    local   i,  j;
    mat:=MutableTransposedMat(mat);
    for i  in [ 1 .. NrRows(mat) ]  do
        for j  in [ 1 .. NrCols(mat) ]  do
            mat[i,j] := mat[i,j]^qq;
        od;
    od;
    return mat;
end;


#############################################################################
##
#F  RECOG.InvariantFormFrobenius( module, fmodule )
##
RECOG.InvariantFormFrobenius := function( module, fmodule )
    local   fro,  hom,  form,  q,  qq,  k,  a,  scalars,  iform,
            field,  i,  m,  j;

    # <fmodule> acts absolutely irreducible without scalars
    fro := SMTX.TwistedDualModule(fmodule);
    hom := MTX.Homomorphisms(fmodule, fro);
    if 0 = Length(hom)  then
        return false;
    elif 1 < Length(hom)  then
        Error( "module acts absolutely irreducibly but two form found" );
    fi;
    Info( InfoRecog_ClassicalNaming, 2,
          "found homomorphism between V and (V^*)^frob" );

    # invariant form might return a scalar multiple of our form
    field    := MTX.Field(module);
    form := hom[1];
    q  := Size(field);
    qq := Characteristic(field)^(DegreeOverPrimeField(field)/2);
    k  := PositionNonZero(form[1]);
    a  := form[1,k] / form[k,1]^qq;
    a := NthRoot(field,a,(1-qq) mod (q-1));
    if a = fail then
        return false;
    fi;
    form := form * a^-1;


    # make sure that the forms commute with the generators of <module>
    scalars  := [];
    iform    := form^-1;
    for i  in MTX.Generators(module)  do
        m := i * form * RECOG.TransposedFrobeniusMat(i,qq) * iform;
        if not RECOG.IsScalarMat(m)  then
            Info( InfoRecog_ClassicalNaming, 2,
                  "form is not invariant under all generators" );
            return false;
        fi;
        Add( scalars, NthRoot(field,m[1,1],qq+1) );
    od;

    # check the type of form
    for i  in [ 1 .. NrRows(form) ]  do
        for j  in [ 1 .. NrRows(form) ]  do
            if form[i,j]^qq <> form[j,i]  then
                Info( InfoRecog_ClassicalNaming, 2, "unknown form" );
                return [ "unknown", "frobenius", form, scalars ];
            fi;
        od;
    od;
    return [ "unitary", form, scalars ];
end;
