#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Maska Law, Alice C. Niemeyer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  This file provides code for recognising a subfamily of large base primitive
##  permutation groups.  To be in that subfamily, a primitive permutation group
##  G on N points must be permutation isomorphic to a subgroup of the product
##  action wreath product G wr S_r, where G is S_n acting on k-sets, and hence
##  N = Binomial(n,k)^r.
##  For a precise description of which groups are recognised by this file
##  confer to the documentation of the function LargeBasePrimitive.
##  This file is based on the article [LNPS06].
##
#############################################################################


DeclareInfoClass( "InfoJellyfish" );
SetInfoLevel( InfoJellyfish, 1 );


#############################################################################
##
#F  NkrGetParameters( <N> )
##
##  Computes all [n,k,r] such that N = Binomial(n,k)^r. Returns those
##  satisfying k*r > 1 and 2*r*k^2 < n (sufficient condition from
##  [BLS97] (Lemma 2.10) that ensures that there is a unique minimal and a
##  unique maximal suborbit of the form which is needed). Note that
##  this last condition can be changed in the last line of the code.

RECOG.NkrGetParameters := function( N )

    local maxr, list, r, k, n, newN, num;

    list:=[];
    maxr:=Gcd(List(Collected(FactorsInt(N)),x->x[2]));
    for r in DivisorsInt(maxr) do
        newN:=RootInt(N,r);
        k:=0;
        repeat
            k:=k+1;
            num:=RootInt(newN*Factorial(k),k);
            for n in [num..num+k-1] do
                if Binomial(n,k)=newN then
                    Add(list, [n,k,r]);
                fi;
            od;
        until Binomial(2*k,k)>newN;
    od;
    #return list;
    return Filtered(list,x-> x[2]*x[3]>1 and x[1]>2*x[2]^2*x[3]);

end;


#############################################################################
##
#F  NkrSchreierTree( <alpha>, <gens>, <gensinv> )
##

RECOG.NkrSchreierTree := function ( alpha, gens, gensinv )

    local sv, stack, i, j, beta, gamma;

    sv := List( [1 .. LargestMovedPoint(gens)], i -> false );
    sv[alpha] := One(gens[1]);

    stack := [alpha];
    i := 1;

    while i <= Length(stack) do
        beta := stack[i];
        for j in [1 .. Length(gens)] do
            gamma := beta^gens[j];
            if sv[gamma] = false then
                sv[gamma] := gensinv[j];
                Add(stack, gamma);
            fi;
        od;
        i := i + 1;
    od;

    return sv;

end;


#############################################################################
##
#F  NkrTraceSchreierTree( <beta>, <sv> )
##

RECOG.NkrTraceSchreierTree := function( beta, sv )

    local o, h;

    if sv[beta] = false then
        return fail;
    fi;

    o := One(sv[beta]);
    h := One(sv[beta]);
    while sv[beta] <> o do
        h := h * sv[beta];
        beta := beta^sv[beta];
    od;

    return h;

end;


#############################################################################
##
#F  NkrOrbitsOfStabiliser( <alpha>, <sv>, <grp> )
##
##  The following function attempts to construct the stabiliser in <G>
##  of a point <alpha>.

RECOG.NkrOrbitsOfStabiliser := function ( alpha, sv, grp )

    local  NextGeneratorStabiliser, N, gens, i, orbs;

    NextGeneratorStabiliser := function( alpha, sv, grp )
        local g;
        g := PseudoRandom( grp );
        return g * RECOG.NkrTraceSchreierTree( alpha^g, sv );
    end;

    N := LargestMovedPoint( grp );

    gens := [];
    for i in [1 .. Maximum( 4, Int(Log(N,2)/2) )] do
        Add( gens, NextGeneratorStabiliser( alpha, sv, grp ) );
    od;

    orbs := OrbitsPerms( gens, Difference( [1..N], [alpha] ) );

    return orbs;

end;


#############################################################################
##
#F  FirstJellyfish( <alpha>, <svalpha>, <gammaalpha>, <deltaalpha>,
##                  <G>, <n>, <k>, <r> )
##
##  The following function attempts to construct a jellyfish, namely the
##  set of all points whose i-th component contains the letter l, for
##  some fixed i in [1..r] and l in [1..n].
##  A jellyfish has size (n-1 choose k-1)*(n choose k)^(r-1).
##
##  The set of points used to construct the jellyfish are returned for
##  use later as an identifier.

RECOG.FirstJellyfish := function( alpha, svalpha, gammaalpha, deltaalpha,
                            G, n, k, r )

    local beta, g, deltabeta, gams, jellyfish, I, gamma, deltagamma, idjf;

    # we need a point <beta> in <gammaalpha> : best to choose random
    # <beta> in <gammaalpha> since <gammaalpha> is small
    # wlog : assume <alpha> and <beta> differ in component 1 and the
    # letter x satisfies x in <beta>[1] and not x in <alpha>[1]
    beta := Random( gammaalpha );
    g := RECOG.NkrTraceSchreierTree( beta, svalpha );
    if g = fail then
        Info(InfoJellyfish,2,"Schreier tracing failed");
        return fail;
    else g := g^-1;
    fi;

    # use <g> to obtain the longest <G>_<beta>-orbit
    deltabeta := List( deltaalpha, i -> i^g );

    # <gams> will be those points <gamma> such that
    # (a)  <gamma>[i] is disjoint from <alpha>[i] for i >= 1;
    # (b)  <gamma>[1] meet <beta>[1] is x.
    gams := Difference( deltaalpha, deltabeta );

    # the domain <D> of all points
    jellyfish := [1..LargestMovedPoint(G)];

    # for each <gamma> in <gams>, we will remove from <D> those points
    # in deltagamma, leaving the jellyfish on x in component 1

    # we can calculate some small number <I> to determine how many
    # points in <gams> are enough, up to some acceptable probability
    I := 4*k*r;
    # <idjf> will record those <gamma> used to construct the jellyfish
    idjf := [ ];
    while I>0 and Size(jellyfish)>Binomial(n-1,k-1)*Binomial(n,k)^(r-1) do
        I := I - 1;
        gamma := Random( gams );
        g := RECOG.NkrTraceSchreierTree( gamma, svalpha );
        if g = fail then
            Info(InfoJellyfish,2,"Schreier tracing failed - 2");
            return fail;
        else g := g^-1;
        fi;
        deltagamma := List( deltaalpha, i -> i^g );
        Add( idjf, gamma );
        jellyfish := Difference( jellyfish, deltagamma );
    od;

    if I = 0 and Size(jellyfish)>Binomial(n-1,k-1)*Binomial(n,k)^(r-1)
        then Info(InfoJellyfish,2,"gammas ran out for ",[n,k,r]);
        return fail;
    elif Size(jellyfish) < Binomial(n-1,k-1)*Binomial(n,k)^(r-1)
        then Info(InfoJellyfish,2,"too small set remained");
        return fail;
    fi;

    return [ jellyfish, Set(idjf) ];

end;


#############################################################################
##
#F  GetAllJellyfish( <jellyfish>, <idjf>, <G>, <n>, <k>, <r> )
##
##  The following function takes a jellyfish <jellyfish> and constructs
##  n*r jellyfish by building up the <G>-orbit of <jellyfish>, since <G>
##  is transitive on jellyfish. The order in which the jellyfish are
##  constructed (as images of some previous jellyfish) determines the
##  number in [1..n*r] that it represents. This correspondence is recorded
##  in the table <T>, the rows of which represent the points and contain
##  the numbers of the jellyfish containing that point.
##
##  Each jellyfish is identified by a subset of its tentacles : the size
##  of these identifying subsets is determined by the number of points
##  <gamma> in Difference( <deltaalpha>, <deltabeta> ) originally needed
##  to construct the first jellyfish. These identifying subsets are also
##  returned for use in constructing more efficiently the permutation
##  corresponding to a given group element.

RECOG.GetAllJellyfish := function( jellyfish, idjf, G, n, k, r )

    local HaveSeen, T, seen, orb, i, top, cnt, gens, jf, id, im, mm, g;

    # if one jellyfish contains the identifying tentacles of another
    # jellyfish, then the two jellyfish are equal

    HaveSeen := function( jellyfish )
        local s;
        for s in seen do
            if IsSubset(jellyfish,s) then
                return true;
            fi;
        od;
        return false;
    end;

    T := List( [1..LargestMovedPoint(G)], i -> [ ] );

    seen := [ idjf ];

    orb := [ rec(jf:=jellyfish,id:=idjf) ];

    for i in jellyfish do
        Add( T[i], 1 );
    od;

    top := 1;
    cnt := 1;

    gens := GeneratorsOfGroup( G );

    while top > 0 do
        jf := orb[top].jf;
        id := orb[top].id;
        for g in gens do
            im := OnSets( jf, g );
            mm := OnSets( id ,g );
            if not HaveSeen(im) then
                cnt := cnt + 1;
                for i in im do
                    Add( T[i], cnt );
                od;
                Add( seen, mm );
                orb[top] := rec(jf:=im,id:=mm);
                top := top + 1;
            fi;
        od;
        top := top - 1;
    od;

    if Length( seen ) <> n*r then
        return fail;
    fi;

    return [ T, seen ];

end;


#########################################################################
##
#F OtherGetAllJellyfish( <jellyfish>, <idjf>, <G>, <n>, <k>, <r> )
##
## A variant of GetAllJellyfish.
##

# FIXME: unused?
RECOG.OtherGetAllJellyfish:=function ( jellyfish, idjf, G, n, k, r )

    local  HaveSeen, T, seen, orb, i, g, gens, cnt, pnt, jf, id, img, mm;

    HaveSeen := function( jellyfish )
        local s;
        for s in seen do
            if IsSubset(jellyfish,s) then
                return true;
            fi;
        od;
        return false;
    end;

    T := List( [1..LargestMovedPoint(G)], i -> [ ] );
    seen := [ idjf ];
    orb := [ rec(jf:=jellyfish,id:=idjf) ];

    for i in jellyfish do
        Add( T[i], 1 );
    od;

    gens := GeneratorsOfGroup( G );
    cnt := 1;

    for pnt in orb do
        jf := pnt.jf;
        id := pnt.id;
        for g in gens do
            img := OnSets( jf, g );
            mm := OnSets( id ,g );
            if not HaveSeen(img) then
                cnt := cnt + 1;
                for i in img do
                    Add( T[i], cnt );
                od;
                Add( orb, rec(jf:=img,id:=mm) );
                Add( seen, mm );
            fi;
        od;
    od;

    if Length( seen ) <> n*r then
        return fail;
    fi;

    return [ T, seen ];

end;


#########################################################################
##
#F AllJellyfish( <G> )
##
## This is the main function.
##
## Note re: the shortest orbit and the longest orbit of <G>_<alpha> :
## (i) the shortest orbit consists of those points in Omega for which
## the k-sets in each of r-1 components are identical to the k-sets of
## <alpha> in those r-1 components and for which the k-set in the
## remaining component meets the k-set of <alpha> in that component in
## k-1 letters. It has size (k choose k-1)*(n-k)*r. Notation: gammaalpha.
## (ii) the longest orbit consists of those points in Omega for which
## the k-set in each component is disjoint from the k-set in the same
## component of <alpha>. It has size (n-k choose k)^r. Notation: deltaalpha.

RECOG.AllJellyfish := function( G )

    local N, D, gens, gensinv, i, g, alpha, svalpha, alphaorbs, sizes,
          s, l, params, p, n, k, r, jellyfishone, alljellyfish;

    N := LargestMovedPoint(G);
    params := RECOG.NkrGetParameters( N );
    if IsEmpty(params) then
        return NeverApplicable;
    fi;

    D := [ 1 .. N ];

    gens := ShallowCopy( GeneratorsOfGroup(G) );
    gensinv := List( gens, g -> g^-1 );
    for i in [1 .. LogInt(N,10)] do
        g := PseudoRandom(G);
        Add( gens, g );
        Add( gensinv, g^-1 );
    od;

    alpha := 1;  # alpha:=Random( [1..LargestMovedPoint(G)] );
    svalpha := RECOG.NkrSchreierTree( alpha, gens, gensinv );
    alphaorbs := RECOG.NkrOrbitsOfStabiliser( alpha, svalpha, G );

    sizes := List( alphaorbs, i -> Length(i) );
    s := Minimum( sizes );
    l := Maximum( sizes );
    if Length(Filtered(sizes,i->i=s)) > 1 or
       Length(Filtered(sizes,i->i=l)) > 1 then
        Info(InfoJellyfish,2,"no unique max or min sized G_alpha orbit");
        return TemporaryFailure;
    fi;
    s := alphaorbs[ Position(sizes,s) ]; # shortest <G>_<alpha>-orbit
    l := alphaorbs[ Position(sizes,l) ]; # longest <G>_<alpha>-orbit

    for p in params do
        n := p[1]; k := p[2]; r := p[3];
        if Size(s) = Binomial(k,k-1) * (n-k) * r and
           Size(l) = Binomial(n-k,k)^r then
            jellyfishone := RECOG.FirstJellyfish(alpha,svalpha,s,l,G,n,k,r);
            if jellyfishone <> fail then
                Info(InfoJellyfish,2,"found jellyfish for ",p);
                alljellyfish := RECOG.GetAllJellyfish( jellyfishone[1],
                                 jellyfishone[2], G,n,k,r );
                if alljellyfish <> fail then
                    return alljellyfish;
                fi;
            fi;
        else
            Info(InfoJellyfish,2,
        "couldn't find orbits of correct size for n=",n," k=",k," r=",r);
        fi;
    od;

    Info(InfoJellyfish,3,"getting jellyfish failed");
    return TemporaryFailure;

end;


########################################################################
##
#F FindImageJellyfish( <g>, <T>, <seen> )
##
## This function returns the permutation of [1..n*r] corresponding to <g>.
##
## A jellyfish is identified by a subset of its tentacles : the size of
## these identifying subsets is determined by the number of points
## <gamma> in Difference( <deltaalpha>, <deltabeta> ) originally needed
## to construct the first jellyfish. The intersection of the images
## under <g> of the points in an identifying subset determines the image
## of the letter of the jellyfish.

RECOG.FindImageJellyfish := function( g, T, seen )

    local nr, h, i, gams, tmp;

    nr := Length( seen );
    h := List( [1..nr], i -> 0 );

    for i in [1..nr] do
        gams := OnSets( seen[i], g );
        if ForAny( gams, t -> not IsBound(T[t])) then
            return fail;
        fi;
        tmp := Intersection( List( gams, t -> T[t] ) );
        if Length(tmp) = 0 then
            return fail;
        fi;
        h[i] := tmp[1];
    od;

    if Size(Set(h)) <> nr then
        return fail;
    else
        return PermList(h);
    fi;

end;

########################################################################
##
#F  FindHomMethodsPerm.LargeBasePrimitive
##

RECOG.JellyHomFunc := function(data,el)
  return RECOG.FindImageJellyfish(el,data.T,data.seen);
end;

#! @BeginChunk LargeBasePrimitive
#! This method tries to determine whether the input group <A>G</A> is a
#! fixed-point-free large-base primitive group that neither is a symmetric nor an alternating
#! group in its natural action.
#! This method is an implementation of <Cite Key="LNPS06"/>.
#!
#! A primitive group <M>H</M> acting on <M>N</M> points is called <E>large</E> if
#! there exist <M>n</M>, <M>k</M>, and <M>r</M> with
#! <M>N = \{n \choose k\}^r</M>, and up to a permutational isomorphism <M>H</M>
#! is a subgroup of the product action wreath product <M>S_n \wr S_r</M>,
#! and an overgroup of <M>(A_n) ^ r</M> where <M>S_n</M> and <M>A_n</M> act on
#! the <M>k</M>-subsets of <M>\{1, ..., n\}</M>.
#! This algorithm recognises fixed-point-free large primitive groups with
#! <M>r \cdot k > 1</M>
#! and <M>2 \cdot r \cdot k^2 \le n</M>.
#!
#! A large primitive group <M>H</M> of the above type which does have fixed
#! points is handled as follows: if the group <M>H</M> does not know yet that
#! it is primitive, then <Ref Func="ThrowAwayFixedPoints"/> returns
#! <K>NotEnoughInformation</K>. After the first call to
#! <C>LargeBasePrimitive</C>, the group <M>H</M> knows that it is primitive,
#! but since it has fixed points <C>LargeBasePrimitive</C> returns
#! <K>NeverApplicable</K>. Since <Ref Func="ThrowAwayFixedPoints"/> previously
#! returned <K>NotEnoughInformation</K>, it will be called again. Then it will
#! use the new information about <M>H</M> being primitive, and is guaranteed to
#! prune away the fixed points and set up a reduction homomorphism.
#! <C>LargeBasePrimitive</C> is then applicable to the image of that
#! homomorphism.
#!
#! If <A>G</A> is imprimitive then the output is
#! <K>NeverApplicable</K>. If <A>G</A> is primitive then
#! the output is either a homomorphism into the
#! natural imprimitive action of <A>G</A> on <M>nr</M> points with
#! <M>r</M> blocks of size <M>n</M>,  or <K>TemporaryFailure</K>, or
#! <K>NeverApplicable</K> if no parameters <M>n</M>, <M>k</M>, and <M>r</M> as
#! above exist.
#! @EndChunk
BindRecogMethod(FindHomMethodsPerm, "LargeBasePrimitive",
"recognises large-base primitive permutation groups",
rec(validatesOrAlwaysValidInput := true),
function(ri, grp)
    local res,T,seen,imgens,hom;
    if not IsPermGroup(grp) then
        return NeverApplicable;
    fi;
    if not IsPrimitive(grp) then
        return NeverApplicable;
    fi;
    RECOG.SetPseudoRandomStamp(grp,"Jellyfish");
    res := RECOG.AllJellyfish(grp);
    RECOG.SetPseudoRandomStamp(grp,"PseudoRandom");
    if res = NeverApplicable or res = TemporaryFailure then
        return res;
    fi;
    ri!.jellyfishinfo := res;
    T := res[1];
    seen := res[2];
    # Build the homomorphism:
    imgens := List(GeneratorsOfGroup(grp),
                   x->RECOG.FindImageJellyfish(x,T,seen));
    hom := GroupHomByFuncWithData(grp,Group(imgens),RECOG.JellyHomFunc,
                                  rec(T := T,seen := seen));
    SetHomom(ri,hom);

    findgensNmeth(ri).method := FindKernelDoNothing;

    return Success;
end);
