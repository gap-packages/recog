#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Implementation stuff for derived subgroup method
##
#############################################################################

RECOG.DerivedSubgroupMonteCarlo := function(g)
  local gens,gens2,i,x,y;
  gens := [];
  for i in [1..10] do
      x := PseudoRandom(g);
      y := PseudoRandom(g);
      Add(gens,Comm(x,y));
  od;
  gens2 := FastNormalClosure(GeneratorsOfGroup(g),gens,10);
  return GroupWithGenerators(gens2);
end;

#! @BeginChunk Derived
#! This method computes the derived subgroup, if this has not yet been done
#! by other methods. It then uses the MeatAxe to decide whether
#! the derived subgroup acts irreducibly or not. If it acts reducibly,
#! then we can apply Clifford theory to the natural module. The natural
#! module restricted to the derived subgroup is a direct sum of simple
#! modules. If all the summands are isomorphic, we immediately get either
#! an action of <A>G</A> on blocks or a tensor decomposition. Otherwise,
#! we get an action of <A>G</A> on the isotypic components. Either way,
#! we find a reduction.
#! 
#! If the derived group acts irreducibly, we return <K>false</K> in the current
#! implementation.
#! @EndChunk
FindHomMethodsProjective.Derived :=
  function(ri,G)
    # We assume G to act absolutely irreducible
    local H,a,basis,collf,conjgensG,f,hom,homcomp,homs,homsimg,kro,o,r,subdim;
    f := ri!.field;
    if not IsBound(ri!.derived) then
      ri!.derived := RECOG.DerivedSubgroupMonteCarlo(G);
      ri!.derived_mtx := GModuleByMats(GeneratorsOfGroup(ri!.derived),f);
    fi;
    if ForAll(GeneratorsOfGroup(ri!.derived),IsOneProjective) then
        Info(InfoRecog,2,"Derived subgroup is trivial.");
        return false;
    fi;
    if MTX.IsIrreducible(ri!.derived_mtx) then
        if not MTX.IsAbsolutelyIrreducible(ri!.derived_mtx) then
            # FIXME: Check for field automorphisms:
            return false;
            Error("not yet done");
        fi;
        return false;
    fi;
    collf := MTX.CollectedFactors(ri!.derived_mtx);
    if Length(collf) = 1 then
        if MTX.Dimension(collf[1][1]) = 1 then
            Error("This should never have happened (2), tell Max.");
            # This should have been caught by the triviality test above.
        fi;
        Info(InfoRecog,2,"Restriction to derived subgroup is homogeneous.");
        homs := MTX.Homomorphisms(collf[1][1],ri!.derived_mtx);
        basis := Concatenation(homs);
        ConvertToMatrixRep(basis);
        subdim := MTX.Dimension(collf[1][1]);
        r := rec(t := basis, ti := basis^-1,
                 blocksize := MTX.Dimension(collf[1][1]));
        # Note that we already checked for semilinear, so we know that
        # the irreducible N-submodule is absolutely irreducible!
        # Now we believe to have a tensor decomposition:
        conjgensG := List(GeneratorsOfGroup(G),x->r.t * x * r.ti);
        kro := List(conjgensG,g->RECOG.IsKroneckerProduct(g,r.blocksize));
        if not(ForAll(kro,k->k[1] = true)) then
            Info(InfoRecog,1,"VERY, VERY, STRANGE!");
            Info(InfoRecog,1,"False alarm, was not a tensor decomposition.");
            return false;
        fi;

        H := GroupWithGenerators(conjgensG);
        hom := GroupHomByFuncWithData(G,H,RECOG.HomDoBaseChange,r);
        SetHomom(ri,hom);

        # Hand down information:
        InitialDataForImageRecogNode(ri).blocksize := r.blocksize;
        InitialDataForImageRecogNode(ri).generatorskronecker := kro;
        Add( InitialDataForImageRecogNode(ri).hints,
             rec( method := FindHomMethodsProjective.KroneckerProduct,
                  rank := 4000, stamp := "KroneckerProduct" ) );
        # This is an isomorphism:
        findgensNmeth(ri).method := FindKernelDoNothing;
        return true;
    fi;
    Info(InfoRecog,2,"Using action on the set of homogeneous components",
         " (",Length(collf)," elements)...");
    # Now find a homogeneous component to act on it:
    homs := MTX.Homomorphisms(collf[1][1],ri!.derived_mtx);
    homsimg := BasisVectors(Basis(VectorSpace(f,Concatenation(homs))));
    homcomp := MutableCopyMat(homsimg);
    # FIXME: This will go:
    ConvertToMatrixRep(homcomp);
    TriangulizeMat(homcomp);
    o := Orb(G,homcomp,OnSubspacesByCanonicalBasis,rec(storenumbers := true));
    Enumerate(o);
    a := OrbActionHomomorphism(G,o);
    SetHomom(ri,a);
    Setmethodsforimage(ri,FindHomDbPerm);

    return true;
  end;
