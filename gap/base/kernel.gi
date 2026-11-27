#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This file's authors include Sergio Siccha.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Implementation of recog methods
##
#############################################################################

# Helper function for FindKernelRandom and RecogniseGeneric.
# Generate `n` random kernel elements for `ri` and return a boolean. If
# `doVerification` is `false`, then add the kernel elements directly to `gensN(ri)`.
# Otherwise, ask the kernel node to write the random kernel elements as SLPs in
# the kernel node's nice generators - we call this "verification of the kernel"
# - and only add a random kernel element to `gensN(ri)`, if it was not possible
# to write it as an SLP.
# The return value is `fail`, iff computing an SLP for a random element of the
# group behind the image node of `ri` failed. This indicates, that something
# went wrong during recognition of the image.
# If computing SLPs in the image node worked, then:
# - if `doVerification` is `true`, return whether the kernel could be verified,
# - if `doVerification` is `false`, return `true`.
BindGlobal( "GenerateRandomKernelElementsAndOptionallyVerifyThem",
  function(ri, n, doVerification)
    local gens, verificationSuccess, x, s, y, z, i;
    gens := gensN(ri);
    verificationSuccess := true;
    # We generate a random element of the kernel as the quotient of a random
    # element and the preimage of its image under the homomorphism.
    for i in [1 .. n] do
        # Finding kernel generators and immediate verification must use
        # different random elements! This is ensured by using the same stamp
        # in both situations.
        x := RandomElm(ri, "GenerateRandomKernelElementsAndOptionallyVerifyThem", true).el;
        Assert(2, ValidateHomomInput(ri, x));
        s := SLPforElement(ImageRecogNode(ri),
                                 ImageElm(Homom(ri), x!.el));
        if s = fail then
            return fail;
        fi;
        y := ResultOfStraightLineProgram(s, ri!.pregensfacwithmem);
        z := x^-1*y;
        if isone(ri)(z) or ForAny(gens, x -> isequal(ri)(x, z)) then
            continue;
        fi;
        if not doVerification or SLPforElement(KernelRecogNode(ri), z!.el) = fail then
            Add(gens, z);
            verificationSuccess := not doVerification;
        fi;
    od;
    return verificationSuccess;
  end );

InstallGlobalFunction( ImmediateVerification,
  function(ri)
    local verified;
    verified := GenerateRandomKernelElementsAndOptionallyVerifyThem(
        ri,
        RECOG_NrElementsInImmediateVerification,
        true
    );
    if verified = fail then
        ErrorNoReturn("Very bad: image was wrongly recognised ",
                      "and  we found out too late");
    fi;
    if verified = true then return true; fi;
    # Now, verified = false.
    Info(InfoRecog,2,
         "Immediate verification: found extra kernel element(s)!");
    if FindKernelFastNormalClosure(ri,5,5) = fail then
        ErrorNoReturn("Very bad: image was wrongly recognised ",
                      "and  we found out too late");
    fi;
    Info(InfoRecog,2,"Have now ",Length(gensN(ri)),
         " generators for kernel.");
    return false;
  end );

InstallGlobalFunction( FindKernelRandom,
  function(ri,n)
    Info(InfoRecog,2,"Creating ",n," random generators for kernel.");
    return GenerateRandomKernelElementsAndOptionallyVerifyThem(ri, n, false);
  end );

InstallGlobalFunction( FindKernelDoNothing,
  function(ri,n1,n2)
    return true;
  end );

InstallGlobalFunction(RECOG_HandleSpecialCaseKernelTrivialAndMarkedForImmediateVerification,
  function(ri)
    # Due to the design decision that trivial kernels are not represented via
    # recognition nodes with size one but via the value `fail`, we need to
    # employ a bit of a hack.
    # Since the responsible method findgensNmeth(ri) only found trivial
    # generators the list gensN(ri) is empty. Thus KernelRecogNode(ri) would be
    # set to fail.
    # However, since immediateverification(ri) is set to true, we need
    # to double-check now, whether the kernel indeed is trivial. Since
    # KernelRecogNode(ri) is not bound yet, we cannot use the function
    # ImmediateVerification. Instead, we call FindKernelFastNormalClosure.
    Info(InfoRecog, 2, "Found only trivial generators for the kernel but the ",
         "kernel is marked for immediate verification. Hence we call ",
         "FindKernelFastNormalClosure.");
    if fail = FindKernelFastNormalClosure(
        ri,
        RECOG_NrElementsInImmediateVerification,
        RECOG_FindKernelFastNormalClosureStandardArgumentValues[2]
    ) then
        ErrorNoReturn("Very bad: image was wrongly recognised ",
                      "and  we found out too late");
    fi;
  end );

# Returns a random subproduct of <a>, a nonempty list of group elements, or of
# GeneratorsOfGroup(<a>) if <a> is a group (which may have no generators):
# each element is chosen independently with probability 1/2, and the chosen
# ones are multiplied in list order. A trivial product is redrawn unless all
# elements are trivial. The optional record <opt> may set
#   RandomSource: the random source, default GlobalMersenneTwister
#   IsOne:        the identity test, default IsOne; e.g. IsOneProjective
# By Lemma 2.3.2 in <Cite Key="Ser03"/>, the product lies outside a given
# proper subgroup K of the group generated by <a> with probability at least
# 1/2. Redrawing trivial products cannot lower this, as K contains them.
InstallGlobalFunction( RandomSubproduct, function(a, opt...)
    local rs, isone, one, list, prod, g;

    rs := GlobalMersenneTwister;
    isone := IsOne;
    if Length(opt) = 1 then
        opt := opt[1];
        if IsBound(opt.RandomSource) then
            rs := opt.RandomSource;
        fi;
        if IsBound(opt.IsOne) then
            isone := opt.IsOne;
        fi;
    elif Length(opt) > 1 then
        ErrorNoReturn("usage: RandomSubproduct( <a>[, <opt>] )");
    fi;

    if IsGroup(a) then
        one := One(a);
        list := GeneratorsOfGroup(a);
    elif IsList(a) then
        if Length(a) = 0 or
            not IsMultiplicativeElementWithInverse(a[1]) then
            ErrorNoReturn("<a> must be a nonempty list of group elements");
        fi;
        one := One(a[1]);
        list := a;
    else
        ErrorNoReturn("<a> must be a group or a nonempty list of group elements");
    fi;

    # Each round is trivial with probability at most 1/2 (take K trivial),
    # so this takes at most 2 rounds on average.
    repeat
        prod := one;
        for g in list do
            if Random( rs, [ true, false ] ) then
                prod := prod * g;
            fi;
        od;
        if not isone(prod) then
            return prod;
        fi;
    until ForAll(list, isone);
    return prod;
end );

# Computes randomly (it might underestimate) the normal closure of <list>
# under conjugation by <G>. <G> can be a group containing <list> or a
# list of generators of such a group. The positive integer <n> controls how
# many new conjugates are computed.
# The error probability can be determined by following Theorem 2.3.9 in
# <Cite Key="Ser03"/>.  According to Lemma 2.3.8, if <G> has 4 or more
# generators, then as long as the result does not generate the full normal closure
# of <list> under <G>, the probability that a conjugate is not contained
# in the group generated by the result is >= 1/4.
InstallGlobalFunction( FastNormalClosure , function( G, list, n )
  local list2, grpgens, fewGenerators, repetitions, randlist, conjugators, i, c;
  if not IsPosInt(n) then
    ErrorNoReturn("<n> must be a positive integer but is ", n);
  fi;
  if IsEmpty(list) then
    return [];
  fi;
  list2 := ShallowCopy(list);
  if IsGroup(G) then
    grpgens := GeneratorsOfGroup(G);
  else
    grpgens := G;
  fi;
  if (IsGroup(G) and HasIsAbelian(G) and IsAbelian(G))
      or (IsGroup(G) and HasIsCyclic(G) and IsCyclic(G))
      or Length(grpgens) = 1 then
    return list2;
  fi;
  fewGenerators := Length(grpgens) <= 3;
  if fewGenerators then
    repetitions := 3 * n;
  else
    repetitions := 6 * n;
  fi;
  for i in [1..repetitions] do
    if Length(list2)=1 then
      randlist := list2[1];
    else
      randlist := RandomSubproduct(list2);
    fi;
    if IsOne(randlist) then
      continue;
    fi;
    # for short generator lists, conjugate with all generators
    if fewGenerators then
      conjugators := grpgens;
    else
      conjugators := [RandomSubproduct(grpgens)];
    fi;
    for c in conjugators do
      if not IsOne(c) then
        Add(list2,randlist ^ c);
      fi;
    od;
  od;
  return list2;
end );

# FIXME: rename FindKernelFastNormalClosure to indicate that it *also* computes random generators
InstallGlobalFunction( FindKernelFastNormalClosure,
  # Used in the generic recursive routine.
  function(ri,n1,n2)
    if FindKernelRandom(ri, n1) = fail then
        return fail;
    fi;

    SetgensN(ri,FastNormalClosure(ri!.gensHmem,gensN(ri),n2));

    return true;
  end);
