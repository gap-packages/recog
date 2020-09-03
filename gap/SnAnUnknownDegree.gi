# Input: Group G, upper error bound eps, upper degree bound N
#
# The following algorithm constructs a set of possible 3-cycles. It is based
# on the simple observation that the product of two involutions t1, t2, which
# only move one common point, squares to a 3-cycle.
#
# TODO: take care of duplicate candidates?
# Creates and returns a function, here called oneThreeCycleCandidate. The
# function oneThreeCycleCandidate returns one of the following:
# - a three cycle candidate, i.e. an element of G
# - TemporaryFailure, if we exhausted all attempts
# - NeverApplicable, if we found out that G can't be an Sn or An
BindGlobal("ThreeCycleCandidatesIterator",
    function(ri, eps, N)
    local
        # involution
        t,
        # integers, controlling the number of iterations
        M, B, T, C, logInt2N,
        # integer, prime, loop variable
        p,
        # counters
        nrInvolutions, nrTriedConjugates, nrThreeCycleCandidates,
        # helper functions
        tryThreeCycleCandidate, oneThreeCycleCandidate;
    # Step 1: Initialization
    # The current involution t_i
    t := fail;

    # Constants
    # TODO: better iteration over primes
    M := 1;
    p := 3;
    while p <= N do
        M := M * p ^ LogInt(N, p);
        p := NextPrimeInt(p);
    od;
    # FIXME: Probably B can be chosen smaller
    B := Int(Ceil(13 * Log2(Float(N)) * Log2(3 / Float(eps))));
    T := Int(Ceil(3 * Log2(3 / Float(eps))));
    C := Int(Ceil(Float(3 * N * T / 5)));
    logInt2N := LogInt(N, 2);

    # Counters
    # Counts the constructed involutions t_i in steps 2 & 3.
    nrInvolutions := 0;
    # Counts the elements c in step 4 that we use to conjugate the current
    # involution t_i.  We initialize nrTriedConjugates to C such that "steps 2
    # & 3" in tryThreeCycleCandidate immediately construct an involution.
    nrTriedConjugates := C;
    # counts the size of the set Gamma_i in step 4 for the current involution
    # t_i
    nrThreeCycleCandidates := 0;

    # Helper functions
    # tryThreeCycleCandidate returns one of the following:
    # - a three cycle candidate, i.e. an element of G
    # - fail, if the random conjugate c from step 4 and t commute
    # - NeverApplicable, if G can not be an Sn or An
    tryThreeCycleCandidate := function()
        local
            # integer, loop variable
            a,
            # elements, in G
            r, tPower, tPowerOld, c;
        # Steps 2 & 3: New involution
        # Check if we either tried enough conjugates or constructed enough
        # three cycle candidates for the current involution t.
        # If this is the case, we need to construct the next involution
        if nrTriedConjugates >= C or nrThreeCycleCandidates >= T then
            r := RandomElm(ri,"simplesocle",true)!.el;
            a := 0;
            tPower := r ^ M;
            # Invariant: tPower = (r ^ M) ^ (2 ^ a)
            repeat
                a := a + 1;
                tPowerOld := tPower;
                tPower := tPower ^ 2;
            until a = logInt2N or isone(ri)(tPower);
            if a = logInt2N then
                return NeverApplicable;
            fi;
            t := tPowerOld;
            nrInvolutions := nrInvolutions + 1;
            nrTriedConjugates := 0;
            nrThreeCycleCandidates := 0;
        fi;
        # Steps 4 & 5: new three cycle candidate
        # Try to construct a three cycle candidate via a conjugate of t. See
        # the comment above this function.
        nrTriedConjugates := nrTriedConjugates + 1;
        c := t ^ RandomElm(ri,"simplesocle",true)!.el;
        if not isequal(ri)(t * c, c * t) then
            nrThreeCycleCandidates := nrThreeCycleCandidates + 1;
            return (t * c) ^ 2;
        else
            return fail;
        fi;
    end;
    # construct the iterator
    oneThreeCycleCandidate := function()
        local candidate;
        repeat
            if nrInvolutions >= B
                and (nrTriedConjugates >= C or nrThreeCycleCandidates >= T)
            then
                # We are done and were not able to recognize Sn or An.
                return TemporaryFailure;
            fi;
            candidate := tryThreeCycleCandidate();
            if candidate = NeverApplicable then
                return NeverApplicable;
            fi;
        until candidate <> fail;
        return candidate;
    end;
    return oneThreeCycleCandidate;
end);

# ri : recog info record with group G
# c : element of G,
#     should be a 3-cycle
# eps : real number, the error bound
# N : integer, upper bound for the degree of G
#
# Returns a list of elements of G.
#
# If the input is as assumed, then this function returns a list of bolstering
# elements with respect to c.
BindGlobal("BolsteringElements",
function(ri, c, eps, N)
    local result, R, S, prebolsteringElms, i, r, cr, cr2;
    result := [];
    R := Int(Ceil(7 / 4 * Log2(Float(eps ^ -1))));
    S := 7 * N * R;
    prebolsteringElms := [];
    i := 0;
    # find pre-bolstering elements
    while i <= S and Length(prebolsteringElms) <= R do
        r := RandomElm(ri,"simplesocle",true)!.el;
        # test whether r is pre-bolstering
        cr := c ^ r;
        cr2 := c ^ (r ^ 2);
        if not isone(ri)(Comm(cr, c))
                and not isequal(ri)(cr2, c)
                and not isequal(ri)(cr2, c ^ 2)
                and isone(ri)(Comm(cr2, c))
        then
            Add(prebolsteringElms, r);
        fi;
        i := i + 1;
    od;
    # construct bolstering elements
    for r in prebolsteringElms do
        if isone(ri)((c ^ (r * c * r)
                      * c ^ (r * c ^ (r ^ 2) * c)) ^ 3)
        then
            Add(result, c ^ 2 * r);
        else
            Add(result, cr);
        fi;
    od;
    return result;
end);

# ri : recog info record with group G
# g : element of G,
#     should be a cycle matching c
# c : element of G,
#     should be a 3-cycle
# r : element of G
#
# Returns a boolean.
#
# If the input is as assumed, then the supports of c and c^(g^2) have exactly
# one point, say alpha, in common and this function returns whether alpha is a
# fixed point of r.
BindGlobal("IsFixedPoint",
function(ri, g, c, r)
    local
        # respectively c ^ (g ^ i)
        cg, cg2, cg3, cg4,
        # temporary holder of H1, H2
        temp,
        # (sets of) elements of G
        H1, H2, x1, x2, x3,
        # helper function
        commutesWithAtMostOne;
    # Helper function
    commutesWithAtMostOne := function(ri, x, H)
        local nrTrivialComm, h;
        nrTrivialComm := 0;
        for h in H do
            if isone(ri)(Comm(x, h)) then
                nrTrivialComm := nrTrivialComm + 1;
            fi;
            if nrTrivialComm >= 2 then
                return false;
            fi;
        od;
        return true;
    end;
    cg := c ^ g;
    cg2 := cg ^ g;
    cg3 := cg2 ^ g;
    cg4 := cg3 ^ g;
    H1 := [ c ^ 2, c ^ cg, ~[2] ^ cg3, ~[3] ^ cg3, ~[4] ^ cg4 ];
    # Test whether an elm of the set X commutes with at least
    # two elements of H1.
    x1 := c ^ r;
    if not commutesWithAtMostOne(ri, x1, H1) then return false; fi;
    x2 := cg2 ^ r;
    if not commutesWithAtMostOne(ri, x2, H1) then return false; fi;
    x3 := ((cg2 ^ cg3) ^ cg4) ^ r;
    if not commutesWithAtMostOne(ri, x3, H1) then return false; fi;
    # Test whether an elm of the set X commutes with at least
    # two elements of H2.
    H2 := [c, cg, ~[2] ^ cg3, ~[3] ^ cg3, ~[4] ^ cg4];
    if not commutesWithAtMostOne(ri, x1, H2) then return false; fi;
    if not commutesWithAtMostOne(ri, x2, H2) then return false; fi;
    if not commutesWithAtMostOne(ri, x3, H2) then return false; fi;
    return true;
end);

# ri : recog info record with group G
# g : element of G,
#     should be a k-cycle matching c
# c : element of G,
#     should be a 3-cycle
# r : element of G,
#     should have at least one moved point in common with g and should fix at
#     least two moved points of g
# k : integer,
#     should be length of cycle g
#
# Returns fail or a conjugate of r.
#
# W.l.o.g. let g = (1, ..., k) and c = (1, 2, 3).
# If the input is as assumed, then the algorithm returns a conjugate r ^ x such
# that r ^ x fixes the points 1, 2 but not the point 3.
BindGlobal("AdjustCycle",
function(ri, g, c, r, k)
    local
        # list of 4 booleans, is point j fixed point
        F4,
        # smallest fixed point
        f1,
        # second smallest fixed point
        f2,
        # smallest non-fixed point
        m,
        # bool, false if |F| < 2 or |F| = k
        success,
        # integer, loop variable over [1 .. k]
        j,
        # element of G, loop variable
        t,
        # conjugating element
        x;
    # According to the paper we have:
    # F := { 1 \leq j \leq k | IsFixedPoint(g, c ^ (g ^ (j - 3)), r) = true }
    # f1 := smallest number in F
    # f2 := second smallest number in F
    # m := smallest number *not* in F
    # We do not store F explicitely. Instead we store the intersection of F and
    # {1, 2, 3, 4} in the variable F4.
    F4 := [false, false, false, false];
    f1 := fail;
    f2 := fail;
    m := fail;
    t := c ^ (g ^ -3);
    for j in [1 .. k] do
        # invariant: t = c ^ (g ^ (j - 3))
        t := t ^ g;
        if IsFixedPoint(ri, g, t, r) then
            if j <= 4 then
                F4[j] := true;
            fi;
            if f1 = fail then
                f1 := j;
            elif f2 = fail then
                f2 := j;
            fi;
        elif m = fail then
            m := j;
        fi;
        # f1 and f2 not being fail is equivalent to |F| >= 2
        # m not being fail is equivalent to |F| < k
        success := f1 <> fail and f2 <> fail and m <> fail;
        if success then
            if j >= 4 then
                break;
            # 2. Case, we do not need to compute F4[4]
            elif f1 = 1 and f2 = 2 and m = 3 then
                return r;
            fi;
        fi;
    od;
    if not success then
        return fail;
    fi;
    # case distinction on F as in the table of Algorithm 4.20
    # via a decision tree
    if F4[1] then
        if F4[2] then
            # We are in the 1. Case, since the 2. Case is handled during the
            # computation of F4 above.
            x := c ^ ((g * c ^ 2) ^ (m - 3) * c) * c;
        else
            if F4[3] then
                if F4[4] then
                    # 3. Case
                    x := c ^ g;
                else
                    # 4. Case
                    x := (c ^ 2) ^ g;
                fi;
            else
                # 5. Case
                x := c ^ ((g * c ^ 2) ^ (f2 - 3) * c);
            fi;
        fi;
    else
        if F4[2] then
            if F4[4] then
                # 6. Case
                x := c ^ (c ^ g);
            else
                if F4[3] then
                    # 7. Case
                    x := (c ^ 2) ^ (c ^ g);
                else
                    # 8. Case
                    x := c ^ ((g * c ^ 2) ^ (f2 - 3) * c ^ g);
                fi;
            fi;
        else
            if F4[3] then
                # 9. Case
                x := (c ^ 2) ^ ((g * c ^ 2) ^ (f2 - 3)) * c ^ 2;
            else
                # 10. Case
                x := c ^ ((g * c ^ 2) ^ (f2 - 3)) * c ^ ((g * c ^ 2) ^ (f1 - 3));
            fi;
        fi;
    fi;
    return r^x;
end);

# ri : recog info record with group G
# g : element of G,
#     should be a k-cycle matching c
# c : element of G,
#     should be a 3-cycle
# r : element of G,
#     should be a cycle as in the return value of AdjustCycle. If e.g.
#     g = (1, 2, ..., k), then r would be a cycle fixing 1 and 2 and moving 3.
# s : element of group G,
#     should be a storage cycle
# k : integer,
#     should be length of cycle g
# k0 : integer,
#      should be length of cycle r
#
# Returns a list consisting of:
# - gTilde: element of G,
#           should be a cycle matching g
# - sTilde: element of G,
#           should be current storage cycle, since we may call AppendPoints
#           several times and may not have used the last sTilde.
# - kTilde: integer,
#           should be the length of gTilde
#
# The algorithm appends new points to the cycle g. Since g will always be a
# cycle of odd length, new points can only be appended in pairs. We identify
# the point j in {1, ..., k} with the 3-cycle c ^ (g ^ (j - 3)). We store new
# points in the storage cycle sTilde until we have found two different points.
# Then we append these to g.

BindGlobal("AppendPoints",
function(ri, g, c, r, s, k, k0)
    local gTilde, sTilde, kTilde, gc2, x, j;
    gTilde := g;
    sTilde := s;
    kTilde := k;
    x := c;
    for j in [1 .. k0 - 1] do
        # invariant: x = c ^ (r ^ j)
        x := x ^ r;
        if isone(ri)(Comm(x, gTilde * c ^ 2)) then
            # If sTilde doesn't already store a point, then store x.
            if isone(ri)(sTilde) then
                sTilde := x;
            fi;
            # Do we now have two different points? If so, append them.
            if not isone(ri)(sTilde) and not isequal(ri)(sTilde, x) then
                kTilde := kTilde + 2;
                gTilde := gTilde * sTilde ^ (x ^ 2);
                sTilde := One(gTilde);
            fi;
        fi;
    od;
    return [gTilde, sTilde, kTilde];
end);

# ri : recog info record with group G
# g : element of G
# p : prime
# Returns whether g is an element of order p.
BindGlobal("IsElmOfPrimeOrder",
function(ri, g, p)
    if not isone(ri)(g) and isone(ri)(g ^ p) then
        return true;
    else
        return false;
    fi;
end);

# ri : recog info record with group G
# c : a 3-cycle of a group G
# x : bolstering element with respect to c
# N : upper bound for degree of G
# returns either fail or a list consisting of:
# - g, cycle matching c
# - k, length of cycle g.
#
# We return fail if one of the following holds:
# - N is not an upper bound for the degree of G
# - c is not a 3-cycle
BindGlobal("BuildCycle",
function(ri, c, x, N)
    local
        # Floor(N / 2)
        N2,
        # min(alpha, beta)
        m,
        # d = c ^ (x ^ (m + 1))
        d,
        # y = c * c ^ x * c ^ (x ^ 2) * ... * c ^ (x ^ m)
        y,
        # is false, if m >= N/2
        isMinInitialized,
        # dx = d ^ x = c ^ (x ^ (m + 2))
        dx,
        # element defined as in the case distinction
        e,
        # d ^ e
        z,
        # z ^ (x ^ 2 * (mDash - 1))
        zxMinus,
        # z ^ (x ^ 2 * (mDash))
        zx,
        # z ^ (x ^ 2 * (mDash + 1))
        zxPlus,
        # integer computed as in Remark 4.9
        mDash,
        # cycle matching c
        g;
    # Here we set m := 0
    N2 := Int(Floor(Float(N) / 2.));
    y := c;
    d := c ^ x;
    isMinInitialized := false;
    for m in [1 .. N2] do
        y := y * d;
        d := d ^ x;
        if not IsElmOfPrimeOrder(ri, d * c, 5) then
            isMinInitialized := true;
            break;
        fi;
    od;
    if not isMinInitialized then
        return fail;
    fi;
    # Case |alpha - beta| = 0
    if isequal(ri)(d, c) or isequal(ri)(d, c ^ 2) then
        return [y, 2 * m + 3];
    fi;
    # Case |alpha - beta| = 1
    dx := d ^ x;
    if not IsElmOfPrimeOrder(ri, dx * c, 5) then
        return [y, 2 * m + 3];
    fi;
    # Case |alpha - beta| >= 2
    # Case distinction on element e
    if IsElmOfPrimeOrder(ri, d * c, 2) then
        # w not in v ^ <x>
        if isone(ri)(Comm(dx, d ^ c)) then
            # Case 4, alpha < beta
            e := (d ^ (x * c)) ^ 2;
        else
            # Case 3, alpha > beta
            e := d ^ (x * c ^ 2);
        fi;
    else
        # w in v ^ <x>
        if isone(ri)(Comm(dx, d ^ c)) then
            # Case 1, alpha > beta
            e := d ^ (x * c);
        else
            # Case 2, alpha < beta
            e := (d ^ (x * c ^ 2)) ^ 2;
        fi;
    fi;
    z := d ^ e;
    # Here we set mDash := 1
    zxMinus := z;
    zx := zxMinus ^ (x ^ 2);
    zxPlus := zx ^ (x ^ 2);
    g := y * zxMinus;
    for mDash in [1 .. N2] do
        if not IsElmOfPrimeOrder(ri, zxPlus, 5) then
            return [g, 2 * mDash + 2 * m + 3];
        fi;
        zxMinus := zx;
        zx := zxPlus;
        zxPlus := zxPlus ^ (x ^ 2);
        g := y * zxMinus;
    od;
    # mDash >= N / 2
    return fail;
end);

# NOTE: Output in paper is reversed.
#
# ri : recog info record with group G
# c : element of G,
#     should be a 3-cycle
# eps : real number, the error bound
# N : integer, upper bound for the degree of G
#
# Returns fail or a list consisting of:
# - g: element of G,
#      should be a k-cycle matching c
# - k: integer,
#      should be length of cycle g.
#
# We return fail if one of the following holds:
# - the list of bolstering elements is too small
# - N is not an upper bound for the degree of G
# - c is not a 3-cycle
BindGlobal("ConstructLongCycle",
function(ri, c, eps, N)
    local g, k, tmp, B, x;
    B := BolsteringElements(ri, c, Float(eps) / 2., N);
    if Length(B) < Int(Ceil(7./4. * Log(2. / Float(eps)))) then
        # the list of bolstering elements is too small
        return fail;
    fi;
    k := 0;
    for x in B do
        tmp := BuildCycle(ri, c, x, N);
        if tmp = fail then
            # One of the following holds:
            # - N is not an upper bound for the degree of G
            # - c is not a 3-cycle
            return fail;
        elif tmp[2] > k then
            g := tmp[1];
            k := tmp[2];
        fi;
    od;
    return [g, k];
end);

# ri : recog info record
# g : cycle matching c
# c : three-cycle
BindGlobal("StandardGenerators",
function(ri, g, c, k, eps, N)
    local s, k0, c2, r, kTilde, gTilde, i, x, m, tmp, cTilde;
    s := One(g);
    k0 := k - 2;
    c2 := c ^ 2;
    r := g * c2;
    kTilde := k;
    gTilde := g;
    for i in [1 .. Int(Ceil(Log(10. / 3.) ^ (-1) * (Log(Float(N)) + Log(1 / Float(eps)))))] do
        x := r ^ RandomElm(ri,"simplesocle",true)!.el;
        m := AdjustCycle(ri, gTilde, c, x, kTilde);
        if m = fail then return fail; fi;
        tmp := AppendPoints(ri, gTilde, c, m, s, kTilde, k0);
        gTilde := tmp[1];
        s := tmp[2];
        kTilde := tmp[3];
        if kTilde > N then return fail; fi;
    od;
    if isone(ri)(s) then
        gTilde := c2 * gTilde;
        cTilde := c;
    else
        kTilde := kTilde + 1;
        gTilde := gTilde * s;
        cTilde := s;
    fi;
    if SatisfiesAnPresentation(ri, gTilde, cTilde, kTilde) then
        return [gTilde, cTilde, kTilde];
    else
        return fail;
    fi;
end);

# UNFINISHED
# currently returns standard gens of An
BindGlobal("RecogniseSnAn",
function(ri, eps, N)
    local T, c, tmp, g, k, n, iterator;
    T := Int(Ceil(Log(1 / Float(eps))));
    repeat
        T := T - 1;
        iterator := ThreeCycleCandidatesIterator(ri, eps, N);
        c := iterator();
        while c <> TemporaryFailure do
            if c = NeverApplicable then return NeverApplicable; fi;
            tmp := ConstructLongCycle(ri, c, 1. / 8., N);
            if tmp = fail then
                c := iterator();
                continue;
            fi;
            g := tmp[1];
            k := tmp[2];
            tmp := StandardGenerators(ri, g, c, k, 1. / 8., N);
            if tmp = fail then
                c := iterator();
                continue;
            fi;
            g := tmp[1];
            c := tmp[2];
            n := tmp[3];
            return [g, c, n];
        od;
    until T = 0;
    return fail;
end);
