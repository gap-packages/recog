# Recognise a classical simple central quotient from an absolutely irreducible
# matrix group G and its group parameter q.
#
# This file's authors include Till Eisenbrand.
#

# RECOG.RecogniseClassicalGraybox(G,q)

# Input: G is an absolutely irreducible matrix group with a classical simple
#   central quotient in defining characteristic p, q=p^f is its group parameter.
#   The coefficient field of G may be a different finite field of characteristic p.
# Output: A record with name, status and candidates.
# A unique result is "probable", otherwise the status is "inconclusive".
# Names L, U, S, O, O+, O- denote simple quotients.
#
#
# Reference:
# Laszlo Babai, William M. Kantor, Peter P. Palfy and Akos Seress,
# "Black-box recognition of finite simple groups of Lie type by statistics
# of element orders", Journal of Group Theory 5 (2002), no. 4, 383-401.

# TODO: Possible improvements:
#  - Use the concept of "large PPDs" and further ideas from classical group
#    recognition in the natural representation in GAP.
#  - Use the orders of a few random elements to restrict the possible natural
#    degrees, as suggested by Frank Luebeck.
#  - Extend the reuse of computed information, including characteristic
#    polynomials, irreducible factors and projective orders.
#  - Return useful intermediate results, including witnesses for PPD tests.
#  - Derive sample budgets from a requested error bound rather than choosing
#    them heuristically. The current budgets may be unnecessarily large.
#  - Use better names for functions.
#  - Record why each candidate was excluded, distinguishing proven
#    incompatibilities from statistical exclusions.
#  - Benchmark the tests on natural and non-natural representations to identify
#    expensive steps and choose a more efficient testing order.



# Input: sample contains g's characteristic polynomial over GF(Q), its distinct
#   factor degrees and ppds (stored results); k > 0 is the PPD index.
#   data contains p, Q=p^a, a, unipotentBound (a p-power killing the unipotent
#   part) and parts (stored primitive parts). ppds and parts start as [].
# Output: true iff an odd primitive prime divisor of p^k-1 divides the projective
#   order of g, false otherwise. No element order is computed.
RECOG.PPDTest := function(sample, k, data)
    local required, part, exponent, common, x;
    # Reuse the answer if this sample has already been tested for index k.
    if IsBound(sample.ppds[k]) then
        return sample.ppds[k];
    fi;
    sample.ppds[k] := false;

    # A primitive prime r has ord_r(p)=k, hence ord_r(Q)=k/gcd(k,a).
    # An eigenvalue whose order is divisible by r therefore needs a factor
    # degree divisible by required. If none occurs, no power test is needed.
    required := k/Gcd(k,data.a);
    if not ForAny(sample.degrees, e -> e mod required = 0) then
        return false;
    fi;

    # Compute the primitive part once for each k and discard the prime 2.
    # Only its odd prime divisors matter in the subsequent gcd computations.
    if not IsBound(data.parts[k]) then
        part := PrimitivePrimeDivisors(k,data.p).ppds;
        while part mod 2 = 0 do part := part/2; od;
        data.parts[k] := part;
    fi;
    part := data.parts[k] ;
    if part = 1 then
        # No odd ppd exists
        return false;
    fi;
    # A root of a degree-e factor lies in GF(Q^e), so its order divides Q^e-1.
    # The lcm covers the semisimple part; unipotentBound kills the unipotent
    # part. Their product is consequently a multiple of the matrix order.
    if not IsBound(sample.exponent) then
        sample.exponent := data.unipotentBound *
            Lcm(List(sample.degrees, e -> data.Q^e-1));
    fi;
    # Remove ALL powers of the primitive primes from that order multiple.
    # Repeated gcds do this without factoring the exponent. All other prime
    # parts are still killed when g is raised to the remaining exponent.
    exponent := sample.exponent;
    common := Gcd(exponent, part);
    if common = 1 then
        # Even the order multiple has no prime divisor in common with part.
        return false;
    fi;
    while common > 1 do
        exponent := exponent/common;
        common := Gcd(exponent, part);
    od;

    # Compute g^exponent through x^exponent modulo its characteristic polynomial.
    # The retained p-power handles repeated factors. A constant remainder means
    # a scalar matrix, so no tested prime survives in the projective order.
    # A nonconstant remainder means that at least one tested prime survives.
    x := IndeterminateOfUnivariateRationalFunction(sample.polynomial);
    sample.ppds[k] :=  Degree(PowerMod(x,exponent,sample.polynomial)) > 0;
    return sample.ppds[k];
end;

# Input: data contains the group, field parameters and saved samples/results;
#   indices lists the required PPD indices relative to data.p; budget limits
#   the search to the first budget samples. Earlier work is reused.
# Searches for ONE element whose projective order has an odd primitive prime
# divisor of p^k-1 for EVERY k in indices (e.g. both k=3 and k=4).
# Output: true if found; false if not found within the budget (not a proof);
#   fail if p^k-1 has no odd primitive prime divisor for some requested k.
RECOG.FindPPD := function(data, indices, budget)
    local key, search, sample, position, k, found, part, g, pol;
    indices := Set(indices);
    for k in indices do
        part := PrimitivePrimeDivisors(k, data.p).ppds;
        while part mod 2 = 0 do part := part/2; od;
        if part = 1 then
            return fail;              
            # No ordinary PPD exists for this index.
        fi;
    od;
    key := String(indices);
    if not IsBound(data.searches.(key)) then
        data.searches.(key) := rec(checked := 0, witness := fail);
    fi;
    search := data.searches.(key);
    if search.witness <> fail then
        return true;
    fi;
    while search.checked < budget do
        position := search.checked+1;
        if position > Length(data.samples) then
            g := PseudoRandom(data.group);
            pol := CharacteristicPolynomial(data.field,data.field,g);
            sample := rec(polynomial := pol, degrees := Set(Factors(PolynomialRing(data.field),pol),Degree),
                ppds := []);
            Add(data.samples,sample);
        fi;
        sample := data.samples[position];
        search.checked := position;
        found := true;
        for k in indices do
            if RECOG.PPDTest(sample,k,data) then
                AddSet(data.invar,k);
            else
                found := false;
            fi;
        od;
        if found then
            search.witness := position;
            return true;
        fi;
    od;
    return false;
end;

# Input: data as in FindPPD, power in [4,9], additional PPD indices, and a budget.
# Output: true if ONE sampled projective order is divisible by power and by an
#   odd PPD for every index. With indices=[], only divisibility by 4 or 9 matters.
#   Returns false if no witness is found (not a proof of nonexistence), or fail
#   if an additional PPD does not exist. Uses fresh samples and direct orders.
# Used for selected classical cases from Babai, Kantor, Palfy and Seress
# (2002), Section 4.3; these replacements are not ordinary PPDs (Remark 3.3).
RECOG.DistinguishSmallCases := function(data, power, indices, budget)
    local parts, k, part, i, order;
    parts := [];
    for k in indices do
        part := PrimitivePrimeDivisors(k,data.p).ppds;
        while part mod 2 = 0 do part := part/2; od;
        if part = 1 then return fail; fi;
        Add(parts,part);
    od;
    for i in [1..budget] do
        order := RECOG.ProjectiveOrder(PseudoRandom(data.group));
        if order mod power = 0 and ForAll(parts,part -> Gcd(order,part) > 1) then
            UniteSet(data.invar,indices);
            return true;
        fi;
    od;
    return false;
end;

# Prepare PPD tests for the groups returned by RECOG.PossibleDegrees(N,q).
# Return a list of records, one per candidate. N is the given representation
# dimension, while d is the candidate group's natural degree.
# allowed lists possible PPD indices from the group-order factors. Finding
# a PPD index outside this list rules out the candidate.
# testIndices lists the indices to search for. Each k means ppd(k,p), with q=p^f.
# For SL(d,q), d>=4, these are [f*(d-2),f*(d-1),f*d]. For SL(5,3), for example,
# allowed=[1,2,3,4,5] and testIndices=[3,4,5].
# The later searches may find these PPDs in different elements and skip indices
# without primitive prime divisors. This function only prepares the records.
# Input: N > 1 is the representation dimension; q=p^f is the group parameter,
#   which need not equal the size of the matrix field.
# Output: a list of candidate records, identifying small-rank isomorphic cases.
#   Each record contains family, natural degree d, q, f, rank, name,
#   coxeter, splittingMultiplier, allowed and testIndices (PPD index lists),
#   and witnessed, initially false. Candidates are not yet verified groups.
RECOG.ClassicalCandidates := function(N, q)
    local degrees, candidates, family, d, candidate, kind, n, size,
          p, f, rank, h, multiplier, prefix, exponents, indices, i, j, top, names;
    degrees := RECOG.PossibleDegrees(N,q);
    candidates := [];
    names := [];
    p := SmallestRootInt(q);
    for family in RecNames(degrees) do
        for d in degrees.(family) do
            # Use one name for isomorphic small-rank cases, e.g. Sp(2,q)=SL(2,q).
            kind := family;
            n := d;
            size := q;
            if d = 2 and family in ["SU","Sp"] then
                kind := "SL";
            elif family = "Oodd" and d = 3 then
                kind := "SL"; n := 2;
            elif family = "Oodd" and (d = 5 or p = 2) then
                kind := "Sp"; n := d-1;
            elif family = "Oplus" and d = 6 then
                kind := "SL"; n := 4;
            elif family = "Ominus" and d = 6 then
                kind := "SU"; n := 4;
            elif family = "Ominus" and d = 4 then
                kind := "SL"; n := 2; size := q^2;
            fi;
            
            # Sp(4,2) has no simple central quotient.
            if kind = "Sp" and n = 4 and size = 2 then
                continue;
            fi;
            
            f := LogInt(size,p);
            multiplier := 1;
            if kind in ["SL","SU"] then
                rank := n-1; h := n;
                exponents := [2..n];
                prefix := "L";
                if kind = "SU" then
                    prefix := "U"; multiplier := 2;
                    exponents := List(exponents, i -> (-1)^i*i);
                fi;
            elif kind in ["Sp","Oodd"] then
                rank := QuoInt(n,2); h := 2*rank;
                exponents := [2,4..2*rank];
                prefix := "S";
                if kind = "Oodd" then
                    prefix := "O"; multiplier := 2;
                fi;
            else
                rank := n/2; h := 2*rank-2; multiplier := 2;
                exponents := [2,4..2*rank-2];
                if kind = "Oplus" then
                    Add(exponents,rank); prefix := "O+";
                else
                    Add(exponents,-rank); prefix := "O-";
                fi;
            fi;
            # Collect possible PPD indices from the factors q^i-1 or q^(-i)+1.
            indices := [];
            for i in exponents do
                if i > 0 then
                    for j in DivisorsInt(f*i) do
                        AddSet(indices,j);
                    od;
                else
                    # For p^m+1, take divisors of 2*m that do not divide m.
                    for j in DivisorsInt(-2*f*i) do
                        if (-f*i) mod j <> 0 then
                            AddSet(indices,j);
                        fi;
                    od;
                fi;
            od;

            # Take at most the three largest indices.
            top := [];
            j := Length(indices);
            while j > 0 and Length(top) < 3 do
                Add(top,indices[j]);
                j := j-1;
            od;
            Sort(top);

            # Neighbouring unitary degrees can share the largest three indices.
            if kind = "SU" and n mod 2 = 0 then
                if n mod 4 = 0 then
                    AddSet(top,n*f);
                else
                    AddSet(top,n*f/2);
                fi;
            fi;

            candidate := rec(family := kind, d := n, q := size,
                f := f,rank := rank,coxeter := h,splittingMultiplier := multiplier,
                allowed := indices,testIndices := top,witnessed := false,
                name := Concatenation(prefix,String(n),"(",String(size),")"));

            # Add isomorphic small-rank cases only once.
            if not candidate.name in names then
                Add(candidates,candidate);
                Add(names,candidate.name);
            fi;
        od;
    od;

    # Input: two candidates. Output: true if a should be tested before b.
    # Larger PPD indices first; equal maxima are sorted by group name.
    Sort(candidates,function(a,b)
        if Maximum(a.allowed) = Maximum(b.allowed) then
            return a.name < b.name;
        fi;
        return Maximum(a.allowed) > Maximum(b.allowed);
    end);
    return candidates;
end;

# Use the sampled polynomials of data.group to shorten the candidate list.
# The splitting-field bound excludes impossible natural degrees. The second
# filter excludes candidates statistically when their large blocks never appear.
# Input:
#   candidates: records returned by RECOG.ClassicalCandidates.
#   data: shared state with group, field, a (matrix field size p^a), and samples.
#   count: the maximum sample position used by the first filter; existing
#     samples are reused, and sampling stops early at at most one candidate.
# Statistical exclusions use a probability threshold of 1/1000.
# Output: the retained candidate records, in their original order.
#   Extends data.samples as needed. The second filter uses ALL stored samples.
RECOG.RestrictPossibleDegreesByGroup := function(candidates, data, count)
    local i, profile, candidate, remaining, h, degrees, lower,
          indices, d, rank, seen, rho, bound, g, pol, threshold;
    threshold := 1/1000;
    for i in [1..count] do
        if Length(candidates) <= 1 then break; fi;
        if i > Length(data.samples) then
            g := PseudoRandom(data.group);
            pol := CharacteristicPolynomial(data.field,data.field,g);
            profile := rec(polynomial := pol, degrees := Set(Factors(PolynomialRing(data.field),pol),Degree),ppds := []);
            Add(data.samples,profile);
        fi;
        profile := data.samples[i];
        remaining := [];
        for candidate in candidates do
            # Over a common field, degree e becomes e/gcd(e,h).
            # The extra factor 2 for orthogonal groups covers the spin kernel.
            h := candidate.f*candidate.splittingMultiplier;
            h := h/Gcd(h, data.a);
            degrees := List(profile.degrees, e -> e/Gcd(e, h));
            # Sum the maximal prime powers in the lcm, e.g. [6,10] gives 2+3+5.
            lower := Sum(Collected(FactorsInt(Lcm(degrees))), x -> x[1]^x[2]);
            if lower <= candidate.d then
                Add(remaining, candidate);
            fi;
        od;
        candidates := remaining;
    od;
    remaining := [];
    for candidate in candidates do
        # With no compatible factor degree, a large-block PPD was not seen.
        d := candidate.d;
        rank := candidate.rank;
        indices := [];
        if candidate.family = "SL" and d >= 4 then
            indices := List([QuoInt(d,2)+1..d-1], e -> candidate.f*e);
        elif candidate.family = "SU" and d >= 5 then
            indices := Filtered([QuoInt(d,2)+1..d], IsOddInt);
            indices := List(indices, e -> 2*candidate.f*e);
        elif candidate.family in ["Sp", "Oodd", "Oplus", "Ominus"] and rank >= 4 then
            indices := List([QuoInt(rank,2)+1..rank-1], e -> 2*candidate.f*e);
        fi;
        indices := Filtered(indices, k -> not (data.p = 2 and k = 6));
        seen := false;
        for profile in data.samples do
            if ForAny(indices,k -> ForAny(profile.degrees,e -> e mod (k/Gcd(k,data.a)) = 0)) then
                seen := true;
                break;
            fi;
        od;
        if not seen and not IsEmpty(indices) then
            rho := Sum(indices, k -> k/((k+1)*candidate.coxeter));
            bound := (1-rho)^Length(data.samples);
            if bound <= threshold then
                continue;
            fi;
        fi;
        Add(remaining, candidate);
    od;
    return remaining;
end;


# Input: G is an absolutely irreducible matrix group with a classical simple
#   central quotient in defining characteristic p; q=p^f is its group parameter.
#   The coefficient field of G may be a different finite field of characteristic p.
# Output: a record with status, name, candidates and samplesUsed.
#   status="probable" and name is a group name if one witnessed candidate remains;
#   otherwise status="inconclusive" and name=fail. candidates lists the remaining
#   names. samplesUsed counts polynomial samples, excluding the special tests'
#   fresh order samples. The recognition uses statistical exclusions.
RECOG.RecogniseClassicalGraybox := function(G, q)
    local N, F, p, f, data, candidates, candidate, required, k,
          answer, result, m, plus, middle, minus, tests, test, remove, u, has,
          suffix, orders, count, trials, s4, l2, s8, o9, ominus8, indices, power;
    # N is the representation dimension; a candidate's natural degree d may differ.
    # q=p^f is the group parameter, while F is the actual matrix field.
    N := DimensionOfMatrixGroup(G);
    F := FieldOfMatrixGroup(G);
    p := Characteristic(F);
    f := LogInt(q,p);
    candidates := RECOG.ClassicalCandidates(N,q);
    # A p-power >= N kills every unipotent Jordan block.
    u := 1; while u < N do u := u*p;od;
    # Share polynomial samples, search results and observed PPD indices (invar).
    data := rec(group := G, field := F, p := p, q := q, Q := Size(F),
        a := DegreeOverPrimeField(F), unipotentBound := u, samples := [],
        parts := [], searches := rec(), invar := []);
    # First narrow the possible group types using sampled polynomial factor degrees.
    candidates := RECOG.RestrictPossibleDegreesByGroup(candidates,data,30);

    # Search each candidate's required PPD indices separately, largest first.
    # These initial witnesses may come from different elements.
    for candidate in candidates do
        if not candidate in candidates then continue; fi;
        required := Filtered(candidate.testIndices, k -> k >= 2 and PrimitivePrimeDivisors(k,p).ppds > 1);
        # Only a nonempty set of successful tests can confirm a candidate.
        candidate.witnessed := not IsEmpty(required);
        for k in Reversed(required) do
            answer := RECOG.FindPPD(data,[k],
                Maximum(Length(data.samples),7*candidate.d));
            # false excludes statistically; fail leaves the candidate unconfirmed.
            if answer <> true then
                candidate.witnessed := false;
                if answer = false then
                    candidates := Filtered(candidates,c -> c <> candidate);
                fi;
                break;
            fi;
            # Every observed index must be allowed by the candidate's group order.
            candidates := Filtered(candidates,c -> IsSubset(c.allowed,data.invar));
            if not candidate in candidates then break; fi;
        od;
    od;

    # Compare simple quotients: plus=O+(2m+2,q), middle=Sp(2m,q) or O(2m+1,q),
    # minus=O-(2m,q). The two middle families are not separated here.
    # BKPS 4.3/Table 3 distinguishes them by possible combinations in maximal tori.
    for m in Set(candidates,c -> c.rank) do
        plus := Filtered(candidates,c -> c.family = "Oplus" and c.rank = m+1);
        middle := Filtered(candidates,c -> c.family in ["Sp","Oodd"] and c.rank = m);
        minus := Filtered(candidates,c -> c.family = "Ominus" and c.rank = m);
        # Each test is [indices, groups admitting a witness, groups forbidding it].
        # ONE projective element order must contain an odd PPD of p^k-1 for EACH k.
        # Since q=p^f, the factor q^d-1 corresponds to index d*f.
        tests := [];
        if m >= 4 then
            if m mod 2 = 0 then
                # Even m: first separate plus from middle and minus.
                Add(tests,[[m*f,(m+2)*f],plus,Concatenation(middle,minus)]);
                # Then middle from minus; m=4 needs the later OMinus8vsSPvsO test.
                if m > 4 then Add(tests,[[(m-2)*f,(m+2)*f],middle,minus]); fi;
            else
                # Odd m: the same two comparisons, with different PPD pairs.
                Add(tests,[[(m-1)*f,(m+3)*f],plus,Concatenation(middle,minus)]);
                Add(tests,[[(m-1)*f,(m+1)*f],middle,minus]);
            fi;
        elif m = 3 and q > 3 then
            # O+(8,q) versus Sp(6,q) or O(7,q) needs three simultaneous PPDs.
            Add(tests,[[f,2*f,4*f],plus,middle]);
        fi;
        for test in tests do
            # Earlier tests may have removed a whole side of this comparison.
            if not ForAny(test[2],c -> c in candidates) or 
               not ForAny(test[3],c -> c in candidates) then continue; fi;
            # BKPS 4.3 replaces missing odd PPDs by divisibility by 4 or 9.
            # Remove only the replaced index; all remaining conditions still apply.
            indices := test[1];
            power := fail;
            if p = 2 and 6 in indices then
                # No PPD of 2^6-1: require 9 instead. For m=4,q=2 this asks for
                # 5*9 | ord(g), possible in O+(10,2), not Sp(8,2) or O-(8,2).
                power := 9; indices := Difference(indices,[6]);
            elif p > 3 and 1 in indices and IsPrimePowerInt(p-1) then
                # Fermat p: p-1 is a power of 2, so replace index 1 by 4.
                power := 4; indices := Difference(indices,[1]);
            elif p > 2 and 2 in indices and IsPrimePowerInt(p+1) then
                # Mersenne p: p+1 is a power of 2, so replace index 2 by 4.
                power := 4; indices := Difference(indices,[2]);
            fi;
            # Simultaneous witnesses are rarer; use the empirically chosen budget 7*m^2.
            if power = fail then
                answer := RECOG.FindPPD(data,indices,7*m^2);
            else
                # Require 4/9 AND the remaining PPDs in the same element order.
                answer := RECOG.DistinguishSmallCases(data,power,indices,7*m^2);
            fi;
            if answer = true then remove := test[3];
            elif answer = false then remove := test[2];
            else continue; fi;
            candidates := Filtered(candidates,c -> not c in remove);
        od;
    od;
    candidates := Filtered(candidates,c -> IsSubset(c.allowed,data.invar));

    # Input: a family, natural degree d and group parameter size.
    # Output: true iff that triple occurs in the current candidate list.
    has := function(family, d, size)
        return ForAny(candidates,
            c -> c.family = family and c.d = d and c.q = size);
    end;
    # Only in some cases we need the existing order-based tests.
    # Requires the local lietype.gi fixes for retries and collected orders.
    orders := [];
    count := 1000;
    trials := 10;
    suffix := Concatenation("(",String(q),")");

    # BKPS (2002), Remark 3.3 and Section 4.3: the missing ppd(2,6)
    # is replaced here by 9. L4(4) and S6(4) have such elements;
    # S4(4) and U4(4), respectively, do not. Do not add 6 to data.invar.
    if q = 4 and has("SL",4,q) and has("Sp",4,q) then
        answer := RECOG.DistinguishSmallCases(data,9,[],count);
        if answer = true then
            candidates := Filtered(candidates,c -> c.name <> "S4(4)");
        elif answer = false then
            candidates := Filtered(candidates,c -> c.name <> "L4(4)");
        fi;
    fi;
    if q = 4 and has("Sp",6,q) and has("SU",4,q) then
        answer := RECOG.DistinguishSmallCases(data,9,[],count);
        if answer = true then
            candidates := Filtered(candidates,c -> c.name <> "U4(4)");
        elif answer = false then
            candidates := Filtered(candidates,c -> c.name <> "S6(4)");
        fi;
    fi;

    # S6(2) has elements of projective order divisible by 9; L4(2) does not.
    if q = 2 and has("SL",4,2) and has("Sp",6,2) then
        answer := RECOG.DistinguishSmallCases(data,9,[],count);
        if answer = true then
            candidates := Filtered(candidates,c -> c.name <> "L4(2)");
        elif answer = false then
            candidates := Filtered(candidates,c -> c.name <> "S6(2)");
        fi;
    fi;

    # U4(2) has elements of projective order divisible by 9; L2(4) does not.
    if q = 2 and has("SL",2,4) and has("SU",4,2) then
        answer := RECOG.DistinguishSmallCases(data,9,[],count);
        if answer = true then
            candidates := Filtered(candidates,c -> c.name <> "L2(4)");
        elif answer = false then
            candidates := Filtered(candidates,c -> c.name <> "U4(2)");
        fi;
    fi;

    if q > 2 and has("Sp",4,q) and has("SL",2,q^2) then
        s4 := Concatenation("S4",suffix);
        l2 := Concatenation("L2(",String(q^2),")");
        answer := RECOG.PSLvsPSP(G,[4*f],q,count,trials,orders);
        if answer = s4 then
            candidates := Filtered(candidates,c -> c.name <> l2);
        elif answer = l2 then
            candidates := Filtered(candidates,c -> c.name <> s4);
        fi;
    fi;

    if q = 2 and has("Sp",6,q) and has("Oplus",8,q) then
        answer := RECOG.OPlus82vsS62(G,orders,count);
        if answer = "S6(2)" then
            candidates := Filtered(candidates,c -> c.name <> "O+8(2)");
        elif answer = "O+8(2)" then
            candidates := Filtered(candidates,c -> c.name <> "S6(2)");
        fi;
    fi;

    if q = 3 and has("Oplus",8,q) and (has("Sp",6,q) or has("Oodd",7,q)) then
        answer := RECOG.OPlus83vsO73vsSP63(G,orders,count);
        if answer = "O+8(3)" then
            candidates := Filtered(candidates,c -> not c.name in ["S6(3)","O7(3)"]);
        elif answer = "S6(3)" and has("Sp",6,q) then
            candidates := Filtered(candidates,c -> not c.name in ["O7(3)","O+8(3)"]);
        elif answer = "O7(3)" and has("Oodd",7,q) then
            candidates := Filtered(candidates,c -> not c.name in ["S6(3)","O+8(3)"]);
        fi;
    fi;

    if has("Ominus",8,q) and (has("Sp",8,q) or has("Oodd",9,q)) then
        s8 := Concatenation("S8",suffix);
        o9 := Concatenation("O9",suffix);
        ominus8 := Concatenation("O-8",suffix);
        # Collect projective orders for the final verification in lietype.gi.
        if IsEmpty(orders) then
            orders := Set(List([1..count],
            i -> RECOG.LieTypeOrderFunc(PseudoRandom(G))));
        fi;
        answer := RECOG.OMinus8vsSPvsO(G,8*f,p,f,orders,count,trials);
        if answer = ominus8 then
            candidates := Filtered(candidates,c -> not c.name in [s8,o9]);
        elif answer = s8 and has("Sp",8,q) then
            candidates := Filtered(candidates,c -> not c.name in [o9,ominus8]);
        elif answer = o9 and has("Oodd",9,q) then
            candidates := Filtered(candidates,c -> not c.name in [s8,ominus8]);
        fi;
    fi;
    # If only Sp(2m,q) and O(2m+1,q) remain, use recog's involution test.
    if IsOddInt(q) and Length(candidates) = 2 then
        m := candidates[1].rank;
        if m >= 3 and has("Sp",2*m,q) and has("Oodd",2*m+1,q) then
            # VerifyOrders needs observed projective orders, not an empty list.
            if IsEmpty(orders) then
                orders := Set(List([1..100],
                    i -> RECOG.LieTypeOrderFunc(PseudoRandom(G))));
            fi;
            answer := RECOG.DistinguishSpO(G,m,p,f,orders);
            if ForAny(candidates,c -> c.name = answer) then
                candidates := Filtered(candidates,c -> c.name = answer);
            fi;
        fi;
    fi;
    result := rec(status := "inconclusive", name := fail,
        candidates := List(candidates,c -> c.name), samplesUsed := Length(data.samples));
    if Length(candidates) = 1 and candidates[1].witnessed then
        result.status := "probable";
        result.name := candidates[1].name;
    fi;
    return result;
end;
