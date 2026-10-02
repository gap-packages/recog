# Possible natural dimensions of classical groups, given an absolutely irreducible
# representation of dimension N in defining characteristic and a group parameter q.
#
# This file's authors include Till Eisenbrand.
#
# Input: a representation dimension N > 1 and a prime power q = p^f.
# The parameter q describes the group, not necessarily the coefficient field
# of the representation. Only the defining characteristic p is prescribed.
#
# RECOG.PossibleDegrees(N, q) returns a record of increasing degree lists
# with components SL, SU, Sp, Oodd, Oplus, and Ominus. Each entry d is a
# candidate natural degree for that family, such as d=35 for SL(35,q).
# The natural degree d need not equal the given representation dimension N.
#
# The algorithm collects tabulated degrees and small-degree formulae for
# each type and rank. These are possible dimensions of the tensor factors
# in Steinberg's decomposition, called building-block degrees below.
# It tests whether a product of these degrees equals N within the factor limit.
# If no match is found, complete data exclude the candidate. With incomplete
# data, missing degrees might still give N, so the candidate remains unresolved.
#
# The output may include extra candidates. A retained candidate does not
# guarantee that a representation of dimension N exists for that group.
#
# Data dependencies:
# DEFREPDATA.g supplies degree-indexed cases through dimension 300.
# SmallDegreeTables.g supplies degrees by type and rank, with completeness bounds.
#
# Mathematical reference:
# F. Luebeck, Small degree representations of finite Chevalley groups in
# defining characteristic, LMS Journal of Computation and Mathematics 4
# (2001), 135--169, revised preprint 2016.
# https://www.math.rwth-aachen.de/~Frank.Luebeck/preprints/smdegdefchar_v2.pdf

# Example: N = 595, q = 3.
#
# 1. Initialise the input data and candidate list.
# RECOG.PrepareData computes p=3, f=1 and divisors [1,5,7,17,35,85,119,595].
# It also calls RECOG.Catalogue to collect the degrees described in step 2.
# RECOG.InitialCandidates returns pairs [family,d] in these ranges:
#   SL, SU: d=2,3,...,595       Sp: d=2,4,...,594
#   Oodd: d=3,5,...,595        Oplus: d=6,8,...,594
#   Ominus: d=4,6,...,594.
#
# 2. RECOG.Catalogue collects building-block dimensions for each type and rank.
# DEFREPDATA is indexed by representation dimension. For example,
# DEFREPDATA[35] contains the listed cases of dimension 35.
# The divisors of 595 covered by this file, apart from 1, are 5,7,17,35,85,119.
# RECOG.Catalogue reads those six entries and keeps cases with one highest
# weight, describing a single tensor building block.
# It also reads the tables in SmallDegreeTables for each type and rank.
# From both sources, it keeps only degrees allowed at p=3 that divide 595.
# Follow ["SL",35], of type A34. DEFREPDATA[35] contains its natural-module
# degree 35, which is allowed at p=3 and divides 595. There is no A34 web table.
# RECOG.Catalogue therefore stores catalogue.A[34].degrees = [35].
#
# 3. RECOG.CheckCandidate translates a group family and natural degree d
# into the algebraic type and rank needed for the degree tables.
# For example, ["SL",35] uses A34 and ["Sp",34] uses C17.
# It sets the tensor-factor limit to f=1, except for Ominus with d=4.
# That case uses A1 over q^2 and allows 2*f=2 factors.
#
# 4. RECOG.ListedCases looks for dimension 595 directly in DEFREPDATA and
# returns type/rank pairs satisfying the characteristic and tensor-factor limit.
# Here it returns [] because DEFREPDATA ends at dimension 300.
# RECOG.CheckCandidate then calls RECOG.CheckType for steps 5 to 7.
#
# 5. RECOG.AddSmallDegrees supplements the tables with Luebeck's formulae.
# First, RECOG.CheckType calls RECOG.InitialiseCatalogueEntry to create an
# entry if needed. The A34 entry already exists, so its list [35] is kept.
# For A34 at p=3, the four smallest distinct nontrivial degrees of
# 3-restricted irreducible modules are:
#   natural: 35, exterior square: 34*35/2=595,
#   symmetric square: 35*36/2=630, adjoint: 35^2-1=1224.
# Both 35 and 595 divide N. The stored 35 is kept and 595 is added once.
# Thus catalogue.A[34].degrees changes from [35] to [35,595].
# Luebeck's theorem guarantees that these formulae omit no nontrivial
# restricted degree up to floor(34^3/8)=4913. Since 595<=4913, all possible
# building-block degrees needed for N=595 have now been considered for A34.
#
# 6. RECOG.ProductWitness searches for factors from this degree list whose
# product is N, using at most maxFactors factors. Repetitions are allowed.
# For SL(35,3), q=3^1 permits at most one nontrivial Steinberg factor.
# RECOG.ProductWitness(595,[35,595],1,divisors) returns [595]: choosing 35
# alone does not give N, but choosing 595 does. With only [35], it would
# return fail.
#
# 7. RECOG.CheckType uses the search result and the completeness of the data.
# The product [595] keeps ["SL",35] with status "product".
# In contrast, SL(36) uses A35, whose formula degrees at p=3 are
# 36,630,666,1294. None divides 595, and the formulae cover every nontrivial
# restricted degree up to floor(35^3/8)=5359. No missing degree can help,
# so RECOG.CheckType returns "excluded" for SL(36).
# In fact, for SL(d) with d>=18, the formula bound is already at least 595.
# The failed product searches therefore exclude all these d except 34,35,595.
# For A2, the data only cover degrees up to 450. An unlisted degree 595
# cannot be ruled out, so SL and SU retain d=3 with status "unresolved".
# B2 only has coverage through 300, leaving Sp(4) and Oodd(5) unresolved.
# The B2/C2 isomorphism gives Sp(4) the same degree data as Spin(5).
#
# 8. RECOG.PossibleDegrees computes RECOG.InitialCandidates once, checks
# every pair, and groups the retained natural degrees by family.
# RECOG.PossibleDegrees(595,3) returns:
# rec(
#   Ominus := [  ],
#   Oodd := [ 5, 35, 595 ],
#   Oplus := [  ],
#   SL := [ 3, 34, 35, 595 ],
#   SU := [ 3, 34, 35, 595 ],
#   Sp := [ 4, 34 ] )
#

# Store references to the input tables. The algorithm does not modify them.
RECOG.defrep := DEFREPDATA;
RECOG.webTables := SmallDegreeTables;
RECOG.families := ["SL", "SU", "Sp", "Oodd", "Oplus", "Ominus"];


# Return the [type, rank] whose degree data should be used.
# Low-rank isomorphisms share tables, for example C2 uses B2.
# For rank >= 3 in characteristic 2, B_r uses C_r. Other pairs are unchanged.
# Input: base in ["A","B","C","D"], a positive rank, and prime characteristic p.
# Output: the pair [base,rank] to use when looking up representation-degree data.
RECOG.TableType := function(base, rank, p)

    # B1 and C1 use the A1 data.
    if rank = 1 and base in ["B", "C"] then
        return ["A", 1];
    fi;

    # D3 is A3.
    if base = "D" and rank = 3 then
        return ["A", 3];
    fi;

    # B2 and C2 have isomorphic simply connected groups and the same degree sets.
    if rank = 2 and base in ["B", "C"] then
        return ["B", 2];
    fi;

    # In characteristic 2, B_r and C_r have the same degree sets.
    if base = "B" and p = 2 then
        return ["C", rank];
    fi;

    return [base, rank];
end;


# Test whether characteristic p is allowed by a DEFREPDATA entry.
# An integer means "only this prime". [[...]] means "except these primes".
# Input: a characteristic condition from DEFREPDATA and a prime p.
# Output: true if the condition permits p, false otherwise.
RECOG.DefrepCharacteristic := function(condition, p)
    local excludedPrimes;

    if IsInt(condition) then
        return condition = p;
    else
        excludedPrimes := condition[1];
        return not p in excludedPrimes;
    fi;
end;


# Test whether characteristic p is allowed by a SmallDegreeTables entry.
# [] means "all". [2,3] means "only 2 and 3". [-2,-3] means "except 2 and 3".
# Input: a characteristic condition from SmallDegreeTables and a prime p.
# Output: true if the condition permits p, false otherwise.
RECOG.WebCharacteristic := function(condition, p)

    if condition = [] then
        return true;
    elif condition[1] > 0 then
        return p in condition;
    else
        return not (-p in condition);
    fi;
end;


# Return distinct classical type/rank pairs listed for dimension N in characteristic p.
# For q=p^f, maxFactors = 2*f for Ominus with d=4 (type A1 over q^2), else f.
# Keep rows with an allowed characteristic and at most maxFactors listed weights.
# Each listed weight counts as one factor in Steinberg's decomposition.
# The code uses the supplied weights without checking their coordinates.
# For N > 300, return [] because DEFREPDATA has no entries in that range.
# Input: representation dimension N, prime p, and a positive limit maxFactors
#   on the number of tensor factors; uses the table stored in RECOG.defrep.
# Output: distinct [type,rank] pairs satisfying the dimension, characteristic
#   and factor-count conditions, or [] if no entry matches.
RECOG.ListedCases := function(N, p, maxFactors)
    local cases, row, base, rank, numberOfFactors, allowedPrime, dataType;
    cases := [];

    if not IsBound(RECOG.defrep[N]) then
        return cases;
    fi;

    # A row has the form [[type,rank], N, [weights], prime_condition].
    for row in RECOG.defrep[N] do
        base := row[1][1];
        rank := row[1][2];
        numberOfFactors := Length(row[3]);
        allowedPrime := RECOG.DefrepCharacteristic(row[4], p);

        if base in ["A", "B", "C", "D"] and allowedPrime then
            # Steinberg factors must fit into the available Frobenius positions.
            if numberOfFactors <= maxFactors then
                dataType := RECOG.TableType(base, rank, p);
                if not dataType in cases then
                    Add(cases, dataType);
                fi;
            fi;
        fi;
    od;

    return cases;
end;


# Create an empty entry for this type and rank if none exists yet.
# catalogue.(base)[rank] means catalogue.A[rank] when base = "A", and likewise
# for B, C, and D. Existing degrees and bounds are left unchanged.
# degrees is initially empty. RECOG.Catalogue and RECOG.AddSmallDegrees fill it.
# Input: a catalogue with lists A, B, C, D and dataType=[type,rank].
# Output: no return value. Creates the catalogue entry in place if it is missing,
#   with degrees=[] and completeThrough=Length(RECOG.defrep).
RECOG.InitialiseCatalogueEntry := function(catalogue, dataType)
    local base, rank;
    base := dataType[1];
    rank := dataType[2];

    if not IsBound(catalogue.(base)[rank]) then
        catalogue.(base)[rank] := rec(
            degrees := [],
            completeThrough := Length(RECOG.defrep));
             # completeThrough is the dimension up to which the source data
            # cover all building-block degrees. DEFREPDATA covers 1..300.
    fi;
end;


# Collect the possible building-block degrees for this N and p.
# Only divisors of N matter: every factor in a product equal to N must divide N.
# Return a record indexed by type and rank, for example catalogue.A[34].
# Each entry stores degrees dividing N and the completeness bound of its sources.
# Input: target representation dimension N, prime p, and divisors=DivisorsInt(N).
#   Reads RECOG.defrep and RECOG.webTables without modifying either table.
# Output: a new catalogue with lists A, B, C, D indexed by rank. Each populated
#   entry has degrees (distinct nontrivial divisors of N) and completeThrough.
RECOG.Catalogue := function(N, p, divisors)
    local catalogue, b, row, base, rank, dataType,
          name, table, degree, allowedPrime;
    catalogue := rec(A := [], B := [], C := [], D := []);

    # First use the single-factor rows of DEFREPDATA.
    # Rows with several factors are handled by RECOG.ListedCases.
    for b in divisors do
        if b > 1 and IsBound(RECOG.defrep[b]) then
            for row in RECOG.defrep[b] do
                base := row[1][1];
                rank := row[1][2];
                allowedPrime := RECOG.DefrepCharacteristic(row[4], p);

                if base in ["A", "B", "C", "D"] and Length(row[3]) = 1 then
                    if allowedPrime then
                        dataType := RECOG.TableType(base, rank, p);
                        base := dataType[1];
                        rank := dataType[2];
                        RECOG.InitialiseCatalogueEntry(catalogue, dataType);
                        # Add b directly to the stored degree list, without duplicates.
                        AddSet(catalogue.(base)[rank].degrees, b);
                    fi;
                fi;
            od;
        fi;
    od;

    # Add the type-indexed tables. A field such as "A10" identifies type A
    # and rank 10. Each table supplies degrees and a completeness bound.
    for name in RecNames(RECOG.webTables) do
        base := name{[1]};
        rank := Int(name{[2..Length(name)]});

        if base in ["A", "B", "C", "D"] then
            dataType := RECOG.TableType(base, rank, p);
            base := dataType[1];
            rank := dataType[2];
            RECOG.InitialiseCatalogueEntry(catalogue, dataType);
            table := RECOG.webTables.(name);

            # This table covers every building-block degree up to table.bound.
            # Raise completeThrough even if no degree in the table divides N.
            if table.bound > catalogue.(base)[rank].completeThrough then
                catalogue.(base)[rank].completeThrough := table.bound;
            fi;

            # A SmallDegreeTables row is [degree, weight, characteristic_condition].
            for row in table.rows do
                degree := row[1];
                allowedPrime := RECOG.WebCharacteristic(row[3], p);

                if degree > 1 and N mod degree = 0 then
                    if allowedPrime then
                        AddSet(catalogue.(base)[rank].degrees, degree);
                    fi;
                fi;
            od;
        fi;
    od;

    return catalogue;
end;


# Add Luebeck's small-degree formulae for one fixed type and rank l.
# The natural degree is l+1 for type A and 2*l for types C and D.
# The variable names identify natural, exterior-square, symmetric-square and
# adjoint formulae. Their values need not equal the full module dimensions.
# The bound is a completeness guarantee. A known degree above the bound
# does not extend the coverage to all smaller degrees.
# RECOG.InitialiseCatalogueEntry must have created the entry first.
# Input: the catalogue, dataType=[type,rank], target dimension N, prime p,
#   and divisors=DivisorsInt(N). The selected catalogue entry must already exist.
# Output: no return value. Adds suitable formula degrees and raises the
#   completeThrough bound in that entry when the formulae supply more coverage.
RECOG.AddSmallDegrees := function(catalogue, dataType, N, p, divisors)
    local base, l, degrees, bound, b,
          natural, exterior, symmetric, adjoint;
    base := dataType[1];
    l := dataType[2];
    degrees := [];

    if base = "A" and l = 1 then
        # Luebeck, Remark 4.5: all restricted A1 degrees are 1,2,...,p.
        # Degree 1 is omitted because it does not change a product.
        for b in divisors do
            if b > 1 and b <= p then
                Add(degrees, b);
            fi;
        od;
        # All restricted A1 degrees are known, so none up to N is missing.
        bound := N;

    elif l > 11 then
        # Theorem 5.1 / Table 2 applies at rank > 11.
        # Use the displayed characteristic conditions without an additional
        # restricted-weight check, including doubled-weight rows at p=2.
        if base = "A" then
            natural := l+1;
            exterior := l*(l+1)/2;
            symmetric := (l+1)*(l+2)/2;
            adjoint := l^2+2*l;
            if (l+1) mod p = 0 then
                adjoint := adjoint - 1;
            fi;
            degrees := [natural, exterior, symmetric, adjoint];
            bound := QuoInt(l^3, 8);

        elif base = "B" then
            # RECOG.TableType already changed B to C when p=2.
            natural := 2*l+1;
            adjoint := 2*l^2+l;
            symmetric := 2*l^2+3*l;
            if (2*l+1) mod p = 0 then
                symmetric := symmetric - 1;
            fi;
            degrees := [natural, adjoint, symmetric];
            bound := l^3;

        elif base = "C" then
            natural := 2*l;
            exterior := 2*l^2-l-1;
            symmetric := 2*l^2+l;
            if l mod p = 0 then
                exterior := exterior - 1;
            fi;
            degrees := [natural, exterior, symmetric];
            bound := l^3;

        else                            
            # Type D.
            natural := 2*l;
            exterior := 2*l^2-l;
            symmetric := 2*l^2+l-1;
            if p = 2 then
                exterior := exterior - Gcd(2, l);
            fi;
            if l mod p = 0 then
                symmetric := symmetric - 1;
            fi;
            degrees := [natural, exterior, symmetric];
            bound := l^3;
        fi;

    else
        # Other low ranks are handled by the tabulated data.
        return;
    fi;

    # Keep the formula degrees that can be factors of N.
    for b in degrees do
        if b > 1 and N mod b = 0 then
            AddSet(catalogue.(base)[l].degrees, b);
        fi;
    od;

    # The formulae cover every nontrivial restricted degree up to bound.
    # Raise completeThrough if this extends the range already covered.
    if bound > catalogue.(base)[l].completeThrough then
        catalogue.(base)[l].completeThrough := bound;
    fi;
end;


# Express N as a product of at most maxFactors numbers from degrees.
# Repeated factors are allowed. Return their sorted list, or fail.
# divisors contains all divisors of N in increasing order, and degrees are > 1.
#
# factorizations[i] stores a factor list whose product is divisors[i], or fail.
# Product-search example: N=12, degrees=[2,3], maxFactors=3.
# A limit of three factors corresponds to f=3 (q=p^3), except for Ominus d=4.
# Start with [] for 1, then process all remaining divisors in increasing order:
#   divisor          1     2     3       4        6          12
#   stored factors  []    [2]   [3]   [2,2]    [3,2]     [3,2,2]
# At 6, try b=2 first. Since 6/2=3 already has [3], append 2 to obtain [3,2].
# At 12, use 12/2=6 and append 2 to [3,2]. Return the sorted list [2,2,3].
#
# For the same divisor, a shorter factor list can replace a longer one safely:
# both have the same product and allow the same further factors to be appended.
# Repetitions are allowed, and the shorter list uses fewer of the permitted slots.
# Input: a positive target N, allowed integer degrees > 1, a nonnegative factor
#   limit maxFactors, and the increasing list divisors=DivisorsInt(N).
# Output: a sorted factor list with product N and length <= maxFactors, or fail
#   if none exists. Factors may repeat; for N=1 the result is the empty list.
RECOG.ProductWitness := function(N, degrees, maxFactors, divisors)
    local factorizations, divisor, i, m, b, quotientPosition, newFactors;
    factorizations := [];
    for divisor in divisors do
        Add(factorizations, fail);
    od;
    factorizations[1] := [];

    for i in [2..Length(divisors)] do
        m := divisors[i];
        for b in degrees do
            if m mod b <> 0 then
                continue;
            fi;

            # A factor list for m/b can be extended by b to give m.
            quotientPosition := Position(divisors, m/b);
            if factorizations[quotientPosition] = fail then
                continue;
            fi;
            if Length(factorizations[quotientPosition]) >= maxFactors then
                # No room for another factor.
                continue;              
            fi;

            # Concatenation creates a new list, leaving the list for m/b intact.
            newFactors := Concatenation(factorizations[quotientPosition], [b]);
            if factorizations[i] = fail or
               Length(newFactors) < Length(factorizations[i]) then
                factorizations[i] := newFactors;
            fi;
        od;
    od;

    # N is the last divisor, so its factor list is the last entry.
    if Last(factorizations) = fail then
        return fail;
    fi;
    return SortedList(Last(factorizations));
end;


# Check dataType = [type, rank] for dimension N in characteristic p.
# catalogue supplies degrees and completeness bounds for each type and rank.
# cases contains the matches from RECOG.ListedCases for N, p, maxFactors.
# divisors contains all divisors of N, maxFactors limits the product length.
# Return status (listed, product, excluded, unresolved), factors, and coverage bound.
# Input: N, prime p, factor limit maxFactors, dataType=[type,rank], the shared
#   catalogue, cases from RECOG.ListedCases, and divisors=DivisorsInt(N).
# Output: rec(status, factors, completeThrough). status is "listed", "product",
#   "excluded" or "unresolved"; factors is a product witness or fail.
#   The selected catalogue entry is created or supplemented in place.
RECOG.CheckType := function(N, p, maxFactors, dataType, catalogue, cases, divisors)
    local base, rank, factors, status;
    base := dataType[1];
    rank := dataType[2];

    RECOG.InitialiseCatalogueEntry(catalogue, dataType);

    # Extend the degree list with formula values, then search for a product equal to N.
    RECOG.AddSmallDegrees(catalogue, dataType, N, p, divisors);

    factors := RECOG.ProductWitness(N, catalogue.(base)[rank].degrees, maxFactors, divisors);

    if dataType in cases then
        status := "listed";
    elif factors <> fail then
        status := "product";
    elif N <= catalogue.(base)[rank].completeThrough then
        # completeThrough is the dimension up to which the source data cover all
        # building-block degrees. RECOG.Catalogue takes the bounds from DEFREPDATA
        # and SmallDegreeTables. The stored degrees keep only divisors of N.
        # RECOG.AddSmallDegrees may extend it using Luebeck's degree formulae.
        # With N within this bound, the failed product search excludes this type.
        status := "excluded";
    else
        # An unknown degree above completeThrough might still be a factor of N.
        status := "unresolved";
    fi;

    return rec(
        status := status,
        factors := factors,
        completeThrough := catalogue.(base)[rank].completeThrough);
end;


# Build the initial list of classical group families and natural dimensions to test.
# Each pair [family,d] describes a candidate, for example ["SL",10] for SL(10,q).
# For SL and SU, try every d from 2 to N. The other families use the ranges below.
# This step only creates the list. Later functions use representation-degree data
# to decide which candidates can be excluded for the given N and q.
# Input: representation dimension N > 1.
# Output: [family,d] pairs for SL, SU, Sp, Oodd, Oplus and Ominus, grouped by
#   family with increasing natural degrees d. No characteristic test is made here.
RECOG.InitialCandidates := function(N)
    local candidates, family, d, l;
    candidates := [];

    # SL(d,q) and SU(d,q): the lower bound is d.
    for family in ["SL", "SU"] do
        for d in [2..N] do
            Add(candidates, [family, d]);
        od;
    od;

    # Sp has natural degree 2*l and lower bound 2*l.
    for l in [1..QuoInt(N,2)] do
        Add(candidates, ["Sp", 2*l]);
    od;

    # For the odd orthogonal family, d=2*l+1. The representation-dimension
    # bound is only N>=2*l, so d=N+1 must also be considered when N is even.
    for l in [1..QuoInt(N,2)] do
        Add(candidates, ["Oodd", 2*l+1]);
    od;

    for family in ["Oplus", "Ominus"] do
        # P Omega_4^-(q) is PSL(2,q^2). Keep this small-rank alias.
        # Oplus degree 4 is omitted because D2 is not simple.
        if family = "Ominus" then
            Add(candidates, [family, 4]);
        fi;

        if N >= 4 then
            # D3 has spin modules of degree 4, although its natural degree is 6.
            # This explains why l=3 is included even at N=4 and N=5.
            for l in [3..Maximum(3, QuoInt(N,2))] do
                Add(candidates, [family, 2*l]);
            od;
        fi;
    od;

    # Families are already grouped, with increasing d inside each family.
    return candidates;
end;


# Compute p and f from q=p^f, the divisors of N, and the degree
# catalogue once. The resulting record is shared by all candidate checks.
# Input: representation dimension N > 1 and prime power q=p^f.
# Output: a new record with N, q, p, f, divisors=DivisorsInt(N) and catalogue.
RECOG.PrepareData := function(N, q)
    local p, f, divisors, catalogue;

    p := SmallestRootInt(q);
    f := LogInt(q, p);
    divisors := DivisorsInt(N);
    catalogue := RECOG.Catalogue(N, p, divisors);

    return rec(
        N := N,
        q := q,
        p := p,
        f := f,
        divisors := divisors,
        catalogue := catalogue);
end;


# Check whether [family, d] remains a candidate for a representation of degree data.N.
# Here d is the group's natural degree. The given representation may have N <> d.
# Translate the family and d to an algebraic type/rank, then apply RECOG.CheckType.
# Input: candidate=[family,d] from InitialCandidates and data from PrepareData.
# Output: a record with status, factors, completeThrough, family, d, q and
#   factorLimit. The shared data.catalogue may be supplemented during the check.
RECOG.CheckCandidate := function(candidate, data)
    local family, d, base, rank, factorLimit, dataType, cases, result;
    family := candidate[1];
    d := candidate[2];
    factorLimit := data.f;

    if family in ["SL", "SU"] then
        base := "A";
        rank := d-1;
    elif family = "Sp" then
        base := "C";
        rank := d/2;
    elif family = "Oodd" then
        base := "B";
        rank := (d-1)/2;
    elif family = "Ominus" and d = 4 then
        # This group uses the SL(2,q^2) data, hence 2*f factors.
        base := "A";
        rank := 1;
        factorLimit := 2*data.f;
    else                                # The other even orthogonal groups.
        base := "D";
        rank := d/2;
    fi;

    dataType := RECOG.TableType(base, rank, data.p);
    cases := RECOG.ListedCases(data.N, data.p, factorLimit);
    result := RECOG.CheckType(data.N, data.p, factorLimit, dataType, data.catalogue, cases, data.divisors);

    # Add the family, natural degree, group parameter, and factor limit.
    result.family := family;
    result.d := d;
    result.q := data.q;
    result.factorLimit := factorLimit;

    return result;
end;


# Main output: only the possible natural degrees, grouped by family.
# No weights or other representation data are returned.
# RECOG.InitialCandidates visits each family/degree once in increasing order.
# Input: representation dimension N > 1 and group parameter q, a prime power.
# Output: a record with components SL, SU, Sp, Oodd, Oplus and Ominus, each an
#   increasing list of retained natural degrees. Incomplete data leave candidates
#   unresolved, so inclusion does not guarantee existence of a representation.
RECOG.PossibleDegrees := function(N, q)
    local result, data, candidates, candidate, checked;
    result := rec(SL := [], SU := [], Sp := [],
                  Oodd := [], Oplus := [], Ominus := []);
    data := RECOG.PrepareData(N, q);
    candidates := RECOG.InitialCandidates(N);

    for candidate in candidates do
        checked := RECOG.CheckCandidate(candidate, data);
        # Incomplete data give "unresolved", so that group stays in the list.
        if checked.status <> "excluded" then
            Add(result.(checked.family), checked.d);
        fi;
    od;

    return result;
end;
