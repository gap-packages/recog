gap> START_TEST("goingup.tst");
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# The root elements of RECOG.SL_RootElements, RECOG.Sp_RootElements,
# RECOG.SU_RootElements and RECOG.Omega_RootElements are the elementary
# matrices resp. the root elements they name.
gap> CheckSLRoots := function(n, q)
>     local f, Y, R, i, j, lambda, M;
>     f := GF(q);
>     Y := GeneratorsWithMemory(
>              RECOG.ClassicalStandardGenerators("SL", n, f).all);
>     R := RECOG.SL_RootElements(Y, n, f);
>     for i in [1 .. n] do
>         for j in Difference([1 .. n], [i]) do
>             lambda := Random(f);
>             M := MutableCopyMat(IdentityMat(n, f));
>             M[i, j] := lambda;
>             if StripMemory(RECOG.SL_ElementaryMatrix(R, i, j, lambda)) <> M
>                then
>                 return [i, j, lambda];
>             fi;
>         od;
>     od;
>     return true;
> end;;
gap> ForAll([[2, 3], [3, 4], [4, 9], [5, 2], [6, 25], [7, 27]],
>           c -> CheckSLRoots(c[1], c[2]) = true);
true
gap> FormRootMatrix := function(R, kind, j, lambda, n)
>     local M, c, eps;
>     M := MutableCopyMat(IdentityMat(n, R.f));
>     c := R.conj(lambda);
>     eps := R.eps;
>     if kind = "Lf" then
>         M[1, 2] := lambda;
>     elif kind = "Le" then
>         M[2, 1] := eps * lambda;
>     elif kind = "See" then
>         M[2, 2 * j - 1] := lambda;
>         M[2 * j, 1] := -eps * c;
>     elif kind = "Sff" then
>         M[1, 2 * j] := lambda;
>         M[2 * j - 1, 2] := -eps * c;
>     elif kind = "M1j" then
>         M[1, 2 * j - 1] := lambda;
>         M[2 * j, 2] := -c;
>     else
>         M[2 * j - 1, 1] := lambda;
>         M[2, 2 * j] := -c;
>     fi;
>     return M;
> end;;
gap> CheckFormRoots := function(type, n, q)
>     local f, Y, R, form, kind, j, c, lambda, M;
>     f := GF(q);
>     Y := GeneratorsWithMemory(
>              RECOG.ClassicalStandardGenerators(type, n, f).all);
>     R := RECOG.GoingUpParameters(type).rootElementsOf(Y, n, f);
>     form := RECOG.ClassicalForm(type, n, f);
>     for kind in Filtered(["Lf", "Le", "See", "Sff", "M1j", "Mj1"],
>                          k -> IsBound(R.(k))) do
>         for j in [2 .. n / 2] do
>             # the parameters of Lf and Le satisfy lambda^sigma = -eps lambda
>             c := Random(f);
>             lambda := c;
>             if kind in ["Lf", "Le"] then
>                 lambda := c - R.eps * R.conj(c);
>             fi;
>             M := FormRootMatrix(R, kind, j, lambda, n);
>             if RECOG.FormRestriction(form, M) <> form
>                or StripMemory(RECOG.Form_RootElement(R, kind, j, lambda))
>                   <> M then
>                 return [kind, j, lambda];
>             fi;
>         od;
>     od;
>     return true;
> end;;
gap> ForAll([["Sp", 4, 3], ["Sp", 6, 5], ["Sp", 8, 9], ["Sp", 10, 27],
>            ["SU", 4, 9], ["SU", 6, 25], ["SU", 8, 81], ["SU", 4, 729],
>            ["SU", 4, 16], ["SU", 6, 64], ["SU", 8, 4],
>            ["O+", 6, 3], ["O+", 10, 5], ["O+", 10, 9], ["O+", 18, 27],
>            ["O+", 6, 2], ["O+", 10, 8], ["Sp", 6, 4], ["Sp", 8, 2]],
>           c -> CallFuncList(CheckFormRoots, c) = true);
true

# The eliminations map vectors to the basis vectors they promise, also
# vectors with few nonzero coordinates, which take the rarer branches. For
# orthogonal groups, Q(y) takes the place of beta(y, y)/2, also for q even.
gap> CheckEliminations := function(n, q)
>     local f, e, R, vecs, y, b, type, form, half;
>     f := GF(q);
>     e := IdentityMat(n, f);
>     vecs := Concatenation(e, List([1 .. 20], i -> Random(f^n)),
>                           List([2 .. n], i -> e[i] + e[1]));
>     vecs := Filtered(vecs, y -> not IsZero(y));
>     R := RECOG.SL_RootElements(GeneratorsWithMemory(
>              RECOG.ClassicalStandardGenerators("SL", n, f).all), n, f);
>     for y in vecs do
>         b := RECOG.SL_MapToLast(R, y);
>         if y * b.mat <> e[n] or StripMemory(b.word) <> b.mat then
>             return ["SL", y];
>         fi;
>     od;
>     if IsOddInt(n) then
>         return true;
>     fi;
>     for type in ["Sp", "SU", "O+"] do
>         if type = "SU" and not IsInt(Sqrt(q)) then
>             continue;
>         fi;
>         R := RECOG.GoingUpParameters(type).rootElementsOf(
>                  GeneratorsWithMemory(
>                      RECOG.ClassicalStandardGenerators(type, n, f).all),
>                  n, f);
>         form := RECOG.ClassicalForm(type, n, f);
>         half := y -> RECOG.FormValue(form, y, y) * RECOG.FormHalf(form);
>         if type = "O+" then
>             half := y -> RECOG.FormQuadraticValue(form, y);
>         elif type = "Sp" then
>             half := y -> Zero(f);
>         fi;
>         for y in vecs do
>             b := RECOG.Form_MapToStd(R, y);
>             if y * b.mat <> e[1] + half(y) * e[2]
>                or StripMemory(b.word) <> b.mat then
>                 return [type, y];
>             fi;
>             # an isotropic vector with beta(e_1, y) = 1
>             y := ShallowCopy(y);
>             y[1] := Zero(f);
>             y[2] := One(f);
>             y[1] := -half(y);
>             b := RECOG.Form_MapToF1FixingE1(R, y);
>             if y * b.mat <> e[2] or e[1] * b.mat <> e[1]
>                or StripMemory(b.word) <> b.mat then
>                 return [type, "fixing e_1", y];
>             fi;
>         od;
>     od;
>     return true;
> end;;
gap> ForAll([[4, 3], [5, 4], [6, 5], [8, 9], [4, 25], [6, 81], [4, 2],
>            [6, 4], [8, 16], [4, 16], [6, 64], [8, 4]],
>           c -> CheckEliminations(c[1], c[2]) = true);
true
gap> CheckExpress := function(n, q)
>     local f, R, E;
>     f := GF(q);
>     R := RECOG.SL_RootElements(GeneratorsWithMemory(
>              RECOG.ClassicalStandardGenerators("SL", n, f).all), n, f);
>     E := {i, j, lambda} -> RECOG.SL_ElementaryMatrix(R, i, j, lambda);
>     return ForAll([1 .. 5], function(k)
>         local M;
>         M := PseudoRandom(SL(n, q));
>         return StripMemory(RECOG.SL_ExpressByElementary(M, E, R.one)) = M;
>     end);
> end;;
gap> ForAll([[2, 5], [3, 2], [5, 9]], c -> CheckExpress(c[1], c[2]));
true

# RECOG.GoingUp, started from the standard generators of an embedded
# CL(n,q), of type + for orthogonal groups, returns words for the standard
# generators of CL(d,q) relative to the basis it returns.
gap> CheckGoingUp := function(type, n, d, q)
>     local f, B, init, std, gens, G, res;
>     f := GF(q);
>     B := RandomInvertibleMat(d, f);
>     init := List(RECOG.ClassicalStandardGenerators(
>                      RECOG.ClassicalPrefixType(type), n, f).all,
>                  x -> B^-1 * RECOG.GoingUpEmbed(x, d, f) * B);
>     std := RECOG.ClassicalStandardGenerators(type, d, f).all;
>     gens := Concatenation(init, List(std, x -> B^-1 * x * B));
>     G := GroupWithMemory(Group(gens));
>     res := RECOG.GoingUp(G, type,
>                rec( slp := StraightLineProgram(
>                                [List([1 .. Length(init)], i -> [i, 1])],
>                                Length(gens)),
>                     bas := B, n := n ));
>     return List(ResultOfStraightLineProgram(res.slp, gens),
>                 x -> res.bas * x * res.bas^-1) = std;
> end;;
gap> ForAll([["SL", 2, 3, 7], ["SL", 2, 8, 4], ["SL", 2, 17, 5],
>            ["SL", 2, 12, 9], ["Sp", 4, 6, 3], ["Sp", 4, 14, 5],
>            ["Sp", 4, 20, 9], ["SU", 4, 6, 9], ["SU", 4, 14, 25],
>            ["SU", 4, 20, 9], ["SU", 4, 5, 9], ["SU", 4, 7, 25],
>            ["SU", 4, 15, 81], ["SU", 4, 21, 9], ["SU", 4, 6, 16],
>            ["SU", 4, 5, 16], ["SU", 4, 14, 64], ["SU", 4, 11, 256],
>            ["SU", 4, 20, 4], ["O+", 6, 8, 3], ["O-", 6, 8, 3],
>            ["O", 6, 9, 3], ["O-", 6, 10, 5], ["O", 6, 11, 7],
>            ["O+", 6, 12, 9], ["O-", 6, 14, 3], ["O", 6, 15, 5],
>            ["O+", 6, 20, 3], ["O-", 6, 22, 7], ["O", 6, 21, 9],
>            ["O+", 6, 8, 2], ["O-", 6, 10, 4], ["O+", 6, 12, 8],
>            ["O-", 6, 14, 2], ["O-", 6, 20, 16], ["Sp", 4, 14, 4],
>            ["Sp", 4, 10, 16]],
>           c -> CallFuncList(CheckGoingUp, c));
true

# RECOG.SL_DirectGoingUp does the same from SL(2,q) in one step
gap> CheckDirectGoingUp := function(d, q)
>     local f, B, init, std, gens, G, res;
>     f := GF(q);
>     B := RandomInvertibleMat(d, f);
>     init := List(RECOG.ClassicalStandardGenerators("SL", 2, f).all,
>                  x -> B^-1 * RECOG.GoingUpEmbed(x, d, f) * B);
>     std := RECOG.ClassicalStandardGenerators("SL", d, f).all;
>     gens := Concatenation(init, List(std, x -> B^-1 * x * B));
>     G := GroupWithMemory(Group(gens));
>     res := RECOG.SL_DirectGoingUp(G,
>                rec( slp := StraightLineProgram(
>                                [List([1 .. Length(init)], i -> [i, 1])],
>                                Length(gens)),
>                     bas := B, n := 2 ));
>     return List(ResultOfStraightLineProgram(res.slp, gens),
>                 x -> res.bas * x * res.bas^-1) = std;
> end;;
gap> ForAll([[3, 2], [3, 3], [3, 4], [4, 2], [4, 3], [4, 9], [5, 5], [6, 7],
>            [9, 2], [10, 2], [12, 3], [13, 4], [20, 5], [21, 8], [8, 25],
>            [9, 49], [7, 211], [6, 1024], [5, 65537]],
>           c -> CallFuncList(CheckDirectGoingUp, c));
true

# RECOG.Sp_DirectGoingUp does the same from Sp(4,q), q odd
gap> CheckSpDirectGoingUp := function(d, q)
>     local f, B, init, std, gens, G, res;
>     f := GF(q);
>     B := RandomInvertibleMat(d, f);
>     init := List(RECOG.ClassicalStandardGenerators("Sp", 4, f).all,
>                  x -> B^-1 * RECOG.GoingUpEmbed(x, d, f) * B);
>     std := RECOG.ClassicalStandardGenerators("Sp", d, f).all;
>     gens := Concatenation(init, List(std, x -> B^-1 * x * B));
>     G := GroupWithMemory(Group(gens));
>     res := RECOG.Sp_DirectGoingUp(G,
>                rec( slp := StraightLineProgram(
>                                [List([1 .. Length(init)], i -> [i, 1])],
>                                Length(gens)),
>                     bas := B, n := 4 ));
>     return List(ResultOfStraightLineProgram(res.slp, gens),
>                 x -> res.bas * x * res.bas^-1) = std;
> end;;
gap> ForAll([[4, 3], [6, 3], [6, 5], [8, 3], [8, 9], [10, 3], [10, 7],
>            [12, 5], [14, 3], [16, 27], [20, 3], [22, 5], [30, 3],
>            [8, 25], [6, 49], [6, 121], [6, 2187], [6, 65537]],
>           c -> CallFuncList(CheckSpDirectGoingUp, c));
true

# also if it has to try all the g h, and another random g
gap> data := RECOG.Sp_DirectGoingUpData;;
gap> skip := 0;;
gap> RECOG.Sp_DirectGoingUpData := function(arg)
>     skip := skip - 1;
>     if skip >= 0 then
>         return "skipped";
>     fi;
>     return CallFuncList(data, arg);
> end;;
gap> ForAll([1 .. 2 * RECOG.Sp_DirectGoingUpCheapTries + 3], function(n)
>     skip := n;
>     return CheckSpDirectGoingUp(8, 5);
> end);
true
gap> RECOG.Sp_DirectGoingUpData := data;;

# RECOG.SU_DirectGoingUp does the same from SU(4,q0), q = q0^2, d even
gap> CheckSUDirectGoingUp := function(d, q)
>     local f, B, init, std, gens, G, res;
>     f := GF(q);
>     B := RandomInvertibleMat(d, f);
>     init := List(RECOG.ClassicalStandardGenerators("SU", 4, f).all,
>                  x -> B^-1 * RECOG.GoingUpEmbed(x, d, f) * B);
>     std := RECOG.ClassicalStandardGenerators("SU", d, f).all;
>     gens := Concatenation(init, List(std, x -> B^-1 * x * B));
>     G := GroupWithMemory(Group(gens));
>     res := RECOG.SU_DirectGoingUp(G,
>                rec( slp := StraightLineProgram(
>                                [List([1 .. Length(init)], i -> [i, 1])],
>                                Length(gens)),
>                     bas := B, n := 4 ));
>     return List(ResultOfStraightLineProgram(res.slp, gens),
>                 x -> res.bas * x * res.bas^-1) = std;
> end;;
gap> ForAll([[4, 9], [6, 9], [6, 4], [8, 9], [8, 16], [10, 9], [10, 4],
>            [12, 25], [14, 9], [16, 4], [20, 9], [22, 16], [30, 9],
>            [8, 49], [6, 64], [6, 81], [6, 121], [6, 729], [6, 1024]],
>           c -> CallFuncList(CheckSUDirectGoingUp, c));
true

# RECOG.MinimalPolynomialOfSequence finds the recurrence of order L which
# gives 2n terms from the start 0, ..., 0, 1
gap> CheckRecurrence := function(q, n, L)
>     local f, c, s, k;
>     f := GF(q);
>     c := List([1 .. L], i -> Random(f));
>     s := ListWithIdenticalEntries(2 * n, Zero(f));
>     if L > 0 then
>         s[L] := One(f);
>         for k in [L + 1 .. 2 * n] do
>             s[k] := c * s{[k - L .. k - 1]};
>         od;
>     fi;
>     return RECOG.MinimalPolynomialOfSequence(f, s)
>            = Concatenation(-c, [One(f)]);
> end;;
gap> ForAll([[2, 9, 7], [3, 5, 5], [3, 8, 3], [4, 6, 6], [5, 6, 0],
>            [7, 12, 1], [9, 10, 10], [25, 7, 6], [257, 6, 4],
>            [65537, 5, 5]],
>           c -> CallFuncList(CheckRecurrence, c));
true

# The functions for polynomials as lists of coefficients satisfy their
# defining equations, and RECOG.PolFactorsSquarefree agrees with Factors
gap> CheckPol := function(n, q)
>     local F, R, x, pol, coeffs, f, fc, facs, u, uc, g, w, crt, c, s, D, e;
>     F := GF(q);
>     R := PolynomialRing(F, 1);
>     x := IndeterminatesOfPolynomialRing(R)[1];
>     pol := c -> UnivariatePolynomial(F, c);
>     coeffs := f -> RECOG.Pol(F, CoefficientsOfUnivariatePolynomial(f));
>     repeat
>       f := x^n + RandomPol(F, n - 1, 1);
>     until DegreeOfLaurentPolynomial(Gcd(f, Derivative(f))) = 0;
>     fc := coeffs(f);
>     facs := List(Factors(R, f), coeffs);
>     if IsOddInt(q) and Set(RECOG.PolFactorsSquarefree(F, fc)) <> Set(facs)
>        then
>       return "factors";
>     fi;
>     u := RandomPol(F, n + 2, 1);
>     uc := coeffs(u);
>     for g in facs do
>       w := RECOG.PolInverseMod(uc, g);
>       if IsZero(u mod pol(g)) <> (w = fail)
>          or (w <> fail and RECOG.PolProductMod(w, uc, g) <> coeffs(x^0)) then
>         return "inverse";
>       fi;
>     od;
>     e := Random(0, q^(n + 1));
>     if RECOG.PolPowerModFrobenius(F, uc, e, fc,
>                                   RECOG.PolFrobeniusMatrix(F, fc))
>        <> RECOG.PolPowerMod(uc, e, fc) then
>       return "power";
>     fi;
>     if RECOG.PolResultant(fc, uc) <> Resultant(f, u, x)
>        or RECOG.PolResultant(uc, facs[1]) <> Resultant(u, pol(facs[1]), x)
>        then
>       return "resultant";
>     fi;
>     c := List(facs, g -> [RECOG.PolMod(uc, g),
>                           coeffs(RandomPol(F, Length(g) - 2, 1))]);
>     crt := RECOG.PolChineseRemainder(fc, facs, c);
>     if crt[1] <> RECOG.PolMod(uc, fc) or Length(crt[2]) > n
>        or ForAny([1 .. Length(facs)],
>                  i -> RECOG.PolMod(crt[2], facs[i]) <> c[i][2]) then
>       return "remainder";
>     fi;
>     # s(x + 1/x) = c_0 + sum_j c_j (x^j + x^-j), times x^D
>     c := List([0 .. n], i -> Random(F));
>     s := RECOG.PolOfReciprocalSum(RECOG.Pol(F, c));
>     D := n + Random(0, 2);
>     if pol(RECOG.PolAtReciprocalSum(F, s, D))
>        <> x^(D - n) * (c[1] * x^n + Sum([1 .. n], j -> c[j + 1]
>                                         * (x^(n + j) + x^(n - j)))) then
>       return "reciprocal sum";
>     fi;
>     if IsEvenInt(q) then
>       w := RECOG.PolSquareRootMod(F, uc, fc);
>       if RECOG.PolProductMod(w, w, fc) <> RECOG.PolMod(uc, fc) then
>         return "square root";
>       fi;
>     fi;
>     return true;
> end;;
gap> ForAll([[1, 3], [2, 3], [3, 3], [7, 3], [40, 3], [9, 5], [30, 5],
>            [25, 7], [20, 9], [12, 25], [30, 121], [8, 243], [10, 257],
>            [6, 65537], [1, 2], [2, 2], [9, 2], [40, 2], [15, 4], [12, 16],
>            [7, 512]],
>           c -> ForAll([1 .. 5], i -> CallFuncList(CheckPol, c) = true));
true

# RECOG.Form_NormPreimage solves z^(q^k+1) = a in the field F[x]/(f) of
# each irreducible factor f = f^dagger of 20 characteristic polynomials
# from SU(d,q), q odd
gap> CheckNormPreimage := function(d, q)
>     local F, R, G, f, k, a;
>     F := GF(q^2);
>     R := PolynomialRing(F, 1);
>     G := SU(d, q);
>     for f in Set(Concatenation(List([1 .. 20], i -> Factors(R,
>                  CharacteristicPolynomial(PseudoRandom(G)))))) do
>       f := RECOG.Pol(F, CoefficientsOfUnivariatePolynomial(f));
>       k := Length(f) - 1;
>       if f <> Reversed(List(f, c -> c^q)) / f[1]^q then
>         continue;
>       fi;
>       repeat
>         a := RECOG.PolPowerMod(RECOG.Pol(F, List([1 .. k], i -> Random(F))),
>                                q^k + 1, f);
>       until Length(a) > 0;
>       if RECOG.PolPowerMod(RECOG.Form_NormPreimage(F, f, a), q^k + 1, f)
>          <> a then
>         return false;
>       fi;
>     od;
>     return true;
> end;;
gap> ForAll([[7, 3], [6, 3], [8, 5], [5, 7], [6, 9], [5, 17], [3, 257]],
>           c -> CallFuncList(CheckNormPreimage, c));
true

# RECOG.Form_QuadraticNormPreimage solves u^2 + u v y + v^2 = a in the
# field F[y]/(g) for the irreducible factors g of 10 polynomials of degree
# n, except y - 2 and y + 2, where the left hand side is (u + v)^2 resp.
# (u - v)^2
gap> CheckQuadraticNormPreimage := function(n, q)
>     local F, R, y, g, k, a, uv, mul;
>     F := GF(q);
>     R := PolynomialRing(F, 1);
>     y := RECOG.Pol(F, [Zero(F), One(F)]);
>     for g in Set(Concatenation(List([1 .. 10], i -> Factors(R,
>                  RandomPol(F, n, 1))))) do
>       g := RECOG.Pol(F, CoefficientsOfUnivariatePolynomial(g));
>       g := g / g[Length(g)];
>       k := Length(g) - 1;
>       if k = 0 or (k = 1 and g[1] in [2, -2] * One(F)) then
>         continue;
>       fi;
>       mul := {u, v} -> RECOG.PolProductMod(u, v, g);
>       repeat
>         a := RECOG.PolMod(RECOG.Pol(F, List([1 .. k], i -> Random(F))), g);
>       until Length(a) > 0;
>       uv := RECOG.Form_QuadraticNormPreimage(F, g, a);
>       if RECOG.PolSum(mul(uv[1], RECOG.PolSum(uv[1], mul(uv[2], y))),
>                       mul(uv[2], uv[2])) <> a then
>         return false;
>       fi;
>     od;
>     return true;
> end;;
gap> ForAll([[1, 3], [2, 3], [5, 3], [12, 3], [30, 3], [1, 5], [8, 5],
>            [6, 7], [10, 9], [1, 17], [6, 17], [9, 25], [5, 49], [4, 257],
>            [3, 65537]],
>           c -> CallFuncList(CheckQuadraticNormPreimage, c));
true

# RECOG.Form_IsotropicKrylovVector, for the isometries h, -h and, for an
# orthogonal group of odd characteristic, h r for a reflection r, where h
# is from the group of the standard generators: e, e h, ..., e h^(k-1) span
# a totally isotropic resp. singular space, and beta(e, e h^k) <> 0. In odd
# dimension x - 1 or x + 1 divides the characteristic polynomial, and both
# do for h r in even dimension.
gap> CheckKrylovVector := function(type, d, q)
>     local F, form, J, G, name, top, w, r, good, i, h, chi, args, e;
>     F := GF(q);
>     if type = "SU" then
>       F := GF(q^2);
>     fi;
>     form := RECOG.ClassicalForm(type, d, F);
>     J := form.gram;
>     G := Group(RECOG.ClassicalStandardGenerators(type, d, F).all);
>     name := type;
>     top := QuoInt(d, 2);
>     if type in ["O+", "O-"] then
>       name := "O+";
>       top := top - 1;
>     fi;
>     r := [];
>     if type in RECOG.OrthogonalTypes and IsOddInt(q) then
>       repeat
>         w := Random(F^d);
>       until not IsZero(w * J * w);
>       r := [List(IdentityMat(d, F),
>                  v -> v - 2 * (v * J * w) / (w * J * w) * w)];
>     fi;
>     good := 0;
>     for i in [1 .. 100] do
>       h := PseudoRandom(G);
>       for h in Concatenation([h, -h], List(r, x -> h * x)) do
>         chi := CharacteristicPolynomial(h);
>         if DegreeOfLaurentPolynomial(Gcd(chi, Derivative(chi))) > 0 then
>           continue;
>         fi;
>         args := [h, J, F, chi, name];
>         if IsBound(form.quad) then
>           Add(args, form.quad);
>         fi;
>         e := CallFuncList(RECOG.Form_IsotropicKrylovVector, args);
>         if e = fail then
>           continue;
>         elif ForAny([0 .. top - 1],
>                     j -> not IsZero(RECOG.FormValue(form, e, e * h^j)))
>              or IsZero(RECOG.FormValue(form, e, e * h^top))
>              or (type in RECOG.OrthogonalTypes
>                  and not IsZero(RECOG.FormQuadraticValue(form, e))) then
>           return false;
>         fi;
>         good := good + 1;
>       od;
>       if good >= 10 then
>         return true;
>       fi;
>     od;
>     return false;
> end;;
gap> ForAll([["Sp", 4, 3], ["Sp", 4, 2], ["SU", 4, 3], ["SU", 5, 3],
>            ["O+", 6, 3], ["O", 7, 3], ["O+", 6, 2],
>            ["Sp", 6, 3], ["Sp", 14, 3], ["Sp", 10, 5], ["Sp", 8, 9],
>            ["Sp", 8, 49], ["Sp", 6, 257], ["Sp", 8, 2], ["Sp", 12, 4],
>            ["Sp", 6, 16], ["SU", 6, 3], ["SU", 7, 3], ["SU", 12, 3],
>            ["SU", 8, 5], ["SU", 9, 7], ["SU", 6, 17], ["SU", 6, 2],
>            ["SU", 9, 2], ["SU", 7, 4], ["SU", 8, 8], ["O+", 8, 3],
>            ["O+", 14, 3], ["O+", 10, 5], ["O+", 8, 9], ["O-", 8, 3],
>            ["O-", 10, 5], ["O-", 12, 7], ["O", 9, 3], ["O", 13, 3],
>            ["O", 11, 5], ["O", 9, 9], ["O+", 8, 2], ["O+", 10, 4],
>            ["O-", 10, 2], ["O-", 8, 8]],
>           c -> CallFuncList(CheckKrylovVector, c));
true

#
gap> STOP_TEST("goingup.tst");
