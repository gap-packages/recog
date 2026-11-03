gap> START_TEST("FindElmOfEvenNormal.tst");

# Each involution obtained by powering up an element of even order must be
# examined, not powered on to the identity. In D10 x C4, half the elements
# centralising a non-central involution have order 4.
gap> G := DirectProduct(DihedralGroup(IsPermGroup, 10),
>                       CyclicGroup(IsPermGroup, 4));;
gap> pending := [];;
gap> orderSpy := function(x)
>      local o;
>      o := Order(x);
>      if IsEvenInt(o) then
>        Add(pending, x^(o/2));
>      fi;
>      return o;
>    end;;
gap> isOneSpy := function(x)
>      local pos;
>      pos := Position(pending, x);
>      if pos <> fail then
>        Remove(pending, pos);
>      fi;
>      return IsOne(x);
>    end;;
gap> bad := 0;;
gap> for i in [1..20] do
>      pending := [];
>      FindElmOfEvenNormalSubgroup(G,
>        rec(Order := orderSpy, IsOne := isOneSpy, SkipTrivAbelian := true));
>      if not IsEmpty(pending) then
>        bad := bad + 1;
>      fi;
>    od;
gap> bad;
0

#
gap> STOP_TEST("FindElmOfEvenNormal.tst");
