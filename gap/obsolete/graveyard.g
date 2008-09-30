          # They even differ only by a scalar from the base field:
          pos := PositionNonZero(newgens[1][1]);
          blpos := QuoInt(blpos+subdim-1,subdim);
          prototype := ExtractSubMatrix(newgens[1],[1..subdim],
                                        [(blpos-1)*subdim..blpos*subdim]);
          inblpos := pos - (blpos-1)*subdim;
          # now pos = (blpos-1)*subdim + inblpos and 1 < inblpos <= subdim
          homgens := [];
          for i in [1..Length(newgens)] do


  # First find a (projective) involution:
  count := 0;
  while true do   # will be left by break or return
      x := PseudoRandom(G);
      o := ProjectiveOrder(x)[1];
      if IsEvenInt(o) then
          x := x^(o/2);
          break;
      fi;
      count := count + 1;
      if count > 100 then 
          Info(InfoRecog,2,"D247: Did not find projective involution.");
          return fail; 
      fi;
  od;

  Print("D247: Trying 21 involutions...\n");

  for i in [1..20] do
      count := 0;
      while true do  # will be left by break or return
          y := PseudoRandom(G);
          c := Comm(x,y);
          o := ProjectiveOrder(c)[1];
          if IsEvenInt(o) then
            x := c^(o/2);
            break;
          else
            z := y*c^((o-1)/2);   # this is evenly distributed in C_g(x)
            o := ProjectiveOrder(z)[1];
            if IsEvenInt(o) then
                x := z^(o/2);
                break;
            fi;
            # otherwise simply try again
          fi;
          count := count + 1;
          if count > 100 then
              Info(InfoRecog,2,"D247: Did not find projective involution (2).");
              return fail;
          fi;
      od;
      Print(".\c");
      res := CheckNormalClosure(x);
      if res in [true,false] then return res; fi;
  od;
