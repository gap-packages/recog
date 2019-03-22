n := 10;; x:= (1,4,9,6,7,2,10,5,3);; slp := AnBB_SLPForAn(x, n);;
res := [ "An", 10, (1,3,5,7,10,9,4,8)(2,6), (2,6,3), [ 2, [ (1,5,9)(2,7,4)(3,10,8), (1,9,5)(2,4,7)(3,8,10) ], [ (2,3,5), (2,3,5)(7,10,9) ], [ true ], 9, (1,4,8)(2,3,5)(7,10,9), 
      (1,2,3,5,7,10,9,4,8), (1,8,4,9,10,7,5,3,2) ] ];; #Result of recognition with degree bound 1000 and epsilon = 1/1024;
preimage := ResultOfStraightLineProgram( slp, [ res[4], res[3] ] );; inv3 := res[4];;
y := AnBB_EvaluateIso( preimage, res[5],n, inv3 );