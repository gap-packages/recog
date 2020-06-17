############################################################################
# Just an example, recognise a cyclic group of order 2:
############################################################################

FindHomMethodsPerm.Cyclic2 :=
   function(ri, H)
     local gens,i;
     # Test applicability (this would no longer be necessary, because we
     # are called only for permutation groups anyway. However, this is an
     # example.
     if not IsPermGroup(H) then
         return NeverApplicable;
     fi;
     # Now we work:
     if Size(H) = 2 then
         # First find the first nontrivial generator:
         gens := GeneratorsOfGroup(H);
         i := 1;
         while IsOne(gens[i]) do
             i := i + 1;
         od;
         ri!.firstnontrivialgen := i;
         SetNiceGens(ri,[GeneratorsOfGroup(H)[i]]);
         Setslptonice(StraightLineProgramNC([[[i,1]]],Length(gens)));
         Setslpforelement(ri,SLPforElementFuncsPerm.Cyclic2);
         SetFilterObj(ri,IsLeaf);
         SetIsRecogInfoForSimpleGroup(ri,true);
         return Success;     # this indicates success
     else
         return NeverApplicable;    # do not call us again
     fi;
   end;

SLPforElementFuncsPerm.Cyclic2 :=
   function(ri, g)
     if IsOne(g) then
         return StraightLineProgram([[1, 0]], 1);
     else
         return StraightLineProgram([[1, 1]], 1);
     fi;
   end;

# The following would install this method with a very low rank if we would
# like to:
#
# AddMethod(FindHomDbPerm,
#           rec(method := FindHomMethodsPerm.Cyclic2,
#               rank := 1,
#               stamp := "Cyclic2",
#               comment := "find a Cyclic2"));
