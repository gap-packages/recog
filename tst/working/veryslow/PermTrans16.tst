gap> for i in [1..NrTransitiveGroups(16)] do
> grp := TransitiveGroup(16,i);;
> RECOG.TestGroup(grp, false, Size(grp), rec(tryNonGroupElements := true));;
> od;;
