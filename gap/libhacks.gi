#############################################################################
##
##  libhacks.gi           recogbase package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Some corrections to the library.
##
#############################################################################


#############################################################################
##
#M  Range( <hom>, <H> ) . . . . . . . . . . . . . . . . . . . . for const hom
##
RanImgSrcSurjTraho:=function(hom)
local   D,H,I,G;
  H:=Source(hom);
  # only worth if the source has a stab chain to utilize
  if not HasStabChainMutable(H) then
    TryNextMethod();
  fi;
  D := Enumerator( UnderlyingExternalSet( hom ) );
  I := EmptyStabChain( [  ], () );
  RemoveStabChain( ConjugateStabChain( StabChainOp( H, D ), I,
          hom, hom!.conperm,
          S -> BasePoint( S ) <> false
            and BasePoint( S ) in D ) );
  #GroupStabChain might give too many generators
  if Length(I.generators)<0 then    # this should not happen!
    return GroupStabChain( I );
  else
    G:=Group(List(GeneratorsOfGroup(H),i->Permutation(i,D)),());
    SetStabChainMutable(G,I);
    return G;
  fi;
end;

InstallMethod( Range,"surjective constituent homomorphism",true,
  [ IsConstituentHomomorphism and IsActionHomomorphism and IsSurjective ],0,
  RanImgSrcSurjTraho);

InstallMethod( ImagesSource,"constituent homomorphism",true,
  [ IsConstituentHomomorphism and IsActionHomomorphism ],0,
  RanImgSrcSurjTraho);


##
##  This program is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program.  If not, see <http://www.gnu.org/licenses/>.
##

