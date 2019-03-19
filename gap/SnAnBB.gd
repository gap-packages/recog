#############################################################################
##
##  AnBB.gi
##                              recog package
##                                                            Martin Leuner
##                                                         Sebastian Jambor
##                                                      & Alice C. Niemeyer
##
##
##  Copyright (C) 2012 by the authors.
##  Lehrstuhl B f"ur Mathematik, RWTH Aachen and
##  the University of Western Australia.
##
##  This file is free software, see license information at the end.
##
##
##  This file provides code for recognising whether a black box group
##  with degree n \le N for given N is isomorphic to A_n or S_n.
##
##  Most of the code is based upon the algorithm presented in the paper
##  "Fast recognition of alternating groups of unknown degree" by
##  Sebastian Jambor, Martin Leuner, Alice C. Niemeyer and Wilhelm Plesken.
##
##  Several functions, namely AnBB_AnPresentationSatisfied, AnBB_SnPresentationSatisfied,
##  AnBB_SLPForAn, AnBB_SLPForSn and AnBB_ComputeIsomorphism are based upon
##  algorithms presented in the paper "A black-box group algorithm for
##  recognizing finite symmetric and alternating groups. I." by Robert Beals,
##  Charles R. Leedham-Green, Alice C. Niemeyer, Cheryl E. Praeger and
##  'Akos Seress.
##
##
##  This file is generated automatically.
##
DeclareInfoClass( "InfoRecAnBB" );

DeclareGlobalFunction("AnBB_InitialList");
DeclareGlobalFunction("AnBB_NextSmallSupportInvolution");
DeclareGlobalFunction("AnBB_IsProbableThreeCycle");
DeclareGlobalFunction("AnBB_NextThreeCycle");
DeclareGlobalFunction("AnBB_NextBolsteringElement");
DeclareGlobalFunction("AnBB_MatchingLongCycle");
DeclareGlobalFunction("AnBB_IsFixedPoint");
DeclareGlobalFunction("AnBB_NextPoint");
DeclareGlobalFunction("AnBB_AdjustCycle");
DeclareGlobalFunction("AnBB_AppendPoints");
DeclareGlobalFunction("AnBB_NiceGenerators");
DeclareGlobalFunction("AnBB_SnPresentationSatisfied");
DeclareGlobalFunction("AnBB_AnPresentationSatisfied");
DeclareGlobalFunction("AnBB_InitialiseIso");
DeclareGlobalFunction("AnBB_NonCommThreeCycle");
DeclareGlobalFunction("AnBB_NonCommTCPoints");
DeclareGlobalFunction("AnBB_CycleNumber");
DeclareGlobalFunction("AnBB_FindSinglePoint");
DeclareGlobalFunction("AnBB_PartialImageAn");
DeclareGlobalFunction("AnBB_EvaluateIso");
DeclareGlobalFunction("AnBB_SLPForAn");
DeclareGlobalFunction("AnBB_SLPForSn");
DeclareGlobalFunction("AnBB_ComputeIsomorphism");
DeclareGlobalFunction("AnBB_Recognise");


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