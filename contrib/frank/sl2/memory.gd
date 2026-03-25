# $Id: memory.gd,v 1.1 2004/10/28 06:37:31 gap Exp $

# Group objects remembering how they were created from the generators.

DeclareFilter("IsObjWithMemoryRankFilter",100); 

DeclareRepresentation("IsObjWithMemory", 
    IsComponentObjectRep and IsObjWithMemoryRankFilter and
    IsMultiplicativeElementWithInverse, ["slp","n","el"]);

DeclareAttribute("TypeOfObjWithMemory",IsFamily);

DeclareGlobalFunction( "GeneratorsWithMemory" );
DeclareGlobalFunction( "StripMemory" );
DeclareGlobalFunction( "StripStabChain" );
DeclareGlobalFunction( "CopyMemory" );
DeclareGlobalFunction( "GroupWithMemory" );
DeclareGlobalFunction( "SLPOfElm" );
DeclareGlobalFunction( "SLPOfElms" );

DeclareGlobalFunction( "SortFunctionWithMemory" );
