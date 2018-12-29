// abstract created and some useful helper functions
requires "haskell-syntax.k"

module HASKELL-ABSTRACT-SYNTAX
       imports HASKELL-SYNTAX

    //error states
    syntax KItem ::= "error"
    syntax KItem ::= error(K) //error with message
    syntax KItem ::= "cyclicImports"
    syntax KItem ::= "typeVarNoInclusive"
    syntax KItem ::= "repeatedNames"
    syntax KItem ::= "cycleAlpha"

    syntax KItem ::= "startChecks"
    syntax KItem ::= "nextChecks"
    syntax KItem ::= "checkNoSameKey"
        //Keys of alpha and keys of T should be unique
    syntax KItem ::= "checkTypeConsDontCollide"
        //Make sure typeconstructors do not collide in T
    syntax KItem ::= "makeAlphaMap"
        //make map for alpha
    syntax KItem ::= putAlphaMap(Map)
    syntax KItem ::= putPreBetaMap(Map)
    syntax KItem ::= putKindMap(Map)
    syntax KItem ::= "collectKindInfo"

    //preprocessing of beta map
    syntax KItem ::= "makePreBetaMap"
    syntax KResult ::= parKnown(K) //partial known for a guess of a kind
    syntax KResult ::= "star" // kind inference base
    syntax KResult ::= kindArrow(K, K) // kind inference arrow case

    //preprocessing of validity checks
    syntax KItem ::= "checkAlphaNoLoops"
        //alpha check for no loops
        //check alpha to make sure that everything points to a T
    syntax KItem ::= "checkArgSortsAreTargets"
           //Make sure argument sorts [U] [W,V] are in the set of keys of alpha and targets of T, (keys of T)
    syntax KItem ::= "checkParUsed"
//NEED TO CHECK all the polymorphic parameters from right appear on left. RIGHT SIDE ONLY
//NEED TO CHECK UNIQUENESS FOR POLY PARAM ON LEFT SIDE ONLY

    syntax KItem ::= "startImportRecursion"
    syntax KItem ::= callInit(K, K)
    //syntax KItem ::= initPreModule(K) [function]
    //syntax KItem ::= tChecker(K) [function]
    syntax KItem ::= dealWithImports(K)
    syntax KItem ::= dealWithImportsAux(K,K)
    syntax KItem ::= impObject(K,K)
    syntax KItem ::= "checkImportCycle"

    syntax KItem ::= "visited"
    syntax KItem ::= "unvisited"
    syntax KItem ::= "none"
    syntax KItem ::= Module(K, K)
    syntax KItem ::= preModule(K,K) //(alpha, T)

 
    //defaul name for the haskell module if not specified.
    syntax KItem ::= "noname"
    syntax KItem ::= "allExports"
    syntax Set ::= toExports(K) //deal with exports
    syntax KItem ::= importElem(K, K, K)
                  //OptQualified, OptAsModId, OptImpSpec 
    syntax KItem ::= "startPreprocessing"
    syntax KItem ::= "selectImport"

    syntax KItem ::= AList(K)
    syntax KItem ::= AObject(K,K) //(1st -> 2nd) map without idempotency

    syntax KItem ::= TList(K) //list of T objects for every new type introduced by data and newtype
    syntax KItem ::= TObject(K,K,K) //(type name, entire list of poly type vars, list of inner T pieces)
    syntax KItem ::= InnerTPiece(K,K,K,K,K) //(type constructor, poly type vars, argument sorts, entire constr block, type name)

    //useful element, elemlist data structure
    syntax Element ::= val(K) [strict] | ElemResult
    syntax ElemResult ::= valValue(K)
    syntax KResult ::= ElemResult
    syntax ElemList ::= List{Element, ","} [strict]
    rule val(K:KResult) => valValue(K) [structural]

    //abstract syntax for type constrs
    syntax KResult ::= TypeResult
    syntax Type ::= TypeResult
    syntax TypeResult ::= TyVar | modVar(TyVar)
                        | typeConst(K, List) //type constror or type var, list of typeResult
    syntax KResult ::= fullName(K, K) //module name, type con
    syntax KResult ::= preBetaEntry(Set, List, Map, Set)
           //optContext, list_of_vars, Body, optDeriving
    syntax TyVar ::= tyVar(K) //convert a var to a tyVar, every record label name is a type
    syntax KResult ::= "recordType" | "recordAssign"
            //two new type con names for records.
    syntax ModId ::= "Prelude"
    //built-in type cons
    syntax KItem ::= tupleType(Int) // the abstract constr of tuple type
    

    syntax KItem ::= tAlphaMap(K) //(AlphaMap) temp alphamap

    syntax KItem ::= countNames(K,K) //put class name, data name into map in modules
    syntax KItem ::= getPreModule(K, K, K)
    syntax KItem ::= dealWithClass(K)

    //useful abstract for module classes
    syntax KItem ::= typeMap(Map) //store all type with their arity in a module.

    syntax KItem ::= names(Set) //store all names
    syntax KItem ::= className(K, List) //name, list of type-vars
    syntax KItem ::= typeClass(K, List, Map) // father, type vars, contents

    //expression syntax
    //1 gendecls are signatures
    syntax KItem ::= typeSig(List,K,K) //contexts, var, type
    syntax KItem ::= fixitySig(K, Int, K) //fixity, precedence, op

    //other declarations define function bodies
    //rhs could be either one of pattern,exp, or 
    //a list of guards 
    syntax KItem ::= decl(Bool, K, List, List)
              //irrefutable?, pattern, rhs, conditions
    syntax KItem ::= guard(List, K) //patterns, exp

endmodule
