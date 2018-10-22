// abstract created and some useful helper functions

module HASKELL-ABSTRACT-SYNTAX

        syntax KItem ::= "error"

    syntax KItem ::= "startChecks"
    syntax KItem ::= "checkNoSameKey"
        //Keys of alpha and keys of T should be unique
    syntax KItem ::= "checkTypeConsDontCollide"
        //Make sure typeconstructors do not collide in T
    syntax KItem ::= "makeAlphaMap"
        //make map for alpha
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
    syntax KItem ::= dealWithImports(K,K)
    syntax KItem ::= dealWithImportsAux(K,K)
    syntax KItem ::= impObject(K,K)
    syntax KItem ::= "checkImportCycle"

    syntax KItem ::= "visited"
    syntax KItem ::= "unvisited"
    syntax KItem ::= "none"
    syntax KItem ::= Module(K, K)
    syntax KItem ::= preModule(K,K) //(alpha, T)


    syntax KItem ::= AList(K)
    syntax KItem ::= AObject(K,K) //(1st -> 2nd) map without idempotency

    syntax KItem ::= TList(K) //list of T objects for every new type introduced by data and newtype
    syntax KItem ::= TObject(K,K,K) //(type name, entire list of poly type vars, list of inner T pieces)
    syntax KItem ::= InnerTPiece(K,K,K,K,K) //(type constructor, poly type vars, argument sorts, entire constr block, type name)

    syntax KItem ::= tAlphaMap(K) //(AlphaMap) temp alphamap

    syntax KItem ::= countNames(K,K) //put class name, data name into map in modules
    syntax KItem ::= getPreModule(K, K, K)
    syntax KItem ::= dealWithClass(K)

    //useful abstract for module classes
    syntax KItem ::= names(Set) //store all names
    syntax KItem ::= fullName(K, K) //module name, item name
    syntax KItem ::= className(K, List) //name, list of type vars
    syntax KItem ::= typeClass(K, List, Map) // father, type vars, contents


endmodule
