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
    syntax KItem ::= "typeNotInScope"
    syntax KItem ::= "typeVarNotInScope"
    syntax KItem ::= "typeConKindBad"
    syntax KItem ::= "typeConKindNumError"
    syntax KItem ::= "typeVarKindBad"
    syntax KItem ::= "typeVarKindNumError"
    syntax KItem ::= "kindUnifierFail"
    syntax KItem ::= "ambiguousTypeVar"
    syntax KItem ::= "classVarCollipse"
    syntax KItem ::= "classVarNotInScope"
    syntax KItem ::= "classMethodVarNotInScope"
    syntax KItem ::= "syntaxError"
    syntax KItem ::= "instanceInstNotDistinct"
    syntax KItem ::= "instanceMethodArgsNoMatch"
    syntax KItem ::= "moreThanOneDefault"

    syntax KItem ::= "startChecks"
    syntax KItem ::= "nextChecks"
    syntax KItem ::= "nextNextChecks"
    syntax KItem ::= "checkNoSameKey"
        //Keys of alpha and keys of T should be unique
    syntax KItem ::= "checkTypeConsDontCollide"
        //Make sure typeconstructors do not collide in T
    syntax KItem ::= "makeAlphaMap"
        //make map for alpha
    syntax KItem ::= "genKindMap"
        //make map for alpha
    syntax KItem ::= putAlphaMap(Map)
    syntax KItem ::= putPreBetaMap(Map)
    syntax KItem ::= "collectKindInfo"

   //transformation of classes
    syntax KItem ::= "collectClassInfo"
    syntax KItem ::= getClassInfo(K)
    syntax KItem ::= getClassInfoAux(K, K, Set, K, K, K)
    syntax KItem ::= getClassInfoAuxAux(K, K)
    syntax KItem ::= putClassMethodNames(Set) [function]
    syntax KItem ::= putTypeClass(K, Set, K, K, K)
               //module, class contexts (super classes),
              // class name, class type-var, putClassMapSet

    syntax KItem ::= "collectInstances"
    syntax KItem ::= getInstances(K)
    syntax KItem ::= getInstancesAux(K, K, Set, K, K)

    syntax KItem ::= "collectExpressions"
    syntax KItem ::= getExpressions(K)
    syntax KItem ::= getExpressionsAux(K)

    //preprocessing of beta map
    syntax KItem ::= "makePreBetaMap"
    syntax KResult ::= "star" // kind inference base
    syntax KResult ::= kindVar(Int) //unknown kind
    syntax KResult ::= kindArrow(K, K) // kind inference arrow case
    syntax KItem ::= returnKind(Int, Set, Set)
             //return-var-count, var-set, return set of kind unifier
    syntax KItem ::= kindTuple(K, K)
    syntax KItem ::= alphaTuple(List, K) //list-of-vars, type

    //preprocessing of validity checks
    syntax KItem ::= "checkPreBetaInScope"
        //check if the beta map generated for the module is within the scope

    /*syntax KItem ::= "checkAlphaNoLoops"
        //alpha check for no loops
        //check alpha to make sure that everything points to a T */
    syntax KItem ::= "checkArgSortsAreTargets"
           //Make sure argument sorts [U] [W,V] are in the set of keys of alpha and targets of T, (keys of T)
    syntax KItem ::= "checkParUsed"
//NEED TO CHECK all the polymorphic parameters from right appear on left. RIGHT SIDE ONLY
//NEED TO CHECK UNIQUENESS FOR POLY PARAM ON LEFT SIDE ONLY

    //check and deal with default in each module
    syntax KItem ::= "checkOnlyDefault"

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
    syntax KItem ::= "haveAll"  //used for import/export
    syntax KItem ::= "absClass" //used for import/export
    syntax KItem ::= "instanceOnly" //used for import/export
    syntax KItem ::= Module(K, K)
    syntax KItem ::= preModule(K,K) //(alpha, T)


    //all kinds of elements that a module can have
    syntax KItem ::= typeName(K) //a name for a type
    syntax KItem ::= constrName(K) //name for a constructor
    syntax KItem ::= funName(K) //name for a function/method
    syntax KItem ::= className(K) //name for a class

    //defaul name for the haskell module if not specified.
    syntax KItem ::= "genModuleChecks"
    syntax KItem ::= "genImportSet"
    syntax KResult ::= resultImportSet(Set)
    syntax KItem ::= importElem(Bool,K,K, Set, Set)
              //isQualified,import-mod, as-mod, set-of-import-specs, hidings
    syntax KItem ::= "genAllModuleNames"
    syntax KItem ::= genAllModuleNamesNext(Set)
    syntax KItem ::= "checkExportScope"

    syntax KItem ::= "noname"
    syntax KItem ::= "allExports"
    syntax KItem ::= genExportSet(K)
    //syntax KItem ::= importElem(K, K, K)
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

    syntax KResult ::= resultSet(Set)
    syntax KResult ::= resultMap(Map)
    syntax KResult ::= resultList(List)
    syntax KResult ::= resultDefaultTypes(K, K)
    syntax KResult ::= resultTyVarKindMap(Int, Set, Map)
                         //new-count, new-kind-vars, new-kind-map
    syntax KResult ::= resultTyVarKindList(Int, Set, List)
                         //new-count, new-kind-vars, new-kind-in-list
    syntax KResult ::= resultIntMap(Int, Map) //counter, map
    syntax KResult ::= resultTrans(Int, K) //int, exp
    syntax KResult ::= resultTransList(Int, List) //int, exp-list
    syntax KResult ::= resultTransMap(Int, Map) //int, exp-map
    syntax KResult ::= resultTransSetMap(Int, Set, Map) //int, fun-sets, map
    syntax KResult ::= resultTransSetTerm(Int, Set, K) //int, fun-sets, map

    //abstract syntax for type constrs
    syntax KResult ::= TypeResult
    syntax Type ::= TypeResult
    syntax TypeResult ::= TyVar | modVar(TyVar)
                        | typeConst(K, List) //type constror or type var, list of typeResult
                        | curryTypes(List, K) //only in the top level
                        | forall(Set, K) //set of vars, type
    syntax KResult ::= fullName(K, K) //module name, type con
    syntax KResult ::= moduleNameAst(K) //module name, type con
    syntax KResult ::= preBetaEntry(Set, List, Map, Set)
           //optContext, list_of_vars, Body, optDeriving
    syntax TyVar ::= tyVar(K, K)
          //curr-name, convert a var to a tyVar, every record label name is a type
    syntax KResult ::= "recordType" | "recordTypeAssign"
                     | "recordParen" | "recordAssign" | "recordUpdate"

            //two new type con names for records.
    //built-in type cons
    syntax KItem ::= tupleType(Int) // the abstract constr of tuple type
    syntax KItem ::= "tupleTypeAll" // the abstract constr of tuple type in importing prelude

    syntax KItem ::= tAlphaMap(K) //(AlphaMap) temp alphamap

    syntax KItem ::= countNames(K,K) //put class name, data name into map in modules
    syntax KItem ::= getPreModule(K, K, K)
    syntax KItem ::= dealWithClass(K)

    //useful abstract for module classes
    syntax KItem ::= typeMap(Map) //store all type with their arity in a module.

    syntax KItem ::= names(Set) //store all names
    syntax KItem ::= classTitle(K, List) //name, list of type-vars
    syntax KItem ::= typeClass(Set, K, Map)
        // father, type var, contents,
    syntax KItem ::= methodDef(Set, K, List) //constraints, Type, list of patterns
        // father, type var, contents,
    syntax KItem ::= methodDecl(K, Set, K) //method-name, constaints, type

    //pattern
    syntax KItem ::= funPat(List) //name, args
    syntax KItem ::= appPat(K, List) //app-name, list of args
    syntax KItem ::= asPat(K, K) //first-name, second-pattern
    syntax KItem ::= "unnamedVar"
    syntax KItem ::= irrefuPat(K) //irrefutable pattern

    //expression syntax
    syntax KItem ::= appExp(K, List) //app-name, args
    syntax KItem ::= "arithSeq1" | "arithSeq2noEnd" | "arithSeq2hasEnd" | "arithSeq3"
                   | "listCompre" | "qualAssignAst" | "qualLetAst"
    syntax KItem ::= lambda(K, K) //var, exp
    syntax KItem ::= lambdaAssign(K, K) //pat-fun-rhs, body
    syntax KItem ::= funAssign(List, K) //args-with-pat, body
    syntax KItem ::= body(K, List) //expressions/guards, list-of-conditions
    syntax KItem ::= genVar(Int)
    syntax KItem ::= letIn(List, K) //var, exp
    syntax KItem ::= ifElse(List, K, K) //generalized ifelse, can deal with guard
                                  //list of conditions, exp1, exp2
    syntax KItem ::= tempGuard(List, K) //temp guard holder in translation
    syntax KItem ::= caseOf(K, List) //exp, cases
    syntax KItem ::= singleCase(K, K, List)//pat, exp, where
    syntax KItem ::= seq(K, K)//first stmt, next
    syntax KItem ::= typedExp(Set, K, K) //contexts, type, exp

    //1 gendecls are signatures
    syntax KItem ::= typeSig(List,K,K) //contexts, var, type
    syntax KItem ::= fixitySig(K, Int, K) //fixity, precedence, op

    //other declarations define function bodies
    //a list of guards 
    syntax KItem ::= body(List, K) //guards, rhs
    syntax KItem ::= rhs(K, List) //rhs-expression, conditoins 

    syntax KItem ::= decl(Bool, K, List, List)
              //irrefutable?, pattern, rhs, conditions
    syntax KItem ::= guard(List, K) //patterns, exp

endmodule
