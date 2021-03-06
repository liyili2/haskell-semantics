// abstract created and some useful helper functions
requires "haskell-syntax.k"

module HASKELL-ABSTRACT-SYNTAX
       imports HASKELL-SYNTAX

    //error states
    syntax KItem ::= "error"
    syntax KResult ::= error(K) //error with message
    syntax KItem ::= "cyclicImports"
    syntax KItem ::= "typeVarNoInclusive"
    syntax KItem ::= "typeVarNotUnique"
    syntax KItem ::= "repeatedNames"
    syntax KItem ::= "cycleAlpha"
    syntax KItem ::= "cycleClasses"
    syntax KItem ::= "typeNotInScope"
    syntax KItem ::= "classNotInScope"
    syntax KItem ::= "constrNotInScope"
    syntax KItem ::= "funNameNotInScope"
    syntax KItem ::= "typeVarNotInScope"
    syntax KItem ::= "labelConstrNotCorrect"
    syntax KItem ::= "labelNotInScope"
    syntax KItem ::= "typeConKindBad"
    syntax KItem ::= "typeConKindNumError"
    syntax KItem ::= "typeVarKindBad"
    syntax KItem ::= "typeVarKindNumError"
    syntax KItem ::= "multipleTypeVar"
    syntax KItem ::= "kindUnifierFail"
    syntax KItem ::= "classKindNotEqual"
    syntax KItem ::= "classKindNotEqualForTypeVar"
    syntax KItem ::= "allBoundClassVarsMustInScope"
    syntax KItem ::= "ambiguousTypeVar"
    syntax KItem ::= "classVarCollipse"
    syntax KItem ::= "classVarNotInScope"
    syntax KItem ::= "classMethodVarNotInScope"
    syntax KItem ::= "instanceMethodVarNotInScope"
    syntax KItem ::= "syntaxError"
    syntax KItem ::= "instanceInstNotDistinct"
    syntax KItem ::= "instanceMethodArgsNoMatch"
    syntax KItem ::= "instanceTypeVarNotInScope"
    syntax KItem ::= "lackParentInstance"
    syntax KItem ::= "duplicateParentInstance"
    syntax KItem ::= "moreThanOneDefault"
    syntax KItem ::= "importFromNoSource"
    syntax KItem ::= "ambiguousTypeName"
    syntax KItem ::= "ambiguousClassName"
    syntax KItem ::= "ambiguousConstrName"
    syntax KItem ::= "ambiguousFunName"
    syntax KItem ::= "badUseFunName"
    syntax KItem ::= "messuseClassTypeName"
    syntax KItem ::= "declNoInstance"
    syntax KItem ::= "duplicateDeriving"
    syntax KItem ::= "duplicateDecl"
    syntax KItem ::= "duplicateInstance"
    syntax KItem ::= "funNameDeclNotDef"
    syntax KItem ::= "funNameDefNotDeclInClass"
    syntax KItem ::= "funNameConflicting"
    syntax KItem ::= "derivingClassHasNoDefault"
    syntax KItem ::= "derivingClassNoKindMatching"
    syntax KItem ::= "boundTypeVarNotShowing"
    syntax KItem ::= "noEnoughInformationForKindVar"

    //checking steps
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
    syntax KItem ::= grabImportKindMaps(K, Set, Map)
               //execute, import-set, kind-map-with-mod
                   | grabImportKindMapsAux(K)

    //post happened results
    syntax KItem ::= putAlphaMap(Map)
    syntax KItem ::= putPreBetaMap(Map)
    syntax KItem ::= putDefSet(Set) 
    syntax KItem ::= putGenFieldMap(Int, Map) 
    syntax KItem ::= "collectKindInfo"
    syntax KItem ::= "checkDefs"
    syntax KItem ::= "collectCheckDefs"
    syntax KItem ::= "checkAllDeclMakeSense"
    syntax KItem ::= "checkAllFixityMakeSense"
    syntax KItem ::= "genRecordFunctions"

   //transformation of classes
    syntax KItem ::= "collectClassInfo"
    syntax KItem ::= getClassInfo(K)
    syntax KItem ::= getClassInfoAux(K, K, K, K, K, K)
    syntax KItem ::= getClassInfoAuxAux(K, K)
    //syntax KItem ::= putClassMethodNames(Set) [function]
    syntax KItem ::= putTypeClass(K, Set, K, K, K)
               //module, class contexts (super classes),
              // class name, class type-var, putClassMapSet

    //dealing with kind inference for classes in a module
              //two checks
              //first the number of tyvars for each data/newtype is
              //greater-equal than the number of deriving classes of that data
              //second, if a class is deriving, all its class methods
              //should have a default def, otherwise, the deriving class is either
              //not having an implementation for the method
              //, or it will be duplicated because of an instance for that data.        
    syntax KItem ::= "derivingClassChecks"
    syntax KItem ::= "allDerivingClassHasDefault"
    syntax KItem ::= classHasDefault(Map, K) [function]
    syntax KItem ::= classHasDefaultAux(Map, Set, K)
    syntax KItem ::= "derivingKindMakeSense"
    syntax KItem ::= derivingKindMakeSense(Map, K, K)
               //temp beta map, key, target
    syntax KItem ::= derivingKindMakeSenseAux(Map, List, K, K)
               //temp beta map, kind-to-list-of-type, key, target

    //kind inference ast here.
    syntax KItem ::= "kindInferClass"
    syntax KItem ::= genInitKindMapClass(Set)
    syntax KItem ::= buildContextMap(Map, K, Set)
    syntax KItem ::= kindClass(Int, Set, Set, K, Map, Set, Map, Set, Map)
                //counter, var-set, done-class-set, curr-class/error, 
               //class-father-map, tuples, kind-map, imports, import-map
    syntax KItem ::= kindClassAux(Set, K, K, Map, Set, Map, Set, Map)
                //done-class-set, classname, execute,
                // class-father-map, tuples, kind-map, imports, import-map
    syntax KItem ::= kindClassCheck(K, Map)
    syntax KItem ::= kindClassCheck2(K, Map, Map)
    syntax KItem ::= kindClassCheck3(Map, Map)
    syntax KItem ::= kindClassFinal(Map, Map)
    syntax KItem ::= kindClassNoKindVar(Map, Map, Set, K, K, Set, Map)

    //dealing with instances
    syntax KItem ::= "genInstanceChecks"
    syntax KItem ::= "collectInstances"
    syntax KItem ::= getInstances(K)
    syntax KItem ::= getInstancesAux(K, K, K, K, K)
    syntax KItem ::= getInstancesNext(K, K)
    syntax KItem ::= returnInstance(Int, Set, K, Set, K, Map)
    syntax KItem ::= instanceTuple(K, K) //class, type
    syntax KItem ::= "initialInstanceInModule"
    syntax KItem ::= "kindCheckInstance"
    syntax KItem ::= kindCheckInstance(Set, Int, Set, K, Map, Set, Map)
    syntax KItem ::= kindCheckInstanceAux(Set, K, K, K, K, Map, Set, Map)
    syntax KItem ::= "checkInstanceParents"
    syntax KItem ::= checkInstanceParents(Set, K)

    //dealing with expressions
    syntax KItem ::= "collectExpressions"
    syntax KItem ::= getExpressions(K)
    syntax KItem ::= "allContextsMakeSense"
    syntax KItem ::= "setUpContextsForVars"
    syntax KItem ::= "checkKindInExpressions"
    syntax KItem ::= checkKindInExpFinal(K)

    //preprocessing of beta map
    syntax KItem ::= "makePreBetaMap"
    syntax KItem ::= "grabAllTypeNames"
    syntax KResult ::= "star" // kind inference base
    syntax KResult ::= kindVar(Int) //unknown kind
    syntax KResult ::= kindArrow(K, K) // kind inference arrow case
    syntax KItem ::= returnKind(Int, Set, Set)
             //return-var-count, var-set, return set of kind unifier
    syntax KItem ::= kindTuple(K, K)
    syntax KItem ::= alphaTuple(List, K) //list-of-vars, type

    //preprocessing of validity checks
    //syntax KItem ::= "checkPreBetaInScope"
        //check if the beta map generated for the module is within the scope
          //has been merged into toAbsType

    /*syntax KItem ::= "checkAlphaNoLoops"
        //alpha check for no loops
        //check alpha to make sure that everything points to a T */
    //syntax KItem ::= "checkArgSortsAreTargets", checked by kind-inference-already
           //Make sure argument sorts [U] [W,V] are in the set of keys of alpha and targets of T, (keys of T)
    //syntax KItem ::= "checkParUsed", checked by kind-inference
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
    syntax KResult ::= resultExportSet(Set)
    syntax KItem ::= Module(K, K)
    syntax KItem ::= preModule(K,K) //(alpha, T)


    //all kinds of elements that a module can have
    syntax KItem ::= typeName(K) //a name for a type
    syntax KItem ::= constrName(K) //name for a constructor
    syntax KItem ::= funName(K) //name for a function/method
    syntax KItem ::= className(K) //name for a class

    syntax KItem ::= "genExportSet"
    syntax KItem ::= toExports(K, Set, Set, Set)
           //term, result-set
           // set of types, set of classes


    //defaul name for the haskell module if not specified.
    syntax KItem ::= "genModuleChecks"
    syntax KItem ::= "genImportSet"
    syntax KResult ::= resultImportSet(Set, Set)
    syntax KItem ::= importElem(K, K, Bool, Set, Map)
              //import-mod, as-mod,
              //isQualified,set-of-import-elements, map-of-import-element
    syntax KItem ::= "genAllModuleNames"
    syntax KItem ::= genAllModuleNamesNext(Set)
    syntax KItem ::= "checkExportScope"
    
    //first check if all imports are in scope of parent exports
    syntax KItem ::= "checkAllImportsGoodFromExports"
    syntax KItem ::= expandExports(Set, K, Set)

    syntax KItem ::= "noname"
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

    syntax KResult ::= contextKind(Set, K)
    syntax KResult ::= resultTupleMap(Map, Map)
    syntax KResult ::= resultTupleSet(K, Set) 
    syntax KResult ::= resultSet(Set)
    syntax KResult ::= resultSetMap(Set, Map)
    syntax KResult ::= resultMap(Map)
    syntax KResult ::= resultList(List)
    syntax KResult ::= resultDefaultTypes(K, K)
    syntax KResult ::= resultTyVarKindMap(Int, Set, Map)
                         //new-count, new-kind-vars, new-kind-map
    syntax KResult ::= resultKindTupleMap(Int, Set, Set, Map)
                         //new-count, new-kind-vars, tuples, new-kind-map

    syntax KResult ::= resultTyVarKindList(Int, Set, List)
                         //new-count, new-kind-vars, new-kind-in-list
    syntax KResult ::= resultIntMap(Int, Map) //counter, map
    syntax KResult ::= resultTrans(Int, K) //int, exp
    syntax KResult ::= resultTransList(Int, List) //int, exp-list
    syntax KResult ::= resultTransMap(Int, Map) //int, exp-map
    syntax KResult ::= resultTransSetMap(Int, Set, Map) //int, fun-sets, map
    syntax KResult ::= resultTransMapMap(Int, Map, Map) //int, fun-map, map
    syntax KResult ::= resultTransSetTerm(Int, Set, K) //int, fun-sets, map
    syntax KResult ::= resultTransSetTerm2(Int, Set, K, K) //int, fun-sets, map

    //abstract syntax for type constrs
    syntax KItem ::= aType(Bool, K) //isStrict?, type
    syntax KResult ::= TypeResult
    syntax Type ::= TypeResult
    syntax TypeResult ::= TyVar | modVar(TyVar)
                        | typeConst(K, List) //type constror or type var, list of typeResult
                        | curryTypes(List, K) //only in the top level
                        | forall(Set, K) //set of vars, type
    syntax KResult ::= fullName(K, K) //module name, type con
    syntax KResult ::= moduleNameAst(K) //module name, type con
    syntax KResult ::= preBetaEntry(List, Map, Set)
           //list_of_vars, Body, optDeriving
    syntax KItem ::= tyVar(K, K)
          //curr-name, convert a var to a tyVar, every record label name is a type
    syntax KResult ::= "recordType" | "recordTypeAssign"
                     | recordParen(K) | "recordAssign" | "recordUpdate"

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
    syntax KItem ::= methodDef(Set, Map, K, List)
            //contexts, ty-var-map (to contexts), type, patterns
    syntax KItem ::= methodDecl(K, Set, Map, K)
              //method-name, constaints,ty-var-map (to contexts), type

    //pattern
    syntax KItem ::= funPat(List) //name, args
    syntax KItem ::= appPat(K, List) //app-name, list of args
    syntax KItem ::= asPat(K, K) //first-name, second-pattern
    syntax KItem ::= "unnamedVar"
    syntax KItem ::= irrefuPat(K) //irrefutable pattern

    //expression syntax
    syntax KItem ::= appExp(K, List) //app-name, args
    syntax KItem ::= "arithSeq1" | "arithSeq2noEnd" | "arithSeq2hasEnd" | "arithSeq3"
                   | "listCompre" | "leftArrow"
    syntax KItem ::= lambda(K, K) //var, exp
    //syntax KItem ::= lambdaAssign(K, K) //pat-fun-rhs, body
    syntax KItem ::= funAssign(K, List, K) //fixed-point, args-with-pat, body
    syntax KItem ::= body(K, List) //expressions/guards, list-of-conditions
    syntax KItem ::= genVar(Int)
    syntax KItem ::= letIn(List, K) //var, exp
    syntax KItem ::= letStmt(List) //list of (pat,exp)
    syntax KItem ::= ifElse(K, K, K) //generalized ifelse, can deal with guard
                                  //list of conditions, exp1, exp2
    syntax KItem ::= guards(List) // guard holder in translation
    syntax KItem ::= caseOf(K, List) //exp, cases
    syntax KItem ::= singleCase(K, K, List)//pat, exp, where
    syntax KItem ::= seq(K, K)//first stmt, next
    syntax KItem ::= typedExp(Set, K, K) //contexts, type, exp
    syntax KItem ::= exnExp(String) //exception 
   
    //built-in construct to generate functions for field label
    syntax KItem ::= labelFactor(K, K, K) //label name, constr name, target type
    syntax KItem ::= findLabelResult(K, K, K)
         //field-constr, label-name, input result will be either the field-content or exnExp
    

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
