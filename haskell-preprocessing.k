//
requires "haskell-syntax.k"
requires "haskell-configuration.k"
requires "haskell-abstract-syntax.k"
requires "haskell-helper.k"
requires "haskell-kindinfer.k"
requires "haskell-transformation.k"
requires "haskell-errors.k"
requires "haskell-modules.k"


module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX
    imports HASKELL-CONFIGURATION
    imports HASKELL-HELPER
    imports HASKELL-ERRORS
    imports HASKELL-KINDINFER
    imports HASKELL-TRANSFORMATION
    imports HASKELL-MODULES

    rule <k> preModule(A:K,T:K) => startChecks ...</k>
         <tempAlpha> OldAlpha:K => A </tempAlpha>
         <tempT> OldT:K => T </tempT>


/*    rule <k> performNextChecks
             => checkUseVars
                ~> (checkLabelUses
                ~> (checkBlockAddress(.K)
                ~> (checkNoNormalBlocksHavingLandingpad(.K, TNS -Set TES)
                ~> (checkAllExpBlocksHavingLandingpad(.K, TES)
                ~> (checkAllExpInFromInvoke(.K, TES)
                ~> (checkLandingpad
                ~> checkLandingDomResumes)))))) ...</k>
              checkNoSameKey
                 checkTypeConsDontCollide */

    rule startChecks => genImportSet
                ~> (collectKindInfo
                ~> (checkDefs
                ~> (makeAlphaMap
                ~> nextChecks)))

    rule checkDefs => collectCheckDefs
                        ~> (checkAllDeclMakeSense
                        ~> genRecordFunctions)

    rule nextChecks => makePreBetaMap
                ~> (grabAllTypeNames
                ~> (genKindMap
                ~> nextNextChecks))

    rule nextNextChecks => (checkOnlyDefault
                 ~> (checkArgSortsAreTargets
                ~> (checkParUsed
                 ~> (collectClassInfo
                //TODO: check kind for class and derivings for data types are all star -> star kind
                ~> (collectExpressions
                ~> genModuleChecks)))))

    rule genModuleChecks => genAllModuleNames
                         ~> (genExportSet
                         ~> checkAllImportsGoodFromExports)

    //collect all defs in a module
    rule <k> collectCheckDefs => collectCheckDefs(B, .Set) ...</k>
         <tempModule> B:K </tempModule>

    rule <k> putDefSet(S:Set) => .K ...</k>
         <currModule> X:K </currModule>
         <moduleName> X </moduleName>
         <moduleDefs> .Set </moduleDefs>

   //check if all decl in a module is defined in the module also
   rule <k> checkAllDeclMakeSense => checkAllDeclMakeSense(B, S) ...</k>
         <tempModule> B:K </tempModule>
         <currModule> X:K </currModule>
         <moduleName> X </moduleName>
         <moduleDefs> S:Set </moduleDefs>

   //generate a map for all functions of getting field content for a module
    rule <k> genRecordFunctions => genRecordFunctions(N, B, .Map) ...</k>
         <tempModule> B:K </tempModule>
         <genVarCounter> N:Int </genVarCounter>

    rule <k> putGenFieldMap(N:Int, M:Map) => .K ...</k>
         <genVarCounter> _:Int => N </genVarCounter>
         <currModule> X:K </currModule>
         <moduleName> X </moduleName>
         <moduleMethods> S:Map (.Map => M) </moduleMethods>


    //grabing all type names from the current module
    rule <k> grabAllTypeNames => .K ...</k>
         <currModule> X:K </currModule>
         <moduleName> X </moduleName>
         <moduleAlpha> A:Map </moduleAlpha>
         <tempBetaMap> B:Map </tempBetaMap>
         <moduleTypeNames> NM:Map
                  => NM[X <- resultSet(keys(A) keys(B))] </moduleTypeNames>

    //genarate export set, and initialize inside module checks
    //TODO: place validity checks for syntax of cname in exports
    //be able to distingush class vs data types
    //check if all exports are valid due to imports
   rule <k> 'moduleExp('moduleName(A:ModId),, C:Exports,, B:K)
              => startChecks ...</k>
        <tempExports> _:K => C </tempExports>
        <tempModule> _:K => B </tempModule>
        <currModule> _:K => A </currModule>
        <moduleMethodNames> MM:Map => MM[A <- resultSet(.Set)] </moduleMethodNames>
        <classMethodNames> CM:Map => CM[A <- resultSet(.Set)] </classMethodNames>
        <classNames> NM:Map => NM[A <- resultSet(.Set)] </classNames>
        (.Bag => <module>...
                    <moduleName> A </moduleName>
                ...</module>)

   rule <k> 'module('moduleName(A:ModId),, B:K) => startChecks ...</k>     
        <tempModule> _:K => B </tempModule>
        <currModule> _:K => A </currModule>
        <moduleMethodNames> MM:Map => MM[A <- resultSet(.Set)] </moduleMethodNames>
        <classMethodNames> CM:Map => CM[A <- resultSet(.Set)] </classMethodNames>
        <classNames> NM:Map => NM[A <- resultSet(.Set)] </classNames>
        <exports> Ex:Map => Ex[A <- resultSet(SetItem(haveAll))] </exports>
        (.Bag => <module>...
                    <moduleName> A </moduleName>
                ...</module>)

   rule <k> 'moduleBody(B:K) => startChecks ...</k>     
        <tempModule> _:K => B </tempModule>
        <currModule> _:K => Main </currModule>
        <moduleMethodNames> MM:Map => MM[Main <- resultSet(.Set)] </moduleMethodNames>
        <classMethodNames> CM:Map => CM[Main <- resultSet(.Set)] </classMethodNames>
        <classNames> NM:Map => NM[Main <- resultSet(.Set)] </classNames>
        <exports> Ex:Map => Ex[Main <- resultSet(SetItem(main))] </exports>
        (.Bag => <module>...
                    <moduleName> Main </moduleName>
                ...</module>)

/*
   rule <k> genExportSet(.Set) => .K ...</k>
        <currModule> X:K </currModule>
        <moduleName> X </moduleName>
        <exports> _:Set => SetItem(instanceOnly) </exports>

   rule <k> genExportSet(SetItem(A:K) S:Set) => .K ...</k>
        <currModule> X:K </currModule>
        <moduleName> X </moduleName>
        <exports> _:Set => SetItem(A:K) S:Set </exports>
   generate all export set, starting by generating all class/type names along the module
   check if all export elements are distint.
*/
   rule <k> genExportSet => toExports(Term, .Set, 
                   allNamesFromModule(X, .K, MI, CM),
                 allNamesFromModule(X, .K, MI, TM)) ...</k>
        <currModule> X:K </currModule>
        <moduleName> X </moduleName>
        <moduleImportMap> MI:Map </moduleImportMap>
        <classNames> CM:Map </classNames>
        <moduleTypeNames> TM:Map </moduleTypeNames>
        <tempExports> Term:K </tempExports>


   //generating import set
   rule <k> genImportSet => genImportSet(S, M,.Set, .Set) ...</k>
        <tempModule> S:K </tempModule>
        <exports> M:Map </exports>

   rule <k> resultImportSet(S1:Set, S:Set) => .K ...</k>
        <moduleImportMap> MI:Map => MI[X <- resultSet(S1)] </moduleImportMap>
        <currModule> X:K </currModule>
        <moduleName> X </moduleName>
        <imports> _:Set => S </imports>

   //collect names for each module, and then start checking imports/exports
   rule <k> genAllModuleNames
            => genAllModuleNamesNext(collectTypeNames(keys(NM))
               collectTypeNames(keys(BM)) collectPreBetaNames(BM, .K)
               toClassNames(getRidWrapper(CM)) collectFunNames(getRidWrapper(CMM))
                collectFunNames(getRidWrapper(MM))) ...</k>
        <currModule> X:K </currModule>
        <moduleName> X </moduleName>
        <tempBetaMap> BM:Map </tempBetaMap>
        <moduleAlpha> NM:Map </moduleAlpha>
        <classNames>... X |-> CM:K ...</classNames>
        <classMethodNames>... X |-> CMM:K ...</classMethodNames>
        <moduleMethodNames>... X |-> MM:K ...</moduleMethodNames>

   rule <k> genAllModuleNamesNext(S:Set) => .Set ...</k>
        <currModule> X:K </currModule>
        <moduleName> X </moduleName>
        <moduleElems> _:Set => S </moduleElems>

   //check if all import names are in scope.
   // first check if all imports are valid compared with exports
/*
   rule <k> checkAllImportsGoodFromExports
               => expandExports(Es, .K, .Set) ...</k>
        <currModule> X:K </currModule>
        <moduleName> X </moduleName>
        <exports> Es:Set </exports>
*/

   rule <k> expandExports(.Set, .K, S:Set) => .K ...</k>
        <currModule> X:K </currModule>
        <moduleName> X </moduleName>
        <imports> Is:Set </imports>

    //deal with alpha map, deal with renaming of type name
    //collect information for the type name and kind in the same module
    rule <k> collectKindInfo => collectTypes(N, S, Mod, TM, .Map) ...</k>
         <tempModule> TM:K </tempModule>
         <currModule> Mod:K </currModule>
         <kindVarCounter> N:Int </kindVarCounter>
         <kindVarSet> S:Set </kindVarSet>

    rule <k> makeAlphaMap => makeAlphaM(Mod, S, .Map, .Map, keys(KM), Is) ...</k>
         <tempModule> S:K </tempModule>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <kindMap> KM:Map </kindMap>
         <imports> Is:Set </imports>

    rule <k> putAlphaMap(M:Map) => .K ...</k>
         <currModule> Mod:K </currModule>
        <moduleName> X </moduleName>
        <moduleAlpha> _:Map => M </moduleAlpha>

    rule <k> putPreBetaMap(M:Map) => .K ...</k>
         <tempBetaMap> _:Map => M </tempBetaMap>

    /*deal with beta map, three steps
      first step is to collect information of a data/newtype, and put them in a list 
      and create a pre-beta-map from type con name to the list.
      REMEMBER to turn type structure into an abstract form.
      second step is to do kind check on the input datatype
      third step, resolve the pre-beta-map to beta map for the module. */
    rule <k> makePreBetaMap => makePreBetaFun(Mod, S, .Map, Ts, Is) ...</k>
         <tempModule> S:K </tempModule>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <moduleNames> Ts:Set </moduleNames>
         <imports> Is:Set </imports>

    //finish
    rule <k> genKindMap => grabImportKindMaps(.K, S, .Map) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <imports> S:Set </imports>

    rule <k> grabImportKindMaps(.K, .Set, Ks:Map)
           => grabImportKindMapsAux(genInitKindMap(N, S, .K, .K, AM BM)) ...</k>
         <tempImportKindMap> _:Map => Ks </tempImportKindMap>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <tempBetaMap> BM:Map </tempBetaMap>
         <moduleAlpha> AM:Map </moduleAlpha>
         <kindVarCounter> N:Int </kindVarCounter>
         <kindVarSet> S:Set </kindVarSet>

    rule <k> grabImportKindMapsAux(resultTyVarKindMap(N:Int, S:Set, TM:Map)) =>
               kindInfer(N, S, Mod, .K, .K, AM BM, TM, .Set, Is, Ks) ...</k>
         <tempImportKindMap> Ks:Map </tempImportKindMap>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <tempBetaMap> BM:Map </tempBetaMap>
         <moduleAlpha> AM:Map </moduleAlpha>
         <imports> Is:Set </imports>

    rule grabImportKindMaps(.K, SetItem(A:K) S:Set, KM:Map)
                => grabImportKindMaps(A, S, As, KM)

    rule <k> grabImportKindMaps(importElem(Mod:K, _:K, _:Bool,
                   Ts:Set, _:Map), S:Set, KM:Map)
                => grabImportKindMaps(.K, S, As,
                             addKindToMap(Mod, .K, Ts, SM, KM) ...</k>
         <moduleName> Mod </moduleName>
         <kindMap> SM:Map </kindMap>
         requires notBool Mod in As

    rule <k> genKindMap => kindInfer(N, S, .K, .K, AM BM, M, .Set) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <tempBetaMap> BM:Map </tempBetaMap>
         <moduleAlpha> AM:Map </moduleAlpha>
         <kindMap> M:Map </kindMap>
         <kindVarCounter> N:Int </kindVarCounter>
         <kindVarSet> S:Set </kindVarSet>

    rule <k> resultTyVarKindMap(N:Int, S:Set, M:Map) => .K ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <kindMap> _:Map => M </kindMap>
         <kindVarCounter> _:Int => N </kindVarCounter>
         <kindVarSet> _:Set => S </kindVarSet>

    //check there is only one default in a module
    rule <k> checkOnlyDefault => checkOnlyDefault(TM) ...</k>
         <tempModule> TM:K </tempModule>

    rule <k> resultDefaultTypes(T1:K, T2:K) => .K ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <defaultInt> _:K => T1 </defaultInt>
         <defaultDouble> _:K => T2 </defaultDouble>

    //deal with type classes. type classes ast gen
   //functions to compile type classes to ast form
    rule <k> collectClassInfo => getClassInfo(TM) ...</k>
         <tempModule> TM:K </tempModule>

    rule getClassInfo('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls))
               => getClassInfo(Ts)
    rule getClassInfo('bodyimpdecls(Is:ImpDecls)) => .K
    rule getClassInfo('bodytopdecls(Ts:TopDecls)) => getClassInfo(Ts)
    rule getClassInfo(.TopDecls) => .K

    rule getClassInfo('topdeclslist(A:TopDecl,, As:TopDecls)) => getClassInfo(As)
         requires notBool isTheClass(A)
         
    rule <k> getClassInfo('topdeclslist('class(Cs:OptContext,,
                  Name:ConId,, Tv:TyVar,, Ds:OptCDecls),, As:TopDecls))
               => getClassInfoAux(transVar(Mod, Name),Tv, contextToSet(Mod, Cs),
                    toAstTypeClass(Mod, Tv, Ds, .Map,
                    getMethodSet(Mod, .K, CM)), Ds, As) ...</k>
         <currModule> Mod:K </currModule>
         <classMethodNames> CM:Map </classMethodNames>
         <classNames> NM:Map => updateMapItem(NM,
                          .K, Mod, transVar(Mod, Name)) </classNames>
         requires notBool hasClassName(Mod, Name, .K, NM)

    rule <k> getClassInfo('topdeclslist('class(Cs:OptContext,,
                  Name:ConId,, Tv:TyVar,, Ds:OptCDecls),, As:TopDecls))
               => error(classVarCollipse) ...</k>
         <currModule> Mod:K </currModule>
         <classNames> NM:Map </classNames>
         requires hasClassName(Mod, Name, .K, NM)

   rule getClassInfoAux(Name:K, Tv:K, S:Set, error(A:K), Ds:K, As:K) => error(A)
   rule <k> getClassInfoAux(Name:K, Tv:K, S:Set,
               resultMap(Methods:Map), Ds:K, As:K)
            => putClassMethodNames(genClassMethodNames(Ds)) ~>
                 (getClassInfoAuxAux(Name, toAstPat(N, Mod, Ds, .K, .K, Methods))
                 ~> getClassInfo(As)) ...</k>
         <genVarCounter> N:Int </genVarCounter>
         <currModule> Mod:K </currModule>
         <classNames> NM:Map </classNames>
         (.Bag => <class>...
                     <classModule> Mod </classModule>
                     <className> Name </className>
                     <classTypeVar> Tv </classTypeVar>
                     <classContext> S </classContext>
                  ...</class>)

  rule <k> putClassMethodNames(S:Set) => .K ...</k>
       <currModule> Mod:K </currModule>
       <classMethodNames> NM:Map
               => updateMapItem(NM, .K, Mod, S) </classMethodNames>

    rule getClassInfoAuxAux(Name:K, error(A:K)) => error(A)
    rule <k> getClassInfoAuxAux(Name:K, resultIntMap(N':Int, M:Map))
              => checkMethodPatNumbers(M, .K) ...</k>
         <genVarCounter> N:Int => N' </genVarCounter>
         <class>...
             <classModule> Mod </classModule>
             <className> Name </className>
             <classMethods> _:Map => M </classMethods>
         ...</class>

   //functions to compile type class instances to ast form
    rule <k> collectInstances => getInstances(TM) ...</k>
         <tempModule> TM:K </tempModule>

    rule getInstances('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls))
               => getInstances(Ts)
    rule getInstances('bodyimpdecls(Is:ImpDecls)) => .K
    rule getInstances('bodytopdecls(Ts:TopDecls)) => getInstances(Ts)
    rule getInstances(.TopDecls) => .K

    rule getInstances('topdeclslist(A:TopDecl,, As:TopDecls)) => getInstances(As)
         requires notBool isTheInstance(A)

    rule <k> getInstances('topdeclslist('instance(Cs:OptContext,,
                  Name:QTyCon,, Tv:Inst,, Ds:OptIDecls),, As:TopDecls))
                 => error(classVarNotInScope) ...</k>
         <currModule> Mod:K </currModule>
         <classNames> NM:Map </classNames>
         requires notBool hasClassName(Mod, transVar(Mod, Name), .K, NM)

    rule getInstances('topdeclslist('instance(Cs:OptContext,,
                  Name:QTyCon,, Tv:Inst,, Ds:OptIDecls),, As:TopDecls))
                 => error(instanceInstNotDistinct)
         requires hasDistinctVars(Tv)

    rule <k> getInstances('topdeclslist('instance(Cs:OptContext,,
                  Name:QTyCon,, Tv:Inst,, Ds:OptIDecls),, As:TopDecls))
               => getInstancesAux(transVar(Mod, Name), toAbsType(Mod, Tv),
                    contextToSet(Mod, Cs),
                    transTopDecls(N, Mod, Ds, keys(Methods)), As) ...</k>
         <genVarCounter> N:Int </genVarCounter>
         <currModule> Mod:K </currModule>
         <classMethodNames> CM:Map </classMethodNames>
         <classNames> NM:Map </classNames>
         <class>...
             <classModule> Mod </classModule>
             <className> transVar(Mod, QTyCon) </className>
             <classMethods> Methods:Map </classMethods>
         ...</class>
         requires hasClassName(Mod, transVar(Mod, Name), .K, NM)
                  andBool notBool hasDistinctVars(Tv)

   rule getInstancesAux(Name:K, Tv:K, S:Set, error(A:K), As:K) => error(A)
   rule <k> getInstancesAux(Name:K, Tv:K, S:Set, resultTransMap(N':Int, M':Map), As:K)
            => checkMethodPatNumbers(M', .K) ~> getInstances(As) ...</k>
         <genVarCounter> N:Int => N' </genVarCounter>
         <currModule> Mod:K </currModule>
         <classMethodNames> CM:Map </classMethodNames>
         <classNames> NM:Map </classNames>
         (.Bag => <instance>...
                     <instanceModule> Mod </instanceModule>
                     <instanceClass> Name </instanceClass>
                     <instanceType> Tv </instanceType>
                     <instanceContext> S </instanceContext>
                     <instanceMethods> M' </instanceMethods>
                  ...</instance>)

   //transformation of expressions in a module
   rule <k> collectExpressions => getExpressions(TM) ...</k>
        <tempModule> TM:K </tempModule>


    rule getExpressions('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls))
               => getExpressions(Ts)
    rule getExpressions('bodyimpdecls(Is:ImpDecls)) => .K
    rule getExpressions('bodytopdecls(Ts:TopDecls)) => getExpressions(Ts)
    rule getExpressions(.TopDecls) => .K

    rule getExpressions('topdeclslist(A:TopDecl,, As:TopDecls)) => getExpressions(As)
         requires notBool isTheExp(A)

    rule <k> getExpressions('topdeclslist('declFunLhsRhs(A:K,, B:K),, As:TopDecls))
              => getExpressionsAux(transDeclFun(N,Mod, 'declFunLhsRhs(A:K,, B:K),
                          getRidWrapper(X) getRidWrapper(Y), M))
                 ~> getExpressions(As) ...</k>
         <currModule> Mod:K </currModule>
         <genVarCounter> N:Int </genVarCounter>
         <classMethodNames>... Mod |-> X:K ...</classMethodNames>
         <moduleMethodNames>... Mod |-> Y:K ...</moduleMethodNames>
         <module>...
            <moduleName> Mod:K </moduleName>
            <moduleMethods> M:Map </moduleMethods>
         ...</module>

   rule getExpressionsAux(error(A:K)) => error(A)
   rule <k> getExpressionsAux(resultTransSetMap(
                    N':Int, S:Set, M':Map)) => .K ...</k>
         <currModule> Mod:K </currModule>
         <genVarCounter> N:Int => N' </genVarCounter>
         <moduleMethodNames> MM:Map => updateMapItem(MM, .K, Mod, S) </moduleMethodNames>
         <module>...
            <moduleName> Mod:K </moduleName>
            <moduleMethods> M:Map => M' </moduleMethods>
         ...</module>

    rule <k> getExpressions('topdeclslist('declPatRhs(A:Pat,, B:Rhs),, As:TopDecls))
                 => getExpressionsAux(transDeclFun(N,Mod, 'declPatRhs(A,, B),
                          setMinus(getFreeVarsInPat(A),.K, getRidWrapper(Y)), M))
                 ~> getExpressions(As) ...</k>
         <currModule> Mod:K </currModule>
         <genVarCounter> N:Int </genVarCounter>
         <classMethodNames>... Mod |-> X:K ...</classMethodNames>
         <moduleMethodNames>... Mod |-> Y:K ...</moduleMethodNames>
         <module>...
            <moduleName> Mod:K </moduleName>
            <moduleMethods> M:Map => createEmptyEntry(M, .K,
                setMinus(getFreeVarsInPat(A),.K, getRidWrapper(Y))) </moduleMethods>
         ...</module>
        requires (notBool isIntersect(getFreeVarsInPat(A),.K,
                        getRidWrapper(X) getRidWrapper(Y)))
                 orBool (isIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))
                       andBool hasNoDefinedPats(getValues(M, .K,
                           getIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))), .K))

    rule <k> getExpressions('topdeclslist('declPatRhs(A:Pat,, B:Rhs),, As:TopDecls))
                 => error(classVarCollipse) ...</k>
         <currModule> Mod:K </currModule>
         <genVarCounter> N:Int </genVarCounter>
         <classMethodNames>... Mod |-> X:K ...</classMethodNames>
         <moduleMethodNames>... Mod |-> Y:K ...</moduleMethodNames>
         <module>...
            <moduleName> Mod:K </moduleName>
            <moduleMethods> M:Map </moduleMethods>
         ...</module>
        requires (isIntersect(getFreeVarsInPat(A),.K,
                        getRidWrapper(X) getRidWrapper(Y)))
                 andBool notBool (isIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))
                       andBool hasNoDefinedPats(getValues(M, .K,
                           getIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))), .K))

   rule <k> getExpressionsAux(resultTransSetTerm(
                    N':Int, S:Set, A:K)) => .K ...</k>
        <currModule> Mod:K </currModule>
        <genVarCounter> N:Int => N' </genVarCounter>
        <moduleMethodNames> MM:Map => updateMapItem(MM, .K, Mod, S) </moduleMethodNames>
        <unnamedModuleExp> L:List (.List => ListItem(A)) </unnamedModuleExp>

   //dealing with method decl in a module
   rule getExpressions('topdeclslist('emptyGenDecl(.KList),, As:TopDecls))
           => getExpressions(As)

    rule <k> getExpressions('topdeclslist('varAssign(A:Vars,, T:Type),, As:TopDecls))
                 => error(classVarCollipse) ...</k>
         <currModule> Mod:K </currModule>
         <genVarCounter> N:Int </genVarCounter>
         <classMethodNames>... Mod |-> X:K ...</classMethodNames>
         <moduleMethodNames>... Mod |-> Y:K ...</moduleMethodNames>
         <module>...
            <moduleName> Mod:K </moduleName>
            <moduleMethods> M:Map </moduleMethods>
         ...</module>
        requires isIntersect(getFreeVarsInPat(A),.K,
                        getRidWrapper(X) getRidWrapper(Y))
                 andBool notBool (isIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))
                       andBool hasNoDefinedTypes(getValues(M, .K,
                           getIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))), .K))

    rule <k> getExpressions('topdeclslist('varAssign(A:Vars,, T:Type),, As:TopDecls))
                 => getExpressions(As) ...</k>
         <currModule> Mod:K </currModule>
         <genVarCounter> N:Int </genVarCounter>
         <classMethodNames>... Mod |-> X:K ...</classMethodNames>
         <moduleMethodNames>... Mod |-> (Y:K => addToSetInK(Y,
                  setMinus(getFreeVarsInPat(A),.K, getRidWrapper(Y)))) ...</moduleMethodNames>
         <module>...
            <moduleName> Mod:K </moduleName>
            <moduleMethods> M:Map => addDeclToMap(M, .K,
                getFreeVarsInPat(A), .Set, toAbsType(Mod, T)) </moduleMethods>
         ...</module>
        requires (notBool isIntersect(getFreeVarsInPat(A),.K,
                        getRidWrapper(X) getRidWrapper(Y)))
                 orBool (isIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))
                       andBool hasNoDefinedTypes(getValues(M, .K,
                           getIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))), .K))

    rule <k> getExpressions('topdeclslist('genAssignContext(
                       A:Vars,, C:Context,, T:Type),, As:TopDecls))
                 => getExpressions(As) ...</k>
         <currModule> Mod:K </currModule>
         <genVarCounter> N:Int </genVarCounter>
         <classMethodNames>... Mod |-> X:K ...</classMethodNames>
         <moduleMethodNames>... Mod |-> (Y:K => addToSetInK(Y,
                  setMinus(getFreeVarsInPat(A),.K, getRidWrapper(Y)))) ...</moduleMethodNames>
         <module>...
            <moduleName> Mod:K </moduleName>
            <moduleMethods> M:Map => addDeclToMap(M, .K,
                getFreeVarsInPat(A), contextToSet(Mod, C), toAbsType(Mod, T)) </moduleMethods>
         ...</module>
        requires (notBool isIntersect(getFreeVarsInPat(A),.K,
                        getRidWrapper(X) getRidWrapper(Y)))
                 orBool (isIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))
                       andBool hasNoDefinedTypes(getValues(M, .K,
                           getIntersect(getFreeVarsInPat(A),.K, getRidWrapper(Y))), .K))


endmodule
