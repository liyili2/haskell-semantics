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

    //also checked if all defs are unique in a module in collectCheckDefs
    rule checkDefs => collectCheckDefs
                        ~> (checkAllDeclMakeSense
                        ~> (checkAllFixityMakeSense
                        ~> genRecordFunctions))

    rule nextChecks => makePreBetaMap
                ~> (grabAllTypeNames
                ~> (genKindMap
                ~> (checkOnlyDefault
            //checkArgSortsAreTargets //checkParUsed
                ~> nextNextChecks)))

    rule nextNextChecks => collectClassInfo
                //TODO: check kind for class and derivings for data types are all star -> star kind
                ~> (kindInferClass
                ~> (derivingClassChecks
                ~> (collectExpressions
                ~> genInstanceChecks)))

    rule genInstanceChecks => initialInstanceInModule
                                  ~> ((collectInstances
                                    ~> kindCheckInstance)
                                      ~> checkInstanceParents)

    rule genModuleChecks => genAllModuleNames
                         ~> (genExportSet
                         ~> checkAllImportsGoodFromExports)

    //collect all defs in a module
    rule <k> collectCheckDefs => collectCheckDefs(B, .Set) ...</k>
         <tempModule> B:K </tempModule>

    rule <k> putDefSet(S:Set) => .K ...</k>
         <currModule> X:K </currModule>
         <moduleName> X </moduleName>
         <moduleDefs> _:Set => S </moduleDefs>

   //check if all fixities in a module is defined in the module also
   rule <k> checkAllFixityMakeSense => checkAllFixityMakeSense(B, .Set, S) ...</k>
         <tempModule> B:K </tempModule>
         <currModule> X:K </currModule>
         <moduleName> X </moduleName>
         <moduleDefs> S:Set </moduleDefs>

   //check if all decl in a module is defined in the module also
   rule <k> checkAllDeclMakeSense => checkAllDeclMakeSense(B, .Set, S) ...</k>
         <tempModule> B:K </tempModule>
         <currModule> X:K </currModule>
         <moduleName> X </moduleName>
         <moduleDefs> S:Set </moduleDefs>

   //generate a map for all functions of getting field content for a module
    rule <k> genRecordFunctions => genRecordFunctions(N, X, B, .Map) ...</k>
         <tempModule> B:K </tempModule>
         <currModule> X:K </currModule>
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
        //<classMethodNames> CM:Map => CM[A <- resultSet(.Set)] </classMethodNames>
        <classNames> NM:Map => NM[A <- resultSet(.Set)] </classNames>
        (.Bag => <module>...
                    <moduleName> A </moduleName>
                ...</module>)

   rule <k> 'module('moduleName(A:ModId),, B:K) => startChecks ...</k>     
        <tempModule> _:K => B </tempModule>
        <currModule> _:K => A </currModule>
        <moduleMethodNames> MM:Map => MM[A <- resultSet(.Set)] </moduleMethodNames>
        //<classMethodNames> CM:Map => CM[A <- resultSet(.Set)] </classMethodNames>
        <classNames> NM:Map => NM[A <- resultSet(.Set)] </classNames>
        <exports> Ex:Map => Ex[A <- resultSet(SetItem(haveAll))] </exports>
        (.Bag => <module>...
                    <moduleName> A </moduleName>
                ...</module>)

   rule <k> 'moduleBody(B:K) => startChecks ...</k>     
        <tempModule> _:K => B </tempModule>
        <currModule> _:K => Main </currModule>
        <moduleMethodNames> MM:Map => MM[Main <- resultSet(.Set)] </moduleMethodNames>
       // <classMethodNames> CM:Map => CM[Main <- resultSet(.Set)] </classMethodNames>
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
   /*rule <k> genAllModuleNames
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
        <moduleElems> _:Set => S </moduleElems> */

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
         <moduleDefs> Ts:Set </moduleDefs>
         <imports> Is:Set </imports>

    //finish
    rule <k> genKindMap => grabImportKindMaps(.K, S, .Map) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <imports> S:Set </imports>

    rule <k> grabImportKindMaps(.K, .Set, Ks:Map)
           => grabImportKindMapsAux(genInitKindMap(N, S, .K, .K, AM, BM)) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <importKindMap> _:Map => Ks </importKindMap>
         <tempBetaMap> BM:Map </tempBetaMap>
         <moduleAlpha> AM:Map </moduleAlpha>
         <kindVarCounter> N:Int </kindVarCounter>
         <kindVarSet> S:Set </kindVarSet>

    rule <k> grabImportKindMapsAux(resultTyVarKindMap(N:Int, S:Set, TM:Map)) =>
               kindInfer(N, S, Mod, .K, .K, AM BM, TM, .Set, Is, Ks) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <importKindMap> Ks:Map </importKindMap>
         <tempBetaMap> BM:Map </tempBetaMap>
         <moduleAlpha> AM:Map </moduleAlpha>
         <imports> Is:Set </imports>

    rule grabImportKindMaps(.K, SetItem(A:K) S:Set, KM:Map)
                => grabImportKindMaps(A, S, KM)

    rule <k> grabImportKindMaps(importElem(Mod:K, _:K, _:Bool,
                   Ts:Set, _:Map), S:Set, KM:Map)
                => grabImportKindMaps(.K, S,
                             addKindToMap(Mod, .K, Ts, SM, KM)) ...</k>
         <moduleName> Mod </moduleName>
         <kindMap> SM:Map </kindMap>

    rule <k> resultTyVarKindMap(N:Int, S:Set, M:Map) => .K ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <kindMap> M':Map => M M' </kindMap>
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
               => getClassInfoAux(className(Name),Tv,
                    contextToSet(Mod, Cs, .K, .Set, Ts, Is),
                    toAstTypeClass(Mod, Tv, Ds, .Map, Ts, Is), Ds, As) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <moduleDefs> Ts:Set </moduleDefs>
         <imports> Is:Set </imports>
         <classNames> NM:Map => updateMapItem(NM,
                          .K, Mod, SetItem(className(Name))) </classNames>
         requires isSContext(Cs)

    rule getClassInfo('topdeclslist('class(Cs:OptContext,,
                  Name:ConId,, Tv:TyVar,, Ds:OptCDecls),, As:TopDecls))
               => error(syntaxError)
         requires notBool isSContext(Cs)

   rule getClassInfoAux(Name:K, Tv:K, error(A:K), T:K, Ds:K, As:K) => error(A)
   rule getClassInfoAux(Name:K, Tv:K, A:K, error(B:K), Ds:K, As:K) => error(B)
   rule <k> getClassInfoAux(Name:K, Tv:K, resultSet(S:Set),
               resultMap(Methods:Map), Ds:K, As:K)
            => checkAllFixityMakeSenseInCDecl(Ds, .Set, dropFullNames(.K, keys(Methods)))
                 ~> (getClassInfoAuxAux(Name, toAstPat(N, Mod, Ds, .K, .K, Methods, Ts, Is))
                 ~> getClassInfo(As)) ...</k>
         <genVarCounter> N:Int </genVarCounter>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <moduleDefs> Ts:Set </moduleDefs>
         <imports> Is:Set </imports>
         <classNames> NM:Map </classNames>
         (.Bag => <class>...
                     <classModule> Mod </classModule>
                     <className> Name </className>
                     <classTypeVar> Tv </classTypeVar>
                     <classContext> S </classContext>
                  ...</class>)

    rule getClassInfoAuxAux(Name:K, error(A:K)) => error(A)
    rule <k> getClassInfoAuxAux(Name:K, resultIntMap(N':Int, M:Map)) => .K ...</k>
         <genVarCounter> N:Int => N' </genVarCounter>
         <class>...
             <classModule> Mod </classModule>
             <className> Name </className>
             <classMethods> _:Map => M </classMethods>
         ...</class>


   //kind inference on classes
   //assuming that kind inferencing on data-type has been done.
    rule <k> kindInferClass
                => genInitKindMapClass(getRidWrapper(A)) ...</k>
         <currModule> Mod:K </currModule>
         <classNames>... Mod |-> A:K ...</classNames>

    rule <k> genInitKindMapClass(SetItem(A:K) S:Set)
                => genInitKindMapClass(S) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <classModule> Mod:K </classModule>
         <className> A </className>
         <classTypeVar> T:K </classTypeVar>
         <classKind> _:K => kindVar(N) </classKind>
         <kindVarCounter> N:Int => N +Int 1 </kindVarCounter>
         <kindVarSet> S:Set (.Set => SetItem(kindVar(N))) </kindVarSet>
         <kindMap> M:Map => M[A <- kindArrow(kindVar(N), star)] </kindMap>

    rule <k> genInitKindMapClass(.Set) =>
               buildContextMap(.Map, .K, keys(M)) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <kindMap> M:Map </kindMap>
 
    //second step, building a map from class-name to contexts
    rule <k> buildContextMap(TM:Map, .K, .Set)
                => kindClass(N, S, .Set, .K, TM, .Set, KM, Is, PM) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <kindVarCounter> N:Int </kindVarCounter>
         <kindVarSet> S:Set </kindVarSet>
         <kindMap> KM:Map </kindMap>
         <importKindMap> PM:Map </importKindMap>
         <classContextMap> _:Map => TM </classContextMap>
         <imports> Is:Set </imports>

    rule buildContextMap(M:Map, .K, SetItem(A:K) S:Set)
             => buildContextMap(M, A, S)
    rule <k> buildContextMap(M:Map, className(A:K), S:Set)
                  => buildContextMap(M (className(A:K)
                       |-> resultSet(getCoreClass(Cs)
                             getContextsMethods(FM, .K, Tv))), .K, S) ...</k>
         <currModule> Mod:K </currModule>
         <class>...
                <classModule> Mod </classModule>
                <className> className(A:K) </className>
                <classContext> Cs:Set </classContext>
                <classMethods> FM:Map </classMethods>
                <classTypeVar> Tv:K </classTypeVar>
         ...</class>

   //third, start kind infer on each class
   //then goes to check contexts. 
   //assume that all contexts for a class on the class type-var
   //are not circular.
   //also assume that for all contexts for a method in a class,
   // their bounded type-vars must appear in the type annotation body of the method.
   rule <k> kindClass(N:Int, S:Set, Rs:Set, .K, .Map,
                  Tu:Set, KM:Map, Is:Set, PM:Map)
             => kindClassCheck(checkAndRemoveNoVarTerms(.K, Tu, .Set), KM) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <kindVarCounter> _:Int => N </kindVarCounter>
         <kindVarSet> _:Set => S </kindVarSet>

   rule kindClassCheck(error(A:K), KM:Map) => error(classKindNotEqual)
   rule kindClassCheck(resultSet(Ts:Set), KM:Map)
          => kindClassCheck(unifInKind(.K, .Set, Ts, .Map), KM)

   rule <k> kindClassCheck(resultMap(M:Map), KM:Map)
          => kindClassNoKindVar(M, replaceAllKindInMap(
                M, KM), getRidWrapper(C), .K, .K, .Set, .Map) ...</k>
        <currModule> Mod:K </currModule>
        <classNames>... Mod |-> C:K  ...</classNames>

   rule kindClassNoKindVar(RM:Map, KM:Map, .Set, .K, .K, Tu:Set, XM:Map)
           => kindClassCheck2(checkAndRemoveNoVarTerms(
                 .K, toKindTuples(RM) Tu, .Set), KM, XM)
   rule <k> kindClassNoKindVar(RM:Map, KM:Map,
               SetItem(A:K) S:Set, .K, .K, Tu:Set, XM:Map)
               => kindClassNoKindVar(RM, KM, S, A,
                  staringAllNonCheckedVarsInMethod(
                       replaceAllKindInMethodMap(RM, .K, .K, MM),
                         .K, .K, .K, .Set, .Map), Tu:Set, XM:Map) ...</k>
        <currModule> Mod:K </currModule>
         <class>...
                <classModule> Mod </classModule>
                <className> A </className>
                <classMethods> MM:Map </classMethods>
         ...</class>

   rule kindClassNoKindVar(RM:Map, KM:Map, S:Set, A:K,
                 resultSetMap(Tu':Set, MM:Map), Tu:Set, XM:Map)
           => kindClassNoKindVar(RM, KM, S, .K, .K, Tu' Tu, (A |-> resultMap(MM)) XM)

   rule kindClassCheck2(error(A:K), KM:Map, XM:Map) => error(classKindNotEqual)
   rule kindClassCheck2(resultSet(Ts:Set), KM:Map, XM:Map)
          => kindClassCheck2(unifInKind(.K, .Set, Ts, .Map), KM, XM)
   rule kindClassCheck2(resultMap(M:Map), KM:Map, XM:Map)
          => kindClassCheck3(replaceAllKindInMap(
                M, KM), replaceAllKindInClassMap(M,.K, .K, XM))

   rule kindClassCheck3(KM:Map, XM:Map) => error(noEnoughInformationForKindVar)
        requires notBool hasNoKindVarsInKindMap(KM, .K)
                  orBool notBool hasNoKindVarsInClassMap(XM, .K)
   rule kindClassCheck3(KM:Map, XM:Map) => kindClassFinal(KM:Map, XM:Map)
        requires hasNoKindVarsInKindMap(KM, .K)
                  andBool hasNoKindVarsInClassMap(XM, .K)

   rule <k> kindClassCheck2(resultMap(M:Map), KM:Map, XM:Map)
          => kindClassCheck3(replaceAllKindInMap(
                M, KM), replaceAllKindInClassMap(M,.K, .K, XM)) ...</k>
        <currModule> Mod:K </currModule>
        <classNames>... Mod |-> C:K  ...</classNames>

   rule <k> kindClassFinal(KM:Map, .Map) => .K ...</k>
        <currModule> Mod:K </currModule>
        <moduleName> Mod:K </moduleName>
        <kindMap> M:Map => KM </kindMap>

   rule <k> kindClassFinal((A |-> kindArrow(X:K, star)) KM:Map,
               (A |-> resultMap(MM':Map)) XM:Map)
               => kindClassFinal((A |-> kindArrow(X:K, star)) KM:Map, XM) ...</k>
        <currModule> Mod:K </currModule>
         <class>...
                <classModule> Mod </classModule>
                <className> A </className>
                <classKind> _:K => X </classKind>
                <classMethods> MM:Map => MM' </classMethods>
         ...</class>
 
   rule kindClass(N:Int, S:Set, Rs:Set, .K, CM:Map, Tu:Set, KM:Map, Is:Set, PM:Map)
               => kindClass(N, S, Rs, searchNoFatherClass(
                               .K, .K, CM, Rs, PM), CM, Tu, KM, Is, PM)
   rule kindClass(N:Int, S:Set, Rs:Set, error(A:K),
           CM:Map, Tu:Set, KM:Map, Is:Set, PM:Map) => error(A)
   rule <k> kindClass(N:Int, S:Set, Rs:Set,
             resultTupleSet(className(A:K), CCs:Set),
                (className(A:K) |-> _:K) CM:Map, Tu:Set, KM:Map, Is:Set, PM:Map)
          => kindClassAux(SetItem(fullName(Mod, className(A:K))) Rs, 
               className(A), kindInferClass(N, S, Mod,
                       F, .K, MM, Cs, (F |-> TK) KM, Is, PM),
                    CM, Tu, KM, Is, PM) ...</k>
         <currModule> Mod:K </currModule>
         <class>...
                <classModule> Mod </classModule>
                <className> className(A:K) </className>
                <classTypeVar> F:K </classTypeVar>
                <classKind> TK:K </classKind> 
                <classContext> Cs:Set </classContext>
                <classMethods> MM:Map </classMethods>
         ...</class>

    rule kindClassAux(Rs:Set, CName:K, error(A:K),
             CM:Map, Tu:Set, KM:Map, Is:Set, PM:Map) => error(A)
    rule <k> kindClassAux(Rs:Set, CName:K, resultKindTupleMap(N:Int, S:Set, Tu:Set, AM:Map),
             CM:Map, Tu':Set, KM:Map, Is:Set, PM:Map)
                => kindClass(N, S, Rs, .K, CM, Tu Tu', KM, Is, PM) ...</k>
         <currModule> Mod:K </currModule>
         <class>...
                <classModule> Mod </classModule>
                <className> CName </className>
                <classMethods> _:Map => AM </classMethods>
         ...</class>


    //check all contexts having correct kinds
    rule derivingClassChecks
                => (allDerivingClassHasDefault
                     ~> derivingKindMakeSense)
    rule <k> allDerivingClassHasDefault
              => classHasDefault(TM, .K) ...</k>
         <tempBetaMap> TM:Map </tempBetaMap>

    //checking every class involving in deriving class has an default
    rule classHasDefault(.Map, .K) => .K
    rule classHasDefault((A:K |-> B:K) M:Map, .K)
              => classHasDefault(M, B)
    rule classHasDefault(M:Map, preBetaEntry(L:List, X:Map, S:Set))
              => classHasDefaultAux(M:Map, S, .K)

    rule classHasDefaultAux(M:Map, .Set, .K) => classHasDefault(M, .K)
    rule classHasDefaultAux(M:Map, SetItem(A:K) S:Set, .K)
              => classHasDefaultAux(M, S, A)
    rule <k> classHasDefaultAux(M:Map, S:Set, fullName(Mod:K, A:K))
                => classHasDefaultAux(M, S, .K) ...</k>
         <class>...
                <classModule> Mod </classModule>
                <className> A:K </className>
                <classMethods> MM:Map </classMethods>
         ...</class>
         requires notEmptyMethodDecl(MM, .K)

    rule <k> classHasDefaultAux(M:Map, S:Set, fullName(Mod:K, A:K))
                => error(derivingClassHasNoDefault) ...</k>
         <class>...
                <classModule> Mod </classModule>
                <className> A:K </className>
                <classMethods> MM:Map </classMethods>
         ...</class>
         requires notBool notEmptyMethodDecl(MM, .K)

    //checking every class involving in deriving class has kind instance
    rule <k> derivingKindMakeSense
              => derivingKindMakeSense(TM, .K, .K) ...</k>
         <tempBetaMap> TM:Map </tempBetaMap>

    rule derivingKindMakeSense(.Map, .K, .K) => .K
    rule derivingKindMakeSense((A:K |-> B:K) M:Map, .K, .K)
              => derivingKindMakeSense(M, A, B)
    rule <k> derivingKindMakeSense(M:Map, A:K, preBetaEntry(L:List, X:Map, S:Set))
              => derivingKindMakeSenseAux(M:Map, kindToList(C), S, .K) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod:K </moduleName>
         <kindMap>... A |-> C:K ...</kindMap>

    rule derivingKindMakeSenseAux(M:Map, A:List, .Set, .K)
           => derivingKindMakeSense(M, .K, .K)
    rule derivingKindMakeSenseAux(M:Map, X:List, SetItem(A:K) S:Set, .K)
              => derivingKindMakeSenseAux(M, X, S, A)
    rule <k> derivingKindMakeSenseAux(M:Map, X:List, S:Set, fullName(Mod:K, A:K))
                => derivingKindMakeSenseAux(M, X, S, .K) ...</k>
         <class>...
                <classModule> Mod </classModule>
                <className> A:K </className>
                <classKind> B:K </classKind>
         ...</class>
         requires derivingKindMatching(X, B)

    rule <k> derivingKindMakeSenseAux(M:Map, X:List, S:Set, fullName(Mod:K, A:K))
                => error(derivingClassNoKindMatching) ...</k>
         <class>...
                <classModule> Mod </classModule>
                <className> A:K </className>
                <classKind> B:K </classKind>
         ...</class>
         requires notBool derivingKindMatching(X, B)


   //functions to compile type class instances to ast form
   rule <k> initialInstanceInModule => .K ...</k>
        <currModule> Mod:K </currModule>
        <instanceNames> M:Map => M[Mod <- resultSet(.Set)] </instanceNames>

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
           => getInstancesAux(Cs,transExpCon(Mod, Name, Ts, Is), Tv, Ds, As) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <moduleDefs> Ts:Set </moduleDefs>
         <imports> Is:Set </imports>

    rule getInstancesAux(Cs:K, error(A:K), Tv:K, Ds:K, As:K) => error(A)
    rule <k> getInstancesAux(Cs:K, fullName(Mod':K, Name:K), Tv:K, Ds:K, As:K)
            => getInstancesNext(transInstance(
                   N, Mod, Cs, Name, Tv, Ds,
                   genInstanceMapClass(MM, .K, .K), Ts, Is), As) ...</k>
         <genVarCounter> N:Int </genVarCounter>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <moduleDefs> Ts:Set </moduleDefs>
         <imports> Is:Set </imports>
         <class>...
                <classModule> Mod':K </classModule>
                <className> Name </className>
                <classMethods> MM:Map </classMethods>
         ...</class>

    rule getInstancesNext(error(A:K), As:K) => error(A)
    rule <k> getInstancesNext(returnInstance(N:Int,
                Cs:Set, A:K, As:Set, T:K, M:Map), As':K)
                   => getInstances(As') ...</k>
         <genVarCounter> _:Int => N </genVarCounter>
         <currModule> Mod:K </currModule>
         <instanceNames> M:Map => updateMapItem(M, .K, Mod,
                    SetItem(instanceTuple(A, getInstanceType(T)))) </instanceNames>
         (.Bag => <instance>
                   <instanceModule> Mod </instanceModule>
                   <instanceClass> A </instanceClass>
                   <instanceType> getInstanceType(T) </instanceType>
                   <instanceVarMap> setUpContextMethodAux(
                               makeVarContextMap(As), .K, Cs) </instanceVarMap>
                   <instanceContext> Cs </instanceContext>
                   <instanceMethods> M </instanceMethods>
                  </instance>)
         requires notBool isInMapSet(instanceTuple(A, getInstanceType(T)), M, .K)

    rule <k> getInstancesNext(returnInstance(N:Int,
                Cs:Set, A:K, As:Set, T:K, M:Map), As':K)
                => error(duplicateInstance) ...</k>
         <currModule> Mod:K </currModule>
         <instanceNames> M:Map </instanceNames>
         requires isInMapSet(instanceTuple(A, getInstanceType(T)), M, .K)

    rule <k> kindCheckInstance
                 => kindCheckInstance(As, N, S, Mod, KM, Is, PM) ...</k>
         <currModule> Mod:K </currModule>
         <moduleName> Mod </moduleName>
         <kindVarCounter> N:Int </kindVarCounter>
         <kindVarSet> S:Set </kindVarSet>
         <kindMap> KM:Map </kindMap>
         <importKindMap> PM:Map </importKindMap>
         <imports> Is:Set </imports>
         <instanceNames>... Mod |-> resultSet(As:Set) ...</instanceNames>

    rule <k> kindCheckInstance(.Set, N:Int, S:Set,
                       Mod:K, KM:Map, Is:Set, PM:Map) => .K ...</k>
         <kindVarCounter> _:Int => N </kindVarCounter>
         <kindVarSet> _:Set => S </kindVarSet>

    rule <k> kindCheckInstance(SetItem(instanceTuple(A:K, T:K)) As:Set,
               N:Int, S:Set, Mod:K, KM:Map, Is:Set, PM:Map) =>
               kindCheckInstanceAux(As, kindSingleInstance(N, S, Mod,
                     A, Cs, Fs, T, KM,Is, PM),
                       A, T, Mod, KM, Is, PM) ...</k>
         <instance>...
             <instanceModule> Mod </instanceModule>
             <instanceClass> A </instanceClass>
             <instanceType> T </instanceType>
             <instanceVarMap> Fs:Map </instanceVarMap>
             <instanceContext> Cs:Set </instanceContext>
         ...</instance>

    rule kindCheckInstanceAux(As:Set, error(A:K),
              A:K, T:K, Mod:K, KM:Map, Is:Set, PM:Map) => error(A)
    rule <k> kindCheckInstanceAux(As:Set, resultTransSetMap(N:Int, S:Set, Fs:Map),
               A:K, T:K, Mod:K, KM:Map, Is:Set, PM:Map)
              => kindCheckInstance(As, N, S, Mod, KM, Is, PM) ...</k>
         <instance>...
             <instanceModule> Mod </instanceModule>
             <instanceClass> A </instanceClass>
             <instanceType> T </instanceType>
             <instanceVarMap> _:Map => Fs </instanceVarMap>
         ...</instance>

   //check if an instance's parrent classes
   // have all properly instantiated by the same type
   rule <k> checkInstanceParents => checkInstanceParents(As, .K) ...</k>
         <currModule> Mod:K </currModule>
         <instanceNames>... Mod |-> resultSet(As:Set) ...</instanceNames>

   rule checkInstanceParents(.Set, .K) => .K
   rule checkInstanceParents(SetItem(A:K) S:Set, .K)
                    => checkInstanceParents(S, A)
   rule <k> checkInstanceParents(S:Set,
              instanceTuple(fullName(Mod:K, A:K), T:K))
                => checkInstanceParent(Cs, .K, T, Ts, Is)
                 ~> checkInstanceParents(combineClassType(Cs, .K, T) S, .K) ...</k>
         <currModule> Mod':K </currModule>
         <moduleName> Mod' </moduleName>
         <moduleDefs> Ts:Set </moduleDefs>
         <imports> Is:Set </imports>
        <class>...
          <classModule> Mod </classModule>
          <className> A:K </className>
          <classContext> Cs:Set </classContext>
        ...</class>

   //transformation of expressions in a module
   //also check the kind information of each decl with the contexts.
   //two checks. First, every bounded vars in the contexts must be
   //a type-var in the type annotation,
   // otherwise, the function cannot be used in a reasonable way,
   //because the type constraint cannot be satisfied. 
   //Second, check kind for each method
   rule <k> collectExpressions
               => getExpressions(transDeclFun(N, Mod, TM, Ts, Is, .Map, .Map))
                  ~> (allContextsMakeSense
                   ~> (setUpContextsForVars
                    ~> checkKindInExpressions)) ...</k>
        <tempModule> TM:K </tempModule>
        <genVarCounter> N:Int </genVarCounter>
        <currModule> Mod:K </currModule>
        <moduleName> Mod </moduleName>
         <moduleDefs> Ts:Set </moduleDefs>
         <imports> Is:Set </imports>

   rule getExpressions(error(A:K)) => error(A)

   rule <k> getExpressions(resultTransMapMap(N:Int, M:Map, RM:Map))
             => .K ...</k>
        <genVarCounter> _:Int => N </genVarCounter>
        <currModule> Mod:K </currModule>
        <moduleName> Mod </moduleName>
        <moduleMethods> _:Map => M </moduleMethods>
        <moduleRefs> _:Map => RM </moduleRefs>

   rule <k> allContextsMakeSense => isContextsMakeSense(M, .K) ...</k>
        <currModule> Mod:K </currModule>
        <moduleName> Mod </moduleName>
        <moduleMethods> M:Map </moduleMethods>

   rule <k> setUpContextsForVars => .K ...</k>
        <currModule> Mod:K </currModule>
        <moduleName> Mod </moduleName>
        <moduleMethods> M:Map => setUpContextMethod(M, .K, .K) </moduleMethods>

   rule <k> checkKindInExpressions
            => checkKindInExpFinal(kindInferExp(N, S, Mod, .Map, .K, .K, M, KM, Is, PM)) ...</k>
        <currModule> Mod:K </currModule>
        <moduleName> Mod </moduleName>
        <moduleMethods> M:Map </moduleMethods>
        <importKindMap> PM:Map </importKindMap>
        <imports> Is:Set </imports>
        <kindMap> KM:Map </kindMap>
        <kindVarCounter> N:Int </kindVarCounter>
        <kindVarSet> S:Set </kindVarSet>

   rule checkKindInExpFinal(error(A:K)) => error(A)

   rule <k> checkKindInExpFinal(resultMap(AM:Map)) => .K ...</k>
        <currModule> Mod:K </currModule>
        <moduleName> Mod </moduleName>
        <moduleMethods> M:Map => AM </moduleMethods>

endmodule
