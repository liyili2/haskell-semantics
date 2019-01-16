//
requires "haskell-syntax.k"
requires "haskell-configuration.k"
requires "haskell-abstract-syntax.k"
requires "haskell-helper.k"
requires "haskell-kindinfer.k"
requires "haskell-transformation.k"
requires "haskell-errors.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX
    imports HASKELL-CONFIGURATION
    imports HASKELL-HELPER
    imports HASKELL-ERRORS
    imports HASKELL-KINDINFER
    imports HASKELL-TRANSFORMATION

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
                ~> checkLandingDomResumes)))))) ...</k> */

    rule startChecks => checkNoSameKey
                ~> (checkTypeConsDontCollide
                ~> (collectKindInfo
                ~> (makeAlphaMap
                ~> nextChecks)))

    rule nextChecks => makePreBetaMap
                ~> (checkPreBetaInScope
                ~> (genKindMap
                ~> (nextNextChecks)))

    rule nextNextChecks => (checkArgSortsAreTargets
                ~> (checkParUsed
                ~> (initClassStartInfo
                 ~> collectClassInfo)))

    //deal with alpha map, deal with renaming of type name
    //collect information for the type name and kind in the same module
    rule <k> collectKindInfo => collectTypes(N, S, Mod, TM, .Map) ...</k>
         <tempModule> TM:K </tempModule>
         <currModule> Mod:K </currModule>
         <kindVarCounter> N:Int </kindVarCounter>
         <kindVarSet> S:Set </kindVarSet>

    rule <k> makeAlphaMap => makeAlphaM(Mod, S, .Map, .Map) ...</k>
         <tempModule> S:K </tempModule>
         <currModule> Mod:K </currModule>

    rule <k> putAlphaMap(M:Map) => .K ...</k>
         <tempAlphaMap> _:Map => M </tempAlphaMap>

    rule <k> putPreBetaMap(M:Map) => .K ...</k>
         <tempBetaMap> _:Map => M </tempBetaMap>

    /*deal with beta map, three steps
      first step is to collect information of a data/newtype, and put them in a list 
      and create a pre-beta-map from type con name to the list.
      REMEMBER to turn type structure into an abstract form.
      second step is to do kind check on the input datatype
      third step, resolve the pre-beta-map to beta map for the module. */
    rule <k> makePreBetaMap => makePreBetaFun(Mod, S, .Map) ...</k>
         <tempModule> S:K </tempModule>
         <currModule> Mod:K </currModule>

    //finish
    rule <k> genKindMap => kindInfer(N, S, .K, .K, AM BM, M, .Set) ...</k>
         <tempBetaMap> BM:Map </tempBetaMap>
         <tempAlphaMap> AM:Map </tempAlphaMap>
         <tempKindMap> M:Map </tempKindMap>
         <kindVarCounter> N:Int </kindVarCounter>
         <kindVarSet> S:Set </kindVarSet>

    rule <k> resultTyVarKindMap(N:Int, S:Set, M:Map) => .K ...</k>
         <tempKindMap> _:Map => M </tempKindMap>
         <kindVarCounter> _:Int => N </kindVarCounter>
         <kindVarSet> _:Set => S </kindVarSet>

    rule <k> checkPreBetaInScope
               => isAllValidTypes(AM M, .K, .K, keys(KM))
                  ~> isAllValidTypeVars(AM M, .K, .K) ...</k>
         <tempBetaMap> M:Map </tempBetaMap>
         <tempKindMap> KM:Map </tempKindMap>
         <tempAlphaMap> AM:Map </tempAlphaMap>


    //deal with type classes. type classes ast gen
    rule <k> initClassStartInfo => .K ...</k>
         <currModule> Mod:K </currModule>
         <classMethodNames> CM:Map (.Map => (Mod |-> resultSet(.Set))) </classMethodNames>
         <classClassNames> NM:Map (.Map => (Mod |-> resultSet(.Set))) </classClassNames>
    
   //functions to compile type classes to ast form
    rule <k> collectClassInfo => getClassInfo(TM) ...</k>
         <tempModule> TM:K </tempModule>

    rule getClassInfo('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls))
               => getClassInfo(Ts)
    rule getClassInfo('bodyimpdecls(Is:ImpDecls)) => .K
    rule getClassInfo('bodytopdecls(Ts:TopDecls)) => getClassInfo(Ts)
    rule getClassInfo(.TopDecls) => .K

    rule <k> getClassInfo('topdeclslist('class(Cs:OptContext,,
                  Name:ConId,, Tv:TyVar,, Ds:OptCDecls),, As:TopDecls))
               => getClassInfoAux(fullName(Mod, Name),Tv, contextToSet(Mod, Cs),
                    toAstTypeClass(Mod, Tv, Ds, .Map,
                    getMethodSet(Mod, .K, CM)), Ds, As) ...</k>
         <currModule> Mod:K </currModule>
         <classMethodNames> CM:Map </classMethodNames>
         <classClassNames> NM:Map </classClassNames>
         requires notBool hasClassName(Mod, Name, .K, NM)

    rule <k> getClassInfo('topdeclslist('class(Cs:OptContext,,
                  Name:ConId,, Tv:TyVar,, Ds:OptCDecls),, As:TopDecls))
               => error(classVarCollipse) ...</k>
         <currModule> Mod:K </currModule>
         <classClassNames> NM:Map </classClassNames>
         requires hasClassName(Mod, Name, .K, NM)

   rule getClassInfoAux(Name:K, Tv:K, S:Set, error(A:K), Ds:K, As:K) => error(A)
   rule <k> getClassInfoAux(Name:K, Tv:K, S:Set,
               putClassMapSet(Methods:Map, MS:Set), Ds:K, As:K)
            => getClassInfoAuxAux(Name, toAstPat(N, Mod, Ds, .K, .K, Methods))
                 ~> getClassInfo(As) ...</k>
         <genVarCounter> N:Int </genVarCounter>
         <currModule> Mod:K </currModule>
         <classMethodNames> CM:Map => CM[Mod <- resultSet(MS)] </classMethodNames>
         <classClassNames> NM:Map </classClassNames>
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

endmodule
