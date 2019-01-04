//
requires "haskell-syntax.k"
requires "haskell-configuration.k"
requires "haskell-abstract-syntax.k"
requires "haskell-helper.k"
requires "haskell-errors.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX
    imports HASKELL-CONFIGURATION
    imports HASKELL-HELPER
    imports HASKELL-ERRORS

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

    rule nextNextChecks => checkAlphaNoLoops
                ~> (checkArgSortsAreTargets
                ~> checkParUsed)

    //deal with alpha map, deal with renaming of type name
    //collect information for the type name and kind in the same module
    rule <k> collectKindInfo => collectTypes(Mod, S, .Map) ...</k>
         <tempModule> S:K </tempModule>
         <currModule> Mod:K </currModule>

    rule <k> makeAlphaMap => makeAlphaM(S, .Map, .Map) ...</k>
         <tempModule> S:K </tempModule>

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

    rule <k> putKindMap(M:Map) => .K ...</k>
         <tempKindMap> _:Map => M </tempKindMap>

    //TODO: add dealing with kind inference for alpha map, and fix the generation of kind map
    rule <k> genKindMap => kindInfer(N, S, .K, .K, BM, M, .Set) ...</k>
         <tempBetaMap> BM:Map </tempBetaMap>
         <tempKindMap> M:Map </tempKindMap>
         <kindVarCounter> N:Int </kindVarCounter>
         <kindVarSet> S:Set </kindVarSet>

    rule <k> resultTyVarKind(N:Int, S:Set, M:Map) => .K ...</k>
         <tempKindMap> _:Map => M </tempKindMap>
         <kindVarCounter> _:Int => N </kindVarCounter>
         <kindVarSet> _:Set => S </kindVarSet>

    rule <k> checkPreBetaInScope
               => isAllValidTypes(M, .K, .K, keys(KM))
                  ~> isAllValidTypeVars(M, .K, .K) ...</k>
         <tempBetaMap> M:Map </tempBetaMap>
         <tempKindMap> KM:Map </tempKindMap>


   


endmodule
