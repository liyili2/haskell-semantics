//helper functions for the haskell semantics.
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"
requires "haskell-helper.k"

module HASKELL-KINDINFER
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX
    imports HASKELL-HELPER

   //a helper function to transform concrete type to abstract type
   syntax Int ::= typeTupleCount(TypeTuple) [function]
   rule typeTupleCount('twoTypeTuple(A:K,, B:K)) => 2
   rule typeTupleCount('typeTupleCon(A:K,, B:K)) => 1 +Int typeTupleCount(B)

   syntax KItem ::= dealWithTuple(K) [function]
   rule dealWithTuple('tupleFun(A:GConCommas)) => tupleType(countOnCommas(A))
   rule dealWithTuple(A:K) => A [owise]

   syntax Map ::= classContentToList(K, K, K, Map, Map, Map) [function]
                   //module, class, decls, type-map, constr-map, import-map
                | singleContentToList(K,K, CDecl, Map, Map, Map) [function]
                | varAssignToList(K,K, Vars, Type, Map, Map, Map) [function]

/*          //mod, cdecls, global type map
   rule classContentToList(Mod:K, C:K, 'emptyOptCDecls(.KList), TM:Map, CM:Map, IM:Map) => .Map
   rule classContentToList(Mod:K,C:K, 'cdeclWhere('cdeclBracket(Cs:CDeclsList)), TM:Map, CM:Map, IM:Map)
            => classContentToList(Mod,C, Cs, TM, CM, IM)
   rule classContentToList(Mod:K,C:K, .CDeclsList, TM:Map, CM:Map, IM:Map) => .Map
   rule classContentToList(Mod:K,D:K, 'cdeclCon(C:CDecl,, Cs:CDeclsList), TM:Map, CM:Map, IM:Map)
           => singleContentToList(Mod,D, C, TM, CM, IM) classContentToList(Mod,D, Cs, TM, CM,IM)
   rule singleContentToList(Mod:K, C:K, 'emptyGenDecl(.KList), TM:Map, CM:Map, IM:Map) => .Map
   rule singleContentToList(Mod:K,C:K, 'varAssign(As:Vars,, T:Type), TM:Map, CM:Map, IM:Map)
              => varAssignToList(Mod,C, As, T, TM, CM,IM)

   rule varAssignToList(Mod:K, V:Var, T:Type, TM:Map, CM:Map, IM:Map)
                  => V |-> T
   rule varAssignToList(Mod:K, 'varCon(V:Var,, Vs:Vars), T:Type, TM:Map)
                => (V |-> T) varAssignToList(Mod, Vs, T, TM)

*/
   syntax KItem ::= getImports(Body) [function]
   rule getImports('bodyimpandtop(A:ImpDecls,, B:TopDecls)) => A
   rule getImports('bodyimpdecls(A:ImpDecls)) => A
   rule getImports('bodytopdecls(A:TopDecls)) => .ImpDecls

   syntax KItem ::= dealWithOpt(K) [function]
   rule dealWithOpt('emptyQualified(.KList)) => .K
   rule dealWithOpt('emptyOptAsModId(.KList)) => .K
   rule dealWithOpt('emptyOptImpSpec(.KList)) => .K
   rule dealWithOpt(A:K) => A [owise]

   //delete a module instance in import map
   syntax Map ::= deleteImport(Map, K, K, K) [function]
   rule deleteImport(.Map, .K, .K, X:K) => .Map
   rule deleteImport((A:K |-> B:K) M:Map, .K, .K, X:K)
               => deleteImport(M, A, B, X)
   rule deleteImport(M:Map, A:K, names(S:Set), A:K)
            => deleteImport(M:Map, .K, .K, A:K)
   rule deleteImport(M:Map, A:K, names(S:Set), X:K)
          => (A |-> names(S -Set SetItem(X))) deleteImport(M, .K, .K, X)
        requires A =/=K X

   //select a module that has no father
   syntax KItem ::= selectNoFather(K, K, Map) [function]
   rule selectNoFather(.K, .K, .Map) => none
   rule selectNoFather(.K, .K, (A:K |-> B:K) M:Map)
         => selectNoFather(A, B, M)
   rule selectNoFather(A:K, names(.Set), M:Map) => A
   rule selectNoFather(A:K, names(SetItem(B:K) S:Set), M:Map)
             => selectNoFather(.K, .K, M)

   //functions to check if an adding edge will cause the graph to have cycle
   syntax Bool ::= hasCycle(K, K, K, Map) [function] //target, source, next-targets, graph
                 | hasCycleAux(K, Set, Map) [function]//target, next-targets, graph
   rule hasCycle(A:K, B:K, .K, M:Map) => false
        requires notBool B in keys(M)
   rule hasCycle(A:K, B:K, .K, (B |-> N:K) M:Map)
         => hasCycle(A, B, N, M)
   rule hasCycle(A:K, B:K, names(S:Set), M:Map) => true
        requires A in S
   rule hasCycle(A:K, B:K, names(S:Set), M:Map)
         => hasCycleAux(A, S, M)

   rule hasCycleAux(A:K, .Set, M:Map) => false
   rule hasCycleAux(A:K, SetItem(B:K) S:Set, M:Map)
           => hasCycle(A, B, .K, M) orBool hasCycleAux(A, S, M)

   //make a alpha map from the input 
   //also check if the alpha has a cycle, and also check if the module has two same name type decls.
   //also check if every type vars in a type decl is defined in the type vars of the type decl name.
   /*syntax Bool ::= isAType(K) [function]
   rule isAType(type A:SimpleType = B:Type) => true
   rule isAType(_:K) => false [owise] */

   syntax Set ::= getConstrNames(K) [function]
   rule getConstrNames('simpleTypeCon(A:TyCon,, B:TyVars)) => SetItem(A)
   rule getConstrNames(T:TyCon) => SetItem(T)
   rule getConstrNames('conTyCon(A:ModId,,T:TyCon)) => .Set
   rule getConstrNames('tupleCover(Ts:TypeTuple)) => getConstrNames(Ts)
   rule getConstrNames('tyList(T:K)) => getConstrNames(T)
   rule getConstrNames('group(T:K)) => getConstrNames(T)
   rule getConstrNames('baTypeCon(T1:K,, T2:K)) => getConstrNames(T1) getConstrNames(T2) 
   rule getConstrNames('typeArrow(T1:K,, T2:K)) => getConstrNames(T1) getConstrNames(T2) 
   rule getConstrNames('twoTypeTuple(T1:K,, T2:K)) => getConstrNames(T1) getConstrNames(T2) 
   rule getConstrNames('typeTupleCon(T1:K,, T2:K)) => getConstrNames(T1) getConstrNames(T2) 
   rule getConstrNames(T:K) => .Set [owise]

   syntax Set ::= getTypeNames(K) [function]
   rule getTypeNames('simpleTypeCon(A:TyCon,, B:TyVars)) => getTypeNames(B)
   rule getTypeNames(.TyVars) => .Set
   rule getTypeNames('typeVars(A:K,, B:K)) => getTypeNames(A) getTypeNames(B)
   rule getTypeNames(T:TyVar) => SetItem(T)
   rule getTypeNames('conTyCon(A:ModId,,T:TyCon)) => .Set
   rule getTypeNames('tupleCover(Ts:TypeTuple)) => getTypeNames(Ts)
   rule getTypeNames('tyList(T:K)) => getTypeNames(T)
   rule getTypeNames('group(T:K)) => getTypeNames(T)
   rule getTypeNames('baTypeCon(T1:K,, T2:K)) => getTypeNames(T1) getTypeNames(T2) 
   rule getTypeNames('typeArrow(T1:K,, T2:K)) => getTypeNames(T1) getTypeNames(T2) 
   rule getTypeNames('twoTypeTuple(T1:K,, T2:K)) => getTypeNames(T1) getTypeNames(T2) 
   rule getTypeNames('typeTupleCon(T1:K,, T2:K)) => getTypeNames(T1) getTypeNames(T2) 
   rule getTypeNames(T:K) => .Set [owise]

   syntax Set ::= getFreeTypeVars(K) [function]
   rule getFreeTypeVars(T:TyVar) => SetItem(T)
   rule getFreeTypeVars(G:GTyCon) => .Set
   rule getFreeTypeVars('tupleCover(As:TypeTuple)) => getFreeTypeVars(As)
   rule getFreeTypeVars('twoTypeTuple(A1:Type,, A2:Type))
        => getFreeTypeVars(A1) getFreeTypeVars(A2)
   rule getFreeTypeVars('typeTupleCon(A1:Type,, A2:TypeTuple))
        => getFreeTypeVars(A1) getFreeTypeVars(A2)
   rule getFreeTypeVars('tyList(A1:Type)) => getFreeTypeVars(A1)
   rule getFreeTypeVars('group(A1:Type)) => getFreeTypeVars(A1)
   rule getFreeTypeVars('typeArrow(A1:BType,, A2:Type))
        => getFreeTypeVars(A1) getFreeTypeVars(A2)
   rule getFreeTypeVars('baTypeCon(A1:AType,, A2:BType))
        => getFreeTypeVars(A1) getFreeTypeVars(A2)

   syntax Map ::= addEdges(Set, Set) [function]
   rule addEdges(SetItem(A:K), SetItem(B:K) S:Set)
          => (A |-> names(SetItem(B) S))

   syntax KItem ::= getSingleton(Set) [function]
   rule getSingleton(SetItem(A:K)) => A

   syntax KItem ::= makeAlphaM(K, K, Map, Map, Set, Set) [function]
              //curr-mod, (Alpha, AlphaMap), temp-map,
              // set-of-types-in-curr, import set
                  | makeAlphaMAux(K, TopDecl, Map, K, Map, Set, Set) [function]
                   //curr-mod, top-decl, checking map, checking-point,
                  // store-map, set-of-types, import set
                  | makeAlphaMAuxAux(K, TopDecl, Map, K, List, K, Map, Set, Set) [function]

   rule makeAlphaM(Mod:K, 'bodyimpandtop(_:ImpDecls,, T:TopDecls),
            M:Map, TM:Map, Ts:Set, Is:Set)
          => makeAlphaM(Mod:K, T, M, TM, Ts:Set, Is:Set)
   rule makeAlphaM(Mod:K, 'bodyimpdecls(_:ImpDecls), M:Map, TM:Map, Ts:Set, Is:Set) => .K
   rule makeAlphaM(Mod:K, 'bodytopdecls(T:TopDecls), M:Map, TM:Map, Ts:Set, Is:Set)
                  => makeAlphaM(Mod:K, T, M, TM, Ts:Set, Is:Set)
   rule makeAlphaM(Mod:K, .TopDecls, M:Map, TM:Map, Ts:Set, Is:Set) => putAlphaMap(TM)
   rule makeAlphaM(Mod:K, 'topdeclslist(A:TopDecl,, As:TopDecls),
             M:Map, TM:Map, Ts:Set, Is:Set)
              => makeAlphaMAux(Mod:K, A, M, As, TM, Ts:Set, Is:Set)

   rule makeAlphaMAux(Mod:K, type A:SimpleType = B:Type,
               M:Map, As:K, TM:Map, Ts:Set, Is:Set)
          => makeAlphaMAuxAux(Mod, As, addEdges(getConstrNames(A), getConstrNames(B)) M,
               typeName(getSingleton(getConstrNames(A))),
                   getTyVarList(A),toAbsType(Mod, B, getTyVarSet(A),Ts,Is), TM, Ts, Is)
        requires getTypeNames(B) <=Set getTypeNames(A)
                  andBool getSingleton(getConstrNames(A)) in keys(M)
                  andBool notBool hasCycleAux(
                               getSingleton(getConstrNames(A)), getConstrNames(B), M)
   rule makeAlphaMAux(Mod:K, type A:SimpleType = B:Type,
                               M:Map, As:K, TM:Map, Ts:Set, Is:Set)
               => error(typeVarNoInclusive)
        requires notBool (getTypeNames(B) <=Set getTypeNames(A))
   rule makeAlphaMAux(Mod:K, type A:SimpleType = B:Type,
                               M:Map, As:K, TM:Map, Ts:Set, Is:Set)
               => error(repeatedNames)
        requires notBool getSingleton(getConstrNames(A)) in keys(M)
   rule makeAlphaMAux(Mod:K, type A:SimpleType = B:Type,
                            M:Map, As:K, TM:Map, Ts:Set, Is:Set) => error(cycleAlpha)
        requires hasCycleAux(getSingleton(getConstrNames(A)), getConstrNames(B), M)
   rule makeAlphaMAux(Mod:K, A:TopDecl, M:Map, As:K, TM:Map, Ts:Set, Is:Set)
                           => makeAlphaM(Mod:K, As, M, TM, Ts:Set, Is:Set) [owise]

   rule makeAlphaMAuxAux(Mod:K, As:K, M:Map, A:K,
                   L:List, error(B:K), TM:Map, Ts:Set, Is:Set) => error(B)
   rule makeAlphaMAuxAux(Mod:K, As:K, M:Map, A:K,
                   L:List, B:K, TM:Map, Ts:Set, Is:Set)
            => makeAlphaM(Mod, As, M, (A |-> alphaTuple(L, B)) TM, Ts, Is) [owise]

   syntax KItem ::= genKindMap(Int, Set, Set, Map) [function]
   rule genKindMap(N:Int, S:Set, .Set, M:Map) => resultTransSetMap(N, S, M)
   rule genKindMap(N:Int, S:Set, SetItem(A:K) Cs:Set, M:Map) 
          => genKindMap(N +Int 1, S SetItem(kindVar(N)), Cs, (A |-> kindVar(N)) M)

   //collect a map for knowing the type name and its partial kind (not proved)
   syntax KItem ::= parKindEntry(Int, Set, K, SimpleType) [function]
           //counter, kind-var-set, curr-mod, simple-type
                  | parKindEntryAux(K, K, K) [function]
                    //curr-mod, simple-type, resultTyVarKind

   rule parKindEntry(N:Int, S:Set, Curr:K, 'simpleTypeCon(T:TyCon,, Vs:TyVars))
            => parKindEntryAux(Curr, T, resolveKindEntry(N, S, Vs, .List))
   rule parKindEntryAux(Curr:K, T:K, resultTyVarKindList(N:Int, S:Set, L:List))
            => resultTyVarKindMap(N, S, (typeName(T) |-> listToKind(L)))

   syntax KItem ::= listToKind(List) [function]
   rule listToKind(.List) => star
   rule listToKind(ListItem(A:K) L:List) => kindArrow(A, listToKind(L))

   syntax KItem ::= resolveKindEntry(Int, Set, TyVars, List) [function]
           //counter, kind-var-set, tyVars, result
   rule resolveKindEntry(N:Int, S:Set, .TyVars, T:List) => resultTyVarKindList(N, S, T)
   rule resolveKindEntry(N:Int, S:Set, 'typeVars(A:TyVar,,B:TyVars), T:List)
          => resolveKindEntry(N +Int 1, S SetItem(kindVar(N)), B, T ListItem(kindVar(N)))

   syntax KItem ::= collectCheckDefs(K, Set) [function]
                  | collectCheckDefsField(K, Set) [function]
                  | collectCheckDefsFieldAux(K, Set) [function]
                  | collectCheckDefsFieldAux1(K, K) [function]
                  | collectCheckDefsAux(K, K) [function]
                  | collectCheckDefsClass(K, K, Set) [function]

   rule collectCheckDefsClass('emptyOptCDecls(.KList), A:K, S:Set)
           => collectCheckDefs(A, S)
   rule collectCheckDefsClass('cdeclWhere(A:K), B:K, S:Set)
           => collectCheckDefsClass(A, B, S)
   rule collectCheckDefsClass('cdeclBracket(A:K), B:K, S:Set)
           => collectCheckDefsClass(A, B, S)
   rule collectCheckDefsClass(.CDeclsList, B:K, S:Set) => collectCheckDefs(B, S)
   rule collectCheckDefsClass('cdeclCon('varAssign(Vs:Vars,, T:Type),, Ds:K), B:K, S:Set)
           => collectCheckDefsClass(Ds, B, collectFunVars(Vs) S)
        requires notBool isIntersect(collectFunVars(Vs), .K, S)
   rule collectCheckDefsClass('cdeclCon('varAssign(Vs:Vars,, T:Type),, Ds:K), B:K, S:Set)
           => error(repeatedNames)
        requires isIntersect(collectFunVars(Vs), .K, S)
   rule collectCheckDefsClass('cdeclCon('genAssignContext(
                Vs:Vars,,C:K,, T:Type),, Ds:K), B:K, S:Set)
           => collectCheckDefsClass(Ds, B, collectFunVars(Vs) S)
        requires notBool isIntersect(collectFunVars(Vs), .K, S)
   rule collectCheckDefsClass('cdeclCon('genAssignContext(
                 Vs:Vars,,C:K,, T:Type),, Ds:K), B:K, S:Set)
           => error(repeatedNames)
        requires isIntersect(collectFunVars(Vs), .K, S)

   rule collectCheckDefsField('emptyConstrs(.KList), S:Set) => resultSet(S)
   rule collectCheckDefsField('nonemptyConstrs(Cs:Constrs), S:Set)
           => collectCheckDefsField(Cs, S)
   rule collectCheckDefsField(C:Constr, S:Set)
            => collectCheckDefsFieldAux1(.K, collectCheckDefsFieldAux(C, S))
   rule collectCheckDefsField('multConstr(N:Con {Fs:FieldDeclList},, B:K), S:Set)
          => collectCheckDefsFieldAux1(B, collectCheckDefsFieldAux(Fs, S))
   rule collectCheckDefsField('newConField(N:Con,, V:Var,, T:Type), S:Set)
                 => resultSet(S SetItem(funName(pillVar(V))))
        requires notBool funName(pillVar(V)) in S
      rule collectCheckDefsField('newConField(N:Con,, V:Var,, T:Type), S:Set)
                 => error(repeatedNames)
        requires funName(pillVar(V)) in S
   rule collectCheckDefsField('newConstrCon(N:Con,, V:AType), S:Set) => resultSet(S)

   rule collectCheckDefsFieldAux1(A:K, error(B:K)) => error(B)
   rule collectCheckDefsFieldAux1(.K, resultSet(S:Set)) => resultSet(S)
   rule collectCheckDefsFieldAux1(Cs:Constrs, resultSet(S:Set))
             => collectCheckDefsField(Cs, S)

   rule collectCheckDefsFieldAux(N:Con {Fs:FieldDeclList}, S:Set)
         => collectCheckDefsFieldAux(Fs, S)
   rule collectCheckDefsFieldAux(.FieldDeclList, S:Set) => resultSet(S)
   rule collectCheckDefsFieldAux('fieldCon('varAssign(A:Vars,, T:Type),, B:K), S:Set)
           => collectCheckDefsFieldAux(B, collectFunVars(A) S)
        requires notBool isIntersect(collectFunVars(A), .K, S)
   rule collectCheckDefsFieldAux('fieldCon('varAssign(A:Vars,, T:Type),, B:K), S:Set)
           => error(repeatedNames)
        requires isIntersect(collectFunVars(A), .K, S)
   rule collectCheckDefsFieldAux('fieldCon(Vs:Vars :: ! A:AType,, B:K), S:Set)
           => collectCheckDefsFieldAux(B, collectFunVars(Vs) S)
        requires notBool isIntersect(collectFunVars(Vs), .K, S)
   rule collectCheckDefsFieldAux('fieldCon(Vs:Vars :: ! A:AType,, B:K), S:Set)
           => error(repeatedNames)
        requires isIntersect(collectFunVars(Vs), .K, S)
   rule collectCheckDefsFieldAux(A:K, S:Set) => resultSet(S) [owise]

   rule collectCheckDefs('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls), S:Set)
          => collectCheckDefs(Ts, S)
   rule collectCheckDefs('bodyimpdecls(Is:ImpDecls), S:Set) => putDefSet(S)
   rule collectCheckDefs('bodytopdecls(Ts:TopDecls), S:Set) => collectCheckDefs(Ts, S)
   rule collectCheckDefs(.TopDecls, S:Set) => putDefSet(S)
   rule collectCheckDefs('topdeclslist(type 'simpleTypeCon(N:TyCon,, Ts:TyVars) = B:Type,,
           As:TopDecls), S:Set)
          => collectCheckDefs(As, S SetItem(typeName(N)))
        requires notBool typeName(N) in S
   rule collectCheckDefs('topdeclslist('data(
              'simpleTypeCon(N:K,, Vs:K),, Cons:K,, Od:K),,As:TopDecls), S:Set)
          => collectCheckDefsAux(As,
                   collectCheckDefsField(Cons, S SetItem(typeName(N))))
        requires notBool typeName(N) in S
   rule collectCheckDefs('topdeclslist('newtype(
              'simpleTypeCon(N:K,, Vs:K),, Cons:NewConstr,, Od:K),,As:TopDecls), S:Set)
          => collectCheckDefsAux(As,
                   collectCheckDefsField(Cons, S SetItem(typeName(N))))
        requires notBool typeName(N) in S
   rule collectCheckDefs('topdeclslist(type 'simpleTypeCon(N:TyCon,, Ts:TyVars) = B:Type,,
           As:TopDecls), S:Set) => error(repeatedNames)
        requires typeName(N) in S
   rule collectCheckDefs('topdeclslist('data(
              'simpleTypeCon(N:K,, Vs:K),, Cons:K,, Od:K),,
           As:TopDecls), S:Set) => error(repeatedNames)
        requires typeName(N) in S
   rule collectCheckDefs('topdeclslist('newtype(
              'simpleTypeCon(N:K,, Vs:K),, Cons:K,, Od:K),,
           As:TopDecls), S:Set) => error(repeatedNames)
        requires typeName(N) in S
   rule collectCheckDefs('topdeclslist('class(Op:OptContext,,
                C:ConId,, Ts:TyVar,, Od:OptCDecls),,
           As:TopDecls), S:Set) => error(repeatedNames)
        requires className(C) in S
   rule collectCheckDefs('topdeclslist('class(Op:OptContext,,
                C:ConId,, Ts:TyVar,, Od:OptCDecls),, As:TopDecls), S:Set)
             => collectCheckDefsClass(Od, As, S SetItem(className(C)))
        requires notBool className(C) in S
   rule collectCheckDefs('topdeclslist('declPatRhs(P:Pat,, R:Rhs),, As:TopDecls), S:Set)
             => collectCheckDefs(As, S getFreeVarsInPat(P))
        requires notBool isIntersect(getFreeVarsInPat(P),.K, S)
   rule collectCheckDefs('topdeclslist('declPatRhs(P:Pat,, R:Rhs),, As:TopDecls), S:Set)
             => error(repeatedNames)
        requires isIntersect(getFreeVarsInPat(P),.K, S)
   rule collectCheckDefs('topdeclslist(
                  'declFunLhsRhs(P:FunLhs,, R:Rhs),, As:TopDecls), S:Set)
             => collectCheckDefs(As, S SetItem(getCoreVar(P)))
        requires notBool getCoreVar(P) in S
   rule collectCheckDefs('topdeclslist(
                  'declFunLhsRhs(P:FunLhs,, R:Rhs),, As:TopDecls), S:Set)
             => error(repeatedNames)
        requires getCoreVar(P) in S
   rule collectCheckDefs('topdeclslist(D:GenDecl,, As:TopDecls), S:Set)
             => collectCheckDefs(As, S) [owise]

   rule collectCheckDefsAux(As:K, error(B:K)) => error(B)
   rule collectCheckDefsAux(As:K, resultSet(S:Set)) => collectCheckDefs(As, S)

   //check if all fixities in a module is defined in the same module
   syntax KItem ::= checkAllFixityMakeSense(K, Set, Set) [function]
                  | checkAllFixityMakeSenseInCDecl(K, Set, Set) [function]
                  | checkAllFixityMakeSenseAux(K, K, Set, Set) [function]
                  | checkAllFixityMakeSenseInCDeclAux(K, K, Set, Set) [function]

   rule checkAllFixityMakeSenseInCDecl('emptyOptCDecls(.KList), As:Set, S:Set) => .K
   rule checkAllFixityMakeSenseInCDecl('cdeclWhere(A:K), As:Set, S:Set)
           => checkAllFixityMakeSenseInCDecl(A, As, S)
   rule checkAllFixityMakeSenseInCDecl('cdeclBracket(A:K), As:Set, S:Set)
           => checkAllFixityMakeSenseInCDecl(A, As, S)
   rule checkAllFixityMakeSenseInCDecl(.CDeclsList, As:Set, S:Set) => .K
   rule checkAllFixityMakeSenseInCDecl(
                 'cdeclCon('fixityOp(T:K,, Vs:Ops),, B:K), As:Set, S:Set)
           => checkAllFixityMakeSenseInCDeclAux(Vs, B, As, S)
   rule checkAllFixityMakeSenseInCDecl('cdeclCon(
                        'fixityIntOp(T:K,, C:K,, Vs:Ops),, B:K), As:Set, S:Set)
           => checkAllFixityMakeSenseInCDeclAux(Vs, B, As, S)
   rule checkAllFixityMakeSenseInCDecl('cdeclCon(A:K,, B:K), As:Set, S:Set)
            => checkAllFixityMakeSenseInCDecl(B, As, S) [owise]

   rule checkAllFixityMakeSenseInCDeclAux(V:VarOp, Ts:K, As:Set, S:Set)
          => checkAllFixityMakeSenseInCDecl(Ts, SetItem(funName(pillVar(V))) As, S)
        requires funName(pillVar(V)) in S andBool notBool funName(pillVar(V)) in As
   rule checkAllFixityMakeSenseInCDeclAux(V:VarOp, Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool funName(pillVar(V)) in S
   rule checkAllFixityMakeSenseInCDeclAux(V:VarOp, Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires funName(pillVar(V)) in As
   rule checkAllFixityMakeSenseInCDeclAux(V:ConOp, Ts:K, As:Set, S:Set)
          => checkAllFixityMakeSenseInCDecl(Ts, SetItem(constrName(pillVar(V))) As, S)
        requires constrName(pillVar(V)) in S andBool notBool constrName(pillVar(V)) in As
   rule checkAllFixityMakeSenseInCDeclAux(V:ConOp, Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool constrName(pillVar(V)) in S
   rule checkAllFixityMakeSenseInCDeclAux(V:ConOp, Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires constrName(pillVar(V)) in As
   rule checkAllFixityMakeSenseInCDeclAux('opCon(V:VarOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => checkAllFixityMakeSenseInCDeclAux(Vs, Ts, SetItem(funName(pillVar(V))) As, S)
        requires funName(pillVar(V)) in S andBool notBool funName(pillVar(V)) in As
   rule checkAllFixityMakeSenseInCDeclAux('opCon(V:VarOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool funName(pillVar(V)) in S
   rule checkAllFixityMakeSenseInCDeclAux('opCon(V:VarOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires funName(pillVar(V)) in As
   rule checkAllFixityMakeSenseInCDeclAux('opCon(V:ConOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => checkAllFixityMakeSenseInCDeclAux(Vs, Ts, SetItem(constrName(pillVar(V))) As, S)
        requires constrName(pillVar(V)) in S andBool notBool constrName(pillVar(V)) in As
   rule checkAllFixityMakeSenseInCDeclAux('opCon(V:ConOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool constrName(pillVar(V)) in S
   rule checkAllFixityMakeSenseInCDeclAux('opCon(V:ConOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires constrName(pillVar(V)) in As

   rule checkAllFixityMakeSense('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls), As:Set, S:Set)
          => checkAllFixityMakeSense(Ts, As, S)
   rule checkAllFixityMakeSense('bodyimpdecls(Is:ImpDecls), As:Set, S:Set) => .K
   rule checkAllFixityMakeSense('bodytopdecls(Ts:TopDecls), As:Set, S:Set)
                 => checkAllFixityMakeSense(Ts, As, S)
   rule checkAllFixityMakeSense(.TopDecls, As:Set, S:Set) => .K
   rule checkAllFixityMakeSense('topdeclslist(
               'fixityOp(T:K,, Vs:Ops),, Ts:K), As:Set, S:Set)
         => checkAllFixityMakeSenseAux(Vs, Ts, As, S)
      rule checkAllFixityMakeSense('topdeclslist(
            'fixityIntOp(T:K,, C:K,, Vs:Ops),, Ts:K), As:Set, S:Set)
         => checkAllFixityMakeSenseAux(Vs, Ts, As, S)
   rule checkAllFixityMakeSense('topdeclslist(
               A:K,, Ts:K), As, S:Set)
         => checkAllFixityMakeSense(Ts, As, S) [owise]

   rule checkAllFixityMakeSenseAux(V:VarOp, Ts:K, As:Set, S:Set)
          => checkAllFixityMakeSense(Ts, SetItem(funName(pillVar(V))) As, S)
        requires funName(pillVar(V)) in S andBool notBool funName(pillVar(V)) in As
   rule checkAllFixityMakeSenseAux(V:VarOp, Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool funName(pillVar(V)) in S
   rule checkAllFixityMakeSenseAux(V:VarOp, Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires funName(pillVar(V)) in As
   rule checkAllFixityMakeSenseAux(V:ConOp, Ts:K, As:Set, S:Set)
          => checkAllFixityMakeSense(Ts, SetItem(constrName(pillVar(V))) As, S)
        requires constrName(pillVar(V)) in S andBool notBool constrName(pillVar(V)) in As
   rule checkAllFixityMakeSenseAux(V:ConOp, Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool constrName(pillVar(V)) in S
   rule checkAllFixityMakeSenseAux(V:ConOp, Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires constrName(pillVar(V)) in As
   rule checkAllFixityMakeSenseAux('opCon(V:VarOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => checkAllFixityMakeSenseAux(Vs, Ts, SetItem(funName(pillVar(V))) As, S)
        requires funName(pillVar(V)) in S andBool notBool funName(pillVar(V)) in As
   rule checkAllFixityMakeSenseAux('opCon(V:VarOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool funName(pillVar(V)) in S
   rule checkAllFixityMakeSenseAux('opCon(V:VarOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires funName(pillVar(V)) in As
   rule checkAllFixityMakeSenseAux('opCon(V:ConOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => checkAllFixityMakeSenseAux(Vs, Ts, SetItem(constrName(pillVar(V))) As, S)
        requires constrName(pillVar(V)) in S andBool notBool constrName(pillVar(V)) in As
   rule checkAllFixityMakeSenseAux('opCon(V:ConOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool constrName(pillVar(V)) in S
   rule checkAllFixityMakeSenseAux('opCon(V:ConOp,, Vs:Ops), Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires constrName(pillVar(V)) in As

   //check if all decl in a module is defined in the same module
   syntax KItem ::= checkAllDeclMakeSense(K, Set, Set) [function]
                  | checkAllDeclMakeSenseAux(K, K, Set, Set) [function]

   rule checkAllDeclMakeSense('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls), As:Set, S:Set)
          => checkAllDeclMakeSense(Ts, As, S)
   rule checkAllDeclMakeSense('bodyimpdecls(Is:ImpDecls), As:Set, S:Set) => .K
   rule checkAllDeclMakeSense('bodytopdecls(Ts:TopDecls), As:Set, S:Set)
                 => checkAllDeclMakeSense(Ts, As, S)
   rule checkAllDeclMakeSense(.TopDecls, As:Set, S:Set) => .K
   rule checkAllDeclMakeSense('topdeclslist(
               'varAssign(Vs:Vars,, T:Type),, Ts:K), As:Set, S:Set)
         => checkAllDeclMakeSenseAux(Vs, Ts, As, S)
      rule checkAllDeclMakeSense('topdeclslist(
            'genAssignContext(Vs:Vars,, C:Context,, T:Type),, Ts:K), As:Set, S:Set)
         => checkAllDeclMakeSenseAux(Vs, Ts, As, S)
   rule checkAllDeclMakeSense('topdeclslist(
               A:K,, Ts:K), As, S:Set)
         => checkAllDeclMakeSense(Ts, As, S) [owise]

   rule checkAllDeclMakeSenseAux(V:Var, Ts:K, As:Set, S:Set)
          => checkAllDeclMakeSense(Ts, SetItem(funName(pillVar(V))) As, S)
        requires funName(pillVar(V)) in S andBool notBool funName(pillVar(V)) in As
   rule checkAllDeclMakeSenseAux(V:Var, Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool funName(pillVar(V)) in S
   rule checkAllDeclMakeSenseAux(V:Var, Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires funName(pillVar(V)) in As
   rule checkAllDeclMakeSenseAux('varCon(V:Var,, Vs:Vars), Ts:K, As:Set, S:Set)
          => checkAllDeclMakeSenseAux(Vs, Ts, SetItem(funName(pillVar(V))) As, S)
        requires funName(pillVar(V)) in S andBool notBool funName(pillVar(V)) in As
   rule checkAllDeclMakeSenseAux('varCon(V:Var,, Vs:Vars), Ts:K, As:Set, S:Set)
          => error(declNoInstance)
        requires notBool funName(pillVar(V)) in S
   rule checkAllDeclMakeSenseAux('varCon(V:Var,, Vs:Vars), Ts:K, As:Set, S:Set)
          => error(duplicateDecl)
        requires funName(pillVar(V)) in As

   //generate functions for getting record content
   syntax KItem ::= genRecordFunctions(Int, K, K, Map) [function]
                  | genRecordFunctionsAux(K, K, K) [function]
                  | genRecordFunctionsField(Int, K, K, Map) [function]
                  | genRecordFunctionsFieldAux(K, K, K) [function]
                  | genRecordFunctionsSingle(Int, K, K, Map) [function]
                  | genRecordFunctionsSingleAux(Int, K, K, K, Map) [function]
                  | genRecordFunctionsSingleAux1(Int, K, K, K,K, Map) [function]

   rule genRecordFunctions(N:Int, Mod:K, 'bodyimpandtop(Is:ImpDecls,, Ts:TopDecls), M:Map)
          => genRecordFunctions(N:Int, Mod, Ts, M)
   rule genRecordFunctions(N:Int, Mod:K, 'bodyimpdecls(Is:ImpDecls), M:Map)
              => putGenFieldMap(N, M)
   rule genRecordFunctions(N:Int, Mod:K, 'bodytopdecls(Ts:TopDecls), M:Map)
                 => genRecordFunctions(N, Mod:K, Ts, M)
   rule genRecordFunctions(N:Int, Mod:K, .TopDecls, M:Map) => putGenFieldMap(N, M)
   rule genRecordFunctions(N:Int, Mod:K, 'topdeclslist(
             'data(S:SimpleType,, Cs:OptConstrs,, Od:OptDeriving),, Ts:K), M:Map)
         => genRecordFunctionsAux(genRecordFunctionsField(N, Mod, Cs, M), Mod, Ts)
   rule genRecordFunctions(N:Int, Mod:K, 'topdeclslist(
             'newType(S:SimpleType,, Cs:NewConstr,, Od:OptDeriving),, Ts:K), M:Map)
         => genRecordFunctionsAux(genRecordFunctionsField(N,Mod, Cs, M), Mod, Ts)
   rule genRecordFunctions(N:Int, Mod:K, 'topdeclslist(
            C:K,, Ts:K), M:Map) => genRecordFunctions(N, Mod:K, Ts, M) [owise]

   rule genRecordFunctionsAux(error(A:K), Mod:K, C:K) => error(A)
   rule genRecordFunctionsAux(putGenFieldMap(N:Int, M:Map), Mod:K, C:K)
            => genRecordFunctions(N, Mod:K, C, M)

   rule genRecordFunctionsField(N:Int, Mod:K, 'emptyConstrs(.KList), M:Map)
           => putGenFieldMap(N, M)
   rule genRecordFunctionsField(N:Int,Mod:K, 'nonemptyConstrs(Cs:Constrs), M:Map)
           => genRecordFunctionsField(N,Mod, Cs, M)
   rule genRecordFunctionsField(N:Int, Mod:K, 'multConstr(C:Constr,, Cs:Constrs), M:Map)
         => genRecordFunctionsFieldAux(genRecordFunctionsSingle(N, Mod, C, M), Mod, Cs)
   rule genRecordFunctionsField(N:Int, Mod:K, C:Constr, M:Map)
         => genRecordFunctionsSingle(N, Mod, C, M)
   rule genRecordFunctionsField(N:Int, Mod:K, 'newConField(C:Con,, V:Var,, T:Type), M:Map)
          =>  putGenFieldMap(N +Int 1, M
           (fullName(Mod, funName(pillVar(V))) |-> resultList(
                  ListItem(funAssign(fullName(Mod, funName(pillVar(V))), ListItem(genVar(N)), 
             findLabelResult(fullName(Mod, constrName(pillVar(C))),
                        fullName(Mod, funName(pillVar(V))), genVar(N)))))))
   rule genRecordFunctionsField(N:Int, Mod:K, C:K, M:Map) => putGenFieldMap(N, M) [owise]

   rule genRecordFunctionsFieldAux(error(A:K), Mod:K, Cs:K) => error(A)
   rule genRecordFunctionsFieldAux(putGenFieldMap(N:Int, M:Map), Mod:K, Cs:K)
            => genRecordFunctionsField(N, Mod, Cs, M)

   rule genRecordFunctionsSingle(N:Int, Mod:K, C:Con { Fs:FieldDeclList }, M:Map)
          => genRecordFunctionsSingleAux(N, Mod:K, fullName(Mod, constrName(pillVar(C))), Fs, M)
   rule genRecordFunctionsSingle(N:Int, Mod:K, C:K, M:Map)
              => putGenFieldMap(N, M) [owise]

   rule genRecordFunctionsSingleAux(N:Int, Mod:K, C:K, .FieldDeclList, M:Map)
            => putGenFieldMap(N, M)
   rule genRecordFunctionsSingleAux(N:Int, Mod:K, C:K,
               'fieldCon('varAssign(Vs:Vars,, T:K),, Fs:K), M:Map)
          => genRecordFunctionsSingleAux1(N, Mod, C, Vs, Fs, M)
   rule genRecordFunctionsSingleAux(N:Int, Mod:K, C:K,
               'fieldCon(Vs:Vars :: ! T:AType,, Fs:K), M:Map)
          => genRecordFunctionsSingleAux1(N, Mod, C, Vs, Fs, M)

   rule genRecordFunctionsSingleAux1(N:Int, Mod:K, C:K, V:Var, Fs:K, M:Map)
          =>  genRecordFunctionsSingleAux(N +Int 1, Mod:K, C, Fs, M
           (fullName(Mod, funName(pillVar(V))) |-> resultList(ListItem(
                funAssign(fullName(Mod, funName(pillVar(V))),ListItem(genVar(N)), 
             findLabelResult(C, fullName(Mod, funName(pillVar(V))), genVar(N)))))))
   rule genRecordFunctionsSingleAux1(N:Int, Mod:K, C:K, 'varCon(V:Var, Vs:Vars), Fs:K, M:Map)
          =>  genRecordFunctionsSingleAux1(N +Int 1, Mod, C, Vs, Fs, M
           (fullName(Mod, funName(pillVar(V))) |-> resultList(ListItem(
                 funAssign(fullName(Mod, funName(pillVar(V))),ListItem(genVar(N)), 
             findLabelResult(C, fullName(Mod, funName(pillVar(V))), genVar(N)))))))

   syntax KItem ::= collectTypes(Int, Set, K, K, Map) [function]
             //couonter, kind-var=set, curr-mod, decls, store-kind-map
                  | collectTypesAux(K, K, K, Map) [function]
               //curr-mod, decls, return-tyvar-kind, store-kind-map
   rule collectTypes(N:Int, S:Set, Mod:K, 'bodyimpandtop(Is:ImpDecls,, Ts:TopDecls), M:Map)
          => collectTypes(N, S, Mod:K, Ts, M)
   rule collectTypes(N:Int, S:Set, Mod:K, 'bodyimpdecls(Is:ImpDecls), M:Map) => .K
   rule collectTypes(N:Int, S:Set, Mod:K, 'bodytopdecls(
                 Ts:TopDecls), M:Map) => collectTypes(N,S, Mod:K, Ts, M)
   rule collectTypes(N:Int, S:Set, Mod:K, .TopDecls, M:Map) => resultTyVarKindMap(N, S, M)
   rule collectTypes(N:Int, S:Set, Mod:K,
            'topdeclslist(type A:SimpleType = B:Type,, As:TopDecls), M:Map)
              => collectTypesAux(Mod:K, As, parKindEntry(N, S, Mod, A), M)
   rule collectTypes(N:Int, S:Set, Mod:K, 'topdeclslist(data A:SimpleType
                        B:OptConstrs D:OptDeriving,, As:TopDecls), M:Map)
              => collectTypesAux(Mod:K, As, parKindEntry(N, S, Mod, A), M)
   rule collectTypes(N:Int, S:Set, Mod:K, 'topdeclslist(newtype A:SimpleType
                       = B:NewConstr D:OptDeriving,, As:TopDecls), M:Map)
              => collectTypesAux(Mod:K, As, parKindEntry(N,S, Mod, A), M)
   rule collectTypes(N:Int, S:Set, Mod:K, 'topdeclslist(A:TopDecl,, As:TopDecls),
                   M:Map) => collectTypes(N, S, Mod:K, As, M) [owise]
   rule collectTypesAux(Mod:K, As:K, resultTyVarKindMap(N:Int, S:Set, NM:Map), M:Map)
          => collectTypes(N, S, Mod, As, NM M)

   //turn type syntax to abstract syntax
   syntax List ::= toTypeList(K) [function]
   rule toTypeList(.TyVars) => .List
   rule toTypeList('typeVars(X:TyVar,, A:TyVars))
           => ListItem(X) toTypeList(A)

   syntax Set ::= toTypeSet(K) [function]
   rule toTypeSet(.TyVars) => .Set
   rule toTypeSet('typeVars(X:TyVar,, A:TyVars))
           => SetItem(X) toTypeSet(A)

   syntax List ::= getTyVarList(K) [function]
   rule getTyVarList('simpleTypeCon(A:TyCon,, B:TyVars))
           => toTypeList(B)

   syntax Set ::= getTyVarSet(K) [function]
   rule getTyVarSet('simpleTypeCon(A:TyCon,, B:TyVars))
           => toTypeSet(B)

   //convert a type con to abs form (fullname)
   //complicated, basic idea is to fully investigate the use of class/type in the curr-mod
   //and in import mods. 
   syntax KItem ::= toAbsClassCon(K, K, Set, Set) [function]
     //curr-mod-name, type-con, curr-types, imports
   rule toAbsClassCon(Mod:K, T:TyCon, Ts:Set, Is:Set) => fullName(Mod, className(T))
        requires className(T) in Ts andBool notBool typeName(T) in Ts
                andBool countGoodNameNoQualified(className(T), .K, Is) ==K 0
                andBool countGoodNameNoQualified(typeName(T), .K, Is) ==K 0
   rule toAbsClassCon(Mod:K, T:TyCon, Ts:Set, Is:Set)
         => fullName(findGoodNameNoQualified(className(T), .K, Is), className(T))
        requires notBool className(T) in Ts andBool notBool typeName(T) in Ts
                andBool countGoodNameNoQualified(className(T), .K, Is) ==K 1
                andBool countGoodNameNoQualified(typeName(T), .K, Is) ==K 0
   rule toAbsClassCon(Mod:K, T:TyCon, Ts:Set, Is:Set) => error(messuseClassTypeName)
        requires typeName(T) in Ts
   rule toAbsClassCon(Mod:K, T:TyCon, Ts:Set, Is:Set) => error(messuseClassTypeName)
        requires countGoodNameNoQualified(typeName(T), .K, Is) =/=K 0
   rule toAbsClassCon(Mod:K, T:TyCon, Ts:Set, Is:Set) => error(ambiguousClassName)
        requires className(T) in Ts
                   andBool countGoodNameNoQualified(className(T), .K, Is) =/=K 0
   rule toAbsClassCon(Mod:K, A:TyCon, Ts:Set, Is:Set) => error(ambiguousClassName)
        requires notBool typeName(A) in Ts andBool notBool className(A) in Ts
            andBool countGoodNameNoQualified(className(A), .K, Is) >Int 1
            andBool countGoodNameNoQualified(typeName(A), .K, Is) ==K 0
   rule toAbsClassCon(Mod:K, A:TyCon, Ts:Set, Is:Set) => error(classNotInScope)
        requires notBool typeName(A) in Ts andBool notBool className(A) in Ts
            andBool countGoodNameNoQualified(typeName(A), .K, Is) ==K 0
            andBool countGoodNameNoQualified(className(A), .K, Is) ==K 0

   rule toAbsClassCon(S:K, 'conTyCon(S,, A:TyCon), Ts:Set, Is:Set)
         => fullName(S, className(A))
        requires className(A) in Ts andBool notBool typeName(A) in Ts
                andBool countGoodNameWithMod(typeName(A), S, .K, Is) ==K 0
                andBool countGoodNameWithMod(className(A), S, .K, Is) ==K 0
   rule toAbsClassCon(S:K, 'conTyCon(S,, A:TyCon), Ts:Set, Is:Set)
         => error(messuseClassTypeName)
        requires typeName(A) in Ts
   rule toAbsClassCon(S:K, 'conTyCon(N:K,, A:TyCon), Ts:Set, Is:Set)
         => error(messuseClassTypeName)
        requires countGoodNameWithMod(typeName(A), N, .K, Is) =/=K 0
   rule toAbsClassCon(S:K, 'conTyCon(S,, A:TyCon), Ts:Set, Is:Set)
         => error(ambiguousTypeName)
        requires className(A) in Ts andBool notBool typeName(A) in Ts
                andBool countGoodNameWithMod(className(A), S, .K, Is) =/=K 0
                andBool countGoodNameWithMod(typeName(A), S, .K, Is) ==K 0
   rule toAbsClassCon(S:K, 'conTyCon(S,, A:TyCon), Ts:Set, Is:Set)
         => error(classNotInScope)
        requires notBool typeName(A) in Ts andBool notBool className(A) in Ts
                andBool countGoodNameWithMod(typeName(A), S, .K, Is) ==K 0
                andBool countGoodNameWithMod(className(A), S, .K, Is) ==K 0
   rule toAbsClassCon(S:K, 'conTyCon(N:K,, A:TyCon), Ts:Set, Is:Set)
         => error(classNotInScope)
        requires S =/=K N
                andBool countGoodNameWithMod(typeName(A), N, .K, Is) ==K 0
                andBool countGoodNameWithMod(className(A), N, .K, Is) ==K 0
   rule toAbsClassCon(S:K, 'conTyCon(N:K,, A:TyCon), Ts:Set, Is:Set)
         => fullName(findGoodNameWithMod(
                        className(A), N, .K, Is),className(A))
        requires S =/=K N
                andBool countGoodNameWithMod(className(A), N, .K, Is) ==K 1
                andBool countGoodNameWithMod(typeName(A), N, .K, Is) ==K 0
   rule toAbsClassCon(S:K, 'conTyCon(S,, A:TyCon), Ts:Set, Is:Set)
         => fullName(findGoodNameWithMod(
                        className(A), S, .K, Is),className(A))
        requires notBool typeName(A) in Ts andBool notBool className(A) in Ts
                andBool countGoodNameWithMod(className(A), S, .K, Is) ==K 1
                andBool countGoodNameWithMod(typeName(A), S, .K, Is) ==K 0
   rule toAbsClassCon(S:K, 'conTyCon(S,, A:TyCon), Ts:Set, Is:Set)
             => error(ambiguousTypeName)
        requires countGoodNameWithMod(className(A), S, .K, Is) >Int 1

   syntax KItem ::= toAbsTypeWithAll(K, K, Set, Set, Set, Set) [function]
           //curr-mod, term, bound-vars, all-vars, types, imports
                  | toAbsTypeWithAllAux(Set, Set, K) [function]
   rule toAbsTypeWithAll(S:K, T:K, Bs:Set, As:Set, Ts:Set, Is:Set)
             => toAbsTypeWithAllAux(Bs, As, toAbsType(S, T, As, Ts, Is))
   rule toAbsTypeWithAllAux(Bs:Set, As:Set, error(A:K)) => error(A)
   rule toAbsTypeWithAllAux(Bs:Set, As:Set, T:K) => T
        requires notBool isError(T) andBool (As -Set Bs) <=Set .Set
   rule toAbsTypeWithAllAux(Bs:Set, As:Set, T:K) => forall(As -Set Bs, T)
        requires notBool isError(T) andBool notBool ((As -Set Bs) <=Set .Set)


   //a function to find the module names of a type in imports
   syntax KItem ::= findGoodName(K, K, Set) [function]
   rule findGoodName(A:K, .K, .Set) => none
   rule findGoodName(A:K, .K, SetItem(B:K) S:Set)
            => findGoodName(A, B, S)
   rule findGoodName(A:K, importElem(Ma:K, Mb:K,
             T:Bool, Es:Set, M:Map), S:Set) => Ma
        requires A in Es 
   rule findGoodName(A:K, importElem(Ma:K, Mb:K,
             T:Bool, Es:Set, M:Map), S:Set)
          => findGoodName(A, .K, S)
        requires notBool A in Es 

   syntax KItem ::= findGoodNameNoQualified(K, K, Set) [function]
   rule findGoodNameNoQualified(A:K, .K, .Set) => none
   rule findGoodNameNoQualified(A:K, .K, SetItem(B:K) S:Set)
            => findGoodNameNoQualified(A, B, S)
   rule findGoodNameNoQualified(A:K, importElem(Ma:K, Mb:K,
             false, Es:Set, M:Map), S:Set) => Ma
        requires A in Es 
   rule findGoodNameNoQualified(A:K, importElem(Ma:K, Mb:K,
             true, Es:Set, M:Map), S:Set)
            => findGoodNameNoQualified(A, .K, S)
   rule findGoodNameNoQualified(A:K, importElem(Ma:K, Mb:K,
             false, Es:Set, M:Map), S:Set)
          => findGoodNameNoQualified(A, .K, S)
        requires notBool A in Es 

   //find the original mod-name not the as mod-name
   syntax KItem ::= findGoodNameWithMod(K, K, K, Set) [function]
   rule findGoodNameWithMod(A:K, B:K, .K, .Set) => 0
   rule findGoodNameWithMod(A:K,B:K, .K, SetItem(C:K) S:Set)
           => findGoodNameWithMod(A,B, C, S)
   rule findGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set) => Ma
        requires A in Es andBool Ma ==K B andBool Mb ==K .K
   rule findGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set) => Ma
        requires A in Es andBool Mb ==K B
   rule findGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => findGoodNameWithMod(A,B, .K, S)
        requires notBool A in Es
   rule findGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => findGoodNameWithMod(A,B, .K, S)
        requires Ma =/=K B andBool Mb ==K .K
   rule findGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => findGoodNameWithMod(A,B, .K, S)
        requires Mb =/=K B andBool Mb =/=K .K

   syntax KItem ::= countGoodName(K, K, Set) [function]
   rule countGoodName(A:K, .K, .Set) => 0
   rule countGoodName(A:K, .K, SetItem(B:K) S:Set)
           => countGoodName(A, B, S)
   rule countGoodName(A:K, importElem(Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => 1 +Int countGoodName(A, .K, S)
        requires A in Es
   rule countGoodName(A:K, importElem(Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => countGoodName(A, .K, S)
        requires notBool A in Es

   syntax KItem ::= countGoodNameWithoutAs(K, K, Set) [function]
   rule countGoodNameWithoutAs(A:K, .K, .Set) => 0
   rule countGoodNameWithoutAs(A:K, .K, SetItem(B:K) S:Set)
           => countGoodNameWithoutAs(A, B, S)
   rule countGoodNameWithoutAs(A:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => 1 +Int countGoodNameWithoutAs(A, .K, S)
        requires A in Es andBool Mb =/=K .K
   rule countGoodNameWithoutAs(A:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => countGoodNameWithoutAs(A, .K, S)
        requires A in Es andBool Mb ==K .K
   rule countGoodNameWithoutAs(A:K, importElem(Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => countGoodNameWithoutAs(A, .K, S)
        requires notBool A in Es

   syntax KItem ::= countGoodNameNoQualified(K, K, Set) [function]
   rule countGoodNameNoQualified(A:K, .K, .Set) => 0
   rule countGoodNameNoQualified(A:K, .K, SetItem(B:K) S:Set)
           => countGoodNameNoQualified(A, B, S)
   rule countGoodNameNoQualified(A:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => 1 +Int countGoodNameNoQualified(A, .K, S)
        requires A in Es andBool notBool T
   rule countGoodNameNoQualified(A:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => countGoodNameNoQualified(A, .K, S)
        requires A in Es andBool T
   rule countGoodNameNoQualified(A:K, importElem(Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => countGoodNameNoQualified(A, .K, S)
        requires notBool A in Es

   syntax KItem ::= countGoodNameWithMod(K, K, K, Set) [function]
   rule countGoodNameWithMod(A:K, B:K, .K, .Set) => 0
   rule countGoodNameWithMod(A:K,B:K, .K, SetItem(C:K) S:Set)
           => countGoodNameWithMod(A,B, C, S)
   rule countGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => 1 +Int countGoodNameWithMod(A,B, .K, S)
        requires A in Es andBool Ma ==K B andBool Mb ==K .K
   rule countGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => 1 +Int countGoodNameWithMod(A,B, .K, S)
        requires A in Es andBool Mb ==K B
   rule countGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => countGoodNameWithMod(A,B, .K, S)
        requires notBool A in Es
   rule countGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => countGoodNameWithMod(A,B, .K, S)
        requires Ma =/=K B andBool Mb ==K .K
   rule countGoodNameWithMod(A:K, B:K, importElem(
                  Ma:K, Mb:K, T:Bool, Es:Set, M:Map), S:Set)
            => countGoodNameWithMod(A,B, .K, S)
        requires Mb =/=K B andBool Mb =/=K .K

   //a function to get the as name in an import
   syntax KItem ::= getAsNameType(K, K, Set) [function]
   rule getAsNameType(A:K, .K, .Set) => none
   rule getAsNameType(A:K, .K, SetItem(B:K) S:Set)
           => getAsNameType(A, B, S)
   rule getAsNameType(A:K, importElem(Mod:K,
                 As:K, F:Bool, Is:Set, Im:Map), S:Set) => As
        requires A in Is andBool As =/=K none
   rule getAsNameType(A:K, importElem(Mod:K,
                 As:K, F:Bool, Is:Set, Im:Map), S:Set)
           => getAsNameType(A, .K, S)
        requires notBool A in Is

   //a set of functions to transform type to ast-type
   // and check if all type-con and typevars are valid
   syntax KItem ::= toAbsTypeList(K, ATypeList, K, List, Set, Set, Set) [function]
          //mod, type-list, execution, store, tyvars, curr-types, imports
   rule toAbsTypeList(S:K, .ATypeList, .K, L:List, As:Set, Ts:Set, Is:Set) => resultList(L)
   rule toAbsTypeList(S:K, 'atypeList(A:K,, L:ATypeList),
                           .K, SL:List, As:Set, Ts:Set, Is:Set)
             => toAbsTypeList(S, L, toAbsType(S, A, As, Ts, Is), SL, As, Ts, Is)
   rule toAbsTypeList(S:K, L:ATypeList, error(A:K),
                SL:List, As:Set, Ts:Set, Is:Set) => error(A)
   rule toAbsTypeList(S:K, L:ATypeList, T:KItem, SL:List, As:Set, Ts:Set, Is:Set)
          => toAbsTypeList(S, L, .K, SL ListItem(T), As, Ts, Is)
        requires notBool isError(T)

   syntax KItem ::= toAbsTypeStrict(K, K, Set, Set, Set) [function]
                  | toAbsTypeStrictAux(K) [function]

   rule toAbsTypeStrict(S:K, T:K, As:Set, Ts:Set, Is:Set)
          => toAbsTypeStrictAux(toAbsType(S, T, As, Ts, Is))
   rule toAbsTypeStrictAux(error(A:K)) => error(A)
   rule toAbsTypeStrictAux(T:K) => aType(true, T) [owise]

   syntax KItem ::= toAbsType(K, K, Set, Set, Set) [function]
                    //current module name, type,
                   //set-of-type-vars, curr-types, imports
                  | toAbsTypeAux(K, K, List, K,K, Set, Set, Set) [function]
                          //curr-mod, type-con-name,type-args, unsolved
                  | toAbsTypeArrow(K, K) [function]
                  | toAbsTypeListAux(K)  [function]
                  | toAbsTypeTupleAux(K, K) [function]
                  | toAbsTypeTuple(K, K, K, List, Set, Set, Set) [function]
                //curr-mod, type-tuple, execute, list.
               // set-of-type-vars, curr-types, imports
                  | toAbsTypeAuxAux(K, List) [function] //type-con, args

   rule toAbsType(S:K, A:TyVar, As:Set, Ts:Set, Is:Set) => A
        requires A in As
   rule toAbsType(S:K, A:TyVar, As:Set, Ts:Set, Is:Set) => error(typeVarNotInScope)
        requires notBool A in As
   rule toAbsType(S:K, A:TyCon, As:Set, Ts:Set, Is:Set)
                      => typeConst(fullName(S,typeName(A)), .List)
        requires typeName(A) in Ts andBool notBool className(A) in Ts
                   andBool countGoodNameNoQualified(typeName(A), .K, Is) ==K 0
                   andBool countGoodNameNoQualified(className(A), .K, Is) ==K 0
   rule toAbsType(S:K, A:TyCon, As:Set, Ts:Set, Is:Set) => error(messuseClassTypeName)
        requires className(A) in Ts
   rule toAbsType(S:K, A:TyCon, As:Set, Ts:Set, Is:Set)
                      => error(ambiguousTypeName)
        requires typeName(A) in Ts
                   andBool countGoodNameNoQualified(typeName(A), .K, Is) =/=K 0
   rule toAbsType(S:K, A:TyCon, As:Set, Ts:Set, Is:Set)
                      => error(messuseClassTypeName)
        requires countGoodNameNoQualified(className(A), .K, Is) =/=K 0
   rule toAbsType(S:K, A:TyCon, As:Set, Ts:Set, Is:Set)
              => typeConst(fullName(findGoodNameNoQualified(
                        typeName(A), .K, Is),typeName(A)), .List)
        requires notBool typeName(A) in Ts andBool notBool className(A) in Ts
            andBool countGoodNameNoQualified(typeName(A), .K, Is) ==K 1
            andBool countGoodNameNoQualified(className(A), .K, Is) ==K 0
   rule toAbsType(S:K, A:TyCon, As:Set, Ts:Set, Is:Set)
              => error(typeNotInScope)
        requires notBool typeName(A) in Ts andBool notBool className(A) in Ts
            andBool countGoodNameNoQualified(typeName(A), .K, Is) ==K 0
            andBool countGoodNameNoQualified(className(A), .K, Is) ==K 0
   rule toAbsType(S:K, A:TyCon, As:Set, Ts:Set, Is:Set)
              => error(ambiguousTypeName)
        requires notBool typeName(A) in Ts andBool notBool className(A) in Ts
            andBool countGoodNameNoQualified(typeName(A), .K, Is) >Int 1
            andBool countGoodNameNoQualified(className(A), .K, Is) ==K 0

   rule toAbsType(S:K,'conTyCon(S,, A:TyCon), As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(S,typeName(A)), .List)
        requires typeName(A) in Ts andBool notBool className(A) in Ts
                andBool countGoodNameWithMod(typeName(A), S, .K, Is) ==K 0
                andBool countGoodNameWithMod(className(A), S, .K, Is) ==K 0
   rule toAbsType(S:K,'conTyCon(S,, A:TyCon), As:Set, Ts:Set, Is:Set)
             => error(messuseClassTypeName)
        requires className(A) in Ts
   rule toAbsType(S:K,'conTyCon(N:K,, A:TyCon), As:Set, Ts:Set, Is:Set)
             => error(messuseClassTypeName)
        requires countGoodNameWithMod(className(A), N, .K, Is) =/=K 0
   rule toAbsType(S:K,'conTyCon(S,, A:TyCon), As:Set, Ts:Set, Is:Set)
             => error(ambiguousTypeName)
        requires typeName(A) in Ts andBool notBool className(A) in Ts
                andBool countGoodNameWithMod(typeName(A), S, .K, Is) =/=K 0
                andBool countGoodNameWithMod(className(A), S, .K, Is) ==K 0
   rule toAbsType(S:K,'conTyCon(S,, A:TyCon), As:Set, Ts:Set, Is:Set)
             => error(typeNotInScope)
        requires notBool typeName(A) in Ts andBool notBool className(A) in Ts
                andBool countGoodNameWithMod(typeName(A), S, .K, Is) ==K 0
                andBool countGoodNameWithMod(className(A), S, .K, Is) ==K 0
   rule toAbsType(S:K,'conTyCon(N:K,, A:TyCon), As:Set, Ts:Set, Is:Set)
             => error(typeNotInScope)
        requires S =/=K N andBool
                countGoodNameWithMod(typeName(A), N, .K, Is) ==K 0
                andBool countGoodNameWithMod(className(A), N, .K, Is) ==K 0
   rule toAbsType(S:K,'conTyCon(N:K,, A:TyCon), As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(findGoodNameWithMod(
                        typeName(A), N, .K, Is),typeName(A)), .List)
        requires S =/=K N
                andBool countGoodNameWithMod(typeName(A), N, .K, Is) ==K 1
                andBool countGoodNameWithMod(className(A), N, .K, Is) ==K 0
   rule toAbsType(S:K,'conTyCon(S,, A:TyCon), As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(findGoodNameWithMod(
                        typeName(A), S, .K, Is),typeName(A)), .List)
        requires notBool typeName(A) in Ts andBool notBool className(A) in Ts
                andBool countGoodNameWithMod(typeName(A), S, .K, Is) ==K 1
                andBool countGoodNameWithMod(className(A), S, .K, Is) ==K 0
   rule toAbsType(S:K,'conTyCon(N:ModId,, A:TyCon), As:Set, Ts:Set, Is:Set)
             => error(ambiguousTypeName)
        requires countGoodNameWithMod(typeName(A), N, .K, Is) >Int 1

   rule toAbsType(S:K,(->), As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(Prelude, typeName((->))), .List)
   rule toAbsType(S:K,[], As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(Prelude, typeName([])), .List)
   rule toAbsType(S:K, 'typeArrow(A:K,, B:K), As:Set, Ts:Set, Is:Set)
             => toAbsTypeArrow(toAbsType(S, A, As:Set, Ts:Set, Is:Set), 
                        toAbsType(S, A, As:Set, Ts:Set, Is:Set))
   rule toAbsTypeArrow(error(A:K), B:K) => error(A)
   rule toAbsTypeArrow(A:K, error(B:K)) => error(B)
   rule toAbsTypeArrow(A:K, B:K) => typeConst(
              fullName(Prelude, typeName((->))), ListItem(A) ListItem(B)) [owise]
   rule toAbsType(S:K, 'tyList(A:K), As:Set, Ts:Set, Is:Set)
             => toAbsTypeListAux(toAbsType(S, A, As:Set, Ts:Set, Is:Set))
   rule toAbsTypeListAux(error(A:K)) => error(A)
   rule toAbsTypeListAux(A:K) => typeConst(
                 fullName(Prelude, typeName([])), ListItem(A)) [owise]
   rule toAbsType(S:K, 'tyVarList(A:K), As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(Prelude, typeName([])), ListItem(A))
   rule toAbsType(S:K, 'typeVarFun(A:K,, B:K), As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(Prelude, typeName((->))), ListItem(A) ListItem(B))
   rule toAbsType(S:K, 'instTupleCover(Tsa:TyVarTuple), As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(Prelude, typeName(tupleType(countOnTypeTuple(Tsa)))),
                 toAbsTypeTuple(S, Tsa))
   rule toAbsType(S:K, 'instAppType(A:GTyCon,, B:TyVars), As:Set, Ts:Set, Is:Set)
             => toAbsTypeAuxAux(toAbsType(S, A, As:Set, Ts:Set, Is:Set),
                   typeVarsToList(B))
   rule toAbsType(S:K, 'unitType(.KList), As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(Prelude, typeName('unitType(.KList))), .List)
   rule toAbsType(S:K, 'tupleFun(Gs:GConCommas), As:Set, Ts:Set, Is:Set)
             => typeConst(fullName(Prelude,
                     typeName(tupleType(countOnCommas(Gs) +Int 1))), .List)
   rule toAbsType(S:K, 'tupleCover(Tsa:TypeTuple), As:Set, Ts:Set, Is:Set)
             => toAbsTypeTupleAux(fullName(Prelude,
                  typeName(tupleType(countOnTypeTuple(Tsa)))),
               toAbsTypeTuple(S, Tsa,.K, .List, As:Set, Ts:Set, Is:Set))
   rule toAbsType(S:K, 'group(T:K), As:Set, Ts:Set, Is:Set)
              => toAbsType(S, T, As:Set, Ts:Set, Is:Set)

   rule toAbsType(S:K, 'baTypeCon(T:K,, T1:K), As:Set, Ts:Set, Is:Set)
          => toAbsTypeAux(S, toAbsType(S, T, As, Ts, Is), .List, .K, T1, As, Ts, Is)

   rule toAbsType(S:K, A:K, As:Set, Ts:Set, Is:Set) => A [owise]

   rule toAbsTypeAux(S:K, error(A:K), L:List,
                  B:K, C:K, As:Set, Ts:Set, Is:Set) => error(A)
   rule toAbsTypeAux(S:K, A:K, L:List, .K, 'baTypeCon(T:K,, T1:K), As:Set, Ts:Set, Is:Set)
           => toAbsTypeAux(S:K, A, L,toAbsType(S, T, As, Ts, Is),
                        T1, As:Set, Ts:Set, Is:Set)
        requires notBool isError(A)
   rule toAbsTypeAux(S:K, A:K, L, error(B:K),
                        T1:K, As:Set, Ts:Set, Is:Set) => error(B)
        requires notBool isError(A)
   rule toAbsTypeAux(S:K, A:K, L, T:KItem,
                        T1:K, As:Set, Ts:Set, Is:Set)
             => toAbsTypeAux(S, A, L ListItem(T), .K, T1, As, Ts, Is)
        requires notBool isError(A) andBool notBool isError(T)
   rule toAbsTypeAux(S:K, A:K, L, .K,
                        T1:K, As:Set, Ts:Set, Is:Set)
           => toAbsTypeAux(S, A, L, toAbsType(S, T1, As, Ts, Is), .K, As, Ts, Is)
        requires notBool isBATypeCon(T1)
      rule toAbsTypeAux(S:K, A:K, L:List, .K,
                        .K, As:Set, Ts:Set, Is:Set)
            => toAbsTypeAuxAux(A, L)
           requires notBool isError(A)


   rule toAbsTypeAuxAux(typeConst(X:K, L:List), L1:List)
             => typeConst(X:K, L L1)
   rule toAbsTypeAuxAux(error(A:K), L2:List) => error(A)
   rule toAbsTypeAuxAux(A:K, L:List) => typeConst(A, L) [owise]


   rule toAbsTypeTupleAux(A:K, error(B:K)) => error(B)
   rule toAbsTypeTupleAux(A:K, resultList(L:List)) => typeConst(A, L)

   rule toAbsTypeTuple(S:K, 'twoTypeTuple(A:K,, B:K),
                .K, L:List, As:Set, Ts:Set, Is:Set)
                => toAbsTypeTuple(S, B, toAbsType(S,
                     A, As:Set, Ts:Set, Is:Set),L, As:Set, Ts:Set, Is:Set)
   rule toAbsTypeTuple(S:K, 'typeTupleCon(A:K,, B:TypeTuple),
                .K, L:List, As:Set, Ts:Set, Is:Set)
                => toAbsTypeTuple(S, B, toAbsType(S,
                     A, As:Set, Ts:Set, Is:Set), L, As:Set, Ts:Set, Is:Set)
   rule toAbsTypeTuple(S:K, A:Type, .K, L:List, As:Set, Ts:Set, Is:Set)
                => toAbsTypeTuple(S, .K, toAbsType(S,
                     A, As:Set, Ts:Set, Is:Set),L, As:Set, Ts:Set, Is:Set)
   rule toAbsTypeTuple(S:K, .K, .K, L:List, As:Set, Ts:Set, Is:Set)
                => resultList(L)
   rule toAbsTypeTuple(S:K, A:K, error(B:K), L:List, As:Set, Ts:Set, Is:Set)
               => error(B)
   rule toAbsTypeTuple(S:K, A:K, T:KItem, L:List, As:Set, Ts:Set, Is:Set)
            => toAbsTypeTuple(S, A, .K, L ListItem(T), As, Ts, Is)
        requires  notBool isError(T)


   //for simple type-vars-title
   syntax List ::= toAbsTypeTuple(K, K) [function]//curr-mod, type-tuple
   rule toAbsTypeTuple(S:K, 'twoTypeVarTuple(A:K,, B:K))
                     => ListItem(A) ListItem(B)
   rule toAbsTypeTuple(S:K, 'typeVarTupleCon(A:K,, B:TypeTuple))
                     => ListItem(A) toAbsTypeTuple(S, B)

   //collecting preBetaMap info
   /*
    syntax OptConstrs  ::= "=" Constrs [klabel('nonemptyConstrs)] | "" [onlyLabel, klabel('emptyConstrs)]
    syntax Constrs     ::= Constr [klabel('singleConstr)] | Constr "|" Constrs [klabel('multConstr)]
    syntax Constr      ::= Con OptBangATypes [klabel('constrCon)] // (arity con  =  k, k ≥ 0) UNFINISHED
                         | SubConstr ConOp SubConstr
                         | Con "{" FieldDeclList "}"
   */

   syntax Bool ::= dealWithBang(OptBang) [function]
   rule dealWithBang('emptyBang(.KList)) => false
   rule dealWithBang(!) => true

   syntax KItem ::= toAbsBangType(K, K, List, Set, Set, Set) [function]
                 //curr-mod-name, types,result,
                // set-of-type-vars, curr-types, imports
                  | toAbsBangTypeAux(K, Bool, K, K, List, Set, Set, Set) [function]
   rule toAbsBangType(S:K, .OptBangATypes, L:List, As:Set, Ts:Set, Is:Set)
              => resultList(L)
   rule toAbsBangType(S:K, 'optBangATypes('optBangAType(Op:OptBang,, A:AType)
        ,, ATs:OptBangATypes), L:List, As:Set, Ts:Set, Is:Set)
            => toAbsBangTypeAux(S,dealWithBang(Op),
                         toAbsType(S, A, As, Ts, Is), ATs,L, As, Ts, Is)
   rule toAbsBangTypeAux(S:K, F:Bool, error(A:K), AT:K,
              L:List, As:Set, Ts:Set, Is:Set) => error(A)
   rule toAbsBangTypeAux(S:K, F:Bool, T:K, AT:K,
              L:List, As:Set, Ts:Set, Is:Set)
          => toAbsBangType(S, AT, L ListItem(aType(F, T)), As, Ts, Is) [owise]

   syntax List ::= expandRecordType(K, Vars, K) [function]
   rule expandRecordType(S:K, A:Var, T:K)
             => ListItem(typeConst(fullName(Prelude, typeName(recordTypeAssign)),
                    ListItem(tyVar(S, funName(pillVar(A)))) ListItem(T)))
   rule expandRecordType(S:K, 'varCon(A:Var,, As:Vars), T:K)
           => ListItem(typeConst(fullName(Prelude, typeName(recordTypeAssign)),
                      ListItem(tyVar(S, funName(pillVar(A))))
                               ListItem(T))) expandRecordType(S, As, T)

   syntax KItem ::= toAbsBangTypeInRecord(K, K, List, Set, Set, Set) [function]
                 //curr-mod-name, types, results
                 //set-of-type-vars, curr-types, imports
                 | toAbsBangTypeInRecordAux(K, K, Bool, K, K, List, Set, Set, Set) [function]
   rule toAbsBangTypeInRecord(S:K, .FieldDeclList, L:List,
         As:Set, Ts:Set, Is:Set) => resultList(L)
   rule toAbsBangTypeInRecord(S:K, 'fieldCon(Vs:Vars :: ! A:AType
           ,, Fs:FieldDeclList),L:List, As:Set, Ts:Set, Is:Set)
              => toAbsBangTypeInRecordAux(S, Vs, true,
                         toAbsType(S, A, As, Ts, Is), Fs, L, As, Ts, Is)
   rule toAbsBangTypeInRecord(S:K, 'fieldCon('varAssign(Vs:Vars,, A:AType)
           ,, Fs:FieldDeclList),L:List, As:Set, Ts:Set, Is:Set)
            => toAbsBangTypeInRecordAux(S, Vs, false,
                         toAbsType(S, A, As, Ts, Is), Fs, L, As, Ts, Is)

   rule toAbsBangTypeInRecordAux(S:K, Vs:Vars, F:Bool, error(A:K),
            Fs:K, L:List, As:Set, Ts:Set, Is:Set) => error(A)
   rule toAbsBangTypeInRecordAux(S:K, Vs:Vars, F:Bool, T:K,
            Fs:K, L:List, As:Set, Ts:Set, Is:Set)
         => toAbsBangTypeInRecord(S, Fs,
                 L expandRecordType(S, Vs, aType(F, T)), As, Ts, Is) [owise]

   syntax KItem ::= dealWithSubCons(K, List, List, Set, Set, Set) [function]
                  | dealWithSubConsAux(K, K, List, List, Set, Set, Set) [function]
   rule dealWithSubCons(S:K, .List, L:List, As:Set, Ts:Set, Is:Set) => resultList(L)
   rule dealWithSubCons(S:K, ListItem(A:BType) L1:List, L:List, As:Set, Ts:Set, Is:Set)
        => dealWithSubConsAux(S, toAbsType(S, A, As, Ts, Is), L1, L, As, Ts, Is)
   rule dealWithSubCons(S:K, ListItem('strictSubCon(A:AType)) L1:List,
               L:List, As:Set, Ts:Set, Is:Set)
        => dealWithSubConsAux(S, toAbsTypeStrict(S, A, As, Ts, Is), L1, L, As, Ts, Is)

   rule dealWithSubConsAux(S:K, error(A:K), L1:List, L:List,
           As:Set, Ts:Set, Is:Set)  => error(A)
   rule dealWithSubConsAux(S:K, T:K, L1:List, L:List,As:Set, Ts:Set, Is:Set)
             => dealWithSubCons(S, L1, L ListItem(T), As, Ts, Is) [owise]


   syntax KItem ::= makeMultiPreBeta(K, K, K, Set, Set, Set) [function]
                  | makeMultiPreBeta1(K, K, K, Map, Set, Set, Set) [function]
                  | makeMultiPreBeta2(K, K, K,K, Map, Set, Set, Set) [function]
                  | makeSinglePreBeta(K, K, K, Set, Set, Set) [function]
          //curr-mod-name, target-type, constrs/newconstr, result
         // set-of-type-vars, curr-types, imports
   //deal with constrs
                  | makeSinglePreBetaField(K, K, K) [function]
                  | makeSinglePreBetaCon(K, K, K) [function]
                  | makeSinglePreBetaNewType(K, K, K) [function]
                  | makeSinglePreBetaNewField(K,K, K, K) [function]

   rule makeSinglePreBeta(S:K, T:K, 'emptyConstrs(.KList),
          As:Set, Ts:Set, Is:Set) => resultMap(.Map)
   rule makeSinglePreBeta(S:K, T:K, 'nonemptyConstrs(Cs:Constrs),
            As:Set, Ts:Set, Is:Set) => makeSinglePreBeta(S, T, Cs, As, Ts, Is)
   rule makeSinglePreBeta(S:K, T:K, 'constrCon(N:Con,, Tk:OptBangATypes),
           As:Set, Ts:Set, Is:Set)
           => makeSinglePreBetaCon(constrName(pillVar(N)),
                     toAbsBangType(S, Tk, .List, As, Ts, Is), T)
   rule makeSinglePreBeta(S:K, T:K, 'mixfixbinCon(
           T1:SubConstr,, C:ConOp,, T2:SubConstr), As:Set, Ts:Set, Is:Set)
           => makeSinglePreBetaCon(constrName(pillVar(C)), dealWithSubCons(
                    S, ListItem(T1) ListItem(T2), .List, As, Ts, Is), T)
   rule makeSinglePreBeta(S:K, T:K, N:Con { F:FieldDeclList }, As:Set, Ts:Set, Is:Set)
           => makeSinglePreBetaField(constrName(pillVar(N)), 
                  toAbsBangTypeInRecord(S, F, .List, As, Ts, Is), T)
   rule makeSinglePreBeta(S:K, T:K, 'newConstrCon(N:Con,, A:AType),
            As:Set, Ts:Set, Is:Set)
         => makeSinglePreBetaNewType(constrName(pillVar(N)),
                toAbsType(S, A, As, Ts, Is), T)
   rule makeSinglePreBeta(S:K, T:K, 'newConField(N:Con,, V:Var,, T':Type),
             As:Set, Ts:Set, Is:Set)
           => makeSinglePreBetaNewField(constrName(pillVar(N)),
               tyVar(S, funName(pillVar(V))), toAbsType(S, T', As, Ts, Is), T)

   rule makeSinglePreBetaField(A:K, error(B:K), T:K) => error(B)
   rule makeSinglePreBetaField(A:K, resultList(L:List), T:K)
            => resultMap(A |-> curryTypes(ListItem(typeConst(
              fullName(Prelude, typeName(recordType)), L)), T))

   rule makeSinglePreBetaCon(A:K, error(B:K), T:K) => error(B)
   rule makeSinglePreBetaCon(A:K, resultList(L:List), T2:K)
               => resultMap(A |-> curryTypes(L, T2))

   rule makeSinglePreBetaNewField(A:K, V:K, error(B:K), T:K) => error(B)
   rule makeSinglePreBetaNewField(A:K, V:K, T1:K, T:K)
            => resultMap(A |-> typeConst(fullName(Prelude, typeName((->))),
                     ListItem(typeConst(fullName(Prelude, typeName(recordType)),
                     ListItem(typeConst(fullName(Prelude, typeName(recordTypeAssign)),
                     ListItem(V) ListItem(T1))))) ListItem(T)))

   rule makeSinglePreBetaNewType(A:K, error(B:K), T:K) => error(B)
   rule makeSinglePreBetaNewType(A:K, T:K, T1:K)
                => resultMap(A |-> curryTypes(ListItem(T), T1)) [owise]

   rule makeMultiPreBeta(S:K, error(A:K), Cons:K, As:Set, Ts:Set, Is:Set)
           => error(A)
   rule makeMultiPreBeta(S:K, T:K, Cons:K, As:Set, Ts:Set, Is:Set)
          => makeMultiPreBeta1(S, T, Cons, .Map, As, Ts, Is)
        requires notBool isError(T)
   rule makeMultiPreBeta1(S:K, T:K, 'multConstr(
               C:Constr,, Cs:Constrs), M:Map, As:Set, Ts:Set, Is:Set)
          => makeMultiPreBeta2(S, T, makeSinglePreBeta(S, T, C, As, Ts, Is),
                  Cs, M, As, Ts, Is)
   rule makeMultiPreBeta1(S:K, T:K, C:K, M:Map, As:Set, Ts:Set, Is:Set)
          => makeMultiPreBeta2(S, T, makeSinglePreBeta(S, T, C, As, Ts, Is),
                  .K, M, As, Ts, Is)  [owise]

   rule makeMultiPreBeta2(S:K, T:K, error(A:K), Cs:K, M:Map, As:Set, Ts:Set, Is:Set)
             => error(A)
   rule makeMultiPreBeta2(S:K, T:K, resultMap(M:Map), Cs:Constrs, M':Map,
                  As:Set, Ts:Set, Is:Set)
             => makeMultiPreBeta1(S, T, Cs, M M', As, Ts, Is)
   rule makeMultiPreBeta2(S:K, T:K, resultMap(M:Map), .K, M':Map,
                  As:Set, Ts:Set, Is:Set) => resultMap(M M')

   //functions to convert class name to abs form and convert context to a set of classes
   syntax KItem ::= toAbsClass(K, Class, Set, Set) [function]
           //curr-mod-name, class, curr-types, imports
                  | toAbsClassNext(K, List)        [function]
                  | toAbsClassAux(K, K, K)         [function]
   rule toAbsClass(Mod:K, 'classCon(T:QTyCon,, V:TyVar), Ts:Set, Is:Set)
             => toAbsClassNext(toAbsClassCon(Mod, T, Ts, Is), ListItem(V))
   rule toAbsClass(Mod:K, 'multiClass(T:QTyCon,, A:TyVar,, As:ATypeList), Ts:Set, Is:Set)
                  => toAbsClassAux(toAbsClassCon(Mod, T, Ts, Is), A,
                        toAbsTypeList(Mod, As, .K, .List, SetItem(A), Ts, Is))

   rule toAbsClassAux(error(A:K), B:K, C:K) => error(A)
   rule toAbsClassAux(A:K, B:K, error(C:K)) => error(C)
   rule toAbsClassAux(A:K, B:K, resultList(L:List))
             => toAbsClassNext(A, ListItem(B) L)
        requires notBool isError(A)
   rule toAbsClassNext(error(A:K), B:List) => error(A)
   rule toAbsClassNext(A:K, B:List) => classTitle(A, B) [owise]

   syntax KItem ::= contextToSet(K, K, K, Set, Set, Set) [function]
          //curr-mod-name, class, execution, store, curr-types, imports
   rule contextToSet(Mod:K, .K, .K, S:Set, Ts:Set, Is:Set) => resultSet(S)
   rule contextToSet(Mod:K, A:K, error(B:K), S:Set, Ts:Set, Is:Set) => error(B)
   rule contextToSet(Mod:K, A:K, classTitle(X:K, Y:List), S:Set, Ts, Is)
            => contextToSet(Mod, A, .K, SetItem(classTitle(X, Y)) S, Ts, Is)
   rule contextToSet(Mod:K, 'emptyContext(.KList),
               .K, S:Set, Ts:Set, Is:Set) => resultSet(S)
   rule contextToSet(Mod:K, C:Class =>, X:K, S:Set, Ts:Set, Is:Set)
             => contextToSet(Mod, .K, toAbsClass(Mod, C, Ts, Is), S, Ts, Is)
   rule contextToSet(Mod:K, 'contextClass(Cs:Classes) =>, .K, S:Set, Ts:Set, Is:Set)
             => contextToSet(Mod, Cs, .K, S, Ts, Is)
   rule contextToSet(Mod:K, .Classes, .K, S:Set, Ts:Set, Is:Set) => resultSet(S)
   rule contextToSet(Mod:K, 'classesCon(A:Class,, B:Classes), .K, S:Set, Ts:Set, Is:Set)
           => contextToSet(Mod, B, toAbsClass(Mod, A, Ts, Is), S, Ts, Is)

   syntax KItem ::= derivingToSet(K, K, Set, Set) [function]
         //curr-mod, opt-deriving, set of types, imports
                | derivingToSetAux(K, DClassList, K, Set, Set, Set) [function]
            //curr-mod, DClassList, execution, store, types, imports
   rule derivingToSet(N:K, 'emptyDeriving(.KList), Ts:Set, Is:Set) => resultSet(.Set)
   rule derivingToSet(N:K, deriving D:DClass, Ts:Set, Is:Set)
           => derivingToSetAux(N, 'dclassCon(D, .DClassList),.K, .Set, Ts, Is)
   rule derivingToSet(N:K, deriving (Ds:DClassList), Ts:Set, Is:Set)
           => derivingToSetAux(N, Ds,.K, .Set, Ts, Is)
   rule derivingToSetAux(N:K, .DClassList, .K, S:Set, Ts:Set, Is:Set) => resultSet(S)
   rule derivingToSetAux(N:K, 'dclassCon(A:QTyCon,,
                        B:DClassList), .K,  S:Set, Ts:Set, Is:Set)
           => derivingToSetAux(N, B, toAbsClassCon(N, A, Ts, Is), S, Ts, Is)
   rule derivingToSetAux(N:K, D:K, error(A:K), S:Set, Ts:Set, Is:Set) => error(A)
   rule derivingToSetAux(N:K, D:K, fullName(X:K, Y:K), S:Set, Ts:Set, Is:Set)
              => derivingToSetAux(N, D, .K, S SetItem(fullName(X:K, Y:K)), Ts, Is)
        requires notBool fullName(X:K, Y:K) in S
   rule derivingToSetAux(N:K, D:K, fullName(X:K, Y:K), S:Set, Ts:Set, Is:Set)
              => error(duplicateDeriving)
        requires fullName(X:K, Y:K) in S

   syntax KItem ::= makePreBetaFun(K, K, Map, Set, Set) [function]
           //curr-mod, term, store, set-of-args, set-of-types, imports
                | makePreBetaFunAux(K, K, K, Map, Set, Set) [function]
                | makePreBetaFunAux1(K, K, K, List, K, K, Map, Set, Set) [function]
   rule makePreBetaFun(S:K, 'bodyimpandtop(I:ImpDecls,, T:TopDecls)
          , M:Map, Ts:Set, Is:Set)
          => makePreBetaFun(S, T, M, Ts, Is)
   rule makePreBetaFun(S:K, 'bodyimpdecls(I:ImpDecls),
                    M:Map, Ts:Set, Is:Set) => .K
   rule makePreBetaFun(S:K, 'bodytopdecls(T:TopDecls)
                  , M:Map, Ts:Set, Is:Set)
                    => makePreBetaFun(S, T, M, Ts, Is)
   rule makePreBetaFun(S:K, .TopDecls, M:Map,
              Ts:Set, Is:Set) => putPreBetaMap(M)
   rule makePreBetaFun(S:K, 'topdeclslist(A:TopDecl,, As:TopDecls)
               , M:Map, Ts:Set, Is:Set)
              => makePreBetaFunAux(S, A, As, M, Ts:Set, Is:Set)

   rule makePreBetaFunAux(S:K, 'data(
              'simpleTypeCon(N:K,, Vs:K),, Cons:K,, Od:K),
                 As:K, M:Map, Ts:Set, Is:Set)
          =>  makePreBetaFunAux1(S, As, buildVar(N),toTypeList(Ts),
                  makeMultiPreBeta(S, buildVar(N), Cons, toTypeSet(Vs), Ts, Is),
               derivingToSet(S, Od, Ts, Is), M, Ts, Is)
        requires size(toTypeList(Vs)) ==K size(toTypeSet(Vs))
   rule makePreBetaFunAux(S:K, 'data(
              'simpleTypeCon(N:K,, Vs:K),, Cons:K,, Od:K)
                  , As:K, M:Map, Ts:Set, Is:Set)
          => error(typeVarNotUnique)
        requires size(toTypeList(Vs)) =/=K size(toTypeSet(Vs))
   rule makePreBetaFunAux(S:K, 'newtype('simpleTypeCon(N:K,, Vs:K),,
               Cons:NewConstr,, Od:K), As:K, M:Map, Ts:Set, Is:Set)
          =>  makePreBetaFunAux1(S, As, buildVar(N),toTypeList(Ts),
                  makeMultiPreBeta(S, buildVar(N), Cons, toTypeSet(Vs), Ts, Is),
               derivingToSet(S, Od, Ts, Is), M, Ts, Is)
        requires size(toTypeList(Vs)) ==K size(toTypeSet(Vs))
   rule makePreBetaFunAux(S:K, 'newtype('simpleTypeCon(N:K,, Vs:K),,
               Cons:NewConstr,, Od:K), As:K, M:Map, Ts:Set, Is:Set)
          => error(typeVarNotUnique)
        requires size(toTypeList(Vs)) =/=K size(toTypeSet(Vs))
   rule makePreBetaFunAux(S:K, A:TopDecl, As:K, TM:Map, Ts:Set, Is:Set)
                  => makePreBetaFun(S, As, TM, Ts:Set, Is:Set) [owise]

   rule makePreBetaFunAux1(S:K, As:K, A:K, Vs:List, error(C:K),
             D:K, M:Map, Ts:Set, Is:Set) => error(C)
   rule makePreBetaFunAux1(S:K, As:K, A:K, Vs:List, C:K,
             error(D:K), M:Map, Ts:Set, Is:Set) => error(D)
   rule makePreBetaFunAux1(S:K, As:K, A:K, Vs:List, resultMap(C:Map),
             resultSet(D:Set), M:Map, Ts:Set, Is:Set)
           => makePreBetaFun(S, As, (A |-> preBetaEntry(Vs, C, D)) M, Ts, Is)

   //kind inference function
   syntax Map ::= addKindToMap(K, K, Set, Map, Map) [function]
               //mod, execution, term-set, kind-map, store
   rule addKindToMap(Mod:K, .K, .Set, SM:Map, KM:Map) => KM
   rule addKindToMap(Mod:K, .K, SetItem(A:K) S:Set, SM:Map, KM:Map)
           => addKindToMap(Mod:K, A, S, SM, KM)
   rule addKindToMap(Mod:K, className(A:K), S:Set,
                     (className(A:K) |-> V:K) SM:Map, KM:Map)
           => addKindToMap(Mod:K, .K, S, SM,
                       (fullName(Mod, className(A:K)) |-> V:K) KM)
        requires notBool fullName(Mod, className(A:K)) in keys(KM)
   rule addKindToMap(Mod:K, typeName(A:K), S:Set,
                     (typeName(A:K) |-> V:K) SM:Map, KM:Map)
           => addKindToMap(Mod:K, .K, S, SM,
                       (fullName(Mod, typeName(A:K)) |-> V:K) KM)
        requires notBool fullName(Mod, typeName(A:K)) in keys(KM)
   rule addKindToMap(Mod:K, A:KItem, S:Set, SM:Map, KM:Map)
           => addKindToMap(Mod:K, .K, S, SM, KM) [owise]

   syntax Bool ::= isTheKind(K, K, K, Map) [function]
   rule isTheKind(A:K, B:K, .K, M:Map) => false
        requires notBool A in keys(M)
   rule isTheKind(A:K, B:K, .K, (A |-> C:K) M:Map)
          => isTheKind(A, B, C, M)
   rule isTheKind(A:K, B:K, B:K, M:Map) => true
   rule isTheKind(A:K, B:K, C:K, M:Map) => false [owise]

   syntax Int ::= countKindLength(K) [function]
   rule countKindLength(kindArrow(X:K, Y:K)) => 1 +Int countKindLength(Y)
   rule countKindLength(A:K) => 0 [owise]

   syntax List ::= formListKind(K) [function]
   rule formListKind(kindArrow(A:K, B:K)) => ListItem(A) formListKind(B)
   rule formListKind(A:K) => .List [owise]

   //kind inference top rule
   syntax KItem ::= genTyVarKind(K, Map, List) [function]
   rule genTyVarKind(A:K, M:Map, .List) => resultMap(M)
   rule genTyVarKind(kindArrow(X:K, Y:K), M:Map, ListItem(A:K) L:List)
           => genTyVarKind(Y, (A |-> X) M, L)

   syntax Bool ::= isCurryType(K) [function]
   rule isCurryType(curryTypes(A:List, B:K)) => true
   rule isCurryType(A:K) => false [owise]

   syntax Set ::= toKindTupleSet(Map) [function]
   rule toKindTupleSet(.Map) => .Set
   rule toKindTupleSet((A:K |-> B:K) M:Map)
           => SetItem(kindTuple(A,B)) toKindTupleSet(M)

   //starting kind inference algorithm
   syntax KItem ::= genArrowKinds(Int, Set, Int, List) [function]
   rule genArrowKinds(N:Int, S:Set, 0, L:List)
           => resultTransSetTerm(N, S, listToKind(L))
   rule genArrowKinds(N:Int, S:Set, I:Int, L:List)
           => genArrowKinds(N +Int 1, S SetItem(kindVar(N)),
                 I -Int 1, L ListItem(kindVar(N)))
        requires I >Int 0

   syntax KItem ::= genInitKindMap(Int, Set, K, K, Map, Map) [function]
                  | genInitKindMapAux(K, K, Map, Map) [function]

   rule genInitKindMap(N:Int, S:Set, .K, .K, .Map, M:Map)
              => resultTyVarKindMap(N, S, M)
   rule genInitKindMap(N:Int, S:Set, .K, .K, (A:K |-> B:K) M:Map, TM:Map)
           => genInitKindMap(N, S, A, B, M, TM)
   rule genInitKindMap(N:Int, S:Set, A:K, preBetaEntry(
                      L:List, SM:Map, SS:Set), M:Map, TM:Map)
          => genInitKindMapAux(A, genArrowKinds(N, S, size(L), .List), M, TM)
   rule genInitKindMap(N:Int, S:Set, A:K, alphaTuple(L:List, T:K), M:Map, TM:Map)
          => genInitKindMapAux(A, genArrowKinds(N, S, size(L), .List), M, TM)

   rule genInitKindMapAux(A:K, resultTransSetTerm(N:Int, S:Set, T:K), M:Map, TM:Map)
          => genInitKindMap(N, S, .K, .K, M, (A |-> T) TM)


   syntax KItem ::= genInitKindMapClass(Int, Set, Set, Map) [function]
   rule genInitKindMapClass(N:Int, S:Set, .Set, T:Map)
            => resultTyVarKindMap(N, S, T)
   rule genInitKindMapClass(N:Int, S:Set, SetItem(A:K) As:Set, T:Map)
            => genInitKindMapClass(N +Int 1, S SetItem(kindVar(N)),
             As, (A |-> kindArrow(kindVar(N), star)) T)

   syntax KItem ::= searchNoFatherClass(K, K, Map, Set, Map) [function]
                //class, contexts, finished classes (with curr-mod), import-maps
   rule searchNoFatherClass(.K, .K, .Map, S:Set, PM:Map) => error(cycleClasses)
   rule searchNoFatherClass(.K, .K, (A:K |-> B:K) M:Map, S:Set, PM:Map)
            => searchNoFatherClass(A, B, M, S, PM)
   rule searchNoFatherClass(className(A:K), resultSet(S:Set), M:Map, Cs:Set, PM:Map)
            => className(A)
        requires S <=Set Cs keys(PM)
   rule searchNoFatherClass(className(A:K), resultSet(S:Set), M:Map, Cs:Set, PM:Map)
            => searchNoFatherClass(.K, .K, M, Cs, PM)
        requires notBool (S <=Set Cs keys(PM))


   syntax KItem ::= kindInfer(Int, Set,K, K, K, Map, Map, Set, Set, Map) [function]
         //counter, kind-var-set, name, entry, beta, kind env, gen-kind-tuples
          //set of imports, import kind map-map(mod to kind-map)
                  | kindInferAux(Int, Set,K, K, K, Map, Map, Map, Set, Set, Map) [function]
                     //counter, kind-var-set, result-type-var-kind, curr-ty-name,
                    //body map, beta, kind-map, gen-kind,tuples, imports, import kind map-map
                  | kindInferAuxAlpha(Int, Set,K, K, K, K, Map, Map, Set, Set, Map) [function]
                     //counter, kind-var-set, result-type-var-kind, curr-ty-name,
                    //body, beta, kind-map, gen-kind,tuples, imports, import kind map-map
                  | kindInferSec(K, K, K, Map, Map, Set, Set, Map) [function]
                   //name, execution, beta, kind-env,
                   // gen-kind-tuples, imports, import kind map-map
                  | kindInferThird(Int, Set,K, K, K, Map, Map, Set, Set, Map) [function]
                  | kindInferLast(Int, Set,K, K, K, Map, Map, Set, Set, Map) [function]
                  | kindNext(Int, Set,K, K, Map, Map, Set, Set, Map) [function]
                  | kindNextList(Int, Set,K, K, List, Map, Map, Set, Set, Map) [function]
                  | kindInferFinal(Int, Set, K, Map) [function]

   rule kindInferFinal(N:Int, S:Set, resultMap(M:Map), KM:Map)
        => resultTyVarKindMap(N, S,
                replaceAllKindVarsWithStar(replaceAllKindInMap(M, KM)))

   rule kindInfer(N:Int, S:Set,Mod:K, .K, .K, .Map, KM:Map, Tu:Set, Is:Set, PM:Map)
             => kindInferFinal(N, S, unifInKind(.K, .Set, Tu, .Map), KM)
   rule kindInfer(N:Int, S:Set,Mod:K, .K, .K,
              (A:K |-> B:K) BM:Map, KM:Map, Tu:Set, Is:Set, PM:Map)
          => kindInfer(N, S,Mod, A, B, BM, KM, Tu, Is, PM)
   rule kindInfer(N:Int, S:Set,Mod:K, A:K, preBetaEntry(
                Vl:List, Body:Map, Od:Set), BM:Map,
                   (A |-> T:K) KM:Map, Tu:Set, Is:Set, PM:Map)
          => kindInferAux(N, S,Mod:K, genTyVarKind(T,
                          .Map, Vl), A, Body, BM, (A |-> T:K) KM, Tu, Is, PM)
   rule kindInfer(N:Int, S:Set,Mod:K, A:K, alphaTuple(Vl:List, Body:K),
                 BM:Map, (A |-> T:K) KM:Map, Tu:Set, Is:Set, PM:Map)
          => kindInferAuxAlpha(N, S, Mod:K, genTyVarKind(T,
                          .Map, Vl), A, Body, BM, (A |-> T:K) KM, Tu, Is, PM)

   rule kindInferAuxAlpha(N:Int, S:Set,Mod:K, resultMap(M:Map), A:K,
                 Body:K, BM:Map, KM:Map, Tu:Set, Is:Set, PM:Map)
          => kindInferSec(Mod,A, kindNext(N, S,Mod:K, Body, .Map,
                           KM M, .Set, Is, PM), BM, KM, Tu, Is, PM)

   rule kindInferAux(N:Int, S:Set, Mod:K,resultMap(M:Map),
                      A:K, Body:Map, BM:Map, KM:Map, Tu:Set, Is:Set, PM:Map)
             => kindInferSec(Mod, A, kindNext(N, S,Mod:K, .K, Body,
                             KM M, .Set, Is, PM), BM, KM, Tu, Is, PM)

   rule kindInferSec(Mod:K, A:K, returnKind(N:Int, S:Set, Tus:Set),
                       BM:Map, KM:Map, Tu:Set, Is:Set, PM:Map)
             => kindInferThird(N, S,Mod:K, A, checkAndRemoveNoVarTerms(
                                     .K, Tus, .Set), BM:Map, KM:Map, Tu, Is, PM)
   rule kindInferSec(Mod:K,A:K, error(X:K), BM:Map, KM:Map,
                          Tu:Set, Is:Set, PM:Map) => error(X)
   rule kindInferThird(N:K, S:Set,Mod:K, A:K, error(X:K),
                    BM:Map, KM:Map, Tu:Set, Is:Set, PM:Map) => error(X)
   rule kindInferThird(N:K, S1:Set,Mod:K, A:K,
                    resultSet(S:Set), BM:Map, KM:Map, Tu:Set, Is:Set, PM:Map)
            => kindInferLast(N, S1, Mod:K, A,
                    unifInKind(.K, .Set, S, .Map), BM, KM, Tu, Is:Set, PM:Map)

   rule kindInferLast(N:Int, S:Set,Mod:K, A:K,
            error(X:K), BM:Map, KM:Map, Tu:Set, Is:Set, PM:Map) => error(X)
   rule kindInferLast(N:Int, S:Set,Mod:K, A:K,
            resultMap(TuM:Map), BM:Map, KM:Map, Tu:Set, Is:Set, PM:Map)
           => kindInfer(N, S,Mod:K, .K, .K, BM, KM, toKindTupleSet(TuM) Tu, Is, PM)

   rule kindNext(N:Int, S:Set,Mod:K, .K, .Map,
                M:Map, Tus:Set, Is:Set, PM:Map) => returnKind(N, S, Tus)
   rule kindNext(N:Int, S:Set,Mod:K, .K,
               (A:K |-> B:K) Body:Map, M:Map, Tus:Set, Is:Set, PM:Map)
          => kindNext(N:Int, S:Set,Mod:K, B, Body, M, Tus, Is, PM)
   rule kindNext(N:Int, S:Set,Mod:K,
             curryTypes(L:List, T:K), Body:Map, M:Map, Tus:Set, Is:Set, PM:Map)
          => kindNextList(N, S,Mod:K, .K, L, Body, M, Tus, Is, PM)
   rule kindNext(N:Int, S:Set,Mod:K, T:KItem, Body:Map, M:Map, Tus:Set, Is:Set, PM:Map)
          => kindNextList(N, S,Mod:K, .K, ListItem(T), Body, M, Tus, Is, PM)
        requires notBool isCurryType(T)

   rule kindNextList(N:Int, S:Set,Mod:K, .K,
                 .List, Body:Map, M:Map, Tus:Set, Is:Set, PM:Map)
            => kindNext(N, S,Mod:K, .K, Body, M, Tus,Is, PM)
   rule kindNextList(N:Int, S:Set,Mod:K, .K,
               ListItem(A:K) L:List, Body:Map, M:Map, Tus:Set, Is:Set, PM:Map)
           => kindNextList(N, S,Mod:K, kindInference(N, S,Mod, A,
                    star, M, Is, PM), L, Body, M, Tus, Is, PM)
   rule kindNextList(N:Int, S:Set,Mod:K, error(X:K),
            L:List, Body:Map, M:Map, Tus:Set, Is:Set, PM:Map) => error(X)
   rule kindNextList(N:Int, S:Set, Mod:K, returnKind(N1:Int, S1:Set, Tu1:Set),
              L:List, Body:Map, M:Map, Tus:Set, Is:Set, PM:Map)
          => kindNextList(N1, S1,Mod:K, .K, L, Body, M, Tus Tu1, Is, PM)

   //a function to kind inference every function in a class
   syntax Bool ::= isSameInMap(K, K, Map) [function]
   rule isSameInMap(A:K, B:K, (A |-> B:K) M:Map) => true
   rule isSameInMap(A:K, B:K, M:Map) => false [owise]

   syntax KItem ::= kindInferClass(Int, Set, K, K, K, Map, Set, Map, Set, Map) [function]
               //counter, kind-var-set, mod, type-var, execute, method-map,
               // contexts, kind env, imports, import-map
                  | kindInferClassAux(K, K, K, K, Map, Map, Set, Map) [function]
                  | kindInferClassCheck(Int, Set, K, K, K, Map, Map, Set, Map) [function]
                  | kindInferClassCheckAux(Int, Set, K, K, K, Map, Map, Set, Map) [function]
                  | kindInferClassCheckAux1(K, K, K, K, Map,Map, Set, Map) [function]
                  | kindInferClassCheckAux2(K, K, K, K, Map,Map, Map, Set, Map) [function]
                  | kindInferClassCheckAux3(Int, Set, K, K, K, Map, Map, Map, Set, Map) [function]

   rule kindInferClass(N:Int, S:Set, Mod:K, A:K,
               .K, .Map, Cs:Set, (A |-> B:K) KM:Map, Is:Set, PM:Map)
              => resultTuple(A, star)
        requires Cs <=Set .Set
   rule kindInferClass(N:Int, S:Set, Mod:K, A:K,
               .K, .Map, Cs:Set, (A |-> B:K) KM:Map, Is:Set, PM:Map)
              => sameAsContextClass
        requires notBool (Cs <=Set .Set)
   rule kindInferClass(N:Int, S:Set, Mod:K, A:K, .K, (X:K |-> Y:K) MM:Map,
                  Cs:Set, KM:Map, Is:Set, PM:Map)
           => kindInferClass(N, S, Mod, A:K, Y, MM, Cs, KM, Is, PM)
   rule kindInferClass(N:Int, S:Set, Mod:K, A:K, methodDef(
             Cs:Set, Fs:Map, T:K, Bin:List), MM:Map, Ccs:Set, KM:Map, Is:Set, PM:Map)
           => kindInferClassAux(Mod:K, A:K, T,
                 genKindMap(N, S, keys(Fs), KM), MM, KM, Is, PM)

   rule kindInferClassAux(Mod:K, A:K, T:K, resultTransSetMap(
              N:Int, S:Set, KM:Map), MM:Map, Old:Map, Is:Set, PM:Map)
           => kindInferClassAux(Mod, A, T, kindInference(
                      N, S, Mod, T, star, KM, Is, PM), MM, Old, Is, PM)
   rule kindInferClassAux(Mod:K, A:K, T:K, error(X:K), MM:Map,
            Old:Map,Is:Set, PM:Map) => error(X)
   rule kindInferClassAux(Mod:K, A:K, T:K, returnKind(
                N:Int, S:Set, Ts:Set), MM:Map, Old:Map,Is:Set, PM:Map)
            => kindInferClassCheck(N, S, Mod, A,
                   unifInKind(.K, .Set, Ts, .Map), MM, Old, Is, PM)
   rule kindInferClassCheck(N:Int, S:Set, Mod:K, A:K, error(B:K),
              MM:Map, KM:Map, Is:Set, PM:Map) => error(B)
   rule kindInferClassCheck(N:Int, S:Set, Mod:K, A:K, resultMap(M:Map),
              MM:Map,  (A |-> T:K) KM:Map, Is:Set, PM:Map)
         => kindInferClassCheckAux(N, S, Mod, A, .K, MM,
                    (A |-> replaceAllKindsInTerm(T:K, M)) KM:Map, Is, PM)
   //a mutural recursive function to check all fuction decls in a class
   //having the same kind for the class typevar for the first one
   rule kindInferClassCheckAux(N:Int, S:Set, Mod:K, A:K, .K, .Map,
                 (A |-> B:K) KM:Map, Is:Set, PM:Map)
          => resultTuple(A, B)
   rule kindInferClassCheckAux(N:Int, S:Set, Mod:K, A:K, .K, (X:K |-> Y:K) MM:Map,
                 KM:Map, Is:Set, PM:Map)
          => kindInferClassCheckAux(N, S, Mod, A, Y, MM, KM, Is, PM)
   rule kindInferClassCheckAux(N:Int, S:Set, Mod:K, A:K, methodDef(
             Cs:Set, Fs:Map, T:K, Bin:List), MM:Map, KM:Map, Is:Set, PM:Map)
          => kindInferClassCheckAux1(Mod:K, A:K, T,
                 genKindMap(N, S, keys(Fs), KM), MM, KM, Is, PM)
   rule kindInferClassCheckAux(N:Int, S:Set, Mod:K, A:K, error(X:K),
            MM:Map, KM:Map, Is:Set, PM:Map) => error(X)

   rule kindInferClassCheckAux1(Mod:K, A:K, T:K, resultTransSetMap(
              N:Int, S:Set, KM:Map), MM:Map, Old:Map, Is:Set, PM:Map)
          => kindInferClassCheckAux2(Mod, A, T, kindInference(
                      N, S, Mod, T, star, KM, Is, PM), MM, KM, Old, Is, PM)
   rule kindInferClassCheckAux2(Mod:K, A:K, T:K, error(X:K),
              MM:Map, KM:Map, Old:Map, Is:Set, PM:Map) => error(X)
   rule kindInferClassCheckAux2(Mod:K, A:K, T:K, returnKind(
                N:Int, S:Set, Ts:Set), MM:Map, KM:Map, Old:Map, Is:Set, PM:Map)
         => kindInferClassCheckAux3(N, S, Mod, A, unifInKind(.K, .Set, Ts, .Map),
                  MM, KM, Old, Is, PM)

   rule kindInferClassCheckAux3(N:Int, S:Set, Mod:K, A:K, error(X:K),
            MM:Map, KM:Map, Old:Map, Is:Set, PM:Map) => error(X)
   rule kindInferClassCheckAux3(N:Int, S:Set, Mod:K, A:K,
             resultMap(M:Map), MM:Map, (A |-> B:K) KM:Map, Old:Map, Is:Set, PM:Map)
           => kindInferClassCheckAux(N, S, Mod, A, .K, MM, Old, Is, PM)
        requires isSameInMap(A, replaceAllKindsInTerm(B, M), Old)
   rule kindInferClassCheckAux3(N:Int, S:Set, Mod:K, A:K,
             resultMap(M:Map (A |-> B:K)),
            MM:Map, KM:Map, Old:Map, Is:Set, PM:Map) => error(classKindNotEqual)
        requires notBool isSameInMap(A, replaceAllKindsInTerm(B, M), Old)


   //kind inference rule -- generate kind unifiers
   syntax KItem ::= kindInference(Int, Set, K, K, K, Map, Set, Map) [function]
               //counter, kind-var-set, mod, exp, assume kind,
               // kind env, imports, import-map
                  | kindInferenceList(Int, Set, K, List, K, K, Set, Map, Set, Map) [function]
               //counter, kind-var-set, mod, list-of-types, assume-kind-of-arrow, execution, 
                //kind-unifiers, kind env., imports, import-map
                  | kindInferenceTyVar(K, K, List, K, K, Map, Set, Map) [function]
               //mod, target-assume, list-of-types, found-assume, execution, args,
                // kind env., imports, import-map

   rule kindInference(N:Int, S:Set, Mod:K,
                        A:TyVar, C:K, (A |-> D:K) M:Map, Is:Set, PM:Map)
             => returnKind(N, S, SetItem(kindTuple(C,D)))
   rule kindInference(N:Int, S:Set, Mod:K,
                        A:TyVar, C:K, M:Map, Is:Set, PM:Map)
             => error(typeVarNotInScope)
        requires notBool A in keys(M)
   rule kindInference(N:Int, S:Set, Mod:K,
                        aType(X:Bool, A:K), C:K, M:Map, Is:Set, PM:Map)
             => kindInference(N, S, Mod, A, C, M, Is, PM)
   rule kindInference(N:Int, S:Set, Mod:K, tyVar(Mod:K, Fn:K),
                     C:K, M:Map, Is:Set, PM:Map)
                => returnKind(N, S, SetItem(kindTuple(C,star)))
   rule kindInference(N:Int, S:Set, Mod:K, typeConst(
               fullName(Mod, B:K), L:List), C:K, (B |-> D:K) M:Map, Is:Set, PM:Map)
          => kindInferenceList(N, S, Mod, L, D, .K,
                   SetItem(kindTuple(C,star)), (B |-> D:K) M:Map, Is:Set, PM:Map)
   rule kindInference(N:Int, S:Set, Mod:K, typeConst(fullName(Mod':K, B:K), L:List),
                C:K, M:Map, Is:Set, (fullName(Mod':K, B:K) |-> D:K) PM:Map)
          => kindInferenceList(N, S, Mod, L, D, .K,
                SetItem(kindTuple(C,star)), M:Map, Is:Set, (fullName(Mod', B:K) |-> D:K) PM:Map)
   rule kindInference(N:Int, S:Set, Mod:K, typeConst(
               fullName(Mod':K, B:K), L:List), C:K, M:Map, Is:Set, PM:Map)
          => error(typeNotInScope)
        requires notBool B in keys(M) orBool notBool fullName(Mod', B:K) in keys(PM)
   rule kindInference(N:Int, S:Set, Mod:K, typeConst(
               A:TyVar, L:List), C:K, (A |-> D:K) M:Map, Is:Set, PM:Map)
          => kindInferenceTyVar(Mod, C, L, D, genArrowKinds(N, S,
                size(L), .List), (A |-> D:K) M:Map, Is:Set, PM:Map)
   rule kindInference(N:Int, S:Set, Mod:K, typeConst(
               A:TyVar, L:List), C:K, M:Map, Is:Set, PM:Map)
          => error(typeVarNotInScope)
        requires notBool A in keys(M)
   rule kindInferenceTyVar(Mod:K, C:K, L:List, D:K,
           resultTransSetTerm(N:Int, S:Set, D':K), M:Map, Is:Set, PM:Map)
         => kindInferenceList(N, S, Mod, L, D', .K, SetItem(kindTuple(C, star))
               SetItem(kindTuple(D, D')),M, Is, PM)

   rule kindInferenceList(N:Int, S:Set, Mod:K,
                   .List, D:K, .K, Ks:Set, M:Map, Is:Set, PM:Map)
           => returnKind(N, S, SetItem(kindTuple(D, star)) Ks)
   rule kindInferenceList(N:Int, S:Set, Mod:K,
                ListItem(A:K) L:List, kindArrow(D1:K, D2:K),
                  .K, Ks:Set, M:Map, Is:Set, PM:Map)
         => kindInferenceList(N, S, Mod, L, D2,
              kindInference(N, S, Mod, A, D1, M, Is, PM), Ks, M, Is, PM)
   rule kindInferenceList(N:Int, S:Set, Mod:K,
            L:List, D:K, error(E:K), Ks:Set, M:Map, Is:Set, PM:Map) => error(E)
   rule kindInferenceList(N:Int, S:Set, Mod:K,
            L:List, D:K, returnKind(N':Int, S':Set, Ks':Set),
                Ks:Set, M:Map, Is:Set, PM:Map)
           => kindInferenceList(N', S', Mod, L, D, .K, Ks' Ks, M, Is, PM)

   //a function to check and remove unifiers that have no variables.
   syntax Bool ::= hasVar(K) [function]
   rule hasVar(star) => false
   rule hasVar(kindVar(X:Int)) => true
   rule hasVar(kindArrow(A:K, B:K)) => hasVar(A) orBool hasVar(B)

   syntax KItem ::= checkAndRemoveNoVarTerms(K, Set, Set) [function]
   rule checkAndRemoveNoVarTerms(.K, .Set, S:Set) => resultSet(S)
   rule checkAndRemoveNoVarTerms(.K, SetItem(A:K) S:Set, S1:Set)
           => checkAndRemoveNoVarTerms(A, S, S1)
   rule checkAndRemoveNoVarTerms(kindTuple(A:K, B:K), S:Set, S1:Set)
           => checkAndRemoveNoVarTerms(.K, S, S1 SetItem(kindTuple(A, B)))
        requires hasVar(A) orBool hasVar(B)
   rule checkAndRemoveNoVarTerms(kindTuple(A:K, A:K), S:Set, S1:Set)
           => checkAndRemoveNoVarTerms(.K, S, S1)
        requires notBool hasVar(A)
   rule checkAndRemoveNoVarTerms(kindTuple(A:K, B:K), S:Set, S1:Set)
           => error(kindUnifierFail)
        requires notBool hasVar(A) andBool notBool hasVar(B) andBool A =/=K B

   //functions to implement the unification in kind
   syntax Bool ::= occurInKind(K, K) [function]
   rule occurInKind(A:K, A:K) => true
   rule occurInKind(A:K, kindArrow(X:K, Y:K))
          => occurInKind(A, X) orBool occurInKind(A, Y)
   rule occurInKind(A:K, B:K) => false [owise]

   syntax KItem ::= replaceKindInTerm(K, K, K) [function]
   rule replaceKindInTerm(A:K, B:K, A:K) => B
   rule replaceKindInTerm(A:K, B:K, kindArrow(X:K, Y:K))
          => kindArrow(replaceKindInTerm(A, B, X), replaceKindInTerm(A, B, Y))
   rule replaceKindInTerm(A:K, B:K, X:K) => X [owise]

   syntax Set ::= replaceKindInSet(K, K, K, Set) [function]
   rule replaceKindInSet(A:K, B:K, .K, .Set) => .Set
   rule replaceKindInSet(A:K, B:K, .K, SetItem(X:K) S:Set)
        => replaceKindInSet(A, B, X, S)
   rule replaceKindInSet(A:K, B:K, kindTuple(X:K, Y:K), S:Set)
        => SetItem(kindTuple(X, replaceKindInTerm(A, B, Y))) replaceKindInSet(A, B, .K, S)

   syntax Map ::= replaceKindInMap(K, K, K, K, Map) [function]
   rule replaceKindInMap(A:K, B:K, .K, .K, .Map) => .Map
   rule replaceKindInMap(A:K, B:K, .K, .K, (X:K |-> Y:K) S:Map)
        => replaceKindInMap(A, B, X, Y, S)
   rule replaceKindInMap(A:K, B:K, X:KItem, Y:KItem, S:Map)
        => (X |-> replaceKindInTerm(A, B, Y)) replaceKindInMap(A, B, .K, .K, S)

   syntax Map ::= replaceAllKindInMap(Map, Map) [function]
   rule replaceAllKindInMap(.Map, M:Map) => M
   rule replaceAllKindInMap((A:K |-> B:K) RM:Map, M:Map)
          => replaceAllKindInMap(RM, replaceKindInMap(A, B, .K, .K, M))

   syntax KItem ::= replaceAllKindsInTerm(K, Map) [function]
   rule replaceAllKindsInTerm(B:K, .Map) => B
   rule replaceAllKindsInTerm(B:K, (X:K |-> Y:K) M:Map)
           => replaceAllKindsInTerm(replaceKindInTerm(B, X, Y), M)

   //replace all kind-varaible with star. happens when 
   //people define data/newtype with an type-var, but never uses the ty-var actually
   syntax KItem ::= replaceKindVarsWithStar(K) [function]
   rule replaceKindVarsWithStar(star) => star
   rule replaceKindVarsWithStar(kindVar(A:Int)) => star
   rule replaceKindVarsWithStar(kindArrow(A:K, B:K))
          => kindArrow(replaceKindVarsWithStar(A), replaceKindVarsWithStar(B))

   syntax Map ::= replaceAllKindVarsWithStar(Map) [function]
   rule replaceAllKindVarsWithStar(.Map) => .Map
   rule replaceAllKindVarsWithStar((A:K |-> B:K) M:Map)
            => (A |-> replaceKindVarsWithStar(B)) replaceAllKindVarsWithStar(M)

   syntax KItem ::= unifInKind(K, Set, Set, Map) [function]
        //curr-tuple, post-tuple, pre-tuple, assignments
   rule unifInKind(.K, .Set, .Set, M:Map) => resultMap(M)
   rule unifInKind(.K, SetItem(A:K) S1:Set, .Set, M:Map)
             => error(kindUnifierFail)
   rule unifInKind(.K, S1:Set, SetItem(A:K) S:Set, M:Map)
             => unifInKind(A, S1, S, M)
   rule unifInKind(kindTuple(A:K, A:K), S1:Set, S:Set, M:Map)
         => unifInKind(.K, S1, S, M)
   rule unifInKind(kindTuple(kindArrow(A:K, B:K),
                kindArrow(A1:K, B1:K)), S1:Set, S:Set, M:Map)
         => unifInKind(.K, .Set, SetItem(kindTuple(A, A1)) SetItem(kindTuple(B, B1)) S1 S, M)
   rule unifInKind(kindTuple(A:K, B:K), S1:Set, S:Set, M:Map)
         => error(kindUnifierFail)
        requires (A ==K star andBool isKindArrow(B))
                orBool (B ==K star andBool isKindArrow(A))
   rule unifInKind(kindTuple(A:K, B:K), S1:Set, S:Set, M:Map)
         => unifInKind(kindTuple(B, A), S1:Set, S:Set, M:Map)
        requires isKindVar(B) andBool notBool isKindVar(A)
   rule unifInKind(kindTuple(kindVar(A:Int), B:K), S1:Set, S:Set, M:Map)
         => unifInKind(.K, .Set, replaceKindInSet(kindVar(A:Int), B, .K, S1 S),
             replaceKindInMap(kindVar(A:Int), B, .K, .K, M))
        requires notBool occurInKind(kindVar(A:Int), B)
   rule unifInKind(kindTuple(kindVar(A:Int), B:K), S1:Set, S:Set, M:Map)
         => error(kindUnifierFail)
        requires occurInKind(kindVar(A:Int), B)

endmodule
