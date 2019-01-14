//helper functions for the haskell semantics.
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"

module HASKELL-HELPER
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX

   //helper function to transfer a list to a set
   syntax Set ::= listToSet(List) [function]
   rule listToSet(.List) => .Set
   rule listToSet(ListItem(A:K) L:List) => SetItem(A) listToSet(L)

   syntax List ::= setToList(Set) [function]
   rule setToList(.Set) => .List
   rule setToList(SetItem(A:K) L:Set) => ListItem(A) setToList(L)

   //boolean functions to determine if a term has no certain klabel
   syntax Bool ::= isBATypeCon(K) [function]
   rule isBATypeCon('baTypeCon(A:AType,, B:BType)) => true
   rule isBATypeCon(A:K) => false [owise]

   //a function to pill varid/varop
   syntax KItem ::= pillVar(K) [function]
   rule pillVar('varSymBracket(A:VarSym)) => A
   rule pillVar('varIdQuote(A:VarId)) => A
   rule pillVar(V:K) => V [owise]

   syntax KItem ::= transVar(K, K) [function]
   rule transVar(Mod:K, 'colon(.KList)) => fullName(Mod, 'colon(.KList))
   rule transVar(Mod:K, C:ConSym) => fullName(Mod, C)
   rule transVar(Mod:K, 'qConSymCon(A:ModId,, C:ConSym)) => fullName(A, C)
   rule transVar(Mod:K, 'qTyConQuote(A:TyCon)) => fullName(Mod, A)
   rule transVar(Mod:K, 'qTyConQuote('conTyCon(A:ModId,, C:TyCon)))
                 => fullName(A, C)
   rule transVar(Mod:K, 'qVarSymCon(A:ModId,, C:ConSym)) => fullName(A, C)
   rule transVar(Mod:K, C:VarSym) => fullName(Mod, C)
   rule transVar(Mod:K, 'qVarIdQuote(A:VarId)) => fullName(Mod, A)
   rule transVar(Mod:K, 'qVarIdQuote('qVarIdCon(C:ModId,, A:VarId)))
                     => fullName(C, A)

   syntax KItem ::= transTypeVar(K, K) [function]
   rule transTypeVar(S:K, V:VarId) => tyVar(S, V)
   rule transTypeVar(S:K, 'qVarIdCon(A:ModId,, B:VarId)) => tyVar(A, B)
   rule transTypeVar(S:K, 'qVarBracket(C:ConSym)) => tyVar(S, C)
   rule transTypeVar(S:K, 'qVarBracket(
           'qConSymCon(A:ModId,, B:ConSym))) => tyVar(S, B)


   syntax Map ::= updateMapItem(Map, K, K, K) [function]
   rule updateMapItem(M:Map, .K, A:K, V:K)
           => M (A |-> names(SetItem(V)))
        requires notBool A in keys(M)
   rule updateMapItem(M:Map (A:K |-> S:K), .K, A:K, V:K)
            => updateMapItem(M, S, A, V)
   rule updateMapItem(M:Map, names(S:Set), A:K, V:K)
             => M (A |-> names(SetItem(V) S))

   //find unique father of a given type name
   syntax KItem ::= findFather(Map, K, Map, K, K) [function]
                 //imports, mod, ty-map, t, hold1
                  | findFatherAux(Map, K, K, Map, K) [function]
                //imports, mod, mods, ty-map, t
   rule findFather(IM:Map, Mod:K, TM:Map, T:K, .K) => none 
        requires notBool Mod in keys(TM)
   rule findFather(IM:Map, Mod:K, (Mod |-> X:K) TM:Map, T:K, .K)
         => findFather(IM:Map, Mod:K, TM, T, X)
   rule findFather(IM:Map, Mod:K, TM:Map, T:K, typeMap(X:Map)) => Mod
        requires T in keys(X)
   rule findFather(IM:Map (Mod |-> Fa:K), Mod:K, TM:Map, T:K, typeMap(X:Map))
               => findFatherAux(IM, .K, Fa, TM, T)
        requires notBool T in keys(X)
   rule findFather(IM:Map, Mod:K, TM:Map, T:K, X:K) => none [owise]

   rule findFatherAux(IM:Map, .K, names(.Set), TM:Map, T:K) => none
   rule findFatherAux(IM:Map, .K, names(SetItem(A:K) S:Set), TM:Map, T:K)
            => findFatherAux(IM, A, names(S), TM, T)
   rule findFatherAux(IM:Map, A:KItem, names(S:Set), TM:Map, T:K)
             => findFather(IM, A, TM, T, .K)
        requires findFatherAux(IM, .K, names(S:Set), TM:Map, T) ==K none
   rule findFatherAux(IM:Map, A:KItem, names(S:Set), TM:Map, T:K)
             => findFatherAux(IM, .K, names(S:Set), TM:Map, T)
        requires findFatherAux(IM, .K, names(S:Set), TM:Map, T) =/=K none
                 andBool findFather(IM, A, TM, T, .K) ==K none

   //find the arity of a given op, if not then return none
   syntax Int ::= countOnCommas(GConCommas) [function]
   rule countOnCommas('dotInTuple(.KList)) => 1
   rule countOnCommas('dotCon(C:GConCommas)) => 1 +Int countOnCommas(C)

   syntax Int ::= countOnTypeTuple(K) [function]
   rule countOnTypeTuple('twoTypeTuple(A:K,, B:K)) => 2
   rule countOnTypeTuple('typeTupleCon(A:K,, B:TypeTuple))
            => 1 +Int countOnTypeTuple(B)
   rule countOnTypeTuple('twoPatTuple(A:K,, B:K)) => 2
   rule countOnTypeTuple('patTupleCon(A:K,, B:K))
            => 1 +Int countOnTypeTuple(B)
   rule countOnTypeTuple('twoExpTuple(A:K,, B:K)) => 2
   rule countOnTypeTuple('expTupleCon(A:K,, B:K))
            => 1 +Int countOnTypeTuple(B)

   syntax Bool ::= isFather(K, K, K, Map) [function]
                 | isFatherAux(K, Set, Map) [function]
   rule isFather(A:K, A:K, .K, M:Map) => true
   rule isFather(A:K, B:K, .K, .Map) => false
        requires A =/=K B
   rule isFather(A:K, B:K, .K, M:Map (B |-> X:K))
           => isFather(A, B, X, M)
        requires A =/=K B
   rule isFather(A:K, B:K, names(S:Set), M:Map)
         => isFatherAux(A, S, M)
   rule isFatherAux(A:K, .Set, M:Map) => false
   rule isFatherAux(A:K, SetItem(B:K) S:Set, M:Map)
           => isFather(A, B, .K, M) orBool isFatherAux(A, S, M)

   syntax KItem ::= getArity(Map, K, K, K) [function]
   rule getArity(M:Map (A |-> C), A:K, B:K, .K)
             => getArity(M, A, B, C)
   rule getArity(M:Map, A:K, B:K, typeMap((B |-> N:K) X:Map))
           => N
   rule getArity(M:Map, A:K, B:K, S:K) => none [owise]

   syntax KItem ::= findArity(K, K, Map, Map) [function]
               //mod, ty, ty-map, imports
   rule findArity(Mod:K, 'tupleCover(T:TypeTuple), TM:Map, IM:Map) => 0
   rule findArity(Mod:K, [T:Type], TM:Map, IM:Map) => 0
   rule findArity(Mod:K, T:TyVar, TM:Map, IM:Map) => none
   rule findArity(Mod:K, 'unitType(.KList), TM:Map, IM:Map) => 0
   rule findArity(Mod:K, [], TM:Map, IM:Map) => 0
   rule findArity(Mod:K, 'tupleFun(C:GConCommas), TM:Map, IM:Map) => countOnCommas(C) +Int 1
   rule findArity(Mod:K, 'conTyCon(M1:K,, T:K), TM:Map, IM:Map)
           => getArity(TM, M1, T, .K)
        requires isFather(M1, Mod, .K, IM)
   rule findArity(Mod:K, T:TyCon, TM:Map, IM:Map)
           => getArity(TM, findFather(IM, Mod, TM, T, .K), T, .K)
        requires findFather(IM, Mod, TM, T, .K) =/=K none
   rule findArity(Mod:K, T:TyCon, TM:Map, IM:Map) => none [owise]

   //a helper function to transform concrete type to abstract type
   syntax Int ::= typeTupleCount(TypeTuple) [function]
   rule typeTupleCount('twoTypeTuple(A:K,, B:K)) => 2
   rule typeTupleCount('typeTupleCon(A:K,, B:K)) => 1 +Int typeTupleCount(B)

   syntax KItem ::= dealWithTuple(K) [function]
   rule dealWithTuple('tupleFun(A:GConCommas)) => tupleType(countOnCommas(A))
   rule dealWithTuple(A:K) => A [owise]

   syntax KItem ::= toAbsTypeInClass(K, Set, K, Map, Map) [function]
                  | toAbsTypeInClassApp(K, Set, K, List, Map,Map) [function]
           //module, type expression, type map, import map
                  | toAbsTypeInClassAppAux(K, Set, K, List, List, Map,Map) [function]
   syntax List ::= toAbsTypeInClassTuple(K, Set, TypeTuple, Map, Map) [function]

   rule toAbsTypeInClass(Mod:K, S:Set, 'typeArrow(B:BType,, T:Type), TM:Map, IM:Map)
            => typeConst(fullName(Prelude, (->)), ListItem(toAbsTypeInClass(Mod,S, B, TM, IM))
                             ListItem(toAbsTypeInClass(Mod,S, T, TM, IM)))
        requires toAbsTypeInClass(Mod,S, B, TM, IM) =/=K none
              andBool toAbsTypeInClass(Mod,S, T, TM, IM) =/=K none
   rule toAbsTypeInClass(Mod:K, S:Set, 'baTypeCon(A:AType,, B:BType), TM:Map, IM:Map)
                => toAbsTypeInClassApp(Mod, S, A, ListItem(B), TM, IM)
   rule toAbsTypeInClass(Mod:K, S:Set, A:TyVar, TM:Map, IM:Map) => A
        requires notBool A in S
   rule toAbsTypeInClass(Mod:K, S:Set, A:TyVar, TM:Map, IM:Map) => modVar(A)
        requires A in S
   rule toAbsTypeInClass(Mod:K, S:Set, 'unitType(.KList), TM:Map, IM:Map)
           => typeConst(fullName(Prelude, 'unitType(.KList)), .List)
   rule toAbsTypeInClass(Mod:K, S:Set, 'tyList(B:K), TM:Map, IM:Map)
           => typeConst(fullName(Prelude, []), ListItem(toAbsTypeInClass(Mod,S, B, TM, IM)))
        requires toAbsTypeInClass(Mod,S, B, TM, IM) =/=K none
   rule toAbsTypeInClass(Mod:K, S:Set, 'tupleCover(B:TypeTuple), TM:Map, IM:Map)
           => typeConst(fullName(Prelude, tupleType(typeTupleCount(B))),
                         ListItem(toAbsTypeInClassTuple(Mod,S, B, TM, IM)))
        requires size(toAbsTypeInClassTuple(Mod,S, B, TM, IM)) =/=K 0
   rule toAbsTypeInClass(Mod:K, S:Set, 'conTyCon(A:K,,T:K), TM:Map, IM:Map)
            => typeConst(T, .List)
        requires isFather(A, Mod, .K, IM) andBool getArity(TM, A, T, .K) ==K 0

   rule toAbsTypeInClass(Mod:K, S:Set, A:K, TM:Map, IM:Map) => none [owise]


   rule toAbsTypeInClassTuple(Mod:K, S:Set, 'twoTypeTuple(A:K,,B:K), TM:Map, IM:Map)
          => ListItem(toAbsTypeInClass(Mod,S, A, TM, IM))
                  ListItem(toAbsTypeInClass(Mod,S, B, TM, IM))
        requires toAbsTypeInClass(Mod,S, A, TM, IM) =/=K none
              andBool toAbsTypeInClass(Mod,S, B, TM, IM) =/=K none
   rule toAbsTypeInClassTuple(Mod:K, S:Set, 'typeTupleCon(A:K,,B:TypeTuple), TM:Map, IM:Map)
          => ListItem(toAbsTypeInClass(Mod,S, A, TM, IM))
                 toAbsTypeInClassTuple(Mod, S, B, TM, IM)
        requires toAbsTypeInClass(Mod,S, A, TM, IM) =/=K none
              andBool size(toAbsTypeInClassTuple(Mod, S, B, TM, IM)) =/=K 0
   rule toAbsTypeInClassTuple(Mod:K, S:Set, A:TypeTuple, TM:Map, IM:Map) => .List [owise]


   rule toAbsTypeInClassApp(Mod:K, S:Set, 'baTypeCon(A:AType,, B:BType),
            L:List, TM:Map, IM:Map) 
            => toAbsTypeInClassApp(Mod, S, A, ListItem(B) L, TM, IM)
   rule toAbsTypeInClassApp(Mod:K, S:Set, A:K, L:List, TM:Map, IM:Map)
           => toAbsTypeInClassAppAux(Mod, S, A, L, .List, TM, IM)
        requires notBool isBATypeCon(A)

   rule toAbsTypeInClassAppAux(Mod:K, S:Set, A:K, .List, L:List, TM:Map, IM:Map)
           => typeConst(modVar(A), L)
        requires A in S
   rule toAbsTypeInClassAppAux(Mod:K, S:Set, A:K, .List, L:List, TM:Map, IM:Map)
           => typeConst(fullName(Prelude, dealWithTuple(A)), L)
        requires notBool A in S andBool findArity(Mod, A, TM, IM) ==K size(L)
   rule toAbsTypeInClassAppAux(Mod:K, S:Set, A:K, .List, L:List, TM:Map, IM:Map) => none
        requires notBool A in S andBool findArity(Mod, A, TM, IM) =/=K size(L)

   rule toAbsTypeInClassAppAux(Mod:K, S:Set, A:K,
             ListItem('baTypeCon(C:AType,, B:BType)) BL:List, L:List, TM:Map, IM:Map)
           => toAbsTypeInClassAppAux(Mod, S, A, ListItem(B) BL,
                      L ListItem(toAbsTypeInClass(Mod, S, C, TM, IM)), TM, IM)
        requires toAbsTypeInClass(Mod, S, C, TM, IM) =/=K none
   rule toAbsTypeInClassAppAux(Mod:K, S:Set, A:K,
             ListItem(C:AType) BL:List, L:List, TM:Map, IM:Map)
           => toAbsTypeInClassAppAux(Mod, S, A, BL,
                      L ListItem(toAbsTypeInClass(Mod, S, C, TM, IM)), TM, IM)
        requires toAbsTypeInClass(Mod, S, C, TM, IM) =/=K none
   rule toAbsTypeInClassAppAux(Mod:K, S:Set, A:K, BL:List, L:List, TM:Map, IM:Map)
               => none   [owise]

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
                | getFreeTypeVarsInList(List) [function]
   rule getFreeTypeVars(T:TyVar) => SetItem(T)
   rule getFreeTypeVars(typeConst(A:K, B:List))
          => getFreeTypeVars(A) getFreeTypeVarsInList(B)
   rule getFreeTypeVars(curryTypes(A:List, B:K))
         => getFreeTypeVarsInList(A) getFreeTypeVars(A)
   rule getFreeTypeVars(forall(A:Set, B:K))
            => getFreeTypeVars(B) -Set A
   rule getFreeTypeVarsInList(.List) => .Set
   rule getFreeTypeVarsInList(ListItem(A:K) L:List)
            => getFreeTypeVars(A) getFreeTypeVarsInList(L)

   syntax Map ::= addEdges(Set, Set) [function]
   rule addEdges(SetItem(A:K), SetItem(B:K) S:Set)
          => (A |-> names(SetItem(B) S))

   syntax KItem ::= getSingleton(Set) [function]
   rule getSingleton(SetItem(A:K)) => A

   syntax KItem ::= makeAlphaM(K, K, Map, Map) [function] //curr-mod, (Alpha, AlphaMap)
                  | makeAlphaMAux(K, TopDecl, Map, K, Map) [function]
                   //curr-mod, top-decl, checking map, checking-point, store-map
   rule makeAlphaM(Mod:K, 'bodyimpandtop(Is:ImpDecls,, Ts:TopDecls), M:Map, TM:Map)
          => makeAlphaM(Mod:K, Ts, M, TM)
   rule makeAlphaM(Mod:K, 'bodyimpdecls(Is:ImpDecls), M:Map, TM:Map) => .K
   rule makeAlphaM(Mod:K, 'bodytopdecls(Ts:TopDecls), M:Map, TM:Map)
                  => makeAlphaM(Mod:K, Ts, M, TM)
   rule makeAlphaM(Mod:K, .TopDecls, M:Map, TM:Map) => putAlphaMap(TM)
   rule makeAlphaM(Mod:K, 'topdeclslist(A:TopDecl,, As:TopDecls), M:Map, TM:Map)
              => makeAlphaMAux(Mod:K, A, M, As, TM)

   rule makeAlphaMAux(Mod:K, type A:SimpleType = B:Type, M:Map, As:K, TM:Map)
            => makeAlphaM(Mod:K, As, addEdges(getConstrNames(A), getConstrNames(B)) M,
                            (getSingleton(getConstrNames(A))
                                 |-> alphaTuple(getTyVarList(A), toAbsType(Mod, B))) TM)
        requires getTypeNames(B) <=Set getTypeNames(A)
                  andBool getSingleton(getConstrNames(A)) in keys(M)
                  andBool notBool hasCycleAux(
                               getSingleton(getConstrNames(A)), getConstrNames(B), M)
   rule makeAlphaMAux(Mod:K, type A:SimpleType = B:Type,
                               M:Map, As:K, TM:Map) => error(typeVarNoInclusive)
        requires notBool (getTypeNames(B) <=Set getTypeNames(A))
   rule makeAlphaMAux(Mod:K, type A:SimpleType = B:Type,
                               M:Map, As:K, TM:Map) => error(repeatedNames)
        requires notBool getSingleton(getConstrNames(A)) in keys(M)
   rule makeAlphaMAux(Mod:K, type A:SimpleType = B:Type,
                            M:Map, As:K, TM:Map) => error(cycleAlpha)
        requires hasCycleAux(getSingleton(getConstrNames(A)), getConstrNames(B), M)
   rule makeAlphaMAux(Mod:K, A:TopDecl, M:Map, As:K, TM:Map)
                           => makeAlphaM(Mod:K, As, M, TM) [owise]


   //collect a map for knowing the type name and its partial kind (not proved)
   syntax KItem ::= parKindEntry(Int, Set, K, SimpleType) [function]
           //counter, kind-var-set, curr-mod, simple-type
                  | parKindEntryAux(K, K, K) [function]
                    //curr-mod, simple-type, resultTyVarKind

   rule parKindEntry(N:Int, S:Set, Curr:K, 'simpleTypeCon(T:TyCon,, Vs:TyVars))
            => parKindEntryAux(Curr, T, resolveKindEntry(N, S, Vs, .List))
   rule parKindEntryAux(Curr:K, T:K, resultTyVarKindList(N:Int, S:Set, L:List))
            => resultTyVarKindMap(N, S, (toAbsTypeCon(Curr,T) |-> listToKind(L)))

   syntax KItem ::= listToKind(List) [function]
   rule listToKind(.List) => star
   rule listToKind(ListItem(A:K) L:List) => kindArrow(A, listToKind(L))

   syntax KItem ::= resolveKindEntry(Int, Set, TyVars, List) [function]
           //counter, kind-var-set, tyVars, result
   rule resolveKindEntry(N:Int, S:Set, .TyVars, T:List) => resultTyVarKindList(N, S, T)
   rule resolveKindEntry(N:Int, S:Set, 'typeVars(A:TyVar,,B:TyVars), T:List)
          => resolveKindEntry(N +Int 1, S SetItem(kindVar(N)), B, T ListItem(kindVar(N)))

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
   rule collectTypes(N:Int, S:Set, Mod:K, 'topdeclslist(data Oc:OptContext A:SimpleType
                        B:OptConstrs D:OptDeriving,, As:TopDecls), M:Map)
              => collectTypesAux(Mod:K, As, parKindEntry(N, S, Mod, A), M)
   rule collectTypes(N:Int, S:Set, Mod:K, 'topdeclslist(newtype Oc:OptContext A:SimpleType
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

   syntax List ::= getTyVarList(K) [function]
   rule getTyVarList('simpleTypeCon(A:TyCon,, B:TyVars))
           => toTypeList(B)

   //convert a type con to abs form (fullname)
   syntax KItem ::= toAbsTypeCon(K, K) [function] //curr-mod-name, type-con
   rule toAbsTypeCon(Mod:K, T:TyCon) => fullName(Mod, T)
   rule toAbsTypeCon(Mod:K, 'conTyCon(Mod':K,, T:K)) => fullName(Mod', T)

   syntax KItem ::= transExpCon(K, K) [function] //curr-mod-name, ExpCon
   rule transExpCon(Mod:K, 'unitType(.KList)) => fullName(Prelude, 'unitType(.KList))
   rule transExpCon(Mod:K, []) => fullName(Prelude, [])
   rule transExpCon(Mod:K, 'tupleFun(Gs:GConCommas))
          => fullName(Prelude, tupleType(countOnCommas(Gs) +Int 1))
   rule transExpCon(Mod:K, T:TyCon) => fullName(Mod, T)
   rule transExpCon(Mod:K, 'conTyCon(A:ModId,, T:TyCon))
              => fullName(A, T)
   rule transExpCon(Mod:K, 'gConBracket('colon(.KList)))
              => fullName(Prelude, 'colon(.KList))
   rule transExpCon(Mod:K, 'gConBracket(C:ConSym))
              => fullName(Mod, C)
   rule transExpCon(Mod:K, 'gConBracket('qConSymCon(A:ModId,, C:ConSym)))
              => fullName(A, C)

   syntax KItem ::= toAbsTypeWithAll(K, Set) [function]
   rule toAbsTypeWithAll(T:K, .Set) => T
   rule toAbsTypeWithAll(T:K, S:Set) => forall(S, T) [owise]

   syntax KItem ::= toAbsType(K, K) [function] //current module name, type
                  | toAbsTypeAux(K, K, List, K) [function]
                          //curr-mod, type-con-name,type-args, unsolved
                  | toAbsTypeAuxAux(K, List) [function] //type-con, args
   syntax List ::= toAbsTypeTuple(K, TypeTuple) [function]//curr-mod, type-tuple
                 | toAbsTypeList(K, ATypeList) [function]//curr-mod, typelist

   rule toAbsTypeList(S:K, .ATypeList) => .List
   rule toAbsTypeList(S:K, 'atypeList(A:AType,, B:ATypeList))
           => ListItem(toAbsType(S, A)) toAbsTypeList(S, B)

   rule toAbsType(S:K, 'simpleTypeCon(T:TyCon,, A:TyVars))
            => typeConst(fullName(S,T), toTypeList(A))
   rule toAbsType(S:K, A:TyVar) => A
   rule toAbsType(S:K, A:TyCon) => typeConst(fullName(S,A), .List)
   rule toAbsType(S:K,'conTyCon(N:ModId,, A:TyCon))
             => typeConst(fullName(N,A), .List)
   rule toAbsType(S:K,(->))
             => typeConst(fullName(Prelude, (->)), .List)
   rule toAbsType(S:K, 'typeArrow(A:K,, B:K))
             => typeConst(fullName(Prelude, (->)),
                         ListItem(toAbsType(S, A)) ListItem(toAbsType(S, B)))
   rule toAbsType(S:K,[])
             => typeConst(fullName(Prelude, []), .List)
   rule toAbsType(S:K, 'tyList(A:K))
             => typeConst(fullName(Prelude, []),
                         ListItem(toAbsType(S, A)))
   rule toAbsType(S:K, 'unitType(.KList))
             => typeConst(fullName(Prelude, 'unitType(.KList)), .List)
   rule toAbsType(S:K, 'tupleFun(Gs:GConCommas))
             => typeConst(fullName(Prelude,
                      tupleType(countOnCommas(Gs) +Int 1)), .List)
   rule toAbsType(S:K, 'tupleCover(Ts:TypeTuple))
             => typeConst(fullName(Prelude,
                      tupleType(countOnTypeTuple(Ts))), toAbsTypeTuple(S, Ts))
   rule toAbsType(S:K, A:K) => A [owise]

   rule toAbsType(S:K, 'group(T:K)) => toAbsType(S, T)
   rule toAbsType(S:K, 'baTypeCon(T:K,, T1:K))
          => toAbsTypeAux(S, toAbsType(S, T), .List, T1)

   rule toAbsTypeAux(S:K, A:K, L:List, 'baTypeCon(T:K,, T1:K))
           => toAbsTypeAux(S:K, A, L ListItem(toAbsType(S, T)), T1)
   rule toAbsTypeAux(S:K, A:K, L:List, T:K)
           => toAbsTypeAuxAux(A, L ListItem(toAbsType(S, T))) [owise]

   rule toAbsTypeAuxAux(typeConst(X:K, L:List), L1:List)
             => typeConst(X:K, L L1)
   rule toAbsTypeAuxAux(A:K, L:List) => typeConst(A, L) [owise]

   rule toAbsTypeTuple(S:K, 'twoTypeTuple(A:K,, B:K))
                     => ListItem(toAbsType(S, A)) ListItem(toAbsType(S, B))
   rule toAbsTypeTuple(S:K, 'typeTupleCon(A:K,, B:TypeTuple))
                     => ListItem(toAbsType(S, A)) toAbsTypeTuple(S, B)


   //collecting preBetaMap info
   /*
    syntax OptConstrs  ::= "=" Constrs [klabel('nonemptyConstrs)] | "" [onlyLabel, klabel('emptyConstrs)]
    syntax Constrs     ::= Constr [klabel('singleConstr)] | Constr "|" Constrs [klabel('multConstr)]
    syntax Constr      ::= Con OptBangATypes [klabel('constrCon)] // (arity con  =  k, k ≥ 0) UNFINISHED
                         | SubConstr ConOp SubConstr
                         | Con "{" FieldDeclList "}"
   */

   syntax List ::= toAbsBangType(K, K) [function]
                 //curr-mod-name, types
   rule toAbsBangType(S:K, .OptBangATypes) => .List
   rule toAbsBangType(S:K, 'optBangATypes('optBangAType(Op:OptBang,, A:AType)
        ,, As:OptBangATypes)) => ListItem(toAbsType(S, A)) toAbsBangType(S:K, As)

   syntax List ::= expandRecordType(K, Vars, K) [function]
   rule expandRecordType(S:K, A:Var, T:K)
             => ListItem(typeConst(fullName(Prelude, recordTypeAssign),
                    ListItem(tyVar(S, pillVar(A))) ListItem(T)))
   rule expandRecordType(S:K, 'varCon(A:Var,, As:Vars), T:K)
           => ListItem(typeConst(fullName(Prelude, recordTypeAssign),
                      ListItem(tyVar(S, pillVar(A))) ListItem(T))) expandRecordType(S, As, T)

   syntax List ::= toAbsBangTypeInRecord(K, K) [function]
                 //curr-mod-name, types
   rule toAbsBangTypeInRecord(S:K, .FieldDeclList) => .List
   rule toAbsBangTypeInRecord(S:K, 'fieldCon(Vs:Vars :: ! A:AType
           ,, Fs:FieldDeclList)) => expandRecordType(S, Vs,
                       toAbsType(S, A)) toAbsBangTypeInRecord(S, Fs)
   rule toAbsBangTypeInRecord(S:K, 'fieldCon('varAssign(Vs:Vars,, A:AType)
           ,, Fs:FieldDeclList)) => expandRecordType(S, Vs,
                       toAbsType(S, A)) toAbsBangTypeInRecord(S, Fs)

   syntax Map ::= makeSinglePreBeta(K, K, K) [function]
          //curr-mod-name, target-type, constrs/newconstr
   //deal with constrs
   rule makeSinglePreBeta(S:K, T:K, 'emptyConstrs(.KList)) => .Map
   rule makeSinglePreBeta(S:K, T:K, 'nonemptyConstrs(Cs:Constrs))
                => makeSinglePreBeta(S, T, Cs)
   rule makeSinglePreBeta(S:K, T:K, 'constrCon(N:Con,, Ts:OptBangATypes))
           => (N |-> curryTypes(toAbsBangType(S, Ts), T))
   rule makeSinglePreBeta(S:K, T:K, N:Con { F:FieldDeclList })
           => (N |-> typeConst(fullName(Prelude, (->)), ListItem(typeConst(
              fullName(Prelude, recordType), toAbsBangTypeInRecord(S, F))) ListItem(T)))
   rule makeSinglePreBeta(S:K, T:K, 'multConstr(
           'constrCon(N:Con,, Ts:OptBangATypes),, Cs:Constrs))
           => (N |-> curryTypes(toAbsBangType(S, Ts), T)) makeSinglePreBeta(S, T, Cs)
   rule makeSinglePreBeta(S:K, T:K, 'multConstr(N:Con { F:FieldDeclList },, Cs:Constrs))
           => (N |-> typeConst(fullName(Prelude, (->)), ListItem(typeConst(
              fullName(Prelude, recordType), toAbsBangTypeInRecord(S, F))) ListItem(T)))
            makeSinglePreBeta(S, T, Cs)
   //deal with newConstr
   rule makeSinglePreBeta(S:K, T:K, 'newConstrCon(N:Con,, A:AType))
           => (N |-> curryTypes(ListItem(toAbsType(S, A)), T))
   rule makeSinglePreBeta(S:K, T:K, 'newConField(N:Con,, V:Var,, T':Type))
           => (N |-> typeConst(fullName(Prelude, (->)), ListItem(typeConst(
              fullName(Prelude, recordType), ListItem(typeConst(fullName(Prelude, recordTypeAssign),
                 ListItem(tyVar(S, pillVar(V))) ListItem(toAbsType(S, T')))))) ListItem(T)))

   //functions to convert class name to abs form and convert context to a set of classes

   syntax KItem ::= toAbsClass(K, Class) [function] //curr-mod-name, class
   rule toAbsClass(Mod:K, 'classCon(T:QTyCon,, V:TyVar))
                  => className(toAbsTypeCon(Mod, T), ListItem(V))
   rule toAbsClass(Mod:K, 'multiClass(T:QTyCon,, A:TyVar,, As:ATypeList))
                  => className(toAbsTypeCon(Mod, T), ListItem(A) toAbsTypeList(Mod, As))

   syntax Set ::= contextToSet(K, K) [function] //curr-mod-name, class
                | contextToSetAux(K, Classes) [function]//curr-mod, classes
   rule contextToSet(S:K, 'emptyContext(.KList)) => .Set
   rule contextToSet(S:K, C:Class =>) => SetItem(toAbsClass(S, C))
   rule contextToSet(S:K, 'contextClass(Cs:Classes) =>)
             => contextToSetAux(S, Cs)
   rule contextToSetAux(S:K, .Classes) => .Set
   rule contextToSetAux(S:K, 'classesCon(A:Class,, B:Classes))
           => contextToSet(S, A) contextToSetAux(S, B)

   syntax Set ::= derivingToSet(K, K) [function]//curr-mod, opt-deriving
                | derivingToSetAux(K, DClassList) [function]//curr-mod, DClassList
   rule derivingToSet(S:K, 'emptyDeriving(.KList)) => .Set
   rule derivingToSet(S:K, deriving D:DClass) => SetItem(toAbsTypeCon(S, D))
   rule derivingToSet(S:K, deriving (Ds:DClassList)) => derivingToSetAux(S, Ds)
   rule derivingToSetAux(S:K, .DClassList) => .Set
   rule derivingToSetAux(S:K, 'dclassCon(A:DClass,, B:DClassList))
             => derivingToSet(S,A) derivingToSetAux(S, B)

   syntax KItem ::= makePreBetaFun(K, K, Map) [function]
                | makePreBetaFunAux(K, K, K, Map) [function]

   rule makePreBetaFun(S:K, 'bodyimpandtop(Is:ImpDecls,, Ts:TopDecls), M:Map)
          => makePreBetaFun(S, Ts, M)
   rule makePreBetaFun(S:K, 'bodyimpdecls(Is:ImpDecls), M:Map) => .K
   rule makePreBetaFun(S:K, 'bodytopdecls(Ts:TopDecls), M:Map) => makePreBetaFun(S, Ts, M)
   rule makePreBetaFun(S:K, .TopDecls, M:Map) => putPreBetaMap(M)
   rule makePreBetaFun(S:K, 'topdeclslist(A:TopDecl,, As:TopDecls), M:Map)
              => makePreBetaFunAux(S, A, As, M)

   rule makePreBetaFunAux(S:K, 'data(Oc:K,,
              'simpleTypeCon(N:K,, Ts:K),, Cons:K,, Od:K), As:K, M:Map)
          =>  makePreBetaFun(S, As, (toAbsTypeCon(S, N)
              |-> preBetaEntry(contextToSet(S, Oc), toTypeList(Ts),
                  makeSinglePreBeta(S, toAbsType(S, N), Cons), derivingToSet(S, Od))) M)
   rule makePreBetaFunAux(S:K, 'newtype(Oc:K,,
              'simpleTypeCon(N:K,, Ts:K),, Cons:NewConstr,, Od:K), As:K, M:Map)
          =>  makePreBetaFun(S, As, (toAbsTypeCon(S, N)
              |-> preBetaEntry(contextToSet(S, Oc), toTypeList(Ts),
                  makeSinglePreBeta(S, toAbsType(S, N), Cons), derivingToSet(S, Od))) M)
   rule makePreBetaFunAux(S:K, A:TopDecl, As:K, TM:Map)
                  => makePreBetaFun(S, As, TM) [owise]

   //a function to check if all used type cons are in the set, return .K or errors
   //a typeConst contains a con that is a fullName (a real Con) or a typeVar
   // that is scoped by the title of the data definition
   syntax Bool ::= isTypeValid(K, Set) [function]
                 | isTypeValidCore(K, Set) [function]
                 | isTypeValidInList(List, Set) [function]
   rule isTypeValid(typeConst(A:K, B:List), S:Set)
         => isTypeValidCore(A, S) andBool isTypeValidInList(B, S)
   rule isTypeValid(A:K, S:Set) => true [owise]

   rule isTypeValidCore(fullName(A:K, tupleType(X:Int)), S:Set)
             => (fullName(Prelude, tupleTypeAll)) in S
   rule isTypeValidCore(A:K, S:Set) => A in S [owise]

   rule isTypeValidInList(.List, S:Set) => true
   rule isTypeValidInList(ListItem(A:K) L:List, S:Set)
             => isTypeValid(A, S) andBool isTypeValidInList(L, S)

   syntax KItem ::= isAllValidTypes(Map, K, K, Set) [function]
                  | isValidTypes(Map, Map, K, K, Set) [function]
   rule isAllValidTypes(.Map, .K, .K, S:Set) => .K
   rule isAllValidTypes((A:K |-> B:K) M:Map, .K, .K, S:Set)
          => isAllValidTypes(M, A, B, S)
   rule isAllValidTypes(M, A:K, preBetaEntry(Os:Set,
             L:List, Body:Map, Oc:Set), S:Set)
          => isValidTypes(M, Body, .K, .K, listToSet(L) S)
 
   rule isAllValidTypes(M, A:K, alphaTuple(L:List, Body:K), S:Set)
          => isAllValidTypes(M, .K, .K, listToSet(L) S)
        requires isTypeValid(Body, listToSet(L) S)
   rule isAllValidTypes(M, A:K, alphaTuple(L:List, Body:K), S:Set)
          => error(typeNotInScope)
        requires notBool isTypeValid(Body, listToSet(L) S)

   rule isValidTypes(M:Map, .Map, .K, .K, S:Set) => isAllValidTypes(M, .K, .K, S)
   rule isValidTypes(M:Map, (A:K |-> B:K) BM:Map, .K, .K, S:Set)
             => isValidTypes(M, BM, A, B, S)
   rule isValidTypes(M:Map, BM:Map, A:KItem, T:Type, S:Set)
                   => isValidTypes(M, BM, .K, .K, S)
        requires isTypeValid(T, S)
   rule isValidTypes(M:Map, BM:Map, A:KItem, T:Type, S:Set)
                   => error(typeNotInScope)
        requires notBool isTypeValid(T, S)

   //a function to check if all typeVar in a data definition is within scope
   syntax Bool ::= isTypeVarValid(K, Set) [function]
                 | isTypeVarValidInList(List, Set) [function]
   rule isTypeVarValid(typeConst(A:K, B:List), S:Set)
         => isTypeValidInList(B, S)
   rule isTypeVarValid(T:TyVar, S:Set) => T in S
   rule isTypeVarValid(A:K, S:Set) => true [owise]

   rule isTypeVarValidInList(.List, S:Set) => true
   rule isTypeVarValidInList(ListItem(A:K) L:List, S:Set)
             => isTypeVarValid(A, S) andBool isTypeVarValidInList(L, S)

   syntax KItem ::= isAllValidTypeVars(Map, K, K) [function]
                  | isValidTypeVars(Map, Map, K, K, Set) [function]

   rule isAllValidTypeVars(.Map, .K, .K) => .K
   rule isAllValidTypeVars((A:K |-> B:K) M:Map, .K, .K)
            => isAllValidTypeVars(M, A, B)
   rule isAllValidTypeVars(M:Map, A:K, preBetaEntry(Os:Set,
             L:List, Body:Map, Oc:Set))
            => isValidTypeVars(M, Body, .K, .K, listToSet(L))
   rule isAllValidTypeVars(M:Map, A:K, alphaTuple(L:List, Body:K))
            => isAllValidTypeVars(M, .K, .K)
        requires isTypeVarValid(Body, listToSet(L))
   rule isAllValidTypeVars(M:Map, A:K, alphaTuple(L:List, Body:K))
            => error(typeVarNotInScope)
        requires notBool isTypeVarValid(Body, listToSet(L))

   rule isValidTypeVars(M:Map, .Map, .K, .K, S:Set) => isAllValidTypeVars(M, .K, .K)
   rule isValidTypeVars(M:Map, (A:K |-> B:K) BM:Map, .K, .K, S:Set)
           => isValidTypeVars(M:Map, BM, A, B, S)
   rule isValidTypeVars(M:Map, BM:Map, A:KItem, B:Type, S:Set)
           => isValidTypeVars(M, BM, .K, .K, S)
        requires isTypeVarValid(B, S)
   rule isValidTypeVars(M:Map, BM:Map, A:KItem, B:Type, S:Set)
                  => error(typeVarNotInScope)
        requires notBool isTypeVarValid(B, S)

   //kind inference function
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

   syntax KItem ::= kindInfer(Int, Set, K, K, Map, Map, Set) [function]
         //counter, kind-var-set, name, entry, beta, kind env, gen-kind-tuples
                  | kindInferAux(Int, Set, K, K, Map, Map, Map, Set) [function]
                     //counter, kind-var-set, result-type-var-kind, curr-ty-name,
                    //body map, beta, kind-map, gen-kind,tuples
                  | kindInferAuxAlpha(Int, Set, K, K, K, Map, Map, Set) [function]
                     //counter, kind-var-set, result-type-var-kind, curr-ty-name,
                    //body, beta, kind-map, gen-kind,tuples
                  | kindInferSec(K, K, Map, Map, Set) [function]
                   //name, execution, beta, kind-env
                  | kindInferThird(Int, Set, K, K, Map, Map, Set) [function]
                  | kindInferLast(Int, Set, K, K, Map, Map, Set) [function]
                  | kindNext(Int, Set, K, Map, Map, Set) [function]
                  | kindNextList(Int, Set, K, List, Map, Map, Set) [function]
                  | kindInferFinal(Int, Set, K, Map) [function]

   rule kindInferFinal(N:Int, S:Set, resultMap(M:Map), KM:Map)
        => resultTyVarKindMap(N, S, replaceAllKindInMap(M, KM))

   rule kindInfer(N:Int, S:Set, .K, .K, .Map, KM:Map, Tu:Set)
             => kindInferFinal(N, S, unifInKind(.K, .Set, Tu, .Map), KM)
   rule kindInfer(N:Int, S:Set, .K, .K, (A:K |-> B:K) BM:Map, KM:Map, Tu:Set)
          => kindInfer(N, S, A, B, BM, KM, Tu)
   rule kindInfer(N:Int, S:Set, A:K, preBetaEntry(Oc:Set,
                Vl:List, Body:Map, Od:Set), BM:Map, (A |-> T:K) KM:Map, Tu:Set)
          => kindInferAux(N, S, genTyVarKind(T,
                          .Map, Vl), A, Body, BM, (A |-> T:K) KM, Tu)
   rule kindInfer(N:Int, S:Set, A:K, alphaTuple(Vl:List, Body:K),
                 BM:Map, (A |-> T:K) KM:Map, Tu:Set)
          => kindInferAuxAlpha(N, S, genTyVarKind(T,
                          .Map, Vl), A, Body, BM, (A |-> T:K) KM, Tu)

   rule kindInferAuxAlpha(N:Int, S:Set, resultMap(M:Map), A:K,
                 Body:K, BM:Map, KM:Map, Tu:Set)
          => kindInferSec(A, kindNext(N, S, Body, .Map, KM M, .Set), BM, KM, Tu)

   rule kindInferAux(N:Int, S:Set, resultMap(M:Map),
                      A:K, Body:Map, BM:Map, KM:Map, Tu:Set)
             => kindInferSec(A, kindNext(N, S, .K, Body, KM M, .Set), BM, KM, Tu)

   rule kindInferSec(A:K, returnKind(N:Int, S:Set, Tus:Set), BM:Map, KM:Map, Tu:Set)
             => kindInferThird(N, S, A, checkAndRemoveNoVarTerms(
                                     .K, Tus, .Set), BM:Map, KM:Map, Tu)
   rule kindInferSec(A:K, error(X:K), BM:Map, KM:Map, Tu:Set) => error(X)
   rule kindInferThird(N:K, S:Set, A:K, error(X:K), BM:Map, KM:Map, Tu:Set) => error(X)
   rule kindInferThird(N:K, S1:Set, A:K, resultSet(S:Set), BM:Map, KM:Map, Tu:Set)
            => kindInferLast(N, S1, A, unifInKind(.K, .Set, S, .Map), BM, KM, Tu)

   rule kindInferLast(N:Int, S:Set, A:K, error(X:K), BM:Map, KM:Map, Tu:Set) => error(X)
   rule kindInferLast(N:Int, S:Set, A:K, resultMap(TuM:Map), BM:Map, KM:Map, Tu:Set)
           => kindInfer(N, S, .K, .K, BM, KM, toKindTupleSet(TuM) Tu)

   rule kindNext(N:Int, S:Set, .K, .Map, M:Map, Tus:Set) => returnKind(N, S, Tus)
   rule kindNext(N:Int, S:Set, .K, (A:K |-> B:K) Body:Map, M:Map, Tus:Set)
          => kindNext(N:Int, S:Set, B, Body, M, Tus)
   rule kindNext(N:Int, S:Set, curryTypes(L:List, T:K), Body:Map, M:Map, Tus:Set)
          => kindNextList(N, S, .K, L, Body, M, Tus)
   rule kindNext(N:Int, S:Set, T:KItem, Body:Map, M:Map, Tus:Set)
          => kindNextList(N, S, .K, ListItem(T), Body, M, Tus)
        requires notBool isCurryType(T)

   rule kindNextList(N:Int, S:Set, .K, .List, Body:Map, M:Map, Tus:Set)
            => kindNext(N, S, .K, Body, M, Tus)
   rule kindNextList(N:Int, S:Set, .K, ListItem(A:K) L:List, Body:Map, M:Map, Tus:Set)
           => kindNextList(N, S, kindInference(N, S, A, star, M), L, Body, M, Tus)
   rule kindNextList(N:Int, S:Set, error(X:K), L:List, Body:Map, M:Map, Tus:Set)
           => error(X)
   rule kindNextList(N:Int, S:Set, returnKind(N1:Int, S1:Set, Tu1:Set),
              L:List, Body:Map, M:Map, Tus:Set)
          => kindNextList(N1, S1, .K, L, Body, M, Tus Tu1)


   //kind inference rule -- generate kind unifiers
   syntax KItem ::= kindInference(Int, Set, K, K, Map) [function]
               //counter, kind-var-set, exp, assume kind, kind env
                  | kindInferenceAux(Int, Set, Set, List, List, Map) [function]
               //counter, kind-var-set, kind-unifiers, args, arg-types, kind env.
                  | kindInferenceAuxAux(List, List, Set, K, Map) [function]
                  | kindInferenceTyVar(Int, Set, K, K, Int, List, Map) [function]
               //counter, kind-var-set, con-type, assume-type, arg-length, args, kind env

   rule kindInference(N:Int, S:Set, fullName(A:K, B:K), star, M:Map)
          => returnKind(N, S, .Set)
   rule kindInference(N:Int, S:Set, fullName(A:K, B:K), C:K, M:Map)
          => error(typeConKindBad)
        requires notBool isTheKind(fullName(A:K, B:K), star, .K, M)
   rule kindInference(N:Int, S:Set, fullName(A:K, B:K), C:K, M:Map)
          => returnKind(N, S, SetItem(kindTuple(C, star)))
        requires C =/=K star andBool isTheKind(fullName(A:K, B:K), star, .K, M)

   rule kindInference(N:Int, S:Set, A:TyVar, C:K, (A |-> D:K) M:Map)
             => returnKind(N, S, SetItem(kindTuple(C,D)))
   rule kindInference(N:Int, S:Set, A:TyVar, C:K, M:Map)
             => error(typeVarNotInScope)
        requires notBool A in keys(M)

   rule kindInference(N:Int, S:Set, typeConst(fullName(X:K, Y:K), B:List),
                 C:K, (fullName(X:K, Y:K) |-> D:K) M:Map)
          => kindInferenceAux(N, S, SetItem(kindTuple(C, D)),
                  B, formListKind(D), (fullName(X:K, Y:K) |-> D:K) M:Map)
        requires size(B) ==K countKindLength(D)
   rule kindInference(N:Int, S:Set, typeConst(fullName(X:K, Y:K), B:List),
                 C:K, (fullName(X:K, Y:K) |-> D:K) M:Map)
          => error(typeConKindNumError)
        requires size(B) =/=K countKindLength(D)
   rule kindInference(N:Int, S:Set, typeConst(X:TyVar, B:List),
                 C:K, (X |-> D:K) M:Map)
          => kindInferenceTyVar(N, S, C, D, size(B), B, (X |-> D:K) M:Map)

   rule kindInferenceTyVar(N:Int, S:Set, C:K, D:K, 0, B:List, M:Map)
         => kindInferenceAux(N, S, SetItem(kindTuple(C, D)), B, formListKind(C), M)
   rule kindInferenceTyVar(N:Int, S:Set, C:K, D:K, I:Int, B:List, M:Map)
         => kindInferenceTyVar(N +Int 1, SetItem(kindVar(N)) S,
                       kindArrow(kindVar(N), C), D, I -Int 1, B, M)
        requires I >Int 0

   rule kindInferenceAux(N:Int, S:Set, Tus:Set, .List, .List, M:Map)
                    => returnKind(N, S, Tus)
   rule kindInferenceAux(N:Int, S:Set, Tus:Set, ListItem(A:K) L:List,
                  ListItem(A':K) L':List, M:Map)
          => kindInferenceAuxAux(L, L', Tus, kindInference(N,
                             S, A, A', M), M)
   rule kindInferenceAuxAux(L:List, L':List, Tus:Set, returnKind(N:Int, S:Set, A:Set), B:Map)
           => kindInferenceAux(N, S, Tus A, L, L', B)
   rule kindInferenceAuxAux(L:List, L'L:List, Tus:Set, error(X:K), B:Map) => error(X)

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
   syntax Bool ::= isKindArrow(K) [function]
   rule isKindArrow(kindArrow(A:K, B:K)) => true
   rule isKindArrow(A:K) => false [owise]
   
   syntax Bool ::= isKindVar(K) [function]
   rule isKindVar(kindVar(A:Int)) => true
   rule isKindVar(A:K) => false [owise]

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

   //functions to compile type classes to ast form
   //only deal with method decl, method pattern will be in separate functions
   syntax Set ::= getTypeVarsInClass(K, Set) [function]
   rule getTypeVarsInClass(.K, .Set) => .Set
   rule getTypeVarsInClass(.K, SetItem(A:K) S:Set)
            => getTypeVarsInClass(A, S)
   rule getTypeVarsInClass(className(A:K, ListItem(C:K) B:List), S:Set)
            => SetItem(C) getTypeVarsInClass(.K, S)

   syntax KItem ::= toAstTypeClass(K, K, K, Map, Set) [function]
             //curr-mod, type-class-var, OptCDecls, gen-class-map, exist-ty-con-set
                  | toAstTypeClassAux(K, K, K, CDeclsList, Map, Set) [function]
            //curr-mod, type-class-var, CDecl,CDeclsList, gen-class-map, exist-ty-con-set
                  | toAstTypeClassList(K, K, K, Set, K, CDeclsList, Map, Set, Set) [function]
            //curr-mod, type-class-var, vars, contexts, type,CDeclsList, gen-class-map,
            // exist-ty-con-set, exist-var-set

   rule toAstTypeClass(Mod:K, V:K, 'emptyOptCDecls(.KList), M:Map, S:Set)
                   => putClassMapSet(M, S)
   rule toAstTypeClass(Mod:K, V:K, 'cdeclWhere('cdeclBracket(Cs:CDeclsList)), M:Map, S:Set)
           => toAstTypeClass(Mod,V, Cs, M, S)
   rule toAstTypeClass(Mod:K, V:K, .CDeclsList, M:Map, S:Set) => putClassMapSet(M, S)
   rule toAstTypeClass(Mod:K, V:K, 'cdeclCon(A:CDecl,, B:CDeclsList),
                     M:Map, S:Set)
         => toAstTypeClassAux(Mod, V:K, A, B, M, S)

   rule toAstTypeClassAux(Mod:K, V:K, 'emptyGenDecl(.KList), B:CDeclsList, M, S)
          => toAstTypeClass(Mod, V, B, M, S)
   rule toAstTypeClassAux(Mod:K, V:K, 'varAssign(X:Vars,, T:Type),
                B:CDeclsList, M:Map, S:Set)
           => toAstTypeClassList(Mod, V, X, .Set, toAbsTypeWithAll(
                 toAbsType(Mod, T), getFreeTypeVars(toAbsType(Mod, T))), B, M,
                  S, getFreeTypeVars(toAbsType(Mod, T)))
        requires V in getFreeTypeVars(toAbsType(Mod, T))
   rule toAstTypeClassAux(Mod:K, V:K, 'varAssign(X:Vars,, T:Type),
                B:CDeclsList, M:Map, S:Set)
           => error(ambiguousTypeVar)
        requires notBool V in getFreeTypeVars(toAbsType(Mod, T))

   rule toAstTypeClassAux(Mod:K, V:K, 'genAssignContext(X:Vars,, C:Context,, T:Type),
                B:CDeclsList, M:Map, S:Set)
           => toAstTypeClassList(Mod, V, X, contextToSet(Mod, C), toAbsTypeWithAll(
                 toAbsType(Mod, T), getFreeTypeVars(toAbsType(Mod, T))), B, M,
                  S, getFreeTypeVars(toAbsType(Mod, T)))
        requires V in getFreeTypeVars(toAbsType(Mod, T))
                  andBool getTypeVarsInClass(.K, contextToSet(Mod, C))
                                     <=Set getFreeTypeVars(toAbsType(Mod, T))
   rule toAstTypeClassAux(Mod:K, V:K, 'genAssignContext(X:Vars,, C:Context,, T:Type),
                B:CDeclsList, M:Map, S:Set)
           => error(ambiguousTypeVar)
        requires (notBool V in getFreeTypeVars(toAbsType(Mod, T)))
                   orBool (notBool getTypeVarsInClass(.K, contextToSet(Mod, C))
                                     <=Set getFreeTypeVars(toAbsType(Mod, T)))
   rule toAstTypeClassAux(Mod:K, V:K, X:K, B:CDeclsList, M:Map, S:Set)
            => toAstTypeClass(Mod, V, B, M, S) [owise]


   rule toAstTypeClassList(Mod:K, V:K, X:Var,
                       Cons:Set, T:K, C:CDeclsList, M:Map, S:Set, S1:Set)
           => toAstTypeClass(Mod, V, C, (methodName(Mod, pillVar(X))
                        |-> methodDef(Cons, T, .List)) M, SetItem(pillVar(X)) S)
        requires notBool pillVar(X) in (S S1)
   rule toAstTypeClassList(Mod:K, V:K, X:Var, Cons:Set,
            T:K, C:CDeclsList, M:Map, S:Set, S1:Set) => error(classVarCollipse)
        requires pillVar(X) in (S S1)
   rule toAstTypeClassList(Mod:K, V:K, 'varCon(X:Var,, Xs:Vars), Cons:Set,
                  T:K, C:CDeclsList, M:Map, S:Set, S1:Set)
           => toAstTypeClassList(Mod, V, Xs, Cons:Set, T, C,
                  (methodName(Mod, pillVar(X))
                     |-> methodDef(Cons, T, .List)) M, SetItem(pillVar(X)) S, S1)
        requires notBool pillVar(X) in (S S1)
   rule toAstTypeClassList(Mod:K, V:K, 'varCon(X:Var,, Xs:Vars), Cons:Set,
             T:K, C:CDeclsList, M:Map, S:Set, S1:Set)
           => error(classVarCollipse)
        requires pillVar(X) in (S S1)

   //functions to add possible pattern rules for type classes
   //only for the right hand side.
   syntax KItem ::= updatePatListInDef(K, K) [function]
   rule updatePatListInDef(methodDef(Cons:Set, A:K, L:List), D:K)
          =>  methodDef(Cons, A, L ListItem(D))

   syntax Map ::= updatePatMapInExp(Map, K, K) [function]
              //map, name, patterns
   rule updatePatMapInExp(M:Map (A |-> D:K), A:K, C:K)
           => M (A |-> updatePatListInDef(D, C))
       rule updatePatMapInExp(M:Map, A:K, C:K) => M [owise]

   syntax KItem ::= toAstPat(Int, K, K, Map) [function]
      //curr-mod, exp, class-map
   rule toAstPat(N:Int, Mod:K, 'emptyOptCDecls(.KList), M:Map) => resultMap(M)
   rule toAstPat(N:Int, Mod:K, 'cdeclWhere('cdeclBracket(Cs:CDeclsList)), M:Map)
         => toAstPat(N, Mod, Cs, M)
   rule toAstPat(N:Int, Mod:K, .CDeclsList, M:Map) => resultMap(M)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon('cdeclVarRhs(X:Var,, Y:Rhs),, B:CDeclsList), M:Map)
            => toAstPat(N, Mod, B, updatePatMapInExp(
                   M, methodName(Mod, pillVar(X)), transRhs(N, Mod, Y)))

   //rule toAstTypeClass(Mod:K, V:K, 'cdeclCon(A:CDecl,, B:CDeclsList),
    //                 M:Map, S:Set)
    //     => toAstTypeClassAux(Mod, V:K, A, B, M, S)
   syntax Bool ::= isTheQCon(K) [function]
   rule isTheQCon(A:QCon) => true
   rule isTheQCon(A:K) => false [owise]

   syntax Int ::= fbSize(FBindList) [function]
   rule fbSize(.FBindList) => 0
   rule fbSize('fbCon(A:FBind,, As:FBindList))
            => 1 +Int fbSize(As)


   //a function to transfer decls to ast form.
   syntax KItem ::= transRhs(Int, K, K) [function]
                  | transExp(Int, K, K) [function]
                  //helper function for app fun
                  | transExpFunAux(K, K, K) [function]
                  | transExpFunAuxAux(K, K) [function]
                  | transExpTupleAux(K, K) [function]
                  | transExpTuple(Int, K, K, K, List) [function]
                       //counter, curr-mod, tuple, curr-buf, stored
                  | transExpList(Int, K, ExpList, K, List) [function]
                       //counter, curr-mod, exp-list, curr-buf, stored
                  | transExpRecord(Int, K, AExp, FBindList) [function]
                  | transExpRecordAux(K, K, K) [function]
                  | transExpRecordAuxAux(K, K) [function]
                  | transFBindList(Int, K,K, FBindList, K, K, List) [function]
                 //Counter, curr-mod, flag, FBindList, curr-buf1,buf2, stored
                  | transExpSeq1(K) [function]
                  | transExpSeq2NoEnd(K, K, K) [function]
                  | transExpSeq2NoEndAux(K, K) [function]
                  | transExpSeq2HasEnd(K, K, K) [function]
                  | transExpSeq2HasEndAux(K, K) [function]
                  | transExpSeq3(K, K, K, K) [function]
                  | transExpSeq3Aux(K, K, K, K) [function]
                  | transExpSeq3AuxAux(K, K, K) [function]
                  | transExpListCompre(K, K, Quals) [function]
                  | transQuals(Int, K, K, K, K, List) [function]
                 //counter, pat, curr-mod, quals, buf, stored
                  | transQual(K, K, K) [function]
                  | transQualPat(K, K) [function]
                  | transQualLet(K) [function]
                  | transDecls(Int, K, K) [function]
                  | transLeftSection(K, K) [function]
                  | transRightSection(K, K) [function]

   syntax List ::= transDecl(Int, K, K) [function]
                 | transQuals(Int, K, Quals) [function]

   syntax List ::= genDeclForVars(K, Vars,Set, K) [function]
   rule genDeclForVars(Mod:K, A:Var,S:Set, T:K)
               => ListItem(methodDecl(methodName(Mod, A), S, T))
   rule genDeclForVars(Mod:K, 'varCon(A:Var, B:Vars),S:Set, T:K)
               => ListItem(methodDecl(methodName(Mod, A), S, T))
                   genDeclForVars(Mod, B,S, T)

   syntax KItem ::= formExpList(List) [function]
   rule formExpList(.List) => fullName(Prelude,[])
   rule formExpList(ListItem(A:K) L:List)
          => appExp(fullName(Prelude, 'colon(.KList)), ListItem(A)
                    ListItem(formExpList(L)))

         //curr-mod-name, exp
   //rule transRhs(Mod:K, 'normalRhs(E:Exp,, D:OptDecls))
    //       => rhs(transExp(Mod, E), transDecls(Mod, D))

   //transExp 
   rule transExp(N:Int, Mod:K, A:QVar) => resultTrans(N, A)
   rule transExp(N:Int, Mod:K, A:GCon) => resultTrans(N, transExpCon(Mod, A))
   rule transExp(N:Int, Mod:K, I:Integer) => resultTrans(N, String2Int(#tokenToString(I)))
   rule transExp(N:Int, Mod:K, I:CusFloat) => resultTrans(N, String2Float(#tokenToString(I)))
   rule transExp(N:Int, Mod:K, I:CusChar) => resultTrans(N, #tokenToString(I))
   rule transExp(N:Int, Mod:K, I:CusString) => resultTrans(N, #tokenToString(I))

   //trans funApp
   rule transExp(N:Int, Mod:K, 'funApp(A:AExp,, B:AExp))
          => transExpFunAux(transExp(N:Int, Mod, A), Mod, B)
   rule transExpFunAux(error(A:K), Mod:K, B:K) => error(A)
   rule transExpFunAux(resultTrans(N:Int, A:K), Mod:K, B:K)
          => transExpFunAuxAux(A, transExp(N:Int, Mod, B))
   rule transExpFunAuxAux(A:K, error(B:K)) => error(B)
   rule transExpFunAuxAux(A:K, resultTrans(N:Int, B:K))
              => resultTrans(N, appExp(A, ListItem(B)))

   //trans tuples 
   rule transExp(N:Int, Mod:K, 'expTuple(As:ExpTuple))
             => transExpTupleAux(fullName(Prelude, tupleType(
                       countOnTypeTuple(As))), transExpTuple(N:Int, Mod, As, .K, .List))
   rule transExpTupleAux(A:K, error(B:K)) => error(B)
   rule transExpTupleAux(A:K, resultTransList(N:Int, B:List))
           => resultTrans(N, appExp(A, B))

   rule transExpTuple(N:Int, Mod:K, .K, .K, L:List) => resultTransList(N, L)
   rule transExpTuple(N:Int, Mod:K, A:Exp, .K, L:List)
           => transExpTuple(N, Mod, .K, transExp(N, Mod, A), L)
   rule transExpTuple(N:Int, Mod:K, 'twoExpTuple(A:Exp,, B:Exp), .K, L:List)
           => transExpTuple(N, Mod, B, transExp(N, Mod, A), L)
   rule transExpTuple(N:Int, Mod:K, 'expTupleCon(A:Exp,, B:ExpTuple), .K, L:List)
           => transExpTuple(N, Mod, B, transExp(N, Mod, A), L)
   rule transExpTuple(N:Int, Mod:K, A:K, error(B:K), L:List) => error(B)
   rule transExpTuple(N:Int, Mod:K, A:K, resultTrans(N':Int, B:K), L:List)
            => transExpTuple(N', Mod, A:K, .K, L ListItem(B))

   //trans exp list
   rule transExp(N:Int, Mod:K, 'expList(As:ExpList))
          => transExpList(N, Mod, As, .K, .List)
   rule transExpList(N:Int, Mod:K, .K, .K, L:List) => resultTrans(N, formExpList(L))
   rule transExpList(N:Int, Mod:K, A:Exp, .K, L:List)
            => transExpList(N, Mod, .K, transExp(N, Mod, A), L)
   rule transExpList(N:Int, Mod:K, 'expListCon(A:Exp,, B:ExpList), .K, L:List)
            => transExpList(N, Mod, B, transExp(N, Mod, A), L)
   rule transExpList(N:Int, Mod:K, A:K, error(B:K), L:List) => error(B)
   rule transExpList(N:Int, Mod:K, A:K, resultTrans(N':Int, B:K), L:List)
         => transExpList(N', Mod, A, .K, L ListItem(B))

   //trans records, two different things. labeled update and label pattern
   rule transExp(N:Int, Mod:K, 'recordExp(A:AExp,, Fs:FBindList))
            =>  transExpRecord(N:Int, Mod, A, Fs)
   rule transExpRecord(N:Int, Mod:K, Q:QCon, Fs:FBindList)
           => transExpRecordAuxAux(transExpCon(Mod, Q),
            transFBindList(N, Mod, recordAssign, Fs, .K, .K, .List))
   rule transExpRecord(N:Int, Mod:K, A:AExp, Fs:FBindList)
           => transExpRecordAux(transExp(N, Mod, A), Mod, Fs)
        requires notBool isTheQCon(A) andBool fbSize(Fs) >Int 0
   rule transExpRecord(N:Int, Mod:K, A:AExp, Fs:FBindList)
           => error(syntaxError) [owise]

   rule transExpRecordAux(error(A:K), Mod:K, B:K) => error(A)
   rule transExpRecordAux(resultTrans(N:Int, A:K), Mod:K, B:K)
          => transExpRecordAuxAux(A, transFBindList(N,
                        Mod, recordUpdate, B, .K, .K, .List))

   rule transExpRecordAuxAux(A:K, error(B:K)) => error(B)
   rule transExpRecordAuxAux(A:K, resultTransList(N:Int, L:List))
           => resultTrans(N, appExp(A, ListItem(appExp(fullName(
                          Prelude, recordParen), L))))

   rule transFBindList(N:Int, Mod:K, S:K, .FBindList, .K, .K, L:List)
           => resultTransList(N, L)
   rule transFBindList(N:Int, Mod:K,S:K, 'fbCon('fbConAssign(
                A:QVar,, B:Exp),, C:FBindList), .K, .K, L:List)
          => transFBindList(N, Mod,S, C, transTypeVar(Mod, A), transExp(N, Mod, B), L)
   rule transFBindList(N:Int, Mod:K,S:K, C:FBindList, X:K, error(B:K), L:List) => error(B)
   rule transFBindList(N:Int, Mod:K,S:K, C:FBindList, X:K, resultTrans(N':Int, A:K), L:List)
          => transFBindList(N', Mod, S, C, .K, .K, L ListItem(appExp(
                fullName(Prelude, S),ListItem(X) ListItem(A))))

   //trans exp sequence1
   rule transExp(N:Int, Mod:K, 'expSeq(E1:Exp,, 'emptyExpComma(.KList),, 'emptyExp(.KList)))
           => transExpSeq1(transExp(N:Int, Mod, E1))
   rule transExpSeq1(error(A:K)) => error(A)
   rule transExpSeq1(resultTrans(N:Int, A:K))
          => resultTrans(N, appExp(fullName(Prelude, arithSeq1), ListItem(A)))

   //trans exp seq2 without end
   rule transExp(N:Int, Mod:K, 'expSeq(E1:Exp,, 'dotExp(E2:Exp),, 'emptyExp(.KList)))
         => transExpSeq2NoEnd(transExp(N:Int, Mod, E1), Mod, E2)
   rule transExpSeq2NoEnd(error(A:K), Mod:K, E2:K) => error(A)
   rule transExpSeq2NoEnd(resultTrans(N:Int, A:K), Mod:K, E2:K)
            => transExpSeq2NoEndAux(A, transExp(N, Mod, E2))
   rule transExpSeq2NoEndAux(A:K, error(B:K)) => error(B)
   rule transExpSeq2NoEndAux(A:K, resultTrans(N:Int, B:K))
          => resultTrans(N, appExp(fullName(Prelude, arithSeq2noEnd),
                   ListItem(A) ListItem(B)))

   //trans exp seq2 has end
   rule transExp(N:Int, Mod:K, 'expSeq(E1:Exp,, 'emptyExpComma(.KList),, E3:Exp))
         => transExpSeq2HasEnd(transExp(N:Int, Mod, E1), Mod, E3)
   rule transExpSeq2HasEnd(error(A:K), Mod:K, E2:K) => error(A)
   rule transExpSeq2HasEnd(resultTrans(N:Int, A:K), Mod:K, E2:K)
            => transExpSeq2HasEndAux(A, transExp(N, Mod, E2))
   rule transExpSeq2HasEndAux(A:K, error(B:K)) => error(B)
   rule transExpSeq2HasEndAux(A:K, resultTrans(N:Int, B:K))
          => resultTrans(N, appExp(fullName(Prelude, arithSeq2hasEnd),
                   ListItem(A) ListItem(B)))

   //trans exp seq3
   rule transExp(N:Int, Mod:K, 'expSeq(E1:Exp,, 'dotExp(E2:Exp),, E3:Exp))
         => transExpSeq3(transExp(N, Mod, E1), Mod, E2, E3)
   rule transExpSeq3(error(A:K), Mod, B:K, C:K) => error(A)
   rule transExpSeq3(resultTrans(N:Int, A:K), Mod, B:K, C:K)
           => transExpSeq3Aux(A, transExp(N, Mod, B), Mod, C)
   rule transExpSeq3Aux(A:K, error(B:K), Mod:K, C:K) => error(B)
   rule transExpSeq3Aux(A:K, resultTrans(N:Int, B:K), Mod:K, C:K)
          => transExpSeq3AuxAux(A, B, transExp(N, Mod, C))
   rule transExpSeq3AuxAux(A:K, B:K, error(C:K)) => error(C)
   rule transExpSeq3AuxAux(A:K, B:K, resultTrans(N:Int, C:K))
            => resultTrans(N, appExp(fullName(Prelude, arithSeq3), ListItem(A)
                      ListItem(B) ListItem(B)))

   //trans list comprehension
   rule transExp(N:Int, Mod:K, 'listComprehension(E1:Exp,, Qs:Quals))
         => transExpListCompre(transExp(N, Mod, E1), Mod, Qs)
   rule transExpListCompre(error(A:K), Mod:K, B:Quals) => error(A)
   rule transExpListCompre(resultTrans(N:Int, A:K), Mod:K, B:Quals)
          => transQuals(N, A, Mod:K, B, .K, .List)

   rule transQuals(N:Int, A:K, Mod:K, .K, .K, L:List)
          => appExp(fullName(Prelude, listCompre), ListItem(A) L)
   rule transQuals(N:Int, A:K, Mod:K, B:Qual, .K, L:List)
           => transQuals(N, A, Mod:K, .K, transQual(N, Mod, B), L:List)
   rule transQuals(N:Int, A:K, Mod:K, 'qualCon(B:Qual,, C:Quals), .K, L:List)
           => transQuals(N, A, Mod:K, C, transQual(N, Mod, B), L:List)
   rule transQuals(N:Int, A:K, Mod:K, C:K, error(D:K), L:List) => error(D)
   rule transQuals(N:Int, A:K, Mod:K, C:K, resultTrans(N':Int, D:K), L:List)
          => transQuals(N', A, Mod, C, .K, L ListItem(D))

   rule transQual(N:Int, Mod:K, 'qualAssign(A:Pat,, B:Exp))
         => transQualPat(transPat(Mod, A), transExp(N, Mod, B))
   rule transQualPat(A:K, error(B:K)) => error(B)
   rule transQualPat(A:K, resultTrans(N':Int, B:K))
           => resultTrans(N', appExp(fullName(Prelude, qualAssignAst),
                           ListItem(A) ListItem(B)))
   rule transQual(N:Int, Mod:K,'qualLet(A:Decls))
         => transQualLet(transDecls(N, Mod, A))
   rule transQualLet(error(A:K)) => error(A)
   rule transQualLet(resultTrans(N:Int, B:K))
         => resultTrans(N, appExp(fullName(Prelude, qualLetAst), B))
   rule transQual(N:Int, Mod:K, A:Exp) => transExp(N, Mod, A)

   //trans left and right sections
   rule transExp(N:Int, Mod:K, 'leftSection(E1:InfixExp,, G:QOp))
          => transLeftSection(transExp(N, Mod, E1), transVar(Mod, G))
   rule transLeftSection(error(A:K), B:K) => error(A)
   rule transLeftSection(resultTrans(N:Int, A:K), B:K)
          => resultTrans(N +Int 1, lambda(genVar(N), appExp(B,
                      ListItem(A) ListItem(genVar(N)))))

   rule transExp(N:Int, Mod:K, 'rightSection(G:QOp,, E1:InfixExp))
          => transRightSection(transVar(Mod, G), transExp(N, Mod, E1))
   rule transRightSection(B:K, error(A:K)) => error(A)
   rule transRightSection(B:K, resultTrans(N:Int, A:K))
          => resultTrans(N +Int 1, lambda(genVar(N), appExp(B,
                       ListItem(genVar(N)) ListItem(A))))

   //transDecls
/*
   rule transDecls(Mod:K, 'emptyOptDecls(.KList)) => .List
   rule transDecls(Mod:K, .DeclsList) => .List
   rule transDecls(Mod:K, 'whereDecls('decls(Ds:DeclsList)))
           => transDecls(Mod, Ds)
   rule transDecls(Mod:K, 'declsCon(D:Decl,, Ds:DeclsList))
           => transDecl(Mod, D) transDecls(Mod, Ds)

   rule transDecl(Mod:K, 'emptyIDecl(.KList)) => .List
   rule transDecl(Mod:K, 'varAssign(A:Vars,, B:Type))
         => genDeclForVars(Mod, A, .Set, toAbsType(Mod, B))
   rule transDecl(Mod:K, 'genAssignContext(A:Vars,, C:Context,, B:Type))
         => genDeclForVars(Mod, A, contextToSet(Mod, C), toAbsType(Mod, B))
*/

   //pattern transformation is self-contained
   syntax KItem ::= transPat(K, K) [function]
                  | transPatList(K, PatList) [function]

   syntax List ::= transFPats(K, FPats) [function]
                 | transPatTuple(K, PatTuple) [function]
                 | transAPatList(K, APatList) [function]

   rule transPat(Mod:K, 'binPattern(A:LPat,, B:QConOp,, C:Pat))
           => appPat(transVar(Mod, B),
                 ListItem(transPat(Mod, A)) ListItem(transPat(Mod, C)))
   rule transPat(Mod:K, V:Var) => V
   rule transPat(Mod:K, V:Var @ A:APat) => asPat(V, transPat(Mod, A))
   rule transPat(Mod:K, G:GCon) => transExpCon(Mod, G)
   rule transPat(Mod:K, 'recordPat(G:QCon,, Fs:FPats))
              => appPat(transExpCon(Mod, G),
                       ListItem(appPat(fullName(
                          Prelude, recordParen), transFPats(Mod, Fs))))
   rule transPat(Mod:K, 'underscore(.KList)) => unnamedVar
   rule transPat(Mod:K, ~ A:APat) => irrefuPat(transPat(Mod, A))
   rule transPat(Mod:K, I:Integer) => String2Int(#tokenToString(I))
   rule transPat(Mod:K, I:CusFloat) => String2Float(#tokenToString(I))
   rule transPat(Mod:K, I:CusChar) => #tokenToString(I)
   rule transPat(Mod:K, I:CusString) => #tokenToString(I)
   rule transPat(Mod:K, 'patTuple(As:PatTuple))
             => appPat(fullName(Prelude, tupleType(
                       countOnTypeTuple(As))), transPatTuple(Mod, As))
   rule transPat(Mod:K, 'patList(As:PatList))
             => appPat(fullName(Prelude, []), transPatList(Mod, As))
   rule transPat(Mod:K, 'minusPat(A:IntFloat))
          => appPat(fullName(Prelude, 'minusCon(.KList)), transPat(Mod, A))
   rule transPat(Mod:K, 'lpatCon(G:GCon,, As:APatList))
          => appPat(transExpCon(Mod, G), transAPatList(Mod, As))

   rule transAPatList(Mod:K, A:APat) => ListItem(transPat(Mod, A))
   rule transAPatList(Mod:K, 'apatCon(A:APat,, As:APatList))
            => ListItem(transPat(Mod, A)) transAPatList(Mod, As)

   rule transPatTuple(Mod:K, 'twoPatTuple(A:Pat,, B:Pat))
           => ListItem(transPat(Mod, A)) ListItem(transPat(Mod, B))
   rule transPatTuple(Mod:K, 'patTupleCon(A:Pat,, B:PatTuple))
           => ListItem(transPat(Mod, A)) transPatTuple(Mod, B)

   rule transPatList(Mod:K, A:Pat) => appPat(fullName(Prelude, 'colon(.KList)),
                            ListItem(transPat(Mod, A)) ListItem(fullName(Prelude, [])))
   rule transPatList(Mod:K, 'patListCon(A:Pat,, B:PatList))
           => appPat(fullName(Prelude, 'colon(.KList)),
                      ListItem(transPat(Mod, A)) ListItem(transPatList(Mod, B)))

   rule transFPats(Mod:K, .FPats) => .List
   rule transFPats(Mod:K, 'fpatCon('recordConAssign(A:QVar,, B:Pat),, C:FPats))
           => ListItem(appPat(fullName(Prelude, recordAssign),
             ListItem(transTypeVar(Mod, A)) ListItem(transPat(Mod, B)))) transFPats(Mod, C)

/*
    syntax Pat ::= LPat QConOp Pat
                 | LPat

    syntax LPat ::= APat
                  | "-" IntFloat    [klabel('minusPat)]
                  | GCon APatList  [klabel('lpatCon), onlyLabel]//arity gcon = k UNFINISHED

    syntax APatList ::= APat | APat APatList [klabel('apatCon), onlyLabel]

    syntax APat ::= Var [klabel('apatVar)]
                  | Var "@" APat
                  | GCon
                  | QCon "{" FPats "}"
                  | Literal [klabel('apatLiteral)]
                  | "_"     [klabel('underscore), onlyLabel]
                  | "(" Pat ")"   [bracket]
                  | "(" PatTuple ")"
                  | "[" PatList "]"
                  | "~" APat


                  | FunLhs Rhs [klabel('declFunLhsRhs), onlyLabel]
                  | Pat Rhs [klabel('declPatRhs), onlyLabel]

    syntax KItem ::= methodDecl(K, Set, K) //method-name, constaints, type


    syntax IDecl ::= FunLhs Rhs [klabel('ideclFunLhsRhs), onlyLabel]
                   | Var Rhs [klabel('ideclVarRhs), onlyLabel]
                   | "" [onlyLabel, klabel('emptyIDecl)]

    syntax GenDecl ::= VarsType
                     | Vars "::" Context "=>" Type   [klabel('genAssignContext)]
                     | Fixity Ops
                     | Fixity Integer Ops
                     | "" [onlyLabel, klabel('emptyGenDecl)]

    //three optional data type for the TopDecl data operator. 
    //deriving data type
    syntax OptDeriving ::= Deriving | "" [onlyLabel, klabel('emptyDeriving)]
    syntax Deriving ::= "deriving" DClass
                      | "deriving" "(" DClassList ")"
    syntax DClassList ::= List{DClass, ","}  [klabel('dclassCon)]
    syntax DClass ::= QTyCon

    syntax FunLhs ::= Var APatList
                    | Pat VarOp Pat
                    | "(" FunLhs ")" APatList

    syntax Rhs ::= "=" Exp OptDecls
                 | GdRhs OptDecls

    syntax GdRhs ::= Guards "=" Exp
                   | Guards "=" Exp GdRhs
    syntax Guards ::= "|" GuardList
    syntax GuardList ::= Guard | Guard "," GuardList  [klabel('guardListCon)]
    syntax Guard ::= Pat "<-" InfixExp
                   | "let" Decls
                   | InfixExp

    //definition of exp
    syntax Exp ::= InfixExp
                 > InfixExp "::" Type  [klabel('expAssign)]
                 | InfixExp "::" Context "=>" Type  [klabel('expAssignContext)]

    syntax InfixExp ::= LExp
                      > "-" InfixExp   [klabel('minusInfix)]
                      > LExp QOp InfixExp

    syntax LExp ::= AExp
                  > "\\" APatList "->" Exp
                  | "let" Decls "in" Exp
                  | "if" Exp OptSemicolon "then" Exp OptSemicolon "else" Exp
                  | "case" Exp "of" "{" Alts "}"
                  | "do" "{" Stmts "}"

    syntax OptSemicolon ::= ";" | "" [onlyLabel, klabel('emptySemicolon)]
    syntax OptComma ::= "," | ""     [onlyLabel, klabel('emptyComma)]

*/
endmodule
