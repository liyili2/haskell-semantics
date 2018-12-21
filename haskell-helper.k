//helper functions for the haskell semantics.
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"

module HASKELL-HELPER
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX

   //boolean functions to determine if a term has no certain klabel
   syntax Bool ::= isBATypeCon(K) [function]
   rule isBATypeCon('baTypeCon(A:AType,, B:BType)) => true
   rule isBATypeCon(A:K) => false [owise]

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

   syntax Int ::= countOnTypeTuple(TypeTuple) [function]
   rule countOnTypeTuple('twoTypeTuple(A:K,, B:K)) => 2
   rule countOnTypeTuple('typeTupleCon(A:K,, B:TypeTuple))
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
            => typeConst((->), ListItem(toAbsTypeInClass(Mod,S, B, TM, IM))
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
           => typeConst('unitType(.KList), .List)
   rule toAbsTypeInClass(Mod:K, S:Set, 'tyList(B:K), TM:Map, IM:Map)
           => typeConst([], ListItem(toAbsTypeInClass(Mod,S, B, TM, IM)))
        requires toAbsTypeInClass(Mod,S, B, TM, IM) =/=K none
   rule toAbsTypeInClass(Mod:K, S:Set, 'tupleCover(B:TypeTuple), TM:Map, IM:Map)
           => typeConst(tupleType(typeTupleCount(B)),
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
           => typeConst(dealWithTuple(A), L)
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

   syntax Map ::= addEdges(Set, Set) [function]
   rule addEdges(A:K, SetItem(B:K) S:Set)
          => (A |-> names(SetItem(B) S))

   syntax KItem ::= getSingleton(Set) [function]
   rule getSingleton(SetItem(A:K)) => A

   syntax KItem ::= makeAlphaM(K, Map, Map) [function] //(Alpha, AlphaMap)
                  | makeAlphaMAux(TopDecl, Map, K, Map) [function]
   rule makeAlphaM('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls), M:Map, TM:Map)
          => makeAlphaM(Ts, M, TM)
   rule makeAlphaM('bodyimpdecls(Is:ImpDecls), M:Map, TM:Map) => .K
   rule makeAlphaM('bodytopdecls(Ts:TopDecls), M:Map, TM:Map) => makeAlphaM(Ts, M, TM)
   rule makeAlphaM(.TopDecls, M:Map, TM:Map) => putAlphaMap(TM)
   rule makeAlphaM('topdeclslist(A:TopDecl,, As:TopDecls), M:Map, TM:Map)
              => makeAlphaMAux(A, M, As, TM)

   rule makeAlphaMAux(type A:SimpleType = B:Type, M:Map, As:K, TM:Map)
            => makeAlphaM(As, addEdges(getConstrNames(A), getConstrNames(B)) M,
                            (getConstrNames(A) |-> B) TM)
        requires getTypeNames(B) <=Set getTypeNames(A)
                  andBool getSingleton(getConstrNames(A)) in keys(M)
                  andBool notBool hasCycleAux(getSingleton(getConstrNames(A)), getConstrNames(B), M)
   rule makeAlphaMAux(type A:SimpleType = B:Type, M:Map, As:K, TM:Map) => error(typeVarNoInclusive)
        requires notBool (getTypeNames(B) <=Set getTypeNames(A))
   rule makeAlphaMAux(type A:SimpleType = B:Type, M:Map, As:K, TM:Map) => error(repeatedNames)
        requires notBool getSingleton(getConstrNames(A)) in keys(M)
   rule makeAlphaMAux(type A:SimpleType = B:Type, M:Map, As:K, TM:Map) => error(cycleAlpha)
        requires hasCycleAux(getSingleton(getConstrNames(A)), getConstrNames(B), M)
   rule makeAlphaMAux(A:TopDecl, M:Map, As:K, TM:Map) => makeAlphaM(As, M, TM) [owise]


   //collect a map for knowing the type name and its partial kind (not proved)
   syntax Map ::= parKindEntry(SimpleType) [function]
   syntax KItem ::= resolveKindEntry(TyVars) [function]
   rule parKindEntry('simpleTypeCon(T:TyCon,, Vs:TyVars))
                    => (T |-> parKnown(resolveKindEntry(Vs)))
   rule resolveKindEntry(.TyVars) => star
   rule resolveKindEntry('typeVars(A:TyVar,,B:TyVars))
          => kindArrow(star, resolveKindEntry(B))

   syntax KItem ::= collectTypes(K, Map) [function] // decls, store-kind-map
   rule collectTypes('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls), M:Map)
          => collectTypes(Ts, M)
   rule collectTypes('bodyimpdecls(Is:ImpDecls), M:Map) => .K
   rule collectTypes('bodytopdecls(Ts:TopDecls), M:Map) => collectTypes(Ts, M)
   rule collectTypes(.TopDecls, M:Map) => putKindMap(M)
   rule collectTypes('topdeclslist(type A:SimpleType = B:Type,, As:TopDecls), M:Map)
              => collectTypes(As, (parKindEntry(A)) M)
   rule collectTypes('topdeclslist(data Oc:OptContext A:SimpleType
                        B:OptConstrs D:OptDeriving,, As:TopDecls), M:Map)
              => collectTypes(As, (parKindEntry(A)) M)
   rule collectTypes('topdeclslist(newtype Oc:OptContext A:SimpleType
                       = B:NewConstr D:OptDeriving,, As:TopDecls), M:Map)
              => collectTypes(As, (parKindEntry(A)) M)
   rule collectTypes('topdeclslist(A:TopDecl,, As:TopDecls),
                   M:Map) => collectTypes(As, M) [owise]

   //turn type syntax to abstract syntax
   syntax List ::= toTypeList(K) [function]
   rule toTypeList(.TyVars) => .List
   rule toTypeList('typeVars(X:TyVar,, A:TyVars))
           => ListItem(X) toTypeList(A)

   syntax KItem ::= toAbsType(K, K) [function] //current module name, type
                  | toAbsTypeAux(K, K, List, K) [function]
                          //curr-mod, type-con-name,type-args, unsolved
   syntax List ::= toAbsTypeTuple(K, TypeTuple) [function]//curr-mod, type-tuple

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

   rule toAbsType(S:K, 'group(T:K)) => toAbsType(S, T)
   rule toAbsType(S:K, 'baTypeCon(T:K,, T1:K))
          => toAbsTypeAux(S, toAbsType(S, T), .List, T1)

   rule toAbsTypeAux(S:K, A:K, L:List, 'baTypeCon(T:K,, T1:K))
           => toAbsTypeAux(S:K, A, L ListItem(toAbsType(S, T)), T1)
   rule toAbsTypeAux(S:K, A:K, L:List, T:K)
           => typeConst(A, L ListItem(toAbsType(S, T))) [owise]

   rule toAbsTypeTuple(S:K, 'twoTypeTuple(A:K,, B:K))
                     => ListItem(toAbsType(S, A)) ListItem(toAbsType(S, B))
   rule toAbsTypeTuple(S:K, 'typeTupleCon(A:K,, B:TypeTuple))
                     => ListItem(toAbsType(S, A)) toAbsTypeTuple(S, B)


   //collecting preBetaMap info
   syntax Map ::= makePreBetaFun(K, K, Map) [function]
   











endmodule
