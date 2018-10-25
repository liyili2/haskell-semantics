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

   //find the arity of a given op, if not then return none
   syntax KItem ::= findArity(K, K, Map, Map) [function]
               //mod, ty, ty-map, imports

   //a helper function to transform concrete type to abstract type
   syntax KItem ::= toAbsTypeInClass(K, Set, K, Map, Map) [function]
                  | toAbsTypeInClassApp(K, Set, K, List, Map,Map) [function]
           //module, type expression, type map, import map
                  | toAbsTypeInClassAppAux(K, Set, K, List, List, Map,Map) [function]

   rule toAbsTypeInClass(Mod:K, S:Set, 'typeArrow(B:BType,, T:Type), TM:Map, IM:Map)
            => typeConst((->), ListItem(toAbsTypeInClass(Mod,S, B, TM, IM))
                             ListItem(toAbsTypeInClass(Mod,S, T, TM, IM)))
        requires toAbsTypeInClass(Mod,S, B, TM, IM) =/=K none
              andBool toAbsTypeInClass(Mod,S, B, TM, IM) =/=K none
   rule toAbsTypeInClass(Mod:K, S:Set, 'baTypeCon(A:AType,, B:BType), TM:Map, IM:Map)
                => toAbsTypeInClassApp(Mod, S, A, ListItem(B), TM, IM)

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
           => typeConst(A, L)
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


endmodule
