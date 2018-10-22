//helper functions for the haskell semantics.
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"

module HASKELL-HELPER
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX

   syntax Map ::= updateMapItem(Map, K, K, K) [function]
   rule updateMapItem(M:Map, .K, A:K, V:K)
           => M (A |-> names(SetItem(V)))
        requires notBool A in keys(M)
   rule updateMapItem(M:Map (A:K |-> S:K), .K, A:K, V:K)
            => updateMapItem(M, S, A, V)
   rule updateMapItem(M:Map, names(S:Set), A:K, V:K)
             => M (A |-> names(SetItem(V) S))

   syntax Map ::= classContentToList(K, K, Map) [function]
                | singleContentToList(K, CDecl, Map) [function]
                | varAssignToList(K, Vars, Type, Map) [function]

          //mod, cdecls, global type map
   rule classContentToList(Mod:K, 'emptyOptCDecls(.KList), TM:Map) => .Map
   rule classContentToList(Mod:K, 'cdeclWhere('cdeclBracket(Cs:CDeclsList)), TM:Map)
            => classContentToList(Mod, Cs, TM)
   rule classContentToList(Mod:K, .CDeclsList, TM:Map) => .Map
   rule classContentToList(Mod:K, 'cdeclCon(C:CDecl,, Cs:CDeclsList), TM:Map)
           => singleContentToList(Mod, C, TM) classContentToList(Mod, Cs, TM)
   rule singleContentToList(Mod:K, 'emptyGenDecl(.KList), TM:Map) => .Map
   rule singleContentToList(Mod:K, 'varAssign(As:Vars,, T:Type), TM:Map)
              => varAssignToList(Mod, As, T, TM)

   rule varAssignToList(Mod:K, V:Var, T:Type, TM:Map) => V |-> T
   rule varAssignToList(Mod:K, 'varCon(V:Var,, Vs:Vars), T:Type, TM:Map)
                => (V |-> T) varAssignToList(Mod, Vs, T, TM)

endmodule
