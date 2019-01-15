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
   rule transVar(Mod:K, 'varIdQuote(A:VarId)) => fullName(Mod, A)
   rule transVar(Mod:K, A:VarSym) => fullName(Prelude, A)

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

   syntax Bool ::= isTheQCon(K) [function]
   rule isTheQCon(A:QCon) => true
   rule isTheQCon(A:K) => false [owise]

   syntax Int ::= fbSize(FBindList) [function]
   rule fbSize(.FBindList) => 0
   rule fbSize('fbCon(A:FBind,, As:FBindList))
            => 1 +Int fbSize(As)

endmodule
