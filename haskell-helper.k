//helper functions for the haskell semantics.
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"

module HASKELL-HELPER
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX

   //add a set term to a warpper of set
   syntax KItem ::= addToSetInK(K, Set) [function]
   rule addToSetInK(resultSet(S:Set), S':Set) => resultSet(S S')

   //helper function to transfer a list to a set
   syntax Set ::= listToSet(List) [function]
   rule listToSet(.List) => .Set
   rule listToSet(ListItem(A:K) L:List) => SetItem(A) listToSet(L)

   syntax List ::= setToList(Set) [function]
   rule setToList(.Set) => .List
   rule setToList(SetItem(A:K) L:Set) => ListItem(A) setToList(L)

   syntax List ::= typeVarsToList(TyVars) [function]
   rule typeVarsToList(.TyVars) => .List
   rule typeVarsToList('typeVars(A:TyVar,, B:TyVars))
            => ListItem(A) typeVarsToList(B)

   //boolean functions to determine if a term has no certain klabel
   syntax Bool ::= isBATypeCon(K) [function]
   rule isBATypeCon('baTypeCon(A:AType,, B:BType)) => true
   rule isBATypeCon(A:K) => false [owise]

   //a function to pill varid/varop
   syntax KItem ::= pillVar(K) [function]
   rule pillVar('varSymBracket(A:VarSym)) => A
   rule pillVar('varIdQuote(A:VarId)) => A
   rule pillVar('conSymBracket(C:ConSym)) => C
   rule pillVar(V:K) => V [owise]

   syntax KItem ::= buildVar(K) [function]
   rule buildVar(V:VarId) => funName(V)
   rule buildVar('qVarIdCon(M:ModId,, V:VarId))
            => fullName(M, funName(V))
   rule buildVar(C:ConSym) => funName(C)
   rule buildVar('qConSymCon(M:ModId,, C:ConSym))
            => fullName(M, funName(C))
   rule buildVar(C:ConId) => typeName(C)

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
   rule transVar(Mod:K, 'conTyCon(A:ModId,, C:TyCon)) => fullName(A, C)
   rule transVar(Mod:K, C:TyCon) => fullName(Mod, C)
   rule transVar(Mod:K, C:ConId) => fullName(Mod, C)
   rule transVar(Mod:K, 'conSymBracket(C:ConSym)) => transVar(Mod, C)

   syntax KItem ::= transTypeVar(K, K) [function]
   rule transTypeVar(S:K, V:VarId) => tyVar(S, V)
   rule transTypeVar(S:K, 'qVarIdCon(A:ModId,, B:VarId)) => tyVar(A, B)
   rule transTypeVar(S:K, 'qVarBracket(C:ConSym)) => tyVar(S, C)
   rule transTypeVar(S:K, 'qVarBracket(
           'qConSymCon(A:ModId,, B:ConSym))) => tyVar(S, B)

   syntax Map ::= updateMapItem(Map, K, K, Set) [function]
   rule updateMapItem(M:Map, .K, A:K, V:Set)
           => M (A |-> resultSet(V))
        requires notBool A in keys(M)
   rule updateMapItem(M:Map (A:K |-> S:K), .K, A:K, V:Set)
            => updateMapItem(M, S, A, V)
   rule updateMapItem(M:Map, resultSet(S:Set), A:K, V:Set)
             => M (A |-> resultSet(V S))

   syntax List::= updateFunExpAux(List, K) [function]
   rule updateFunExpAux(L:List, A:K) => L ListItem(A)

   syntax Map ::= updateFunExp(Map, K, K) [function]
   rule updateFunExp(M:Map, A:K, V:K)
           => M (A |-> resultList(ListItem(V)))
        requires notBool A in keys(M)
   rule updateFunExp(M:Map (A:K |-> S:K), A:K, V:K) => M (A |-> updateFunExpAux(S, V))


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
   rule countOnTypeTuple('twoTypeVarTuple(A:K,, B:K)) => 2
   rule countOnTypeTuple('typeVarTupleCon(A:K,, B:K))
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

   syntax Int ::= fbSize(FBindList) [function]
   rule fbSize(.FBindList) => 0
   rule fbSize('fbCon(A:FBind,, As:FBindList))
            => 1 +Int fbSize(As)

   //check if a module contains the same class name before
   syntax Bool ::= hasClassName(K, K, K, Map) [function]
   rule hasClassName(A:K, C:K, .K, (A:K |-> B:K) M:Map)
          => hasClassName(A,C, B, M)
   rule hasClassName(A:K, C:K, resultSet(S:Set), M:Map) => C in S
   rule hasClassName(A:K, B:K, C:K, M:Map) => false [owise]

   //get a set of methods defined in a module
   syntax Set ::= getMethodSet(K, K, Map) [function]
   rule getMethodSet(A:K, .K, (A:K |-> B:K) M:Map)
          => getMethodSet(A, B, M)
   rule getMethodSet(A:K, resultSet(S:Set), M:Map) => S
   rule getMethodSet(A:K, B:K, M:Map) => .Set [owise]

   //identify functions 
   syntax Bool ::= isTheQCon(K) [function]
   rule isTheQCon(A:QCon) => true
   rule isTheQCon(A:K) => false [owise]

   syntax Bool ::= isTheClass(K) [function]
   rule isTheClass('class(A:K,, B:K,, C:K,, D:K)) => true
   rule isTheClass(A:K) => false [owise]

   syntax Bool ::= isTheDefault(K) [function]
   rule isTheDefault('default(Ts:K)) => true
   rule isTheDefault(A:K) => false [owise]

   syntax Bool ::= isIntersect(Set, K, Set) [function]
   rule isIntersect(.Set, .K, S':Set) => false
   rule isIntersect(SetItem(A:K) S:Set, .K, S':Set)
          => isIntersect(S, A, S')
   rule isIntersect(S:Set, A:KItem, S':Set) => isIntersect(S:Set, .K, S')
        requires notBool (A in S')
   rule isIntersect(S:Set, A:KItem, S':Set) => true
        requires A in S'

   syntax Set ::= getIntersect(Set, K, Set) [function]
   rule getIntersect(.Set, .K, S':Set) => .Set
   rule getIntersect(SetItem(A:K) S:Set, .K, S':Set)
          => getIntersect(S, A, S')
   rule getIntersect(S:Set, A:KItem, S':Set) => getIntersect(S:Set, .K, S')
        requires notBool (A in S')
   rule getIntersect(S:Set, A:KItem, S':Set) => SetItem(A) getIntersect(S, .K, S')
        requires A in S'

   syntax Set ::= setMinus(Set, K, Set) [function]
   rule setMinus(.Set, .K, S':Set) => .Set
   rule setMinus(SetItem(A:K) S:Set, .K, S':Set)
          => setMinus(S, A, S')
   rule setMinus(S:Set, A:KItem, S':Set) => setMinus(S:Set, .K, S')
        requires (A in S')
   rule setMinus(S:Set, A:KItem, S':Set) => SetItem(A) setMinus(S, .K, S')
        requires notBool A in S'

   syntax Map ::= mapMinus(Map, K, K, Map) [function]
   rule mapMinus(.Map, .K, .K, M':Map) => .Map
   rule mapMinus((A:K |-> B:K) S:Map, .K,.K, S':Map)
          => mapMinus(S, A,B, S')
   rule mapMinus(S:Map, A:KItem,B:KItem, S':Map) => mapMinus(S:Map, .K,.K, S')
        requires A in keys(S')
   rule mapMinus(S:Map, A:KItem,B:KItem, S':Map) => (A |-> B) mapMinus(S, .K,.K, S')
        requires notBool A in keys(S')


   syntax Set ::= "intTypeSet" [function]
   rule intTypeSet => SetItem("Int") SetItem("Int8") SetItem("Int16")
                      SetItem("Int32") SetItem("Int64") SetItem("Integer")
                      SetItem("Word") SetItem("Word8") SetItem("Word16")
                      SetItem("Word32") SetItem("Word64") 

   syntax Set ::= "floatTypeSet" [function]
   rule floatTypeSet => SetItem("Float") SetItem("Double")

   syntax Bool ::= isIntType(K) [function]
   rule isIntType(A:TyCon) => #tokenToString(A) in intTypeSet
   rule isIntType('conTyCon(Prelude,, B:TyCon))
            => #tokenToString(B) in intTypeSet
   rule isIntType(A:K) => false [owise]

   syntax Bool ::= isFloatType(K) [function]
   rule isFloatType(A:TyCon) => #tokenToString(A) in floatTypeSet
   rule isFloatType('conTyCon(Prelude,, B:TyCon))
            => #tokenToString(B) in floatTypeSet
   rule isFloatType(A:K) => false [owise]

   syntax Bool ::= isTheExp(K) [function]
   rule isTheExp(A:Decl) => true
   rule isTheExp(A:K) => false [owise]

   syntax Bool ::= isTheInstance(K) [function]
   rule isTheInstance('instance(A:K,, B:K,, C:K,, D:K)) => true
   rule isTheInstance(A:K) => false [owise]

   syntax Bool ::= hasDistinctVars(K) [function]
                 | hasDistinctVarsAux(K, Set) [function]
   rule hasDistinctVars('instAppType(A:K,, B:K)) => hasDistinctVarsAux(B, .Set)
   rule hasDistinctVars('instTupleCover(A:K)) => hasDistinctVarsAux(A, .Set)
   rule hasDistinctVars('typeVarFun(A:K,, A:K)) => true
   rule hasDistinctVars('typeVarFun(A:K,, B:K)) => false
        requires A =/=K B
   rule hasDistinctVars(A:K) => true [owise]

   rule hasDistinctVarsAux(.TyVars, S:Set) => true
   rule hasDistinctVarsAux('typeVars(A:TyVar,, B:TyVars), S:Set)
           => hasDistinctVarsAux(B, SetItem(A) S)
        requires notBool A in S
   rule hasDistinctVarsAux('typeVars(A:TyVar,, B:TyVars), S:Set) => false
        requires A in S
   rule hasDistinctVarsAux('twoTypeVarTuple(A:TyVar,, B:TyVar), S:Set) => true
        requires notBool A in S andBool notBool B in S andBool A =/=K B
   rule hasDistinctVarsAux('twoTypeVarTuple(A:TyVar,, B:TyVar), S:Set) => false
        requires A in S orBool B in S orBool A ==K B
   rule hasDistinctVarsAux('typeVarTupleCon(A:TyVar,, B:TyVarTuple), S:Set)
           => hasDistinctVarsAux(B, SetItem(A) S)
        requires notBool A in S
   rule hasDistinctVarsAux('typeVarTupleCon(A:TyVar,, B:TyVarTuple), S:Set) => false
        requires A in S

   //check there is only one default in a module
   syntax KItem ::= checkOnlyDefault(K) [function]
                  | checkOnlyDefaultAux(K, K, K, K) [function]
                  | checkOnlyDefaultNext(K, K) [function]

   rule checkOnlyDefault('bodyimpandtop(Is:ImpDecls,, Ts:TopDecls))
           => checkOnlyDefault(Ts)
   rule checkOnlyDefault('bodyimpdecls(Is:ImpDecls)) => .K
   rule checkOnlyDefault('bodyimpdecls(Ts:TopDecls)) => checkOnlyDefault(Ts)
   rule checkOnlyDefault(.TopDecls) => .K
   rule checkOnlyDefault('topdeclslist('default(Ts:K),, As:TopDecls))
          => checkOnlyDefaultAux(Ts, As, Integer, Double)
   rule checkOnlyDefault('topdeclslist(A:TopDecl,, As:TopDecls)) => checkOnlyDefault(As)
        requires notBool isTheDefault(A)

   rule checkOnlyDefaultAux(.Types, As:K, T1:K, T2:K)
              => checkOnlyDefaultNext(resultDefaultTypes(T1, T2), As)
   rule checkOnlyDefaultAux('typeCon(T:Type,, Ts:Types), As:K, T1:K, T2:K)
             => checkOnlyDefaultAux(Ts, As, T, T2)
        requires isIntType(T)
   rule checkOnlyDefaultAux('typeCon(T:Type,, Ts:Types), As:K, T1:K, T2:K)
             => checkOnlyDefaultAux(Ts, As, T1, T)
        requires isFloatType(T)
   rule checkOnlyDefaultAux('typeCon(T:Type,, Ts:Types), As:K, T1:K, T2:K)
             => checkOnlyDefaultAux(Ts, As, T1, T2) [owise]

   rule checkOnlyDefaultNext(A:K, .TopDecls) => A
   rule checkOnlyDefaultNext(A:K, 'topdeclslist('default(Ts:K),, As:TopDecls))
          => error(moreThanOneDefault)
   rule checkOnlyDefaultNext(X:K, 'topdeclslist(A:TopDecl,, As:TopDecls))
               => checkOnlyDefaultNext(X, As)
        requires notBool isTheDefault(A)

   syntax Set ::= getFreeVarsInPat(K) [function]
   rule getFreeVarsInPat('binPattern(P1:LPat,, Op:QConOp,, P2:Pat))
            => getFreeVarsInPat(P1) getFreeVarsInPat(P2)
   rule getFreeVarsInPat('minusPat(A:K)) => .Set
   rule getFreeVarsInPat('lpatCon(G:GCon,, As:APatList))
           => getFreeVarsInPat(As)
   rule getFreeVarsInPat('apatCon(A:K,, As:K))
          => getFreeVarsInPat(A) getFreeVarsInPat(As)
   rule getFreeVarsInPat(A:Var) => SetItem(pillVar(A))
   rule getFreeVarsInPat(A:Var @ P:APat)
            => SetItem(pillVar(A)) getFreeVarsInPat(P)
   rule getFreeVarsInPat(A:GCon) => .Set
   rule getFreeVarsInPat('recordPat(A:GCon,, F:FPats))
          => getFreeVarsInPat(F)
   rule getFreeVarsInPat(A:Literal) => .Set
   rule getFreeVarsInPat('underscore(.KList)) => .Set
   rule getFreeVarsInPat('patTuple(P:PatTuple)) => getFreeVarsInPat(P)
   rule getFreeVarsInPat('patList(P:PatList)) => getFreeVarsInPat(P)
   rule getFreeVarsInPat('irrefutablePat(P:APat)) => getFreeVarsInPat(P)
   rule getFreeVarsInPat('twoPatTuple(P1:Pat,, P2:Pat))
             => getFreeVarsInPat(P1) getFreeVarsInPat(P2)
   rule getFreeVarsInPat('patTupleCon(P1:Pat,, P2:PatTuple))
             => getFreeVarsInPat(P1) getFreeVarsInPat(P2)
   rule getFreeVarsInPat('patListCon(P1:Pat,, P2:PatList))
             => getFreeVarsInPat(P1) getFreeVarsInPat(P2)
   rule getFreeVarsInPat(.FPats) => .Set
   rule getFreeVarsInPat('fpatCon(P1:FPat,, P2:FPats))
             => getFreeVarsInPat(P1) getFreeVarsInPat(P2)
   rule getFreeVarsInPat('recordConAssign(P1:QVar,, P2:Pat))
             => getFreeVarsInPat(P2)
   rule getFreeVarsInPat('varCon(A:Var,, As:Vars))
           => SetItem(pillVar(A)) getFreeVarsInPat(As)

   syntax Set ::= getRidWrapper(K) [function]
   rule getRidWrapper(resultSet(S:Set)) => S

   syntax Set ::= getValues(Map, K, Set) [function]
   rule getValues(M:Map, .K, .Set) => .Set
   rule getValues(M:Map, .K, SetItem(A:K) S:Set)
           => getValues(M, A, S)
   rule getValues(M:Map (A |-> B:K), A:KItem, S:Set)
         => SetItem(B) getValues(M, .K, S)
   rule getValues(M:Map, A:KItem, S:Set) => getValues(M, .K, S) [owise]

endmodule
