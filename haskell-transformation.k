//helper functions for the haskell semantics.
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"
requires "haskell-helper.k"
requires "haskell-kindinfer.k"

module HASKELL-TRANSFORMATION
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX
    imports HASKELL-HELPER
    imports HASKELL-KINDINFER

   //only deal with method decl, method pattern will be in separate functions
   syntax Set ::= getTypeVarsInClassAux(K, Set) [function]
   rule getTypeVarsInClassAux(.K, .Set) => .Set
   rule getTypeVarsInClassAux(.K, SetItem(A:K) S:Set)
            => getTypeVarsInClassAux(A, S)
   rule getTypeVarsInClassAux(classTitle(A:K, ListItem(C:K) B:List), S:Set)
            => SetItem(C) getTypeVarsInClassAux(.K, S)

   syntax Set ::= getTypeVarsInClass(K) [function]
   rule getTypeVarsInClass(error(A:K)) => .Set
   rule getTypeVarsInClass(resultSet(S:Set)) => getTypeVarsInClassAux(.K, S)

   //forming a cons list from a K list
   syntax KItem ::= formExpList(List) [function]
   rule formExpList(.List) => fullName(Prelude,constrName([]))
   rule formExpList(ListItem(A:K) L:List)
          => appExp(fullName(Prelude, constrName('colon(.KList))), ListItem(A)
                    ListItem(formExpList(L)))

   //forming a cons list comprehension with syntactic suger
   syntax KItem ::= formListCompre(K, List) [function]
   rule formListCompre(A:K, .List) => A
   rule formListCompre(A:K, ListItem(B:K) L:List)
          => appExp(fullName(Prelude, constrName(listCompre)), ListItem(B)
                    ListItem(formListCompre(A, L)))

   syntax KItem ::= formLambdaList(List, K) [function]
   rule formLambdaList(.List, A:K) => A
   rule formLambdaList(ListItem(A:K) L:List, B:K)
          => lambda(A, formLambdaList(L, B))

   syntax KItem ::= formDoCons(List, K) [function]
   rule formDoCons(.List, A:K) => A
   rule formDoCons(ListItem(A:K) L:List, B:K)
         => seq(A, formDoCons(L, B))

   syntax List ::= genDeclForVars(K, Vars,Set, K) [function]
   rule genDeclForVars(Mod:K, A:Var,S:Set, T:K)
               => ListItem(makeMethodDecl(funName(pillVar(A)), S, T))
   rule genDeclForVars(Mod:K, 'varCon(A:Var, B:Vars),S:Set, T:K)
               => ListItem(makeMethodDecl(funName(pillVar(A)), S, T))
                   genDeclForVars(Mod, B,S, T)

   //make a method decl by method-name, contexts, and type
   syntax KItem ::= makeMethodDecl(K, Set, K) [function]
   rule makeMethodDecl(F:K, C:Set, forall(A:Set, T:K))
              => methodDecl(F, C, makeVarContextMap(A), T)
   rule makeMethodDecl(F:K, C:Set, T:K) => methodDecl(F, C, .Map, T) [owise]

   //a function to set up contexts for type-vars in a method
   syntax KItem ::= updateSingleContextAux(K, K) [function]
   rule updateSingleContextAux(contextKind(X:Set, Y:K), B:K)
             => contextKind(X SetItem(B), Y)

   syntax Map ::= updateSingleContext(Map, K, K) [function]
   rule updateSingleContext((X |-> C:K) M:Map, X, Y:K)
           => (X |-> updateSingleContextAux(C, Y)) M

   syntax Map ::= setUpContextMethod(Map, K, K) [function]
                | setUpContextMethodAux(Map, K, Set) [function]
   rule setUpContextMethod(.Map, .K, .K) => .Map
   rule setUpContextMethod((A:K |-> B:K) M:Map, .K, .K)
            => setUpContextMethod(M, A, B)
   rule setUpContextMethod(M:Map, A:K, methodDef(Cs:Set, M:Map, T:K, L:List))
           => setUpContextMethod(M, .K, .K)
                 (A |-> methodDef(Cs, setUpContextMethodAux(M, .K, Cs), T, L))

   rule setUpContextMethodAux(M:Map, .K, .Set) => M
   rule setUpContextMethodAux(M:Map, .K, SetItem(A:K) S:Set)
          => setUpContextMethodAux(M, A, S)
   rule setUpContextMethodAux(M:Map, classTitle(A:K, ListItem(X:K) L:List), S:Set)
           => setUpContextMethodAux(updateSingleContext(M, X, A), .K, S)

   //make a method def by context and forall types
   syntax Map ::= makeVarContextMap(Set) [function]
   rule makeVarContextMap(.Set) => .Map
   rule makeVarContextMap(SetItem(A:K) S:Set)
            => (A |-> contextKind(.Set, .K)) makeVarContextMap(S)

   syntax KItem ::= makeMethodDef(Set, K) [function]
   rule makeMethodDef(C:Set, forall(A:Set, T:K))
              => methodDef(C, makeVarContextMap(A), T, .List)
   rule makeMethodDef(C:Set, T:K) => methodDef(C, .Map, T, .List) [owise]

   syntax KItem ::= makeMethodDefWithList(Set, K, List) [function]
   rule makeMethodDefWithList(C:Set, forall(A:Set, T:K), L:List)
              => methodDef(C, makeVarContextMap(A), T, L)
   rule makeMethodDefWithList(C:Set, T:K, L:List) => methodDef(C, .Map, T, L) [owise]

   //transformation of funlhs and patterns in all cases
   syntax KItem ::= transPosPat(K, K, Set, Set) [function]
                  | transNegPat(K, K, Set, Set) [function]
                  | transLiteral(K) [function]
                  | transPatBinAux(K, K, K) [function]
                  | transPatLPatCon(K, K) [function]
                  | transPosPatList(K, K, Set, Set, K, List) [function]
                  | transNegPatList(K, K, Set, Set, K, List) [function]
                  | transAsPat(K, K) [function]
                  | transPosRecordPat(K, K, K, Set, Set) [function]
                  | transNegRecordPat(K, K, K, Set, Set) [function]
                  | transPosRecordPatAux(K, K, K, Set, Set, K, K, List) [function]
                  | transNegRecordPatAux(K, K, K, Set, Set, K, K, List) [function]
                  | transPatIrreFut(K)  [function]
                  | transPatPatList(K)  [function]
                  | transPatPatTuple(K) [function]
                  | transPosFunLhs(K, K, Set, Set) [function]
                  | transNegFunLhs(K, K, Set, Set) [function]
                  | transFunPat(K) [function]
                  | transFunPatNormal(K, K) [function]
                  | transFunPatBin(K, K, K) [function]
                  | transFunPatGroup(K, K)  [function]

   rule transLiteral(I:Integer) => String2Int(#tokenToString(I))
   rule transLiteral(I:CusFloat) => String2Float(#tokenToString(I))
   rule transLiteral(I:CusChar) => #tokenToString(I)
   rule transLiteral(I:CusString) => #tokenToString(I)


   //transformation of funLhs on the top-decl, classes and instances
   //not dealing with funLhs in the where statement of a fun body
   rule transFunPat(error(A:K)) => error(A)
   rule transFunPat(A:K) => funPat(ListItem(A)) [owise]

   rule transFunPatNormal(error(A:K), B:K) => error(A)
   rule transFunPatNormal(A:K, error(B:K)) => error(B)
   rule transFunPatNormal(A:K, resultList(L:List)) => funPat(ListItem(A) L) [owise]

   rule transFunPatBin(error(A:K), B:K, C:K) => error(A)
   rule transFunPatBin(A:K, error(B:K), C:K) => error(B)
   rule transFunPatBin(A:K, B:K, error(C:K)) => error(C)
   rule transFunPatBin(A:K, B:K, C:K)
                => funPat(ListItem(A) ListItem(B) ListItem(C)) [owise]

   rule transFunPatGroup(error(A:K), B:K) => error(A)
   rule transFunPatGroup(A:K, error(B:K)) => error(B)
   rule transFunPatGroup(funPat(L1:List), resultList(L2:List))
             => funPat(L1 L2) [owise]

   rule transPosFunLhs(Mod:K, P:Pat, Ts:Set, Is:Set)
                => transFunPat(transPosPat(Mod, P, Ts, Is))
   rule transPosFunLhs(Mod:K, 'normalLhs(V:Var,, As:APatList), Ts:Set, Is:Set)
          => transFunPatNormal(fullName(Mod, funName(pillVar(V))),
                  transNegPatList(Mod, V, Ts, Is, .K, .List))
   rule transPosFunLhs(Mod:K, 'binLhs(P1:Pat,, V:VarOp,, P2:Pat), Ts:Set, Is:Set)
          => transFunPatBin(fullName(Mod, funName(pillVar(V))),
                  transNegPat(Mod, P1, Ts, Is), transNegPat(Mod, P1, Ts, Is))
   rule transPosFunLhs(Mod:K, 'groupLhs(F:FunLhs,, As:APatList), Ts:Set, Is:Set)
         => transFunPatGroup(transPosFunLhs(Mod, F, Ts, Is),
                      transNegPatList(Mod, As, Ts, Is, .K, .List))

   rule transNegFunLhs(Mod:K, P:Pat, Ts:Set, Is:Set)
                => transFunPat(transNegPat(Mod, P, Ts, Is))
   rule transNegFunLhs(Mod:K, 'normalLhs(V:Var,, As:APatList), Ts:Set, Is:Set)
          => transFunPatNormal(funName(pillVar(V)),
                  transNegPatList(Mod, V, Ts, Is, .K, .List))
   rule transNegFunLhs(Mod:K, 'binLhs(P1:Pat,, V:VarOp,, P2:Pat), Ts:Set, Is:Set)
          => transFunPatBin(funName(pillVar(V)),
                  transNegPat(Mod, P1, Ts, Is), transNegPat(Mod, P1, Ts, Is))
   rule transNegFunLhs(Mod:K, 'groupLhs(F:FunLhs,, As:APatList), Ts:Set, Is:Set)
         => transFunPatGroup(transNegFunLhs(Mod, F, Ts, Is),
                      transNegPatList(Mod, As, Ts, Is, .K, .List))

   //trans pat if the variables of patterns need to be global vars
   rule transPosPat(Mod:K, 'binPattern(A:LPat,, B:QConOp,, C:Pat), Ts:Set, Is:Set)
          => transPatBinAux(transConstrVar(Mod, pillVar(B), Ts, Is),
                 transPosPat(Mod, A, Ts, Is), transPosPat(Mod, C, Ts, Is))
   rule transPosPat(Mod:K, 'minusPat(A:K), Ts:Set, Is:Set)
              =>  appPat(fullName(Prelude, funName('minusCon(.KList))), transLiteral(A))
   rule transPosPat(Mod:K, V:Var, Ts:Set, Is:Set) => fullName(Mod, funName(pillVar(V)))
   rule transPosPat(Mod:K, V:Var @ A:APat, Ts:Set, Is:Set)
            => transAsPat(fullName(Mod, funName(pillVar(V))), transPosPat(Mod, A, Ts, Is))
   rule transPosPat(Mod:K, G:GCon, Ts:Set, Is:Set) => transExpCon(Mod, G, Ts, Is)
   rule transPosPat(Mod:K, 'lpatCon(G:GCon,, As:APatList), Ts:Set, Is:Set)
            => transPatLPatCon(transExpCon(
                   Mod, G, Ts, Is), transPosPatList(Mod, As, Ts, Is, .K, .List))
   rule transPosPat(Mod:K, 'underscore(.KList), Ts:Set, Is:Set) => unnamedVar
   rule transPosPat(Mod:K, A:Literal, Ts:Set, Is:Set) => transLiteral(A)
   rule transPosPat(Mod:K, 'recordPat(G:QCon,, Fs:FPats), Ts:Set, Is:Set)
           => transPosRecordPat(Mod, transExpCon(Mod, G, Ts, Is), Fs, Ts, Is)
   rule transPosPat(Mod:K, 'irrefutablePat(A:K), Ts:Set, Is:Set)
         => transPatIrreFut(transPosPat(Mod, A, Ts, Is))
   rule transPosPat(Mod:K, 'patList(A:K), Ts:Set, Is:Set)
          => transPatPatList(transPosPatList(Mod, A, Ts, Is, .K, .List))
   rule transPosPat(Mod:K, 'patTuple(A:K), Ts:Set, Is:Set)
          => transPatPatTuple(transPosPatList(Mod, A, Ts, Is, .K, .List))

   rule transPosRecordPat(Mod:K, error(A:K), Fs:K, Ts:Set, Is:Set) => error(A)
   rule transPosRecordPat(Mod:K, fullName(Mod':K, G:K), Fs:K, Ts:Set, Is:Set)
             => transPosRecordPatAux(Mod, fullName(Mod', G:K), Fs, Ts, Is, .K, .K, .List)

   rule transPosRecordPatAux(Mod:K, A:K, .FPats, Ts:Set, Is:Set, .K, .K, L:List)
           => appPat(A, ListItem(appPat(fullName(Prelude, constrName(recordParen(A))), L)))
   rule transPosRecordPatAux(Mod:K, fullName(Mod':K, G:K),
                  'fpatCon('recordConAssign(A:K,, B:K),, C:K), Ts:Set, Is:Set, .K, .K, L:List)
            => transPosRecordPatAux(Mod, fullName(Mod':K, G:K), C, Ts, Is,
                   transFunVar(Mod', A, .Set, Ts, Is), transPosPat(Mod, B, Ts, Is), L)
   rule transPosRecordPatAux(Mod:K, A:K, B:K, Ts:Set, Is:Set,
             error(X:K), Y:K, L:List) => error(X)
   rule transPosRecordPatAux(Mod:K, A:K, B:K, Ts:Set, Is:Set,
             X:K, error(Y:K), L:List) => error(Y)
   rule transPosRecordPatAux(Mod:K, A:K, B:K, Ts:Set, Is:Set, X:KItem, Y:KItem, L:List)
          => transPosRecordPatAux(Mod, A, B, Ts, Is, .K, .K,
              L ListItem(appPat(fullName(Prelude,
                 constrName(recordAssign)), ListItem(X) ListItem(Y)))) [owise]

   rule transPosPatList(Mod:K, A:Pat, Ts:Set, Is:Set, .K, L:List)
              => transPosPatList(Mod, .K, Ts, Is, transPosPat(Mod, A, Ts, Is), L)
   rule transPosPatList(Mod:K, .K, Ts:Set, Is:Set, error(A:K), L:List) => error(A)
   rule transPosPatList(Mod:K, .K, Ts:Set, Is:Set, .K, L:List) => resultList(L)
   rule transPosPatList(Mod:K, Rest:K, Ts:Set, Is:Set, A:KItem, L:List)
            => transPosPatList(Mod, Rest, Ts, Is, .K, L ListItem(A))
        requires notBool isError(A)
   rule transPosPatList(Mod:K, 'twoPatTuple(A:K,, B:K), Ts:Set, Is:Set, .K, L:List)
             => transPosPatList(Mod, B, Ts, Is, transPosPat(Mod, A, Ts, Is), L)
   rule transPosPatList(Mod:K, 'patTupleCon(A:K,, B:K), Ts:Set, Is:Set, .K, L:List)
             => transPosPatList(Mod, B, Ts, Is, transPosPat(Mod, A, Ts, Is), L)
   rule transPosPatList(Mod:K, 'patListCon(A:K,, B:K), Ts:Set, Is:Set, .K, L:List)
             => transPosPatList(Mod, B, Ts, Is, transPosPat(Mod, A, Ts, Is), L)
   rule transPosPatList(Mod:K, 'apatCon(A:K,, B:K), Ts:Set, Is:Set, .K, L:List)
             => transPosPatList(Mod, B, Ts, Is, transPosPat(Mod, A, Ts, Is), L)

   //functions that share commonly in pos and neg trans
   rule transPatPatTuple(error(A:K)) => error(A)
   rule transPatPatTuple(resultList(L:List))
             => appPat(fullName(Prelude, constrName(tupleType(size(L)))), L)

   rule transPatPatList(error(A:K)) => error(A)
   rule transPatPatList(resultList(L:List)) => appPat(fullName(Prelude, constrName([])), L)

   rule transPatIrreFut(error(A:K)) => error(A)
   rule transPatIrreFut(A:K) => irrefuPat(A) [owise]

   rule transPatLPatCon(error(A:K), B:K) => error(A)
   rule transPatLPatCon(A:K, error(B:K)) => error(B)
   rule transPatLPatCon(A:K, resultList(B:List)) => appPat(A, B) [owise]

   rule transAsPat(error(A:K), B:K) => error(A)
   rule transAsPat(A:K, error(B:K)) => error(B)
   rule transAsPat(A:K, B:K) => asPat(A, B) [owise]

   rule transPatBinAux(error(A:K), B:K, C:K) => error(A)
   rule transPatBinAux(A:K, error(B:K), C:K) => error(B)
   rule transPatBinAux(A:K, B:K, error(C:K)) => error(C)
   rule transPatBinAux(A:K, B:K, C:K) => appPat(A, ListItem(B) ListItem(C)) [owise]

   //trans negative pattern if variables of pattern is only local.
   rule transNegPat(Mod:K, 'binPattern(A:LPat,, B:QConOp,, C:Pat), Ts:Set, Is:Set)
          => transPatBinAux(transConstrVar(Mod, pillVar(B), Ts, Is),
                 transNegPat(Mod, A, Ts, Is), transNegPat(Mod, C, Ts, Is))
   rule transNegPat(Mod:K, 'minusPat(A:K), Ts:Set, Is:Set)
              =>  appPat(fullName(Prelude, funName('minusCon(.KList))), transLiteral(A))
   rule transNegPat(Mod:K, V:Var, Ts:Set, Is:Set) => addFunName(pillVar(V))
   rule transNegPat(Mod:K, V:Var @ A:APat, Ts:Set, Is:Set)
            => transAsPat(addFunName(pillVar(V)), transNegPat(Mod, A, Ts, Is))
   rule transNegPat(Mod:K, G:GCon, Ts:Set, Is:Set) => transExpCon(Mod, G, Ts, Is)
   rule transNegPat(Mod:K, 'lpatCon(G:GCon,, As:APatList), Ts:Set, Is:Set)
            => transPatLPatCon(transExpCon(
                   Mod, G, Ts, Is), transNegPatList(Mod, As, Ts, Is, .K, .List))
   rule transNegPat(Mod:K, 'underscore(.KList), Ts:Set, Is:Set) => unnamedVar
   rule transNegPat(Mod:K, A:Literal, Ts:Set, Is:Set) => transLiteral(A)
   rule transNegPat(Mod:K, 'recordPat(G:QCon,, Fs:FPats), Ts:Set, Is:Set)
           => transNegRecordPat(Mod, transExpCon(Mod, G, Ts, Is), Fs, Ts, Is)
   rule transNegPat(Mod:K, 'irrefutablePat(A:K), Ts:Set, Is:Set)
         => transPatIrreFut(transNegPat(Mod, A, Ts, Is))
   rule transNegPat(Mod:K, 'patList(A:K), Ts:Set, Is:Set)
          => transPatPatList(transNegPatList(Mod, A, Ts, Is, .K, .List))
   rule transNegPat(Mod:K, 'patTuple(A:K), Ts:Set, Is:Set)
          => transPatPatTuple(transNegPatList(Mod, A, Ts, Is, .K, .List))

   rule transNegRecordPat(Mod:K, error(A:K), Fs:K, Ts:Set, Is:Set) => error(A)
   rule transNegRecordPat(Mod:K, fullName(Mod':K, G:K), Fs:K, Ts:Set, Is:Set)
             => transNegRecordPatAux(Mod, fullName(Mod', G:K), Fs, Ts, Is, .K, .K, .List)

   rule transNegRecordPatAux(Mod:K, A:K, .FPats, Ts:Set, Is:Set, .K, .K, L:List)
           => appPat(A, ListItem(appPat(fullName(Prelude, constrName(recordParen(A))), L)))
   rule transNegRecordPatAux(Mod:K, fullName(Mod':K, G:K),
                  'fpatCon('recordConAssign(A:K,, B:K),, C:K), Ts:Set, Is:Set, .K, .K, L:List)
            => transNegRecordPatAux(Mod, fullName(Mod':K, G:K), C, Ts, Is,
                   transFunVar(Mod', A, .Set, Ts, Is), transNegPat(Mod, B, Ts, Is), L)
   rule transNegRecordPatAux(Mod:K, A:K, B:K, Ts:Set, Is:Set,
             error(X:K), Y:K, L:List) => error(X)
   rule transNegRecordPatAux(Mod:K, A:K, B:K, Ts:Set, Is:Set,
             X:K, error(Y:K), L:List) => error(Y)
   rule transNegRecordPatAux(Mod:K, A:K, B:K, Ts:Set, Is:Set, X:KItem, Y:KItem, L:List)
          => transNegRecordPatAux(Mod, A, B, Ts, Is, .K, .K,
              L ListItem(appPat(fullName(
              Prelude, constrName(recordAssign)), ListItem(X) ListItem(Y)))) [owise]

   rule transNegPatList(Mod:K, A:Pat, Ts:Set, Is:Set, .K, L:List)
              => transNegPatList(Mod, .K, Ts, Is, transNegPat(Mod, A, Ts, Is), L)
   rule transNegPatList(Mod:K, .K, Ts:Set, Is:Set, error(A:K), L:List) => error(A)
   rule transNegPatList(Mod:K, .K, Ts:Set, Is:Set, .K, L:List) => resultList(L)
   rule transNegPatList(Mod:K, Rest:K, Ts:Set, Is:Set, A:KItem, L:List)
            => transNegPatList(Mod, Rest, Ts, Is, .K, L ListItem(A))
        requires notBool isError(A)
   rule transNegPatList(Mod:K, 'twoPatTuple(A:K,, B:K), Ts:Set, Is:Set, .K, L:List)
             => transNegPatList(Mod, B, Ts, Is, transNegPat(Mod, A, Ts, Is), L)
   rule transNegPatList(Mod:K, 'patTupleCon(A:K,, B:K), Ts:Set, Is:Set, .K, L:List)
             => transNegPatList(Mod, B, Ts, Is, transNegPat(Mod, A, Ts, Is), L)
   rule transNegPatList(Mod:K, 'patListCon(A:K,, B:K), Ts:Set, Is:Set, .K, L:List)
             => transNegPatList(Mod, B, Ts, Is, transNegPat(Mod, A, Ts, Is), L)
   rule transNegPatList(Mod:K, 'apatCon(A:K,, B:K), Ts:Set, Is:Set, .K, L:List)
             => transNegPatList(Mod, B, Ts, Is, transNegPat(Mod, A, Ts, Is), L)

   //transform expressions. 
   syntax KItem ::= transExp(Int, K, K, Set, Set, Set) [function]
           //counter, curr-mod, exp, local-vars, types, imports
                  //group of functions to trans decls
                  | transDecls(Int, K, K, Set, Set, Set) [function]
                  | transDeclsAux(Int, K, DeclsList, K, List, Set, Set, Set) [function]
                  | transDecl(Int, K, K, Set, Set, Set) [function]
                  | transDeclDeclAux(Int, K, K, K) [function]
                  | transDeclDeclAux1(Int, K, K, K, K, Set, Set, Set) [function]
                  | transDeclDeclAux2(Int, K, K, Set, K) [function]
                  | transDeclAux(K, K) [function]
                 //trans rhs
                  | transRhs(Int, K, K, Set, Set, Set) [function]
                  | transRhsAux(K, K, K, Set, Set, Set) [function]
                  | transRhsAuxAux(K, K) [function]
                 // guards transformation
                  | transGuards(Int, K, K, K, List, Set, Set, Set) [function]
                  | transSingleGuard(Int, K, K, Set, Set, Set) [function]
                  | transGuard(Int, K, K, K, List, K, Set, Set, Set) [function]
                  | transExpFun(Int, K, List, K, List, Set, Set, Set) [function]
                  | transExpTuple(Int, K, K, K, K, List, Set, Set, Set)  [function]
                  | transExpList(Int, K, K, K, List, Set, Set, Set)  [function]
                  | transExpQVar(K, K) [function]
                  | transExpSeq1(K) [function]
                  | transExpSeq2NoEnd(K, K, K, Set, Set, Set) [function]
                  | transExpSeq2NoEndAux(K, K) [function]
                  | transExpSeq2HasEnd(K, K, K, Set, Set, Set) [function]
                  | transExpSeq2HasEndAux(K, K) [function]
                  | transExpSeq3(K, K, K, K, Set, Set, Set)    [function]
                  | transExpSeq3Aux(K, K, K, K, Set, Set, Set) [function]
                  | transExpSeq3AuxAux(K, K, K) [function]
                  | transExpListCompre(Int, K, List, K, List, K, Set, Set, Set) [function]
                  | transQual(Int, K, K, Set, Set, Set) [function]
                      //counter,curr-mod, qual,
                      // free-var-possible, local-vars, types, imports
                  | transQualPat(K, K) [function]
                  | transQualLet(K)    [function]
                  | transVar(K, K, Set, Set, Set) [function]
                  | transLeftSection(K, K) [function]
                  | transRightSection(K, K) [function]
                  | transExpRecord(Int, K, AExp, FBindList, Set, Set, Set) [function]
                  | transExpRecordAux(K, K, K, Set, Set, Set)  [function]
                  | transExpRecordAuxAux(K, K)                 [function]
                  | transExpRecordAuxAux1(K, K)                [function]
                  | transFBindList(Int, K, FBindList, K, K, List, Set, Set, Set) [function]
                 //Counter, curr-mod, flag, FBindList, curr-buf1,buf2, stored
                 //counter, pat, curr-mod, quals, buf, stored
                  | transLambda(K, K) [function]
                  //helper functions for let in
                  | transLetIn(K, K, K, Set, Set, Set) [function]
                  | transLetInAux(List, K) [function]
                  //helper functions for if statements
                  | transExpIf(K, K, K, K, Set, Set, Set)    [function]
                  | transExpIfAux(K, K, K, K, Set, Set, Set) [function]
                  | transExpIfAuxAux(K, K, K)                [function]
                  //helper functions for case of
                  | transExpCase(K, K, K, Set, Set, Set) [function]
                  | transExpAlts(K, Int, K, K, K, List, Set, Set, Set) [function]
                  | transExpAlt(K, K, K, Set, Set, Set) [function]
                  | transExpAltAux2(K, K) [function]
                  | transExpAltAux(K, K, K, K, Set, Set, Set) [function]
                  | transExpAltAuxAux(K, K, K) [function]
                  //helper funtions for do stmt
                  | transExpDo(Int, K, K, K, List, K, Set, Set, Set) [function]
                  | transSingleDo(Int, K, K, Set, Set, Set) [function]
                  | transExpMinus(K) [function]
                  | transExpInfix(K, K, K, K, Set, Set, Set) [function]
                  | transExpInfixAux(K, K, K) [function]
                  | transExpAssign(K, K) [function]
                  | transExpAssignContext(K, K, K, K, Set, Set) [function]
                  | transExpAssignContextAux(K, K, Set, K) [function]

   //trans Decls
   rule transDecls(N:Int, Mod:K, 'emptyOptDecls(.KList), Ls:Set, Ts:Set, Is:Set)
            => resultTransList(N, .List)
   rule transDecls(N:Int, Mod:K, 'whereDecls(Ds:K), Ls:Set, Ts:Set, Is:Set)
           => transDecls(N, Mod, Ds, Ls, Ts, Is)
   rule transDecls(N:Int, Mod:K, 'decls(Ds:DeclsList), Ls:Set, Ts:Set, Is:Set)
           => transDeclsAux(N, Mod, Ds, .K, .List, getFreeVarsInDefs(Ds) Ls, Ts, Is)
        requires (getFreeVarsInDecls(Ds) <=Set getFreeVarsInDefs(Ds))
   rule transDecls(N:Int, Mod:K, 'decls(Ds:K), Ls:Set, Ts:Set, Is:Set)
          => error(funNameDeclNotDef)
        requires notBool (getFreeVarsInDecls(Ds) <=Set getFreeVarsInDefs(Ds))

   rule transDeclsAux(N:Int, Mod:K, .DeclsList, .K, L:List, Ls:Set, Ts:Set, Is:Set)
           => resultTransList(N, L)
   rule transDeclsAux(N:Int, Mod:K, 'declsCon(D:Decl,, Ds:DeclsList),
                     .K, L:List, Ls:Set, Ts:Set, Is:Set)
           => transDeclsAux(N, Mod, Ds, transDecl(N, Mod, D, Ls, Ts, Is), L, Ls, Ts, Is)
   rule transDeclsAux(N:Int, Mod:K, Ds:DeclsList, error(A:K),
             L:List, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transDeclsAux(N:Int, Mod:K, Ds:DeclsList, resultTransList(N':Int, A:List),
             L:List, Ls:Set, Ts:Set, Is:Set)
             => transDeclsAux(N', Mod, Ds, .K, L A, Ls:Set, Ts:Set, Is:Set)

   rule transDecl(N:Int, Mod:K, 'emptyGenDecl(.KList), Ls:Set, Ts:Set, Is:Set)
               => resultTransList(N, .List)
   rule transDecl(N:Int, Mod:K, 'varAssign(A:Vars,, B:Type), Ls:Set, Ts:Set, Is:Set)
         => transDeclDeclAux(N, Mod, A,
                    toAbsTypeWithAll(Mod, B, .Set, getFreeTypeVars(B), Ts, Is))
   rule transDecl(N:Int, Mod:K, 'genAssignContext(A:Vars,,
                  C:Context,, B:Type), Ls:Set, Ts:Set, Is:Set)
         => transDeclDeclAux1(N, Mod, A, contextToSet(Mod, C,
                  .K, .Set, Ts, Is), B, Ls:Set, Ts:Set, Is:Set)
   rule transDecl(N:Int, Mod:K, 'declFunLhsRhs(A:FunLhs,, B:Rhs), Ls:Set, Ts:Set, Is:Set)
         => transDeclAux(transNegFunLhs(Mod, A, Ts, Is),
                       transRhs(N, Mod, B, getBoundVarsInPat(A) Ls, Ts, Is))
        requires hasNoConflictAllVars(A)
   rule transDecl(N:Int, Mod:K, 'declFunLhsRhs(A:FunLhs,, B:Rhs), Ls:Set, Ts:Set, Is:Set)
         => error(funNameConflicting)
        requires notBool hasNoConflictAllVars(A)
   rule transDecl(N:Int, Mod:K, 'declPatRhs(A:Pat,, B:Rhs), Ls:Set, Ts:Set, Is:Set)
         => transDeclAux(transNegFunLhs(Mod, A, Ts, Is), transRhs(N, Mod, B, Ls, Ts, Is))
        requires hasNoConflictVars(A)
   rule transDecl(N:Int, Mod:K, 'declPatRhs(A:Pat,, B:Rhs), Ls:Set, Ts:Set, Is:Set)
         => error(funNameConflicting)
        requires notBool hasNoConflictVars(A)

   rule transDeclDeclAux(N:Int, Mod:K, A:K, error(B:K)) => error(B)
   rule transDeclDeclAux(N:Int, Mod:K, A:K, B:K)
             => resultTransList(N, genDeclForVars(Mod, A, .Set, B)) [owise]

   rule transDeclDeclAux1(N:Int, Mod:K, A:K,
                  error(C:K), B:K, Ls:Set, Ts:Set, Is:Set) => error(C)
   rule transDeclDeclAux1(N:Int, Mod:K, A:K,
                      resultSet(S:Set), B:K, Ls:Set, Ts:Set, Is:Set)
           => transDeclDeclAux2(N, Mod, A, S,
                    toAbsTypeWithAll(Mod, B, .Set, getFreeTypeVars(B), Ts, Is))

   rule transDeclDeclAux2(N:Int, Mod:K, A:K, S:Set, error(T:K)) => error(T)
   rule transDeclDeclAux2(N:Int, Mod:K, A:K, S:Set, T:K)
           => resultTransList(N, genDeclForVars(Mod, A, S, T)) [owise]

   rule transDeclAux(error(A:K), error(B:K)) => error(A)
   rule transDeclAux(A:K, error(B:K)) => error(B)
   rule transDeclAux(funPat(ListItem(X:K) L:List), resultTrans(N:Int, B:K))
                => resultTransList(N, ListItem(funAssign(X, L, B))) [owise]

   //trans rhs 
   rule transRhs(N:Int, Mod:K, 'normalRhs(A:Exp,, B:OptDecls), Ls:Set, Ts:Set, Is:Set)
          => transRhsAux(transExp(N, Mod, A, Ls, Ts, Is), Mod, B, Ls, Ts, Is)
   rule transRhs(N:Int, Mod:K, 'guardRhs(A:GdRhs,, B:OptDecls), Ls:Set, Ts:Set, Is:Set)
          => transRhsAux(transGuards(N, Mod,
                        A, .K, .List, Ls, Ts, Is), Mod, B, Ls:Set, Ts:Set, Is:Set)

   rule transRhsAux(error(A:K), Mod:K, B:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transRhsAux(resultTrans(N:Int, A:K), Mod:K, B:K, Ls:Set, Ts:Set, Is:Set)
           => transRhsAuxAux(A, transDecls(N, Mod, B, Ls, Ts, Is))

   rule transRhsAuxAux(A:K, error(B:K)) => error(B)
   rule transRhsAuxAux(A:K, resultTransList(N:Int, B:List))
           => resultTrans(N, body(A, B))

   //trans guards in rhs
   rule transSingleGuard(N:Int, Mod:K, A:InfixExp, Ls:Set, Ts:Set, Is:Set)
            => transQual(N, Mod, A, Ls, Ts, Is)
   rule transSingleGuard(N:Int, Mod:K, 'guardAssign(A:K,, B:K), Ls:Set, Ts:Set, Is:Set)
            => transQual(N, Mod, 'qualAssign(A,, B), Ls, Ts, Is)
   rule transSingleGuard(N:Int, Mod:K, 'guardLet(A:K), Ls:Set, Ts:Set, Is:Set)
            => transQual(N, Mod, 'qualLet(A), Ls, Ts, Is)

   rule transGuards(N:Int, Mod:K, .K, .K, L:List, Ls:Set, Ts:Set, Is:Set)
            => resultTrans(N, guards(L))
   rule transGuards(N:Int, Mod:K, X:K, error(B:K), L:List,
           Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transGuards(N:Int, Mod:K, X:K, resultTrans(N':K, B:K), L:List,
           Ls:Set, Ts:Set, Is:Set)
          => transGuards(N', Mod, X, .K, L ListItem(B), Ls, Ts, Is)
   rule transGuards(N:Int, Mod:K, 'guardSingle('startGuardCons(G:GuardList),,
                E:Exp), .K, L:List, Ls:Set, Ts:Set, Is:Set)
          => transGuards(N, Mod, .K, transGuard(N,
                     Mod, G, .K, .List, E, Ls, Ts, Is), L, Ls, Ts, Is)
   rule transGuards(N:Int, Mod:K, 'guardCon('startGuardCons(G:GuardList),,
              E:Exp,, Gs:GdRhs), .K, L:List, Ls:Set, Ts:Set, Is:Set)
          => transGuards(N, Mod, Gs, transGuard(N,
                     Mod, G, .K, .List, E, Ls, Ts, Is), L, Ls, Ts, Is)

   rule transGuard(N:Int, Mod:K, .K, resultTrans(N':Int, A:K),
              L:List, .K, Ls:Set, Ts:Set, Is:Set) => resultTrans(N',formDoCons(L, A))
   rule transGuard(N:Int, Mod:K, A:K, error(B:K),
              L:List, E:K, Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transGuard(N:Int, Mod:K, .K, .K,
              L:List, E:Exp, Ls:Set, Ts:Set, Is:Set)
         => transGuard(N, Mod, .K, transExp(N,
                     Mod, E, Ls, Ts, Is), L, .K, Ls, Ts, Is)
   rule transGuard(N:Int, Mod:K, G:Guard, .K,
              L:List, E:K, Ls:Set, Ts:Set, Is:Set)
         => transGuard(N:Int, Mod:K, .K, transSingleGuard(
             N, Mod, G, Ls, Ts, Is), L, E, getFreeVarsInDefs(G) Ls, Ts, Is)
   rule transGuard(N:Int, Mod:K, 'guardListCon(G:Guard,, Gs:GuardList), .K,
              L:List, E:K, Ls:Set, Ts:Set, Is:Set)
         => transGuard(N:Int, Mod:K, Gs, transSingleGuard(
             N, Mod, G, Ls, Ts, Is), L, E, getFreeVarsInDefs(G) Ls, Ts, Is)
   rule transGuard(N:Int, Mod:K, A:K, resultTrans(N':Int, B:K),
              L:List, E:Exp, Ls:Set, Ts:Set, Is:Set)
         => transGuard(N', Mod, A, .K, L ListItem(B), E, Ls, Ts, Is)

   //transform variable/constrs, and exps
   rule transVar(Mod:K, fullName(A:K, B:K), Ls:Set, Ts:Set, Is:Set)
            => transFunVar(Mod, fullName(A:K, B:K), Ls, Ts, Is)
        requires isFunVar(B)
   rule transVar(Mod:K, A:K, Ls:Set, Ts:Set, Is:Set)
            => transFunVar(Mod, A, Ls, Ts, Is)
        requires isFunVar(A)
   rule transVar(Mod:K, fullName(A:K, B:K), Ls:Set, Ts:Set, Is:Set)
            => transExpCon(Mod, fullName(A:K, B:K), Ts, Is)
        requires notBool isFunVar(B)
   rule transVar(Mod:K, A:K, Ls:Set, Ts:Set, Is:Set)
            => transExpCon(Mod, A, Ts, Is)
        requires notBool isFunVar(A)

   rule transExp(C:Int, Mod:K, A:QVar, Ls:Set, Ts:Set, Is:Set)
            => transExpQVar(C, transFunVar(Mod, pillVar(A), Ls, Ts, Is))
   rule transExp(C:Int, Mod:K, A:GCon, Ls:Set, Ts:Set, Is:Set)
            => transExpQVar(C, transConstrVar(Mod, pillVar(A), Ts, Is))
   rule transExp(C:Int, Mod:K, A:Literal, Ls:Set, Ts:Set, Is:Set)
             => resultTrans(C, transLiteral(A))
   rule transExp(C:Int, Mod:K, 'funApp(A:K,, B:K), Ls:Set, Ts:Set, Is:Set)
             => transExpFun(C, Mod, ListItem(A) ListItem(B), .K, .List, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'expTuple(As:ExpTuple), Ls:Set, Ts:Set, Is:Set)
          => transExpTuple(N, Mod, fullName(Prelude, constrName(tupleType(
                       countOnTypeTuple(As)))), As, .K, .List, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'expList(As:ExpList), Ls:Set, Ts:Set, Is:Set)
               => transExpList(N, Mod, As, .K, .List, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'expSeq(E1:Exp,,
          'emptyExpComma(.KList),, 'emptyExp(.KList)), Ls:Set, Ts:Set, Is:Set)
           => transExpSeq1(transExp(N:Int, Mod, E1, Ls, Ts, Is))
   rule transExp(N:Int, Mod:K, 'expSeq(E1:Exp,,
               'dotExp(E2:Exp),, 'emptyExp(.KList)), Ls:Set, Ts:Set, Is:Set)
         => transExpSeq2NoEnd(transExp(N:Int, Mod, E1, Ls, Ts, Is), Mod, E2, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'expSeq(E1:Exp,,
               'emptyExpComma(.KList),, E3:Exp), Ls:Set, Ts:Set, Is:Set)
         => transExpSeq2HasEnd(transExp(N:Int, Mod, E1, Ls, Ts, Is), Mod, E3, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'listComprehension(
                     E1:Exp,, Qs:Quals), Ls:Set, Ts:Set, Is:Set)
         => transExpListCompre(N, Mod, qualsToList(Qs), .K, .List, E1, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'recordExp(A:AExp,, Fs:FBindList), Ls:Set, Ts:Set, Is:Set)
            => transExpRecord(N:Int, Mod, A, Fs, Ls:Set, Ts:Set, Is:Set)
   rule transExp(N:Int, Mod:K, 'lambdaExp(As:APatList,, B:Exp), Ls:Set, Ts:Set, Is:Set)
         => transLambda(transNegPatList(Mod, As, Ts, Is, .K, .List),
                     transExp(N, Mod, B, getFreeVarsInPat(As) Ls, Ts, Is))
        requires hasNoConflictVars(As)
   rule transExp(N:Int, Mod:K, 'lambdaExp(As:APatList,, B:Exp), Ls:Set, Ts:Set, Is:Set)
         => error(funNameConflicting)
        requires notBool hasNoConflictVars(As)
   rule transExp(N:Int, Mod:K, 'letInExp(As:Decls,, B:Exp), Ls:Set, Ts:Set, Is:Set)
           => transLetIn(transDecls(N, Mod, As, Ls, Ts, Is), Mod, B,
                         getFreeVarsInPat(As) Ls:Set, Ts:Set, Is:Set)
   rule transExp(N:Int, Mod:K, 'ifElseExp(A:Exp,, Op1:OptSemicolon,,
               B:Exp,, Op2:OptSemicolon,, C:Exp), Ls:Set, Ts:Set, Is:Set)
          => transExpIf(transExp(N, Mod, A, Ls, Ts, Is), Mod, B, C, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'caseExp(A:Exp,, Bs:Alts), Ls:Set, Ts:Set, Is:Set)
          =>  transExpCase(transExp(N, Mod, A, Ls, Ts, Is), Mod, Bs, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'doExp(
            'stmtMain(A:StmtList,, B:Exp,, C:OptSemicolon)), Ls:Set, Ts:Set, Is:Set)
           => transExpDo(N, Mod, A, .K, .List, B, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'minusInfix(E:InfixExp), Ls:Set, Ts:Set, Is:Set)
            => transExpMinus(transExp(N, Mod, E, Ls:Set, Ts:Set, Is:Set))
   rule transExp(N:Int, Mod:K, 'binInfixExp(
                     A:LExp,, G:QOp,, B:InfixExp), Ls:Set, Ts:Set, Is:Set)
          => transExpInfix(transVar(Mod, pillVar(G), Ls, Ts, Is),
                transExp(N, Mod, A, Ls, Ts, Is), Mod, B, Ls, Ts, Is)
   rule transExp(N:Int, Mod:K, 'expAssign(E:Exp,, T:Type), Ls:Set, Ts:Set, Is:Set)
             => transExpAssign(transExp(N, Mod, E, Ls, Ts, Is),
                       toAbsType(Mod, T, .Set, Ts, Is))
   rule transExp(N:Int, Mod:K, 'expAssignContext(
                     E:Exp,, C:Context,, T:Type), Ls:Set, Ts:Set, Is:Set)
             => transExpAssignContext(transExp(N, Mod, E, Ls, Ts, Is),
                  contextToSet(Mod, C, .K, .Set, Ts, Is), Mod, T, Ts, Is)

   //trans exp with types
   rule transExpAssign(A:K, error(T:K)) => error(T)
   rule transExpAssign(error(A:K), T:K) => error(A)
   rule transExpAssign(resultTrans(N:Int, A:K), T:K)
            => resultTrans(N, typedExp(.Set, T, A)) [owise]

   rule transExpAssignContext(error(A:K), S:K, Mod:K, T:K, Ts:Set, Is:Set) => error(A)
   rule transExpAssignContext(A:K, error(S:K), Mod:K, T:K, Ts:Set, Is:Set) => error(S)
   rule transExpAssignContext(resultTrans(N:Int, A:K),
                      resultSet(S:Set), Mod:K, T:K, Ts:Set, Is:Set)
            => transExpAssignContextAux(N, A, S, toAbsType(Mod, T, S, Ts, Is))
   rule transExpAssignContextAux(N:Int, A:K, S:Set, error(B:K)) => error(B)
   rule transExpAssignContextAux(N:Int, A:K, S:Set, T:K) 
           => resultTrans(N, typedExp(S, T, A)) [owise]

   //transform infix ops
   rule transExpInfix(error(A:K), B:K, Mod:K, C:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpInfix(A:K, error(B:K), Mod:K, C:K, Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transExpInfix(A:K, resultTrans(N:Int, B:K), Mod:K, C:K, Ls:Set, Ts:Set, Is:Set)
          => transExpInfixAux(A, B, transExp(N, Mod, C, Ls, Ts, Is))
        requires notBool isError(A)
   rule transExpInfixAux(A:K, B:K, error(C:K)) => error(C)
   rule transExpInfixAux(A:K, B:K, resultTrans(N:Int, C:K))
           => resultTrans(N, appExp(A, ListItem(appExp(B, ListItem(C)))))

   //trans minus infix exp
   rule transExpMinus(error(A:K)) => error(A)
   rule transExpMinus(resultTrans(N:Int, A:K))
           => resultTrans(N, appExp(fullName(Prelude, funName('minusCon(.KList))), ListItem(A)))

   //trans do stmt
   rule transSingleDo(N:Int, Mod:K, 'expStmt(A:Exp), Ls:Set, Ts:Set, Is:Set)
            => transQual(N, Mod, A, Ls, Ts, Is)
   rule transSingleDo(N:Int, Mod:K, 'patExpStmt(A:Pat,, B:Exp), Ls:Set, Ts:Set, Is:Set)
            => transQual(N, Mod, 'qualAssign(A,, B), Ls, Ts, Is)
   rule transSingleDo(N:Int, Mod:K, 'letStmt(A:K), Ls:Set, Ts:Set, Is:Set)
            => transQual(N, Mod, 'qualLet(A), Ls, Ts, Is)
   rule transSingleDo(N:Int, Mod:K, 'emptyAlt(.KList), Ls:Set, Ts:Set, Is:Set)
            => none

   rule transExpDo(N:Int, Mod:K, A:K, error(B:K), L:List, C:K,
            Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transExpDo(N:Int, Mod:K, A:K, none, L:List, C:K,
            Ls:Set, Ts:Set, Is:Set) => transExpDo(N, Mod, A, .K, L, C, Ls, Ts, Is)
   rule transExpDo(N:Int, Mod:K, .StmtList, resultTrans(N':Int, B:K), L:List, .K,
            Ls:Set, Ts:Set, Is:Set) => resultTrans(N', formDoCons(L, B))
   rule transExpDo(N:Int, Mod:K, .StmtList, .K, L:List, B:Exp, Ls:Set, Ts:Set, Is:Set)
           => transExpDo(N, Mod, .StmtList, transExp(N, Mod, B, Ls, Ts, Is), L, .K, Ls, Ts, Is)
   rule transExpDo(N:Int, Mod:K, 'stmtCon(S:K,, SL:K),
                    .K, L:List, B:Exp, Ls:Set, Ts:Set, Is:Set)
           => transExpDo(N, Mod, SL, transSingleDo(N, Mod, S, Ls, Ts, Is), L,
                       .K, getFreeVarsInDefs(S) Ls, Ts, Is)
   rule transExpDo(N:Int, Mod:K, SL:K, resultTrans(N':Int, A:K),
                 L:List, B:K, Ls:Set, Ts:Set, Is:Set)
          => transExpDo(N', Mod, SL, .K, L ListItem(A), B, Ls, Ts, Is)

   //trans lambdaexp 
   rule transLambda(error(L:K), A:K) => error(L)
   rule transLambda(L:K, error(A:K)) => error(A)
   rule transLambda(resultList(L:List), resultTrans(N:Int, A:K))
            => resultTrans(N, formLambdaList(L, A))

   //trans let term
   rule transLetIn(error(A:K), Mod:K, B:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transLetIn(resultTransList(N:Int, A:List), Mod:K, B:K, Ls:Set, Ts:Set, Is:Set)
          => transLetInAux(A, transExp(N, Mod, B, Ls, Ts, Is))
   rule transLetInAux(As:List, error(B:K)) => error(B)
   rule transLetInAux(As:List, resultTrans(N:Int, B:K))
             => resultTrans(N, letIn(As, B))

   //trans if statement
   rule transExpIf(error(A:K), Mod:K, B:K, C:K,  Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpIf(resultTrans(N:Int, A:K), Mod:K, B:K, C:K, Ls:Set, Ts:Set, Is:Set)
         => transExpIfAux(A, transExp(
                  N, Mod, B, Ls, Ts, Is), Mod, C, Ls:Set, Ts:Set, Is:Set)
   rule transExpIfAux(A:K, error(B:K), Mod:K, C:K, Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transExpIfAux(A:K, resultTrans(N:Int, B:K), Mod:K, C:K, Ls:Set, Ts:Set, Is:Set)
           => transExpIfAuxAux(A, B, transExp(N, Mod, C, Ls, Ts, Is))
   rule transExpIfAuxAux(A:K, B:K, error(C:K)) => error(C)
   rule transExpIfAuxAux(A:K, B:K, resultTrans(N:Int, C:K))
         => resultTrans(N, ifElse(A, B, C))

   //trans case analysis
   rule transExpCase(error(A:K), Mod:K, Bs:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpCase(resultTrans(N:Int, A:K), Mod:K, Bs:K, Ls:Set, Ts:Set, Is:Set)
           => transExpAlts(A, N, Mod, Bs, .K, .List, Ls:Set, Ts:Set, Is:Set)
   
   rule transExpAlts(A:K, N:Int, Mod:K, .K, .K, L:List, Ls:Set, Ts:Set, Is:Set)
          => resultTrans(N, caseOf(A, L))
   rule transExpAlts(A:K, N:Int, Mod:K, B:Alt, .K, L:List, Ls:Set, Ts:Set, Is:Set)
          => transExpAlts(A, N, Mod, .K,
                  transExpAlt(N, Mod, B, Ls, Ts, Is), L, Ls:Set, Ts:Set, Is:Set)
   rule transExpAlts(A:K, N:Int, Mod:K,
                    'altCon(B:Alt,, Bs:Alts), .K, L:List, Ls:Set, Ts:Set, Is:Set)
          => transExpAlts(A, N, Mod, Bs, transExpAlt(N, Mod, B, Ls,Ts, Is), L, Ls, Ts, Is)
   rule transExpAlts(A:K, N:Int, Mod:K, Bs:K,
                   error(B:K), L:List, Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transExpAlts(A:K, N:Int, Mod:K, Bs:K,
                resultTransList(N':Int, B:List), L:List, Ls:Set, Ts:Set, Is:Set)
           => transExpAlts(A, N', Mod, Bs, .K, L B, Ls, Ts, Is)

   rule transExpAlt(N:Int, Mod:K, 'altArrow(A:Pat,, B:Exp), Ls:Set, Ts:Set, Is:Set)
           => transExpAltAux2(transNegPat(Mod, A, Ts, Is),
                 transExp(N, Mod, B, getFreeVarsInPat(A) Ls, Ts, Is))
        requires hasNoConflictVars(A)
   rule transExpAlt(N:Int, Mod:K, 'altArrow(A:Pat,, B:Exp), Ls:Set, Ts:Set, Is:Set)
           => error(funNameConflicting)
        requires notBool hasNoConflictVars(A)
   rule transExpAlt(N:Int, Mod:K, 'emptyAlt(.KList), Ls:Set, Ts:Set, Is:Set)
             => resultTransList(N, .List)
   rule transExpAlt(N:Int, Mod:K, 'altArrow(A:Pat,, B:Exp,, C:Decls), Ls:Set, Ts:Set, Is:Set)
          => transExpAltAux(transNegPat(Mod,A, Ts, Is),
           transExp(N, Mod, B, getFreeVarsInPat(A)
                 getFreeVarsInDefs(C) Ls, Ts, Is), Mod, C, getFreeVarsInPat(A) Ls, Ts, Is)
        requires hasNoConflictVars(A)
   rule transExpAlt(N:Int, Mod:K, 'altArrow(A:Pat,, B:Exp,, C:Decls), Ls:Set, Ts:Set, Is:Set)
          => error(funNameConflicting)
        requires notBool hasNoConflictVars(A)

   rule transExpAltAux2(error(A:K), B:K) => error(A)
   rule transExpAltAux2(A:K, error(B:K)) => error(B)
   rule transExpAltAux2(A:K, resultTrans(N:Int, B:K))
                 => resultTransList(N, ListItem(singleCase(A, B, .List))) [owise]

   rule transExpAltAux(error(A:K), B:K, Mod:K, C:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpAltAux(A:K, error(B:K), Mod:K, C:K, Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transExpAltAux(A:K, resultTrans(N:Int, B:K), Mod:K, C:K, Ls:Set, Ts:Set, Is:Set)
          => transExpAltAuxAux(A, B, transDecls(N, Mod, C, Ls, Ts, Is)) [owise]
   rule transExpAltAuxAux(A:K, B:K, error(C:K)) => error(C)
   rule transExpAltAuxAux(A:K, B:K, resultTransList(N:Int, C:List))
          => resultTransList(N, ListItem(singleCase(A, B, C)))

   //trans records, two different things. labeled update and label pattern
   rule transExpRecord(N:Int, Mod:K, Q:QCon, Fs:FBindList, Ls:Set, Ts:Set, Is:Set)
           => transExpRecordAuxAux(transExpCon(Mod, Q, Ts:Set, Is:Set),
            transFBindList(N, Mod, Fs, .K, .K, .List, Ls, Ts, Is))
   rule transExpRecord(N:Int, Mod:K, A:AExp, Fs:FBindList, Ls:Set, Ts:Set, Is:Set)
           => transExpRecordAux(transExp(N, Mod, A, Ls, Ts, Is), Mod, Fs, Ls, Ts, Is)
        requires notBool isTheQCon(A) andBool fbSize(Fs) >Int 0
   rule transExpRecord(N:Int, Mod:K, A:AExp, Fs:FBindList, Ls:Set, Ts:Set, Is:Set)
           => error(syntaxError) [owise]

   rule transExpRecordAux(error(A:K), Mod:K, B:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpRecordAux(resultTrans(N:Int, A:K), Mod:K, B:K, Ls:Set, Ts:Set, Is:Set)
          => transExpRecordAuxAux1(A, transFBindList(N,
                        Mod, B, .K, .K, .List, Ls, Ts, Is))

   rule transExpRecordAuxAux1(error(A:K), B:K) => error(A)
   rule transExpRecordAuxAux1(A:K, error(B:K)) => error(B)
   rule transExpRecordAuxAux1(A:K, resultTransList(N:Int, L:List))
           => resultTrans(N, appExp(fullName(Prelude, funName(recordUpdate)), L)) [owise]

   rule transExpRecordAuxAux(error(A:K), B:K) => error(A)
   rule transExpRecordAuxAux(A:K, error(B:K)) => error(B)
   rule transExpRecordAuxAux(A:K, resultTransList(N:Int, L:List))
           => resultTrans(N, appExp(fullName(Prelude, constrName(recordParen(A))), L)) [owise]

   rule transFBindList(N:Int, Mod:K, .FBindList, .K, .K, L:List, Ls:Set, Ts:Set, Is:Set)
           => resultTransList(N, L)
   rule transFBindList(N:Int, Mod:K, 'fbCon('fbConAssign(
                A:QVar,, B:Exp),, C:FBindList), .K, .K, L:List, Ls:Set, Ts:Set, Is:Set)
          => transFBindList(N, Mod, C, transFunVar(Mod, A, .Set, Ts, Is),
                     transExp(N, Mod, B, Ls, Ts, Is), L, Ls:Set, Ts:Set, Is:Set)
   rule transFBindList(N:Int, Mod:K, C:FBindList,
                  error(X:K), B:K, L:List, Ls:Set, Ts:Set, Is:Set) => error(X)
   rule transFBindList(N:Int, Mod:K, C:FBindList,
                    X:K, error(B:K), L:List, Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transFBindList(N:Int, Mod:K, C:FBindList,
               X:K, resultTrans(N':Int, A:K), L:List, Ls:Set, Ts:Set, Is:Set)
          => transFBindList(N', Mod, C, .K, .K, L ListItem(appExp(
                fullName(Prelude, constrName(recordAssign)),
                     ListItem(X) ListItem(A))), Ls:Set, Ts:Set, Is:Set)


   //trans list comprehension
   //haskell list comprehension == [S | S1, ... Sn] -> [ [ [... S | Sn...] | S3] | S2] | S1]
   rule transExpListCompre(N:Int, Mod:K, .List, resultTrans(N':Int, A:K),
              L:List, .K, Ls:Set, Ts:Set, Is:Set)
             => resultTrans(N', formListCompre(A, L))
   rule transExpListCompre(N:Int, Mod:K, L1:List, error(A:K),
                   L2:List, B:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpListCompre(N:Int, Mod:K, L1:List, resultTrans(N':Int, A:K),
                   L2:List, B:Exp, Ls:Set, Ts:Set, Is:Set)
            => transExpListCompre(N', Mod, L1, .K, L2 ListItem(A), B, Ls, Ts, Is)
   rule transExpListCompre(N:Int, Mod:K, ListItem(A:K) L1:List,
                  .K, L2:List, E1:K, Ls:Set, Ts:Set, Is:Set)
             => transExpListCompre(N, Mod, L1,
                      transQual(N, Mod, A, Ls, Ts, Is),
                      L2, E1, getFreeVarsInDefs(A) Ls, Ts, Is)
   rule transExpListCompre(N:Int, Mod:K, .List,
                  .K, L2:List, E1:K, Ls:Set, Ts:Set, Is:Set)
             => transExpListCompre(N, Mod, .List,
                      transExp(N, Mod, E1, Ls, Ts, Is), L2, .K, Ls, Ts, Is)

   rule transQual(N:Int, Mod:K, 'qualAssign(A:Pat,, B:Exp), Ls:Set, Ts:Set, Is:Set)
         => transQualPat(transNegPat(Mod, A, Ts, Is),
                       transExp(N, Mod, B, Ls, Ts, Is))
        requires hasNoConflictVars(A)
   rule transQual(N:Int, Mod:K, 'qualAssign(A:Pat,, B:Exp), Ls:Set, Ts:Set, Is:Set)
         => error(funNameConflicting)
        requires notBool hasNoConflictVars(A)

   rule transQualPat(error(A:K), B:K) => error(A)
   rule transQualPat(A:K, error(B:K)) => error(B)
   rule transQualPat(A:K, resultTrans(N':Int, B:K))
           => resultTrans(N', appExp(fullName(Prelude, constrName(leftArrow)),
                           ListItem(A) ListItem(B))) [owise]

   rule transQual(N:Int, Mod:K,'qualLet(A:Decls), Ls:Set, Ts:Set, Is:Set)
         => transQualLet(transDecls(N, Mod, A, Ls, Ts, Is))
   rule transQualLet(error(A:K)) => error(A)
   rule transQualLet(resultTransList(N:Int, B:List))
         => resultTrans(N, letStmt(B))
   rule transQual(N:Int, Mod:K, A:Exp, Ls:Set, Ts:Set, Is:Set)
            => transExp(N, Mod, A, Ls, Ts, Is)

   //trans exp sequence1
   rule transExpSeq1(error(A:K)) => error(A)
   rule transExpSeq1(resultTrans(N:Int, A:K))
          => resultTrans(N, appExp(fullName(Prelude, arithSeq1), ListItem(A)))

   //trans exp seq2 without end
   rule transExpSeq2NoEnd(error(A:K), Mod:K, E2:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpSeq2NoEnd(resultTrans(N:Int, A:K), Mod:K, E2:K, Ls:Set, Ts:Set, Is:Set)
            => transExpSeq2NoEndAux(A, transExp(N, Mod, E2, Ls, Ts, Is))
   rule transExpSeq2NoEndAux(A:K, error(B:K)) => error(B)
   rule transExpSeq2NoEndAux(A:K, resultTrans(N:Int, B:K))
          => resultTrans(N, appExp(fullName(Prelude, arithSeq2noEnd),
                   ListItem(A) ListItem(B)))

   //trans exp seq2 has end
   rule transExpSeq2HasEnd(error(A:K), Mod:K, E2:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpSeq2HasEnd(resultTrans(N:Int, A:K), Mod:K, E2:K, Ls:Set, Ts:Set, Is:Set)
            => transExpSeq2HasEndAux(A, transExp(N, Mod, E2, Ls, Ts, Is))
   rule transExpSeq2HasEndAux(A:K, error(B:K)) => error(B)
   rule transExpSeq2HasEndAux(A:K, resultTrans(N:Int, B:K))
          => resultTrans(N, appExp(fullName(Prelude, arithSeq2hasEnd),
                   ListItem(A) ListItem(B)))

   //trans exp seq3
   rule transExp(N:Int, Mod:K, 'expSeq(E1:Exp,,
               'dotExp(E2:Exp),, E3:Exp), Ls:Set, Ts:Set, Is:Set)
         => transExpSeq3(transExp(N, Mod, E1, Ls, Ts, Is), Mod, E2, E3, Ls, Ts, Is)
   rule transExpSeq3(error(A:K), Mod, B:K, C:K, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpSeq3(resultTrans(N:Int, A:K), Mod, B:K, C:K, Ls:Set, Ts:Set, Is:Set)
           => transExpSeq3Aux(A, transExp(N, Mod, B, Ls, Ts, Is), Mod, C, Ls, Ts, Is)
   rule transExpSeq3Aux(A:K, error(B:K), Mod:K, C:K, Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transExpSeq3Aux(A:K, resultTrans(N:Int, B:K), Mod:K, C:K, Ls:Set, Ts:Set, Is:Set)
          => transExpSeq3AuxAux(A, B, transExp(N, Mod, C, Ls, Ts, Is))
   rule transExpSeq3AuxAux(A:K, B:K, error(C:K)) => error(C)
   rule transExpSeq3AuxAux(A:K, B:K, resultTrans(N:Int, C:K))
            => resultTrans(N, appExp(fullName(Prelude, arithSeq3), ListItem(A)
                      ListItem(B) ListItem(B)))

   //trans exp list
   rule transExpList(N:Int, Mod:K, .K, .K, L:List, Ls:Set, Ts:Set, Is:Set)
           => resultTrans(N, formExpList(L))
   rule transExpList(N:Int, Mod:K, A:Exp, .K, L:List, Ls:Set, Ts:Set, Is:Set)
            => transExpList(N, Mod, .K,
                transExp(N, Mod, A, Ls, Ts, Is), L, Ls:Set, Ts:Set, Is:Set)
   rule transExpList(N:Int, Mod:K, 'expListCon(A:K,, B:K),
                .K, L:List, Ls:Set, Ts:Set, Is:Set)
            => transExpList(N, Mod, B,
                transExp(N, Mod, A, Ls, Ts, Is), L, Ls:Set, Ts:Set, Is:Set)
   rule transExpList(N:Int, Mod:K, A:K,
                error(B:K), L:List, Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transExpList(N:Int, Mod:K, A:K,
               resultTrans(N':K, B:K), L:List, Ls:Set, Ts:Set, Is:Set)
          => transExpList(N', Mod, A, .K, L ListItem(B), Ls, Ts, Is)

   //trans tuples 
   rule transExpTuple(N:Int, Mod:K, C:K, .K, .K, L:List, Ls:Set, Ts:Set, Is:Set)
           => resultTrans(N, appExp(C, L))
   rule transExpTuple(N:Int, Mod:K, C:K, 'twoExpTuple(A:K,, B:K),
              .K, L:List, Ls:Set, Ts:Set, Is:Set)
           =>  transExpTuple(N, Mod, C, B,
                  transExp(N, Mod, A, Ls, Ts, Is), L, Ls, Ts, Is)
   rule transExpTuple(N:Int, Mod:K, C:K, 'expTupleCon(A:K,, B:K),
              .K, L:List, Ls:Set, Ts:Set, Is:Set)
           =>  transExpTuple(N, Mod, C, B,
                  transExp(N, Mod, A, Ls, Ts, Is), L, Ls, Ts, Is)
   rule transExpTuple(N:Int, Mod:K, C:K, A:Exp,
              .K, L:List, Ls:Set, Ts:Set, Is:Set)
           =>  transExpTuple(N, Mod, C, .K,
                  transExp(N, Mod, A, Ls, Ts, Is), L, Ls, Ts, Is)
   rule transExpTuple(N:Int, Mod:K, C:K, A:K,
              error(B:K), L:List, Ls:Set, Ts:Set, Is:Set) => error(B)
   rule transExpTuple(N:Int, Mod:K, C:K, A:K,
              resultTrans(N':Int, B:K), L:List, Ls:Set, Ts:Set, Is:Set)
             => transExpTuple(N', Mod, C, A, .K, L ListItem(B), Ls, Ts, Is)

   //trans funApp
   rule transExpFun(C:Int, Mod:K, .List, .K, ListItem(A:K) L:List,
           Ls:Set, Ts:Set, Is:Set) => resultTrans(C, appExp(A, L))
   rule transExpFun(C:Int, Mod:K, ListItem(A:K) L:List, .K, L1:List,
           Ls:Set, Ts:Set, Is:Set) => transExpFun(C, Mod,
                   L, transExp(C, Mod, A, Ls, Ts, Is), L1, Ls, Ts, Is)
   rule transExpFun(C:Int, Mod:K, L:List, error(A:K),
           L1:List, Ls:Set, Ts:Set, Is:Set) => error(A)
   rule transExpFun(C:Int, Mod:K, L:List, resultTrans(C':K, A:K),
           L1:List, Ls:Set, Ts:Set, Is:Set)
            => transExpFun(C', Mod, L, .K, L1 ListItem(A), Ls, Ts, Is)

   //trans qvar/gcon
   rule transExpQVar(C:K, error(A:K)) => error(A)
   rule transExpQVar(C:K, A:K) => resultTrans(C, A) [owise]

   //trans left and right sections
   rule transExp(N:Int, Mod:K, 'leftSection(E1:InfixExp,, G:QOp), Ls:Set, Ts:Set, Is:Set)
          => transLeftSection(transExp(N, Mod, E1, Ls, Ts, Is), transVar(Mod, G, Ls, Ts, Is))

   rule transLeftSection(error(A:K), B:K) => error(A)
   rule transLeftSection(A:K, error(B:K)) => error(B)
   rule transLeftSection(resultTrans(N:Int, A:K), B:K)
          => resultTrans(N +Int 1, lambda(genVar(N), appExp(B,
                      ListItem(A) ListItem(genVar(N))))) [owise]

   rule transExp(N:Int, Mod:K, 'rightSection(G:QOp,, E1:InfixExp), Ls:Set, Ts:Set, Is:Set)
          => transRightSection(transVar(Mod, G, Ls, Ts, Is), transExp(N, Mod, E1, Ls, Ts, Is))
        requires G =/=K 'minusCon(.KList)
   rule transExp(N:Int, Mod:K, 'rightSection(
                    'minusCon(.KList),, E1:InfixExp), Ls:Set, Ts:Set, Is:Set)
                 => error(syntaxError)

   rule transRightSection(error(B:K), A:K) => error(B)
   rule transRightSection(B:K, error(A:K)) => error(A)
   rule transRightSection(B:K, resultTrans(N:Int, A:K))
          => resultTrans(N +Int 1, lambda(genVar(N), appExp(B,
                       ListItem(genVar(N)) ListItem(A)))) [owise]

   syntax KItem ::= toAstTypeClass(K, K, K, Map, Set, Set) [function]
             //curr-mod, type-class-var, OptCDecls, gen-class-map, types, imports
                  | toAstTypeClassAux(K, K, K, CDeclsList, Map, Set, Set) [function]
            //curr-mod, type-class-var, CDecl,CDeclsList, gen-class-map , types, imports
                  | toAstTypeClassList(K, K, K, K, K,
                                 CDeclsList, Map, Set, Set) [function]
            //curr-mod, type-class-var, vars, contexts, type,CDeclsList, gen-class-map,
            //  exist-var-setm, types, imports
                  | toAstTypeClassList1(K, K, K, Set, K,
                                 CDeclsList, Map, Set, Set) [function]

   rule toAstTypeClass(Mod:K, V:K, 'emptyOptCDecls(.KList), M:Map, S:Set, Is:Set)
                   => resultMap(M)
   rule toAstTypeClass(Mod:K, V:K, 'cdeclWhere(
                 'cdeclBracket(Cs:CDeclsList)), M:Map, S:Set, Is:Set)
           => toAstTypeClass(Mod,V, Cs, M, S, Is)
   rule toAstTypeClass(Mod:K, V:K,
              .CDeclsList, M:Map, S:Set, Is:Set) => resultMap(M)
   rule toAstTypeClass(Mod:K, V:K, 'cdeclCon(A:CDecl,, B:CDeclsList),
                     M:Map, S:Set, Is:Set)
         => toAstTypeClassAux(Mod, V:K, A, B, M, S, Is)

   rule toAstTypeClassAux(Mod:K, V:K,
                  'emptyGenDecl(.KList), B:CDeclsList, M, S, Is:Set)
          => toAstTypeClass(Mod, V, B, M, S, Is)
   rule toAstTypeClassAux(Mod:K, V:K, 'varAssign(X:Vars,, T:Type),
                B:CDeclsList, M:Map, S:Set, Is:Set)
           => toAstTypeClassList(Mod, V, X, resultSet(.Set), toAbsTypeWithAll(
               Mod, T, SetItem(V), getFreeTypeVars(T), S, Is), B, M, S, Is)
        requires V in getFreeTypeVars(T)
   rule toAstTypeClassAux(Mod:K, V:K, 'varAssign(X:Vars,, T:Type),
                B:CDeclsList, M:Map, S:Set, Is:Set)
           => error(ambiguousTypeVar)
        requires notBool V in getFreeTypeVars(T)
   rule toAstTypeClassAux(Mod:K, V:K, 'genAssignContext(X:Vars,, C:Context,, T:Type),
                B:CDeclsList, M:Map, S:Set, Is:Set)
           => toAstTypeClassList(Mod, V, X,
                  contextToSet(Mod, C, .K, .Set, S, Is), toAbsTypeWithAll(
                 Mod, T, SetItem(V), getFreeTypeVars(T), S, Is), B, M, S, Is)
        requires V in getFreeTypeVars(T) andBool getTypeVarsInClass(
                    contextToSet(Mod, C, .K, .Set, S, Is))
                                     <=Set getFreeTypeVars(T)
   rule toAstTypeClassAux(Mod:K, V:K, 'genAssignContext(X:Vars,, C:Context,, T:Type),
                B:CDeclsList, M:Map, S:Set, Is:Set)
           => error(ambiguousTypeVar)
        requires (notBool V in getFreeTypeVars(T))
                   orBool (notBool getTypeVarsInClass(
                    contextToSet(Mod, C, .K, .Set, S, Is))  <=Set getFreeTypeVars(T))
   rule toAstTypeClassAux(Mod:K, V:K, X:K, B:CDeclsList, M:Map, S:Set, Is:Set)
            => toAstTypeClass(Mod, V, B, M, S, Is) [owise]

   rule toAstTypeClassList(Mod:K, V:K, X:K, error(A:K), T:K,
             C:CDeclsList, M:Map, Ts:Set, Is:Set) => error(A)
   rule toAstTypeClassList(Mod:K, V:K, X:K, A:K, error(T:K),
             C:CDeclsList, M:Map, Ts:Set, Is:Set) => error(T)
   rule toAstTypeClassList(Mod:K, V:K, X:K, resultSet(Cons:Set), T:K,
             C:CDeclsList, M:Map, Ts:Set, Is:Set)
         => toAstTypeClassList1(Mod, V, X, Cons, T, C, M, Ts, Is) [owise]
   rule toAstTypeClassList1(Mod:K, V:K, X:Var,
                       Cons:Set, T:K, C:CDeclsList, M:Map, Ts:Set, Is:Set)
           => toAstTypeClass(Mod, V, C, (fullName(Mod, funName(pillVar(X)))
                        |-> makeMethodDef(Cons, T)) M, Ts, Is)
        requires isNewDeclClass(M, fullName(Mod, funName(pillVar(X))))
   rule toAstTypeClassList1(Mod:K, V:K, X:Var,
                       Cons:Set, T:K, C:CDeclsList, M:Map, Ts:Set, Is:Set)
           => error(classVarCollipse)
        requires notBool isNewDeclClass(M, fullName(Mod, funName(pillVar(X))))
   rule toAstTypeClassList1(Mod:K, V:K, 'varCon(X:Var,, Xs:Vars), Cons:Set,
                  T:K, C:CDeclsList, M:Map, Ts:Set, Is:Set)
           => toAstTypeClassList1(Mod, V, Xs, Cons:Set, T, C,
                  (fullName(Mod, funName(pillVar(X)))
                             |-> makeMethodDef(Cons, T)) M, Ts, Is)
        requires isNewDeclClass(M, fullName(Mod, funName(pillVar(X))))
   rule toAstTypeClassList1(Mod:K, V:K, 'varCon(X:Var,, Xs:Vars), Cons:Set,
                  T:K, C:CDeclsList, M:Map, Ts:Set, Is:Set)
           => error(classVarCollipse)
        requires notBool isNewDeclClass(M, fullName(Mod, funName(pillVar(X))))

   //functions to add possible pattern rules for type classes
   //only for the right hand side.

   //check if a list of def variables have been defined before (false) or new (true)
   syntax Bool ::= isNewPats(Map, K, Set, K) [function]
   rule isNewPats(M:Map, .K, .Set, .K) => true
   rule isNewPats(M:Map, .K, SetItem(A:K) S:Set, .K)
         => isNewPats(M, .K, S, A)
   rule isNewPats(M:Map, .K, S:Set, A:KItem)
         => isNewPats(M, .K, S, .K)
        requires notBool (A in keys(M))
   rule isNewPats((A |-> B:K) M:Map, .K, S:Set, A:KItem)
           => isNewPats(M, B, S, A)
   rule isNewPats(M:Map, methodDef(Cs:Set, Ts:Map, T:K, ListItem(B:K) L:List), S:Set, A:KItem)
           => false
   rule isNewPats(M:Map, methodDef(Cs:Set, Ts:Map, T:K, .List), S:Set, A:KItem)
           => isNewPats(M, .K, S, .K)

   //check if a list of decl variables have been defined before (false) or new (true)
   syntax Bool ::= isNewDeclClass(Map, K) [function]
                 | isNewDeclClassAux(K) [function]
   rule isNewDeclClass((A:K |-> C:K) M:Map, A)
            => isNewDeclClassAux(C)
   rule isNewDeclClass(M:Map, A) => true [owise]
   rule isNewDeclClassAux(methodDef(S:Set, M:Map, .K, B:List)) => true
   rule isNewDeclClassAux(methodDef(S:Set, M:Map, T:K, B:List)) => false [owise]

   syntax Bool ::= isNewDecl(Map, K, K, K) [function]
   rule isNewDecl(M:Map, .K, A:Var, .K) => true
        requires notBool (funName(pillVar(A)) in keys(M))
   rule isNewDecl(M:Map, .K, 'varCon(A:Var,, As:Vars), .K)
             => isNewDecl(M, .K, As, .K)
        requires notBool (funName(pillVar(A)) in keys(M))
   rule isNewDecl(M:Map, .K, A:Var, .K)
            => isNewDecl(M, .K, .K, funName(pillVar(A)))
   rule isNewDecl((A |-> B:K) M:Map, .K, .K, A:KItem)
           => isNewDecl(M, B, .K, A)
   rule isNewDecl(M:Map, methodDef(Cs:Set, Ts:Map, .K, L:List),
         .K, A:KItem) => true
   rule isNewDecl(M:Map, .K, 'varCon(A:Var,, As:Vars), .K)
            => isNewDecl(M, .K, As, funName(pillVar(A)))
   rule isNewDecl((A |-> B:K) M:Map, .K, As:Vars, A:KItem)
            => isNewDecl(M, B, As, A)
   rule isNewDecl(M:Map, methodDef(Cs:Set, Ts:Map, .K, L:List),
         As:Vars, A:KItem) => isNewDecl(M, .K, As, .K)
   rule isNewDecl(M:Map, methodDef(Cs:Set, Ts:Map, T:KItem, L:List),
         As:Vars, A:KItem) => false

   syntax Map ::= updatePatMapInSet(Map, K, Set, K) [function]
   rule updatePatMapInSet(M:Map, .K, .Set, A:K) => M
   rule updatePatMapInSet(M:Map, .K, SetItem(A:K) S:Set, B:K)
          => updatePatMapInSet(M, A, S, B)
   rule updatePatMapInSet(M:Map, A:KItem, S:Set, B:K)
          => updatePatMapInSet(M[A <- methodDef(.Set, .Map, .K, ListItem(B))],.K, S, B)
        requires notBool (A in keys(M))
   rule updatePatMapInSet((A |-> C:K) M:Map, A:KItem, S:Set, B:K)
          => updatePatMapInSet((A |-> updatePatListInDef(C, B)) M, .K, S, B)

   syntax KItem ::= updatePatListInDef(K, K) [function]
   rule updatePatListInDef(methodDef(Cons:Set, S:Map, A:K, L:List), D:K)
          =>  methodDef(Cons, S, A, L ListItem(D))

   syntax Map ::= updatePatMapInExp(Map, K, K) [function]
              //map, name, patterns
   rule updatePatMapInExp(M:Map (A |-> D:K), A:K, C:K)
           => M (A |-> updatePatListInDef(D, C))
   rule updatePatMapInExp(M:Map, A:K, C:K)
                  => M (A |-> methodDef(.Set, .Map, .K, ListItem(C))) [owise]

   syntax KItem ::= updateDeclInDef(K, Set, K) [function]
   rule updateDeclInDef(methodDef(.Set, .Map, .K, L:List), Cs:Set, forall(As:Set, T:K))
          => methodDef(Cs, makeVarContextMap(As), T, L)
   rule updateDeclInDef(methodDef(.Set, .Map, .K, L:List), Cs:Set, T:K)
          => methodDef(Cs, .Map, T, L)
        requires notBool isForAll(T)

   syntax Map ::= updateDeclMapInExp(Map, K, Set, K) [function]
   rule updateDeclMapInExp(M:Map, A:K, Cs:Set, forall(As:Set, T:K))
         => M (A |-> methodDef(Cs, makeVarContextMap(As), T, .List))
        requires notBool (A in keys(M))
   rule updateDeclMapInExp(M:Map, A:K, Cs:Set, T:K)
         => M (A |-> methodDef(Cs, .Map, T, .List))
        requires notBool (A in keys(M)) andBool notBool isForAll(T)
   rule updateDeclMapInExp((A |-> B:K) M:Map, A:K, Cs:Set, T:K)
         => (A |-> updateDeclInDef(B, Cs, T)) M

   syntax Map ::= updateDeclMapList(Map, Vars, Set, K) [function]
   rule updateDeclMapList(M:Map, V:Var, Cs:Set, T:K)
          => updateDeclMapInExp(M, funName(pillVar(V)), Cs, T)
   rule updateDeclMapList(M:Map, 'varCon(A:Var,, As:Vars), Cs:Set, T:K)
          => updateDeclMapList(updateDeclMapInExp(M,
                 funName(pillVar(A)), Cs, T), As, Cs, T)

   //transform patterns
   syntax KItem ::= toAstPat(Int, K, K, K, K, Map, Set, Set) [function]
      //var-counter, curr-mod, CDecls, var, exp, class-map
                  | transCDecl(K, K) [function]

   rule toAstPat(N:Int, Mod:K, 'emptyOptCDecls(.KList), U:K, V:K, M:Map, Ts:Set, Is:Set)
              => resultIntMap(N, M)
   rule toAstPat(N:Int, Mod:K, 'cdeclWhere('cdeclBracket(Cs:CDeclsList)),
            U:K, V:K, M:Map, Ts:Set, Is:Set)
         => toAstPat(N, Mod, Cs, U, V, M, Ts, Is)
        requires (getFreeVarsInDefs(Cs) <=Set getFreeVarsInCDecls(Cs))
   rule toAstPat(N:Int, Mod:K, 'cdeclWhere('cdeclBracket(Cs:CDeclsList)),
            U:K, V:K, M:Map, Ts:Set, Is:Set) => error(funNameDefNotDeclInClass)
        requires notBool (getFreeVarsInDefs(Cs) <=Set getFreeVarsInCDecls(Cs))
   rule toAstPat(N:Int, Mod:K, .CDeclsList,
              U:K, V:K, M:Map, Ts:Set, Is:Set) => resultIntMap(N, M)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(
            'cdeclVarRhs(X:Var,, Y:Rhs),, B:CDeclsList),.K, .K, M:Map, Ts:Set, Is:Set)
            => toAstPat(N, Mod, B, fullName(Mod, funName(pillVar(X))), transCDecl(
              transPosFunLhs(Mod, X, Ts, Is),
                 transRhs(N, Mod, Y, .Set, Ts, Is)), M, Ts:Set, Is:Set)
        requires fullName(Mod, X) in keys(M)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(
            'cdeclVarRhs(X:Var,, Y:Rhs),, B:CDeclsList),.K, .K, M:Map, Ts:Set, Is:Set)
            => error(classMethodVarNotInScope)
        requires notBool fullName(Mod, X) in keys(M)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(
              'cdeclFunLhsRhs(X:FunLhs,, Y:Rhs),, B:CDeclsList),.K, .K, M:Map, Ts:Set, Is:Set)
            => toAstPat(N, Mod, B, fullName(Mod, getCoreVar(X)),
                    transCDecl(transPosFunLhs(Mod, X, Ts, Is),
                       transRhs(N, Mod, Y, getBoundVarsInPat(X), Ts, Is)), M, Ts, Is)
        requires fullName(Mod, getCoreVar(X)) in keys(M)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(
              'cdeclFunLhsRhs(X:FunLhs,, Y:Rhs),, B:CDeclsList),.K, .K, M:Map, Ts:Set, Is:Set)
            => error(classMethodVarNotInScope)
        requires notBool fullName(Mod, getCoreVar(X)) in keys(M)
   rule toAstPat(N:Int, Mod:K, A:K, X:K, error(B:K), M:Map, Ts:Set, Is:Set) => error(B)
   rule toAstPat(N:Int, Mod:K, A:K, X:K, resultTrans(N':Int, B:K), M:Map, Ts:Set, Is:Set)
         => toAstPat(N', Mod, A, .K, .K, updatePatMapInExp(M, X, B), Ts:Set, Is:Set)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(A:CDecl,, B:CDeclsList),.K,.K, M:Map, Ts:Set, Is:Set)
            => toAstPat(N, Mod, B, .K, .K, M, Ts:Set, Is:Set) [owise]

   rule transCDecl(error(A:K), B:K) => error(A)
   rule transCDecl(A:K, error(B:K)) => error(B)
   rule transCDecl(funPat(ListItem(X:K) L:List), resultTrans(N:Int, A:K))
            =>  resultTrans(N, funAssign(X, L, A))

   //transformation of expressions in a module, bascially an exp is a decl
   //and also check the kind for decl of each function
   syntax KItem ::= transDeclFun(Int, K, K, Set, Set, Map, Map)  [function]
           //gen-var, cur-mod, topdecls, type-set, import-set, store fun-map, store exp-map
                  | transDeclFunAux(Int, K, K, K, Set, Set, Map, Map)    [function]
                  | transDeclFunAux1(K, K, K, K, Set, Set, Map, Map)    [function]
                  | transDeclFunAux2(K, Set, K, K, K, Set, Set, Map, Map)    [function]
                  | transDeclFunAux3(Int, K, Vars, Set, K, K, Set, Set, Map, Map) [function]
                  | transDeclFunAux4(Int, K, Vars, K, K, K, Set, Set, Map, Map) [function]

    rule transDeclFun(N:Int, Mod:K, 'bodyimpandtop(I:ImpDecls,,
                  T:TopDecls), Ts:Set, Is:Set, M:Map, RM:Map)
           => transDeclFun(N, Mod, T, Ts, Is, M, RM)
    rule transDeclFun(N:Int, Mod:K,'bodyimpdecls(_:ImpDecls),
                Ts:Set, Is:Set, M:Map, RM:Map) => resultTransMapMap(N, M, RM)
    rule transDeclFun(N:Int, Mod:K, 'bodytopdecls(T:TopDecls),
                Ts:Set, Is:Set, M:Map, RM:Map)
             => transDeclFun(N, Mod, T, Ts, Is, M, RM)
    rule transDeclFun(N:Int, Mod:K, .TopDecls,
                Ts:Set, Is:Set, M:Map, RM:Map) => resultTransMapMap(N, M, RM)

    rule transDeclFun(N:Int, Mod:K, 'topdeclslist(A:TopDecl,, As:TopDecls),
             Ts:Set, Is:Set, M:Map, RM:Map)
           => transDeclFunAux(N, Mod, A, As, Ts, Is, M, RM)
   rule transDeclFunAux(N:Int, Mod:K, 'declFunLhsRhs(F:FunLhs,, R:Rhs),
          As:K, Ts:Set, Is:Set, M:Map, RM:Map)
           => transDeclFunAux1(Mod, transPosFunLhs(Mod, F, Ts, Is), 
                transRhs(N, Mod, R, getBoundVarsInPat(F), Ts, Is),
                    As, Ts, Is, M, RM)
        requires hasNoConflictAllVars(F)
   rule transDeclFunAux(N:Int, Mod:K, 'declFunLhsRhs(F:FunLhs,, R:Rhs),
          As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => error(funNameConflicting)
        requires notBool hasNoConflictAllVars(F)
   rule transDeclFunAux(N:Int, Mod:K, 'declPatRhs(F:Pat,, R:Rhs),
               As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => transDeclFunAux2(Mod, getFreeVarsInPat(F),
                  transPosFunLhs(Mod, F, Ts, Is), 
                transRhs(N, Mod, R, .Set, Ts, Is),
                    As, Ts, Is, M, RM)
        requires hasNoConflictAllVars(F)
   rule transDeclFunAux(N:Int, Mod:K, 'declPatRhs(F:Pat,, R:Rhs),
               As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => error(funNameConflicting)
        requires notBool hasNoConflictVars(F)
   rule transDeclFunAux(N:Int, Mod:K, 'varAssign(A:Vars,, B:Type),
               As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => transDeclFunAux3(N, Mod, A, .Set, toAbsTypeWithAll(Mod,
                 B, .Set, getFreeTypeVars(B), Ts, Is), As, Ts, Is, M, RM)
        requires isNewDecl(M, .K, A, .K)
   rule transDeclFunAux(N:Int, Mod:K, 'varAssign(A:Vars,, B:Type),
               As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => error(duplicateDecl)
        requires notBool isNewDecl(M, .K, A, .K)

   rule transDeclFunAux(N:Int, Mod:K, 'genAssignContext(A:Vars,,
                  C:Context,, B:Type),
               As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => transDeclFunAux4(N, Mod, A, contextToSet(Mod, C,
                  .K, .Set, Ts, Is), B, As, Ts, Is, M, RM)
        requires isNewDecl(M, .K, A, .K)
   rule transDeclFunAux(N:Int, Mod:K, 'genAssignContext(A:Vars,,
                  C:Context,, B:Type),
               As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => error(duplicateDecl)
        requires notBool isNewDecl(M, .K, A, .K)
   rule transDeclFunAux(N:Int, Mod:K, A:K,
          As:K, Ts:Set, Is:Set, M:Map, RM:Map)
               => transDeclFun(N, Mod, As, Ts, Is, M, RM) [owise]

   rule transDeclFunAux1(Mod:K, error(A:K), B:K, As:K, Ts:Set,
          Is:Set, M:Map, RM:Map) => error(A)
   rule transDeclFunAux1(Mod:K, A:K, error(B:K), As:K, Ts:Set,
          Is:Set, M:Map, RM:Map) => error(B)
   rule transDeclFunAux1(Mod:K, funPat(ListItem(X:K) L:List), resultTrans(N:Int, B:K),
            As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => transDeclFun(N, Mod, As, Ts, Is,
                  updatePatMapInExp(M, X, funAssign(X, L, B)), RM)

   rule transDeclFunAux2(Mod:K, S:Set, error(A:K), B:K, As:K, Ts:Set,
          Is:Set, M:Map, RM:Map) => error(A)
   rule transDeclFunAux2(Mod:K, S:Set, A:K, error(B:K), As:K, Ts:Set,
          Is:Set, M:Map, RM:Map) => error(B)
   rule transDeclFunAux2(Mod:K, S:Set, funPat(ListItem(X:K)), resultTrans(N:Int, B:K),
            As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => transDeclFun(N +Int 1, Mod, As, Ts, Is,
                  updatePatMapInSet(M, .K, S, genVar(N)),
                  (genVar(N) |-> funAssign(X, .List, B)) RM)
        requires isNewPats(M, .K, S, .K)
   rule transDeclFunAux2(Mod:K, S:Set, funPat(ListItem(X:K)), resultTrans(N:Int, B:K),
            As:K, Ts:Set, Is:Set, M:Map, RM:Map)
         => error(repeatedNames)
        requires notBool isNewPats(M, .K, S, .K)

   rule transDeclFunAux3(N:Int, Mod:K, A:Vars, C:Set, error(B:K),
             As:K, Ts:Set, Is:Set, M:Map, RM:Map) => error(B)
   rule transDeclFunAux3(N:Int, Mod:K, A:Vars, C:Set,
           B:K, As:K, Ts:Set, Is:Set, M:Map, RM:Map)
          => transDeclFun(N, Mod, As, Ts, Is,
                   updateDeclMapList(M, A, C, B), RM) [owise]

   rule transDeclFunAux4(N:Int, Mod:K, A:Vars, error(C:K), B:K,
          As:K, Ts:Set, Is:Set, M:Map, RM:Map) => error(C)
   rule transDeclFunAux4(N:Int, Mod:K, A:Vars, resultSet(C:Set), B:K,
          As:K, Ts:Set, Is:Set, M:Map, RM:Map)
          => transDeclFunAux3(N, Mod, A, C, toAbsTypeWithAll(Mod,
                 B, .Set, getFreeTypeVars(B), Ts, Is), As, Ts, Is, M, RM)

   //add type/context to method def in a map
   syntax KItem ::= addDeclToK(K, Set, K) [function]
   rule addDeclToK(methodDef(Cs:Set, S:Map, T:K, L:List), S1:Set, T1:K)
           => makeMethodDefWithList(S1, T1, L)

   syntax Map ::= addDeclToMap(Map, K, Set, Set, K) [function]
          //def map, execute, Set-of-keys, contexts, type
   rule addDeclToMap(M:Map, .K, .Set, S:Set, T:K) => M
   rule addDeclToMap(M:Map, .K, SetItem(A:K) S:Set, S1:Set, T:K)
         => addDeclToMap(M, A, S, S1, T)
   rule addDeclToMap(M:Map (A |-> B:K), A:KItem, S:Set, S1:Set, T:K)
          => (A |-> addDeclToK(B, S1, T)) addDeclToMap(M, .K, S, S1, T)
   rule addDeclToMap(M:Map, A:KItem, S:Set, S1:Set, T:K)
          => addDeclToMap(M, .K, S, S1, T) [owise]


   //create an empty entry in the method definition map
   syntax Map ::= createEmptyEntry(Map, K, Set) [function]
   rule createEmptyEntry(M:Map, .K, .Set) => M
   rule createEmptyEntry(M:Map, .K, SetItem(A:K) S:Set)
            => createEmptyEntry(M, A, S)
   rule createEmptyEntry(M:Map, A:KItem, S:Set)
          => createEmptyEntry(M (A |-> methodDef(.Set, .Map, .K, ListItem(none))), .K, S)

   //check if the method definition has defined pattern /types
   syntax Bool ::= hasDefinedPat(K) [function]
                 | hasNoDefinedPats(Set, K) [function]
   rule hasDefinedPat(methodDef(A:Set, S:Map, B:K, .List)) => false
   rule hasDefinedPat(methodDef(A:Set, S:Map, B:K, ListItem(C:K) L:List)) => true
   rule hasNoDefinedPats(.Set, .K) => true
   rule hasNoDefinedPats(SetItem(A:K) S:Set, .K)
          => hasNoDefinedPats(S, A)
   rule hasNoDefinedPats(S:Set, A:KItem) => hasNoDefinedPats(S, .K)
        requires notBool hasDefinedPat(A)
   rule hasNoDefinedPats(S:Set, A:KItem) => false
        requires hasDefinedPat(A)

   syntax Bool ::= hasDefinedType(K) [function]
                 | hasNoDefinedTypes(Set, K) [function]
   rule hasDefinedType(methodDef(A:Set, S:Map, T:K, L:List)) => T =/=K .K
   rule hasNoDefinedTypes(.Set, .K) => true
   rule hasNoDefinedTypes(SetItem(A:K) S:Set, .K)
          => hasNoDefinedTypes(S, A)
   rule hasNoDefinedTypes(S:Set, A:KItem) => hasNoDefinedTypes(S, .K)
        requires notBool hasDefinedType(A)
   rule hasNoDefinedTypes(S:Set, A:KItem) => false
        requires hasDefinedType(A)


   //trans top level decls
/*
   syntax KItem ::= transTopDecls(Int, K, K, Set) [function]
                    //int, cur-mod, idecls, set-of-funcions
                  | transTopDeclsAux(Int, K, K, K, Map, Set) [function]
                  | transTopDecl(Int, K, K, Map, Set) [function]
                  | transTopDeclAux(K, K, Map)   [function]

   rule transTopDecls(N:Int, Mod:K, 'emptyOptIDecls(.KList), Cs:Set)
         => resultTransMap(N, .Map)
   rule transTopDecls(N:Int, Mod:K, 'ideclWhere('ideclBracket(Ds:DeclsList)), Cs:Set)
           => transTopDeclsAux(N, Mod, Ds, .K, .Map, Cs)
   rule transTopDeclsAux(N:Int, Mod:K, .IDeclsList, .K, M:Map, Cs:Set)
             => resultTransMap(N, M)
   rule transTopDeclsAux(N:Int, Mod:K, 'ideclsCon(D:IDecl,, Ds:IDeclsList),
                     .K, M:Map, Cs:Set)
           => transTopDeclsAux(N, Mod, Ds, transTopDecl(N, Mod, D, M, Cs), M:Map, Cs:Set)
   rule transTopDeclsAux(N:Int, Mod:K, Ds:K, error(A:K), M:Map, Cs:Set) => error(A)
   rule transTopDeclsAux(N:Int, Mod:K, Ds:K, resultTransMap(N':Int, M':Map), M:Map, Cs:Set)
          => transTopDeclsAux(N', Mod, Ds, .K, M', Cs:Set)
   
   rule transTopDecl(N:Int, Mod:K, 'emptyIDecl(.KList), M:Map, Cs:Set) => resultTransMap(N, M)
   rule transTopDecl(N:Int, Mod:K, 'ideclFunLhsRhs(A:FunLhs,, B:Rhs), M:Map, Cs:Set)
         => transTopDeclAux(transFunLhs(Mod, A), transRhs(N, Mod, B), M)
        requires getCoreVar(A) in Cs
   rule transTopDecl(N:Int, Mod:K, 'ideclFunLhsRhs(A:FunLhs,, B:Rhs), M:Map, Cs:Set)
         => error(classMethodVarNotInScope)
        requires notBool getCoreVar(A) in Cs
   rule transTopDecl(N:Int, Mod:K, 'ideclVarRhs(A:Var,, B:Rhs), M:Map, Cs:Set)
         => transTopDeclAux(transFunLhs(Mod, A), transRhs(N, Mod, B), M)
        requires A in Cs
   rule transTopDecl(N:Int, Mod:K, 'ideclVarRhs(A:Var,, B:Rhs), M:Map, Cs:Set)
         => error(classMethodVarNotInScope)
        requires notBool A in Cs

   rule transTopDeclAux(A:K, error(B:K), M:Map) => error(B)
   rule transTopDeclAux(funPat(ListItem(A:K) L:List), resultTrans(N:Int, B:K), M:Map)
                => resultTransMap(N, updateFunExp(M, A, funAssign(L, B)))
*/

   //transfer variables according to if it is in different set
   syntax KItem ::= transExpCon(K, K, Set, Set) [function]
            //curr-mod-name, ExpCon, types, imports
   rule transExpCon(Mod:K, 'unitType(.KList), Ts:Set, Is:Set)
                  => fullName(Prelude, constrName('unitType(.KList)))
   rule transExpCon(Mod:K, [], Ts:Set, Is:Set) => fullName(Prelude, constrName([]))
   rule transExpCon(Mod:K, 'tupleFun(Gs:GConCommas), Ts:Set, Is:Set)
          => fullName(Prelude, constrName(tupleType(countOnCommas(Gs) +Int 1)))
   rule transExpCon(Mod:K, T:QTyCon, Ts:Set, Is:Set)
             => transConstrVar(Mod, pillVar(T), Ts, Is)
   rule transExpCon(Mod:K, 'gConBracket('colon(.KList)), Ts:Set, Is:Set)
              => fullName(Prelude, constrName('colon(.KList)))
   rule transExpCon(Mod:K, 'gConBracket(C:K), Ts:Set, Is:Set)
              => transConstrVar(Mod, pillVar('gConBracket(C:K)), Ts, Is)

   syntax KItem ::= transConstrVar(K, K, Set, Set) [function]
   rule transConstrVar(S:K, A:K,Ts:Set, Is:Set)
           => fullName(S, constrName(A))
        requires notBool isFullName(A) andBool A in Ts
                andBool countGoodNameNoQualified(constrName(A), .K, Is) ==K 0
   rule transConstrVar(S:K, A:K,Ts:Set, Is:Set)
           => fullName(findGoodNameNoQualified(constrName(A), .K, Is), constrName(A))
        requires notBool isFullName(A) andBool notBool A in Ts
                andBool countGoodNameNoQualified(constrName(A), .K, Is) ==K 1
   rule transConstrVar(S:K, A:K,Ts:Set, Is:Set) => error(ambiguousConstrName)
        requires notBool isFullName(A) andBool constrName(A) in Ts
                   andBool countGoodNameNoQualified(constrName(A), .K, Is) =/=K 0
   rule transConstrVar(S:K, A:K,Ts:Set, Is:Set) => error(ambiguousConstrName)
        requires notBool isFullName(A) andBool notBool constrName(A) in Ts
                   andBool countGoodNameNoQualified(constrName(A), .K, Is) >Int 1
   rule transConstrVar(S:K, A:K,Ts:Set, Is:Set) => error(constrNotInScope)
        requires notBool isFullName(A) andBool notBool constrName(A) in Ts
                   andBool countGoodNameNoQualified(constrName(A), .K, Is)==K 0

   rule transConstrVar(S:K, fullName(S, A:K), Ts:Set, Is:Set)
         => fullName(S, constrName(A))
        requires constrName(A) in Ts
                andBool countGoodNameWithMod(constrName(A), S, .K, Is) ==K 0
   rule transConstrVar(S:K, fullName(S, A:K), Ts:Set, Is:Set)
         => error(ambiguousConstrName)
        requires constrName(A) in Ts
                andBool countGoodNameWithMod(constrName(A), S, .K, Is) =/=K 0
   rule transConstrVar(S:K, fullName(S, A:K), Ts:Set, Is:Set)
         => error(constrNotInScope)
        requires notBool constrName(A) in Ts
                andBool countGoodNameWithMod(constrName(A),S, .K, Is)==K 0
   rule transConstrVar(S:K, fullName(N:K, A:K), Ts:Set, Is:Set)
         => error(constrNotInScope)
        requires S =/=K N
                andBool countGoodNameWithMod(constrName(A),N, .K, Is)==K 0
   rule transConstrVar(S:K, fullName(N:K, A:K), Ts:Set, Is:Set)
         => fullName(findGoodNameWithMod(
                        constrName(A), N, .K, Is),constrName(A))
        requires S =/=K N
                andBool countGoodNameWithMod(constrName(A),N, .K, Is)==K 1
   rule transConstrVar(S:K, fullName(S:K, A:K), Ts:Set, Is:Set)
         => fullName(findGoodNameWithMod(
                        constrName(A), S, .K, Is),constrName(A))
        requires notBool constrName(A) in Ts
                andBool countGoodNameWithMod(constrName(A),S, .K, Is)==K 1
   rule transConstrVar(S:K, fullName(S:K, A:K), Ts:Set, Is:Set)
             => error(ambiguousConstrName)
        requires countGoodNameWithMod(constrName(A), S, .K, Is) >Int 1

   syntax KItem ::= transFunVar(K, K, Set, Set, Set) [function]
          //curr-mod, term, bound-vars, types, imports
   rule transFunVar(S:K, A:K,As:Set, Ts:Set, Is:Set) => funName(A)
        requires notBool isFullName(A) andBool funName(A) in As
   rule transFunVar(S:K, A:K,As:Set, Ts:Set, Is:Set)
           => fullName(S, funName(A))
        requires notBool isFullName(A) andBool funName(A) in Ts
                andBool countGoodNameNoQualified(funName(A), .K, Is) ==K 0
   rule transFunVar(S:K, A:K, As:Set, Ts:Set, Is:Set)
           => fullName(findGoodNameNoQualified(funName(A), .K, Is), funName(A))
        requires notBool isFullName(A) andBool notBool funName(A) in Ts
                andBool countGoodNameNoQualified(funName(A), .K, Is) ==K 1
   rule transFunVar(S:K, A:K, As:Set, Ts:Set, Is:Set) => error(ambiguousFunName)
        requires notBool isFullName(A) andBool funName(A) in Ts
                   andBool countGoodNameNoQualified(funName(A), .K, Is) =/=K 0
   rule transFunVar(S:K, A:K,As:Set, Ts:Set, Is:Set) => error(ambiguousFunName)
        requires notBool isFullName(A) andBool notBool funName(A) in Ts
                   andBool countGoodNameNoQualified(funName(A), .K, Is) >Int 1
   rule transFunVar(S:K, A:K, As:Set, Ts:Set, Is:Set) => error(constrNotInScope)
        requires notBool isFullName(A) andBool notBool funName(A) in Ts
                   andBool countGoodNameNoQualified(funName(A), .K, Is)==K 0
   rule transFunVar(S:K, fullName(S':K, A:K), As:Set, Ts:Set, Is:Set)
                => error(ambiguousFunName)
        requires funName(A) in As
   rule transFunVar(S:K, fullName(S, A:K), As:Set, Ts:Set, Is:Set)
         => fullName(S, funName(A))
        requires notBool (funName(A) in As) andBool funName(A) in Ts
                andBool countGoodNameWithMod(funName(A), S, .K, Is) ==K 0
   rule transFunVar(S:K, fullName(S, A:K), As:Set, Ts:Set, Is:Set)
         => error(ambiguousFunName)
        requires notBool (funName(A) in As) andBool funName(A) in Ts
                andBool countGoodNameWithMod(funName(A), S, .K, Is) =/=K 0
   rule transFunVar(S:K, fullName(S, A:K), As:Set, Ts:Set, Is:Set)
         => error(funNameNotInScope)
        requires  notBool (funName(A) in As) andBool notBool funName(A) in Ts
                andBool countGoodNameWithMod(funName(A),S, .K, Is)==K 0
   rule transFunVar(S:K, fullName(N:K, A:K), As:Set, Ts:Set, Is:Set)
         => error(funNameNotInScope)
        requires notBool (funName(A) in As) andBool S =/=K N
                andBool countGoodNameWithMod(funName(A),N, .K, Is)==K 0
   rule transFunVar(S:K, fullName(N:K, A:K), As:Set, Ts:Set, Is:Set)
         => fullName(findGoodNameWithMod(
                        funName(A), N, .K, Is),funName(A))
        requires notBool (funName(A) in As) andBool S =/=K N
                andBool countGoodNameWithMod(funName(A),N, .K, Is)==K 1
   rule transFunVar(S:K, fullName(S:K, A:K), As:Set, Ts:Set, Is:Set)
         => fullName(findGoodNameWithMod(
                        funName(A), S, .K, Is),funName(A))
        requires notBool (funName(A) in As) andBool notBool funName(A) in Ts
                andBool countGoodNameWithMod(funName(A),S, .K, Is)==K 1
   rule transFunVar(S:K, fullName(S:K, A:K), As:Set, Ts:Set, Is:Set)
             => error(ambiguousFunName)
        requires notBool (funName(A) in As) andBool
                     countGoodNameWithMod(funName(A), S, .K, Is) >Int 1

   syntax KItem ::= findLabelsInBetaMap(K, K, Map) [function]
   rule findLabelsInBetaMap(A:K, .K, (A |-> D:Map) M:Map)
           => findLabelsInBetaMap(A, D, M)
   rule findLabelsInBetaMap(A:K, curryTypes(ListItem(typeConst(
              fullName(Prelude, typeName(recordType)), L:List)), T:K), M:Map)
            => resultList(L)
   rule findLabelsInBetaMap(A:K, .K, M:Map) => none
        requires notBool A in keys(M)
   rule findLabelsInBetaMap(A:K, B:K, M:Map) => error(labelConstrNotCorrect) [owise]

   syntax KItem ::= findLabelsInPreBeta(K, K, K, Map) [function]
   rule findLabelsInPreBeta(A:K, .K, .K, .Map) => none
   rule findLabelsInPreBeta(A:K, .K, .K, (C:K |-> B:K) S:Map)
              => findLabelsInPreBeta(A, .K, B, S)
   rule findLabelsInPreBeta(A:K, .K, preBetaEntry(X:List, Y:Map, Z:Set), S:Map)
          => findLabelsInPreBeta(A, findLabelsInBetaMap(A, .K, Y), .K, S)
   rule findLabelsInPreBeta(A:K, error(B:K), .K, S:Map) => error(B)
   rule findLabelsInPreBeta(A:K, none, .K, S:Map) => findLabelsInPreBeta(A, .K, .K, S)
   rule findLabelsInPreBeta(A:K, resultList(L:List), .K, S:Map) => resultList(L)

   syntax KItem ::= findLabelsInImports(K, K, K, Map) [function]
                  //mod, constr, store, import-betas
                  | findLabelsInImportsAux(K, K, Map) [function]

   rule findLabelsInImportsAux(A:K, .K, (A |-> B:K) M:Map)
             => findLabelsInImportsAux(A, B, M)
   rule findLabelsInImportsAux(A:K, typeConst(fullName(Prelude, typeName((->))),
                  ListItem(typeConst(fullName(Prelude,
                         typeName(recordType)), Tar:List)) L:List), M:Map)
            => resultList(Tar)
   rule findLabelsInImportsAux(A:K, X:K, M:Map) => error(labelConstrNotCorrect) [owise]

   rule findLabelsInImports(A:K, B:K, .K, (A |-> C:K) M:Map)
            => findLabelsInImports(A, B, C, M)
   rule findLabelsInImports(A:K, B:K, resultMap(X:Map), M:Map)
              => findLabelsInImportsAux(B, .K, X)


   //pattern transformation is self-contained
   syntax KItem ::= compareLabel(K, K, List) [function]
                  | compareLabelAux(K, List) [function]
   rule compareLabel(Mod:K, fullName(X:K, Y:K), L:List) => error(labelNotInScope)
        requires Mod =/=K X
   rule compareLabel(Mod:K, fullName(Mod, Y:K), L:List)
        => compareLabelAux(funName(Y), L)
   rule compareLabel(Mod:K, Y:K, L:List) => compareLabelAux(funName(Y), L) [owise]

   rule compareLabelAux(Y:K, .List) => error(labelNotInScope)
   rule compareLabelAux(Y:K, ListItem(tyVar(S:K, Y:K)) L:List) => fullName(S, Y)
   rule compareLabelAux(Y:K, ListItem(tyVar(S:K, Y':K)) L:List)
         => compareLabelAux(Y, L) [owise]

endmodule
