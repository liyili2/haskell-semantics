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
   syntax Set ::= getTypeVarsInClass(K, Set) [function]
   rule getTypeVarsInClass(.K, .Set) => .Set
   rule getTypeVarsInClass(.K, SetItem(A:K) S:Set)
            => getTypeVarsInClass(A, S)
   rule getTypeVarsInClass(className(A:K, ListItem(C:K) B:List), S:Set)
            => SetItem(C) getTypeVarsInClass(.K, S)

   //a function to generate class method names in a class
   syntax Set ::= genClassMethodNames(K) [function]
   rule genClassMethodNames('emptyOptCDecls(.KList)) => .Set
   rule genClassMethodNames('cdeclWhere('cdeclBracket(Cs:CDecls)))
         => genClassMethodNames(Cs)
   rule genClassMethodNames('cdeclCon(C:CDecl,, Cs:CDeclsList))
         => genClassMethodNames(C) genClassMethodNames(Cs)
   rule genClassMethodNames('varAssign(Vs:Vars,, T:Type))
           => genClassMethodNames(Vs)
   rule genClassMethodNames(V:Var) => SetItem(pillVar(V))
   rule genClassMethodNames('varCon(V:Var,, Vs:Vars))
               => SetItem(pillVar(V)) genClassMethodNames(Vs)
   rule genClassMethodNames('genAssignContext(Vs:Vars,, C:Context,, T:Type))
               => genClassMethodNames(Vs)
   rule genClassMethodNames(A:K) => .Set  [owise]

   syntax KItem ::= toAstTypeClass(K, K, K, Map, Set) [function]
             //curr-mod, type-class-var, OptCDecls, gen-class-map, exist-ty-con-set
                  | toAstTypeClassAux(K, K, K, CDeclsList, Map, Set) [function]
            //curr-mod, type-class-var, CDecl,CDeclsList, gen-class-map, exist-ty-con-set
                  | toAstTypeClassList(K, K, K, Set, K, CDeclsList, Map, Set, Set) [function]
            //curr-mod, type-class-var, vars, contexts, type,CDeclsList, gen-class-map,
            // exist-ty-con-set, exist-var-set

   rule toAstTypeClass(Mod:K, V:K, 'emptyOptCDecls(.KList), M:Map, S:Set)
                   => resultMap(M)
   rule toAstTypeClass(Mod:K, V:K, 'cdeclWhere('cdeclBracket(Cs:CDeclsList)), M:Map, S:Set)
           => toAstTypeClass(Mod,V, Cs, M, S)
   rule toAstTypeClass(Mod:K, V:K, .CDeclsList, M:Map, S:Set) => resultMap(M)
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
           => toAstTypeClass(Mod, V, C, (pillVar(X)
                        |-> methodDef(Cons, T, .List)) M, S)
        requires notBool pillVar(X) in (S S1)
   rule toAstTypeClassList(Mod:K, V:K, X:Var, Cons:Set,
            T:K, C:CDeclsList, M:Map, S:Set, S1:Set) => error(classVarCollipse)
        requires pillVar(X) in (S S1)
   rule toAstTypeClassList(Mod:K, V:K, 'varCon(X:Var,, Xs:Vars), Cons:Set,
                  T:K, C:CDeclsList, M:Map, S:Set, S1:Set)
           => toAstTypeClassList(Mod, V, Xs, Cons:Set, T, C,
                  (pillVar(X)
                     |-> methodDef(Cons, T, .List)) M, S, S1)
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
   rule updatePatMapInExp(M:Map, A:K, C:K)
                  => M (A |-> methodDef(.Set, .K, ListItem(C))) [owise]

   //get the core var of an exp
   syntax KItem ::= getCoreVar(FunLhs) [function]
   rule getCoreVar('normalLhs(X:Var,, As:APatList)) => pillVar(X)
   rule getCoreVar('binLhs(A:Pat,, B:VarOp,, C:Pat)) => pillVar(B)
   rule getCoreVar('groupLhs(A:FunLhs,, B:APatList)) => getCoreVar(A)

   syntax KItem ::= toAstPat(Int, K, K, K, K, Map) [function]
      //var-counter, curr-mod, CDecls, var, exp, class-map
                  | transCDecl(K, K) [function]

   rule toAstPat(N:Int, Mod:K, 'emptyOptCDecls(.KList), U:K, V:K, M:Map)
              => resultIntMap(N, M)
   rule toAstPat(N:Int, Mod:K, 'cdeclWhere('cdeclBracket(Cs:CDeclsList)), U:K, V:K, M:Map)
         => toAstPat(N, Mod, Cs, U, V, M)
   rule toAstPat(N:Int, Mod:K, .CDeclsList,U:K, V:K, M:Map) => resultIntMap(N, M)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(
            'cdeclVarRhs(X:Var,, Y:Rhs),, B:CDeclsList),.K, .K, M:Map)
            => toAstPat(N, Mod, B, pillVar(X),
                        transCDecl(transFunLhs(Mod, X), transRhs(N, Mod, Y)), M)
        requires X in keys(M)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(
            'cdeclVarRhs(X:Var,, Y:Rhs),, B:CDeclsList),.K, .K, M:Map)
            => error(classMethodVarNotInScope)
        requires notBool X in keys(M)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(
              'cdeclFunLhsRhs(X:FunLhs,, Y:Rhs),, B:CDeclsList),.K, .K, M:Map)
            => toAstPat(N, Mod, B, getCoreVar(X),
                    transCDecl(transFunLhs(Mod, X), transRhs(N, Mod, Y)), M)
        requires getCoreVar(X) in keys(M)
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(
              'cdeclFunLhsRhs(X:FunLhs,, Y:Rhs),, B:CDeclsList),.K, .K, M:Map)
            => error(classMethodVarNotInScope)
        requires notBool getCoreVar(X) in keys(M)
   rule toAstPat(N:Int, Mod:K, A:K, X:K, error(B:K), M:Map) => error(B)
   rule toAstPat(N:Int, Mod:K, A:K, X:K, resultTrans(N':Int, B:K), M:Map)
         => toAstPat(N', Mod, A, .K, .K, updatePatMapInExp(M, X, B))
   rule toAstPat(N:Int, Mod:K, 'cdeclCon(A:CDecl,, B:CDeclsList),.K,.K, M:Map)
            => toAstPat(N, Mod, B, .K, .K, M) [owise]

   rule transCDecl(A:K, error(B:K)) => error(B)
   rule transCDecl(funPat(ListItem(X:K) L:List), resultTrans(N:Int, A:K))
            =>  resultTrans(N, funAssign(L, A))

   syntax KItem ::= formExpList(List) [function]
   rule formExpList(.List) => fullName(Prelude,[])
   rule formExpList(ListItem(A:K) L:List)
          => appExp(fullName(Prelude, 'colon(.KList)), ListItem(A)
                    ListItem(formExpList(L)))

   syntax KItem ::= formLambdaList(List, K) [function]
   rule formLambdaList(.List, A:K) => A
   rule formLambdaList(ListItem(A:K) L:List, B:K)
          => lambda(A, formLambdaList(L, B))

   syntax KItem ::= formDoCons(List, K) [function]
   rule formDoCons(.List, A:K) => A
   rule formDoCons(ListItem(A:K) L:List, B:K)
         => seq(A, formDoCons(L, B))

   syntax KItem ::= formGuardCons(List) [function]
   rule formGuardCons(.List) => none
   rule formGuardCons(ListItem(tempGuard(A:List, B:K)) L:List)
          => ifElse(A, B, formGuardCons(L))

   //check if the pattern list in a function in a class has all same number of args
   syntax KItem ::= checkMethodPatNumbers(Map, K) [function]
                  | checkMethodPatNumbersList(Map, List) [function]
                  | checkMethodPatNumbersListAux(Map, List, Int) [function]
   rule checkMethodPatNumbers(.Map, .K) => .K
   rule checkMethodPatNumbers(M:Map (A:K |-> B:K), .K)
          => checkMethodPatNumbers(M, B)
   rule checkMethodPatNumbers(M:Map, resultList(L:List))
         => checkMethodPatNumbersList(M, L)
   rule checkMethodPatNumbers(M:Map, methodDef(S:Set, T:K, L:List))
         => checkMethodPatNumbersList(M, L)

   rule checkMethodPatNumbersList(M:Map, .List)
                         => checkMethodPatNumbers(M, .K)
   rule checkMethodPatNumbersList(M:Map, ListItem(funAssign(A:List, B:K)) L:List)
              => checkMethodPatNumbersListAux(M, L, size(A))
   rule checkMethodPatNumbersListAux(M:Map, .List, N:Int)
              => checkMethodPatNumbers(M, .K)
   rule checkMethodPatNumbersListAux(M:Map,
              ListItem(funAssign(A:List, B:K)) L:List, N:Int)
            => checkMethodPatNumbersListAux(M, L, N)
        requires size(A) ==K N
   rule checkMethodPatNumbersListAux(M:Map,
              ListItem(funAssign(A:List, B:K)) L:List, N:Int)
            => error(instanceMethodArgsNoMatch)
        requires size(A) =/=K N

   //transformation of expressions in a module, bascially an exp is a decl
   syntax KItem ::= transDeclFun(Int, K, K, Set, Map)  [function]
                  | transDeclFunAux(K, K, Set, Map)    [function]
                  | transDeclFunAux1(K, K, Set)        [function]
                 //gen-var, cur-mod, decl, function-name-set, fun-map
   rule transDeclFun(N:Int, Mod:K, 'declFunLhsRhs(F:FunLhs,, R:Rhs), S:Set, M:Map)
          => transDeclFunAux(transFunLhs(Mod, F), transRhs(N, Mod, R), S, M)
        requires notBool getCoreVar(F) in S orBool getCoreVar(F) in keys(M)
   rule transDeclFun(N:Int, Mod:K, 'declFunLhsRhs(F:FunLhs,, R:Rhs), S:Set, M:Map)
          => error(classVarCollipse)
        requires getCoreVar(F) in S andBool notBool getCoreVar(F) in keys(M)
   rule transDeclFun(N:Int, Mod:K, 'declPatRhs(F:Pat,, R:Rhs), S:Set, M:Map)
          => transDeclFunAux1(transPat(Mod, F), transRhs(N, Mod, R), S)

   rule transDeclFunAux(funPat(ListItem(X:K) L:List), resultTrans(N:Int, B:K), S:Set, M:Map)
             => resultTransSetMap(N, SetItem(X), updatePatMapInExp(M, X, funAssign(L, B)))
   rule transDeclFunAux(A:K, error(B:K), S:Set, M:Map) => error(B)

   rule transDeclFunAux1(A:K, error(B:K), S:Set) => error(B)
   rule transDeclFunAux1(A:K, resultTrans(N:Int, B:K), S:Set)
             => resultTransSetTerm(N, S, lambdaAssign(A, B))

   //add type/context to method def in a map
   syntax KItem ::= addDeclToK(K, Set, K) [function]
   rule addDeclToK(methodDef(S:Set, T:K, L:List), S1:Set, T1:K)
           => methodDef(S1, T1, L)

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
          => createEmptyEntry(M (A |-> methodDef(.Set, .K, ListItem(none))), .K, S)

   //check if the method definition has defined pattern /types
   syntax Bool ::= hasDefinedPat(K) [function]
                 | hasNoDefinedPats(Set, K) [function]
   rule hasDefinedPat(methodDef(A:Set, B:K, .List)) => false
   rule hasDefinedPat(methodDef(A:Set, B:K, ListItem(C:K) L:List)) => true
   rule hasNoDefinedPats(.Set, .K) => true
   rule hasNoDefinedPats(SetItem(A:K) S:Set, .K)
          => hasNoDefinedPats(S, A)
   rule hasNoDefinedPats(S:Set, A:KItem) => hasNoDefinedPats(S, .K)
        requires notBool hasDefinedPat(A)
   rule hasNoDefinedPats(S:Set, A:KItem) => false
        requires hasDefinedPat(A)

   syntax Bool ::= hasDefinedType(K) [function]
                 | hasNoDefinedTypes(Set, K) [function]
   rule hasDefinedType(methodDef(A:Set, T:K, L:List)) => T =/=K .K
   rule hasNoDefinedTypes(.Set, .K) => true
   rule hasNoDefinedTypes(SetItem(A:K) S:Set, .K)
          => hasNoDefinedTypes(S, A)
   rule hasNoDefinedTypes(S:Set, A:KItem) => hasNoDefinedTypes(S, .K)
        requires notBool hasDefinedType(A)
   rule hasNoDefinedTypes(S:Set, A:KItem) => false
        requires hasDefinedType(A)


   //trans top level decls
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


   //a function to transfer decls to ast form.
   syntax KItem ::= transRhs(Int, K, K) [function]
                  | transRhsAux(K, K, K) [function]
                  | transRhsAuxAux(K, K) [function]
                  //group of functions to trans decls
                  | transDecls(Int, K, K) [function]
                  | transDeclsAux(Int, K, DeclsList, K, List) [function]
                  | transDecl(Int, K, K) [function]
                  | transDeclAux(K, K)   [function]
                  //trans guards
                  | transGuards(Int, K, K, List) [function]
                  | transGuardsAux(K, K, K, K, List) [function]
                  | transGuardsAuxAux(K, K, K, K, List) [function]
                  | transGuardCons(Int, K, K, K, List) [function]
                  | transGuardCon(Int, K, K) [function]
                  | transGuardConAux(K, K)   [function]
                  | transGuardConAux1(K)     [function]
                  //trans expressions
                  | transExp(Int, K, K) [function]
                  | transLambda(List, K) [function]
                  | transExpMinus(K) [function]
                  | transExpInfix(K, K, K, K) [function]
                  | transExpInfixAux(K, K, K) [function]
                  | transExpAssign(K, K) [function]
                  | transExpAssignContext(K, Set, K) [function]
                  //helper functions for let in
                  | transLetIn(K, K, K) [function]
                  | transLetInAux(List, K) [function]
                  //helper functions for if statements
                  | transExpIf(K, K, K, K) [function]
                  | transExpIfAux(K, K, K, K) [function]
                  | transExpIfAuxAux(K, K, K) [function]
                  //helper functions for case of
                  | transExpCase(K, K, K) [function]
                  | transExpAlts(K, Int, K, K, K, List) [function]
                  | transExpAlt(K, K, K) [function]
                  | transExpAltAux2(K, K) [function]
                  | transExpAltAux(K, K, K, K) [function]
                  | transExpAltAuxAux(K, K, K) [function]
                  //helper funtions for do stmt
                  | transExpDo(K, K, K) [function]
                  | transExpStmts(K, Int, K, StmtList, K, List) [function]
                  | transExpStmt(Int, K, K) [function]
                  | transExpStmtAux(K) [function]
                  | transExpStmtAux1(K, K) [function]
                  | transExpStmtAux2(K) [function]
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
                  | transLeftSection(K, K) [function]
                  | transRightSection(K, K) [function]

   syntax List ::= genDeclForVars(K, Vars,Set, K) [function]
   rule genDeclForVars(Mod:K, A:Var,S:Set, T:K)
               => ListItem(methodDecl(pillVar(A), S, T))
   rule genDeclForVars(Mod:K, 'varCon(A:Var, B:Vars),S:Set, T:K)
               => ListItem(methodDecl(pillVar(A), S, T))
                   genDeclForVars(Mod, B,S, T)

         //curr-mod-name, exp
   //rule transRhs(Mod:K, 'normalRhs(E:Exp,, D:OptDecls))
    //       => rhs(transExp(Mod, E), transDecls(Mod, D))
   //trans lambdaexp 
   rule transExp(N:Int, Mod:K, 'lambdaExp(As:APatList,, B:Exp))
         => transLambda(transAPatList(Mod, As), transExp(N, Mod, B))
   rule transLambda(L:List, error(A:K)) => error(A)
   rule transLambda(L:List, resultTrans(N:Int, A:K))
            => resultTrans(N, formLambdaList(L, A))

   //trans let term
   rule transExp(N:Int, Mod:K, 'letInExp(As:Decls,, B:Exp))
           => transLetIn(transDecls(N, Mod, As), Mod, B)
   rule transLetIn(error(A:K), Mod:K, B:K) => error(A)
   rule transLetIn(resultTransList(N:Int, A:List), Mod:K, B:K)
          => transLetInAux(A, transExp(N, Mod, B))
   rule transLetInAux(As:List, error(B:K)) => error(B)
   rule transLetInAux(As:List, resultTrans(N:Int, B:K))
             => resultTrans(N, letIn(As, B))

   //trans if statement
   rule transExp(N:Int, Mod:K, 'ifElseExp(A:Exp,,
            Op1:OptSemicolon,, B:Exp,, Op2:OptSemicolon,, C:Exp))
          => transExpIf(transExp(N, Mod, A), Mod, B, C)
   rule transExpIf(error(A:K), Mod:K, B:K, C:K) => error(A)
   rule transExpIf(resultTrans(N:Int, A:K), Mod:K, B:K, C:K)
         => transExpIfAux(A, transExp(N, Mod, B), Mod, C)
   rule transExpIfAux(A:K, error(B:K), Mod:K, C:K) => error(B)
   rule transExpIfAux(A:K, resultTrans(N:Int, B:K), Mod:K, C:K)
           => transExpIfAuxAux(A, B, transExp(N, Mod, C))
   rule transExpIfAuxAux(A:K, B:K, error(C:K)) => error(C)
   rule transExpIfAuxAux(A:K, B:K, resultTrans(N:Int, C:K))
         => resultTrans(N, ifElse(ListItem(A), B, C))

   //trans case analysis
   rule transExp(N:Int, Mod:K, 'caseExp(A:Exp,, Bs:Alts))
          =>  transExpCase(transExp(N, Mod, A), Mod, Bs)
   rule transExpCase(error(A:K), Mod:K, Bs:K) => error(A)
   rule transExpCase(resultTrans(N:Int, A:K), Mod:K, Bs:K)
           => transExpAlts(A, N, Mod, Bs, .K, .List)
   
   rule transExpAlts(A:K, N:Int, Mod:K, .K, .K, L:List)
          => resultTrans(N, caseOf(A, L))
   rule transExpAlts(A:K, N:Int, Mod:K, B:Alt, .K, L:List)
          => transExpAlts(A, N, Mod, .K, transExpAlt(N, Mod, B), L)
   rule transExpAlts(A:K, N:Int, Mod:K,
                    'altCon(B:Alt,, Bs:Alts), .K, L:List)
          => transExpAlts(A, N, Mod, Bs, transExpAlt(N, Mod, B), L)
   rule transExpAlts(A:K, N:Int, Mod:K, Bs:K, error(B:K), L:List) => error(B)
   rule transExpAlts(A:K, N:Int, Mod:K, Bs:K, resultTransList(N':Int, B:List), L:List)
           => transExpAlts(A, N', Mod, Bs, .K, L B)

   rule transExpAlt(N:Int, Mod:K, 'altArrow(A:Pat,, B:Exp))
           => transExpAltAux2(transPat(Mod, A), transExp(N, Mod, B))
   rule transExpAlt(N:Int, Mod:K, 'emptyAlt(.KList))
             => resultTransList(N, .List)
   rule transExpAlt(N:Int, Mod:K, 'altArrow(A:Pat,, B:Exp,, C:Decls))
          => transExpAltAux(transPat(Mod,A), transExp(N, Mod, B), Mod, C)

   rule transExpAltAux2(A:K, error(B:K)) => error(B)
   rule transExpAltAux2(A:K, resultTrans(N:Int, B:K))
                 => resultTransList(N, ListItem(singleCase(A, B, .List)))
   rule transExpAltAux(A:K, error(B:K), Mod:K, C:K) => error(B)
   rule transExpAltAux(A:K, resultTrans(N:Int, B:K), Mod:K, C:K)
          => transExpAltAuxAux(A, B, transDecls(N, Mod, C))
   rule transExpAltAuxAux(A:K, B:K, error(C:K)) => error(C)
   rule transExpAltAuxAux(A:K, B:K, resultTransList(N:Int, C:List))
          => resultTransList(N, ListItem(singleCase(A, B, C)))

   //trans do stmt
   rule transExp(N:Int, Mod:K, 'doExp(
            'stmtMain(A:StmtList,, B:Exp,, C:OptSemicolon)))
           => transExpDo(Mod, A, transExp(N, Mod, B))
   rule transExpDo(Mod:K, A:K, error(B:K)) => error(B)
   rule transExpDo(Mod:K, A:StmtList, resultTrans(N:Int, B:K))
          => transExpStmts(B, N, Mod, A, .K, .List)

   rule transExpStmts(B:K, N:Int, Mod:K, .StmtList, .K, L:List)
            => resultTrans(N, formDoCons(L, B))
   rule transExpStmts(B:K, N:Int, Mod:K, 'stmtCon(A:Stmt,, As:StmtList), .K, L:List)
            => transExpStmts(B, N, Mod, As, transExpStmt(N, Mod, A), L)
   rule transExpStmts(B:K, N:Int, Mod:K, As:K, error(A:K), L:List) => error(A)
   rule transExpStmts(B:K, N:Int, Mod:K, As:K, resultTransList(N':Int, A:List), L:List)
            => transExpStmts(B, N', Mod, As, .K, L A)

   rule transExpStmt(N:Int, Mod:K, 'expStmt(E:Exp))
           => transExpStmtAux(transExp(N, Mod, E))
   rule transExpStmt(N:Int, Mod:K, 'patExpStmt(A:Pat,, E:Exp))
           => transExpStmtAux1(transPat(Mod, A), transExp(N, Mod, E))
   rule transExpStmt(N:Int, Mod:K, 'letStmt(Ds:Decls))
           => transExpStmtAux2(transDecls(N, Mod, Ds))
   rule transExpStmt(N:Int, Mod:K, 'emptyStmt(.KList)) => resultTrans(N, .List)
   rule transExpStmtAux(error(A:K)) => error(A)
   rule transExpStmtAux(resultTrans(N:Int, A:K))
           => resultTransList(N, ListItem(A))
   rule transExpStmtAux1(A:K, error(B:K)) => error(B)
   rule transExpStmtAux1(A:K, resultTrans(N:Int, B:K))
          => resultTransList(N, ListItem(appExp(fullName(Prelude, qualAssignAst),
                           ListItem(A) ListItem(B))))
   rule transExpStmtAux2(error(A:K)) => error(A)
   rule transExpStmtAux2(resultTransList(N:Int, A:List))
          => resultTransList(N, ListItem(appExp(fullName(Prelude, qualLetAst), A)))

   //trans basic Exp 
   rule transExp(N:Int, Mod:K, A:QVar) => resultTrans(N, A)
   rule transExp(N:Int, Mod:K, A:GCon) => resultTrans(N, transExpCon(Mod, A))
   rule transExp(N:Int, Mod:K, I:Integer) => resultTrans(N, String2Int(#tokenToString(I)))
   rule transExp(N:Int, Mod:K, I:CusFloat) => resultTrans(N, String2Float(#tokenToString(I)))
   rule transExp(N:Int, Mod:K, I:CusChar) => resultTrans(N, #tokenToString(I))
   rule transExp(N:Int, Mod:K, I:CusString) => resultTrans(N, #tokenToString(I))
   rule transExp(N:Int, Mod:K, 'minusInfix(E:InfixExp))
            => transExpMinus(transExp(N, Mod, E))
   rule transExpMinus(error(A:K)) => error(A)
   rule transExpMinus(resultTrans(N:Int, A:K))
           => resultTrans(N, appExp('minusCon(.KList), ListItem(A)))

   rule transExp(N:Int, Mod:K, 'binInfixExp(A:LExp,, G:QOp,, B:InfixExp))
          => transExpInfix(transVar(Mod, G), transExp(N, Mod, A), Mod, B)
   rule transExpInfix(A:K, error(B:K), Mod:K, C:K) => error(B)
   rule transExpInfix(A:K, resultTrans(N:Int, B:K), Mod:K, C:K)
          => transExpInfixAux(A, B, transExp(N, Mod, C))
   rule transExpInfixAux(A:K, B:K, error(C:K)) => error(C)
   rule transExpInfixAux(A:K, B:K, resultTrans(N:Int, C:K))
           => resultTrans(N, appExp(A, ListItem(appExp(B, ListItem(C)))))

   //trans exp with types
   rule transExp(N:Int, Mod:K, 'expAssign(E:Exp,, T:Type))
             => transExpAssign(transExp(N, Mod, E), toAbsType(Mod, T))
   rule transExpAssign(error(A:K), T:K) => error(A)
   rule transExpAssign(resultTrans(N:Int, A:K), T:K)
            => resultTrans(N, typedExp(.Set, T, A))
   rule transExp(N:Int, Mod:K, 'expAssignContext(E:Exp,, C:Context,, T:Type))
             => transExpAssignContext(transExp(N, Mod, E),
                      contextToSet(Mod, C), toAbsType(Mod, T))
   rule transExpAssignContext(error(A:K), S:Set, T:K) => error(A)
   rule transExpAssignContext(resultTrans(N:Int, A:K), S:Set, T:K)
            => resultTrans(N, typedExp(S, T, A))

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
   rule transQualLet(resultTransList(N:Int, B:List))
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
        requires G =/=K 'minusCon(.KList)
   rule transExp(N:Int, Mod:K, 'rightSection('minusCon(.KList),, E1:InfixExp))
                 => error(syntaxError)

   rule transRightSection(B:K, error(A:K)) => error(A)
   rule transRightSection(B:K, resultTrans(N:Int, A:K))
          => resultTrans(N +Int 1, lambda(genVar(N), appExp(B,
                       ListItem(genVar(N)) ListItem(A))))

   //trans Decls
   rule transDecls(N:Int, Mod:K, 'emptyOptDecls(.KList))
            => resultTransList(N, .List)
   rule transDecls(N:Int, Mod:K, 'whereDecls('decls(Ds:DeclsList)))
           => transDeclsAux(N, Mod, Ds, .K, .List)
   
   rule transDeclsAux(N:Int, Mod:K, .DeclsList, .K, L:List)
           => resultTransList(N, L)
   rule transDeclsAux(N:Int, Mod:K, 'declsCon(D:Decl,, Ds:DeclsList),
                     .K, L:List)
           => transDeclsAux(N, Mod, Ds, transDecl(N, Mod, D), L)
   rule transDeclsAux(N:Int, Mod:K, Ds:DeclsList, error(A:K), L:List)
          => error(A)
   rule transDeclsAux(N:Int, Mod:K, Ds:DeclsList, resultTransList(N':Int, A:List), L:List)
             => transDeclsAux(N', Mod, Ds, .K, L A)

   rule transDecl(N:Int, Mod:K, 'emptyGenDecl(.KList)) => resultTransList(N, .List)
   rule transDecl(N:Int, Mod:K, 'varAssign(A:Vars,, B:Type))
         => resultTransList(N, genDeclForVars(Mod, A, .Set, toAbsType(Mod, B)))
   rule transDecl(N:Int, Mod:K, 'genAssignContext(A:Vars,, C:Context,, B:Type))
         => resultTransList(N, genDeclForVars(Mod, A,
                       contextToSet(Mod, C), toAbsType(Mod, B)))
   rule transDecl(N:Int, Mod:K, 'declFunLhsRhs(A:FunLhs,, B:Rhs))
         => transDeclAux(transFunLhs(Mod, A), transRhs(N, Mod, B))
   rule transDecl(N:Int, Mod:K, 'declPatRhs(A:Pat,, B:Rhs))
         => transDeclAux(transFunLhs(Mod, A), transRhs(N, Mod, B))

   rule transDeclAux(A:K, error(B:K)) => error(B)
   rule transDeclAux(A:K, resultTrans(N:Int, B:K))
                => resultTransList(N, ListItem(lambdaAssign(A, B)))

   //trans rhs 
   rule transRhs(N:Int, Mod:K, 'normalRhs(A:Exp,, B:OptDecls))
          => transRhsAux(transExp(N, Mod, A), Mod, B)
   rule transRhs(N:Int, Mod:K, 'guardRhs(A:GdRhs,, B:OptDecls))
          => transRhsAux(transGuards(N, Mod, A, .List), Mod, B)

   rule transRhsAux(error(A:K), Mod:K, B:K) => error(A)
   rule transRhsAux(resultTrans(N:Int, A:K), Mod:K, B:K)
           => transRhsAuxAux(A, transDecls(N, Mod, B))
   rule transRhsAuxAux(A:K, error(B:K)) => error(B)
   rule transRhsAuxAux(A:K, resultTransList(N:Int, B:List))
           => resultTrans(N, body(A, B))

   //trans guards in rhs
   rule transGuards(N:Int, Mod:K, 'guardSingle(
                  'startGuardCons(G:GuardList),, E:Exp), L:List)
           => transGuardsAux(Mod, G, transExp(N, Mod, E), .K,  L)
   rule transGuards(N:Int, Mod:K, 'guardCon(
               'startGuardCons(G:GuardList),, E:Exp,, Gs:GdRhs), L:List)
           => transGuardsAux(Mod, G, transExp(N, Mod, E), Gs,  L)

   rule transGuardsAux(Mod:K, G:K, error(A:K), Es:K, L:List) => error(A)
   rule transGuardsAux(Mod:K, G:K, resultTrans(N:Int, B:K), Es:K, L:List)
            => transGuardsAuxAux(Mod, transGuardCons(N, Mod, G, .K, .List), B, Es, L)

   rule transGuardsAuxAux(Mod:K, error(A:K), B:K, Es:K, L:List) => error(A)
   rule transGuardsAuxAux(Mod:K,resultTransList(N:Int, A:List), B:K, .K, L:List)
          => resultTrans(N, formGuardCons(L ListItem(tempGuard(A, B))))
   rule transGuardsAuxAux(Mod:K,resultTransList(N:Int, A:List), B:K, Es:GdRhs, L:List)
          => transGuards(N, Mod, Es, L ListItem(tempGuard(A, B)))

   rule transGuardCons(N:Int, Mod:K, .K, .K, L:List) => resultTransList(N, L)
   rule transGuardCons(N:Int, Mod:K, A:Guard, .K, L:List)
          => transGuardCons(N, Mod, .K, transGuardCon(N, Mod, A), L)
   rule transGuardCons(N:Int, Mod:K,
            'guardListCon(A:Guard,, As:GuardList), .K, L:List)
          => transGuardCons(N, Mod, As, transGuardCon(N, Mod, A), L)
   rule transGuardCons(N:Int, Mod:K, G:K, error(A:K), L:List) => error(A)
   rule transGuardCons(N:Int, Mod:K, G:K, resultTrans(N':Int, A:K), L:List)
                   => transGuardCons(N', Mod, G, .K, L)

   rule transGuardCon(N:Int, Mod:K, 'guardAssign(A:Pat,, B:InfixExp))
            => transGuardConAux(transPat(Mod,A), transExp(N, Mod, B))
   rule transGuardCon(N:Int, Mod:K, 'guardLet(A:Decls))
            => transGuardConAux1(transDecls(N, Mod, A))
   rule transGuardCon(N:Int, Mod:K, A:InfixExp) => transExp(N, Mod, A)

   rule transGuardConAux(A:K, error(B:K)) => error(B)
   rule transGuardConAux(A:K, resultTrans(N:Int, B:K))
             => resultTrans(N, appExp(fullName(Prelude, qualAssignAst),
                           ListItem(A) ListItem(B)))
   rule transGuardConAux1(error(B:K)) => error(B)
   rule transGuardConAux1(resultTransList(N:Int, L:List))
            => resultTrans(N, appExp(fullName(Prelude, qualLetAst), L))

   //pattern transformation is self-contained
   syntax KItem ::= transPat(K, K) [function]
                  | transPatList(K, PatList) [function]
                  | transFunLhs(K, K) [function]
                  | insertAPatList(K, List) [function]

   syntax List ::= transFPats(K, FPats) [function]
                 | transPatTuple(K, PatTuple) [function]
                 | transAPatList(K, APatList) [function]

   rule transFunLhs(Mod:K, P:Pat)
         => funPat(ListItem(transPat(Mod, P)))
   rule transFunLhs(Mod:K, 'normalLhs(V:Var,, As:APatList))
         => funPat(ListItem(transPat(Mod, V)) transAPatList(Mod, As))
   rule transFunLhs(Mod:K, 'binLhs(P1:Pat,, V:VarOp,, P2:Pat))
         => funPat(ListItem(transVar(Mod,V))
                  ListItem(transPat(Mod, P1)) ListItem(transPat(Mod, P2)))
   rule transFunLhs(Mod:K, 'groupLhs(F:FunLhs,, As:APatList))
         => insertAPatList(transFunLhs(Mod, F), transAPatList(Mod, As))
   rule insertAPatList(funPat(L:List), L2:List) => funPat(L L2)

   rule transPat(Mod:K, 'binPattern(A:LPat,, B:QConOp,, C:Pat))
           => appPat(transVar(Mod, B),
                 ListItem(transPat(Mod, A)) ListItem(transPat(Mod, C)))
   rule transPat(Mod:K, V:Var) => pillVar(V)
   rule transPat(Mod:K, V:Var @ A:APat) => asPat(pillVar(V), transPat(Mod, A))
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

endmodule
