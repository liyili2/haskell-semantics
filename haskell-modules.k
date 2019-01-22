//helper functions for the haskell semantics.
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"
requires "haskell-helper.k"
requires "haskell-kindinfer.k"
requires "haskell-transformation.k"

module HASKELL-MODULES
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX
    imports HASKELL-HELPER
    imports HASKELL-KINDINFER
    imports HASKELL-TRANSFORMATION

    syntax Set ::= toExports(K, K) [function]
           //deal with exports, curr-mod, term, result-set
    syntax KItem ::= toExportsAux(K, List) [function]
    rule toExports(Mod:K, 'exportWrap(A:K,, B:K)) => toExports(Mod, A)
    rule toExports(Mod:K, .ExportList) => .Set
    rule toExports(Mod:K, 'exportCon(A:QVar,, B:ExportList))
           => SetItem(transVar(Mod, A)) toExports(Mod, B)
    rule toExports(Mod:K, 'exportCon('moduleName(A:K),, B:ExportList))
           => SetItem(moduleNameAst(A)) toExports(Mod, B)
    rule toExports(Mod:K, 'exportCon('exportTyCon(A:K,, B:K),, C:ExportList))
           => SetItem(toExportsAux(transVar(Mod, A), transCName(Mod, B))) toExports(Mod, C)

    rule toExportsAux(A:K, .List) => appExp(A, ListItem(absClass))
    rule toExportsAux(A:K, ListItem(B:K) L:List)
                  => appExp(A, ListItem(B:K) L:List)

    syntax List ::= transCName(K, K) [function]
    rule transCName(Mod:K, 'allInclude(.KList)) => ListItem(haveAll)
    rule transCName(Mod:K, 'emptyOptCNameList(.KList)) => .List
    rule transCName(Mod:K, .CQList) => .List
    rule transCName(Mod:K, 'cnameCon(A:K,, B:K))
          => transCName(Mod:K, A) transCName(Mod:K, B)
    rule transCName(Mod:K, V:CQName) => transVar(Mod, V)

    syntax KItem ::= transCNameWithFailure(K, K, List) [function]
    rule transCNameWithFailure(Mod:K, 'allInclude(.KList), L:List)
            => resultList(ListItem(haveAll))
    rule transCNameWithFailure(Mod:K, 'emptyOptCNameList(.KList), L:List)
           => resultList(.List)
    rule transCNameWithFailure(Mod:K, .CQList, L:List) => resultList(L)
    rule transCNameWithFailure(Mod:K, 'cnameCon(A:Var,, B:K), L:List)
          => transCNameWithFailure(Mod:K, B, L ListItem(transVar(Mod, A)))
    rule transCNameWithFailure(Mod:K, 'cnameCon(A:Con,, B:K), L:List)
          => transCNameWithFailure(Mod:K, B, L ListItem(transVar(Mod, A)))
    rule transCNameWithFailure(Mod:K, 'cnameCon(A:QVar,, B:K), L:List)
          => error(syntaxError)


    //transformation of imports 
    syntax Bool ::= transQualified(K) [function]
    rule transQualified('emptyQualified(.KList)) => false
    rule transQualified(qualified) => true

    syntax KItem ::= getAsModId(K) [function]
    rule getAsModId('emptyOptAsModId(.KList)) => .K
    rule getAsModId('asModid(A:K)) => A

    syntax KItem ::= transImportList(K, K, Set) [function]
                   | transImportListAux(K, K, K, K, Set) [function]
    rule transImportList(Mod:K, .ImportList, S:Set) => resultSet(S)
    rule transImportList(Mod:K, 'importCon(A:Var,, As:ImportList), S:Set)
             => transImportList(Mod, As, SetItem(transVar(Mod, A)) S)
    rule transImportList(Mod:K, 'importCon(
             'importTyCon(T:TyCon,, C:OptCQList),, As:ImportList), S:Set)
             => transImportListAux(Mod, As, transVar(Mod, T),
                      transCNameWithFailure(Mod, C, .List), S)
    rule transImportListAux(Mod:K, As:K, A:K, error(B:K), S:Set) => error(B)
    rule transImportListAux(Mod:K, As:K, A:K, resultList(L:List), S:Set)
            => transImportList(Mod, As, S SetItem(appExp(A, L)))



    syntax KItem ::= genImportSet(K, K, Set) [function]
                   | genImportSetAux(K, K, K, Set) [function]
                   | genImportSetNext(K, K, K, K, Set) [function]
                   | genImportSetNext1(K, K, K, K, Set) [function]
                   | genImportSetNext2(K, K, K, K, Set) [function]

    rule genImportSet(Mod:K, 'bodyimpandtop(I:ImpDecls,, T:TopDecls), S:Set)
          => genImportSet(Mod, I, S)
    rule genImportSet(Mod:K, 'bodyimpdecls(I:ImpDecls), S:Set)
          => genImportSet(Mod, I, S)
    rule genImportSet(Mod:K, 'bodytopdecls(T:TopDecls), S:Set) => resultImportSet(S)
    rule genImportSet(Mod:K, .ImpDecls, S:Set) => resultImportSet(S)
    rule genImportSet(Mod:K, 'impDecls(I:ImpDecl,, Is:ImpDecls), S:Set)
            => genImportSetAux(Mod, I, Is, S)
    rule genImportSetAux(Mod:K, 'emptyImpDecl(.KList), Is:K, S:Set)
           => genImportSet(Mod, Is, S)
    rule genImportSetAux(Mod:K, 'impDecl(A:OptQualified,, B:ModId,,
                  C:OptAsModId,, D:OptImpSpec), Is:K, S:Set)
          => genImportSetNext(Mod, Is, importElem(
                transQualified(A), B, getAsModId(C), .Set, .Set), D, S)

    rule genImportSetNext(Mod:K, Is:K, A:K, 'emptyOptImpSpec(.KList), S:Set)
            => genImportSet(Mod, Is, SetItem(A) S)
    rule genImportSetNext(Mod:K, Is:K, X:K, 'impSpecKey(
            A:ImportList,, P:OptComma), S:Set)
          => genImportSetNext1(Mod, Is, X, transImportList(Mod, A, .Set), S)
    rule genImportSetNext(Mod:K, Is:K, X:K, 'hidingCon('impSpecKey(
            A:ImportList,, P:OptComma)), S:Set)
          => genImportSetNext2(Mod, Is, X, transImportList(Mod, A, .Set), S)

    rule genImportSetNext1(Mod:K, Is:K, X, error(A:K), S:Set) => error(A)
    rule genImportSetNext1(Mod:K, Is:K, importElem(
             X:K, Y:K, Z:K, As:Set, Ns:Set), resultSet(As':Set), S:Set)
           => genImportSet(Mod, Is, S SetItem(importElem(X, Y, Z, As', Ns)))
    rule genImportSetNext2(Mod:K, Is:K, X, error(A:K), S:Set) => error(A)
    rule genImportSetNext2(Mod:K, Is:K, importElem(
             X:K, Y:K, Z:K, As:Set, Ns:Set), resultSet(Ns':Set), S:Set)
           => genImportSet(Mod, Is, S SetItem(importElem(X, Y, Z, As, Ns')))




endmodule
