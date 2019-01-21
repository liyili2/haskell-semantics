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



endmodule
