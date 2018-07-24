requires "haskell-syntax.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX

    configuration <k> getPreModule($PGM:Module) </k>

    syntax KItem ::= Module(K, K)

    //rule getPreModule(module I:ModId where J:Body) => preModule(J)
    //rule getPreModule({I:TopDecls}) => getPreModule(I)
    //rule getPreModule(data I:OptContext J K L) => preModule(I)

    syntax KItem ::= fetchTypes (K) [function]
    syntax KItem ::= getPreModule (K) [function]
    syntax KItem ::= preModule(K, K)
    rule getPreModule('module(I:ModuleName,, J:K)) => getPreModule(J) ~> preModule(.K,J)
    rule getPreModule({ I:TopDecls }:Body) => getPreModule(I)
    rule getPreModule(data I:K J:K L:K M:K ; _) => fetchTypes(J)
    //rule getPreModule('module(I:ModuleName,L:K, J:K)) => preModule(J)

    rule fetchTypes(I:TyCon _) ~> preModule(L:K, J:K) => preModule((I,L),J)
endmodule
