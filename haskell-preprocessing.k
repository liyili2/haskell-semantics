requires "haskell-syntax.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX

    configuration <k> getPreModule($PGM:Module) </k>

    syntax KItem ::= Module(K, K)

    //rule getPreModule(module I:ModId where J:Body) => preModule(J)
    //rule getPreModule({I:TopDecls}) => getPreModule(I)
    //rule getPreModule(data I:OptContext J K L) => preModule(I)

    syntax KItem ::= getPreModule (K) [function]
    syntax KItem ::= preModule(K)
    rule getPreModule('module(I:ModuleName,, J:K)) => preModule(J)
endmodule
