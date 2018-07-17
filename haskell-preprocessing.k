requires "haskell-syntax.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX

    syntax KItem ::= preModule(K)
    syntax KItem ::= Module(K, K)
    syntax KItem ::= getPreModule (K) [function]
    rule getPreModule(module I:ModId where J:Body) => preModule(J)
    //rule getPreModule({I:TopDecls}) => getPreModule(I)
    //rule getPreModule(data I:OptContext J K L) => preModule(I)

configuration <k> getPreModule($PGM:Module) </k>
endmodule
