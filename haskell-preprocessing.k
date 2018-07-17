requires "haskell-syntax.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX

    syntax KItem ::= preModule(K)
    syntax KItem ::= Module(K, K)
    syntax KItem ::= getPreModule (K) [function]
    rule getPreModule((I:Body):Module) => preModule(I)

configuration <k> getPreModule($PGM:Module) </k>
endmodule
