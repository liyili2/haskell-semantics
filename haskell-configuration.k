requires "haskell-syntax.k"

module HASKELL-CONFIGURATION
    imports HASKELL-SYNTAX

    syntax KItem ::= callInit(K)
    //syntax KItem ::= initPreModule(K) [function]
    //syntax KItem ::= tChecker(K) [function]

    configuration 
        <T>
            <k> callInit($PGM:Module) </k>
            <tempModule> .K </tempModule>
            <tempAlpha> .Map </tempAlpha>
            <tempT> .K </tempT>
        </T>

endmodule
