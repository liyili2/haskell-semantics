requires "haskell-syntax.k"

module HASKELL-CONFIGURATION
    imports HASKELL-SYNTAX

    syntax KItem ::= initPreModule(K) [function]
    syntax KItem ::= tChecker(K) [function]

    configuration 
        <T>
            <k> tChecker(initPreModule($PGM:Module)) </k>
        </T>

endmodule
