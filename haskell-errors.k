//configuration of haskell
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"
requires "haskell-configuration.k"

module HASKELL-ERRORS
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX
    imports HASKELL-CONFIGURATION

    rule <k> error(cyclicImports) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a circle in the import relations")) </output>

endmodule
