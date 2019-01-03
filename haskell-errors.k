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

    rule <k> error(typeVarNoInclusive) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type whose typevars are not inclusive with the type declaration.")) </output>

    rule <k> error(repeatedNames) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type/data-type whose name is repeated once in the module.")) </output>

    rule <k> error(cycleAlpha) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have type delcarations having cycles in the renaming.")) </output>

    rule <k> error(typeNotInScope) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type delcaration whose type cons might not be properly imported or created.")) </output>

    rule <k> error(typeVarNotInScope) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type delcaration whose used type vars might not be properly declared in the title of the type.")) </output>

    rule <k> error(typeConKindBad) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type delcaration having a type con that appears in the wrong position or has bad number of arguments.")) </output>

    rule <k> error(typeConKindNumError) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type delcaration having a type con that has wrong number of arguments.")) </output>

    rule <k> error(typeVarKindBad) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type delcaration having a type variable that appears in the wrong position or has bad number of arguments.")) </output>

    rule <k> error(typeVarKindNumError) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type delcaration having a type variable that has wrong number of arguments.")) </output>

endmodule
