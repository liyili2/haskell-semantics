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

    rule <k> error(kindUnifierFail) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type delcaration that uses a type variable or type con in the wrong position causing kind inference failure.")) </output>

    rule <k> error(ambiguousTypeVar) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type class whose method does not define the type var for the type class, so it is an ambiguous type variable.")) </output>

    rule <k> error(classVarCollipse) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type class/method whose name or method name copplipses with the type variables or the methods names.")) </output>

    rule <k> error(classVarNotInScope) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type instance whose name does not show in the original type class.")) </output>

    rule <k> error(classMethodVarNotInScope) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type class one of whose method name for a method definition does not show in the original type class.")) </output>

    rule <k> error(syntaxError) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a expression that has syntactic error.")) </output>

    rule <k> error(instanceInstNotDistinct) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have an instance having type vars that are not distinct in a type.")) </output>

    rule <k> error(instanceMethodArgsNoMatch) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have an instance having method definitions that have different size of arguments.")) </output>

    rule <k> error(moreThanOneDefault) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module have more than one default definitions.")) </output>

    rule <k> error(importFromNoSource) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module have an import a construct/type/function that is not in the original module.")) </output>

endmodule
