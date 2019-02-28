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

    rule <k> error(typeVarNotUnique) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type whose at least two of the typevars having the same name.")) </output>

    rule <k> error(repeatedNames) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type/data-type whose name is repeated once in the module.")) </output>

    rule <k> error(declNoInstance) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type/data-type whose name is repeated once in the module.")) </output>

    rule <k> error(cycleAlpha) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type signature lacking an accompanying binding.")) </output>

    rule <k> error(funNameDeclNotDef) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules declare a function but never define it.")) </output>

    rule <k> error(funNameDefNotDeclInClass) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a class that defines a function but never declares it.")) </output>

    rule <k> error(funNameConflicting) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module has a pattern uses conflicting arguments where it has more than two pattern variables having the same name.")) </output>

    rule <k> error(duplicateDecl) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module declares a same function twice.")) </output>

    rule <k> error(typeNotInScope) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type delcaration whose type cons might not be properly imported or created.")) </output>

    rule <k> error(labelConstrNotCorrect) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a use of field whose constructor is not correctly stated or misused.")) </output>

    rule <k> error(labelNotInScope) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a use of field, and one of its label has wrongly declared module name, or the label is not in the definition of the labels of the field.")) </output>

    rule <k> error(classNotInScope) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module uses a class name that might not be properly imported or created.")) </output>

    rule <k> error(constrNotInScope) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module uses a constructor that might not be properly imported or created.")) </output>

    rule <k> error(funNameNotInScope) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module uses a function name that has not defined.")) </output>

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
         <output> L:List (.List => ListItem("The modules have a type declaration that uses a type variable or type con in the wrong position causing kind inference failure.")) </output>

    rule <k> error(ambiguousTypeVar) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The modules have a type class whose method does not define the type var for the type class, so it is an ambiguous type variable.")) </output>

    rule <k> error(ambiguousTypeName) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module uses a type whose names are defined previously.")) </output>

    rule <k> error(ambiguousConstrName) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module uses a constructor whose names are defined previously.")) </output>

    rule <k> error(ambiguousFunName) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module uses a function that uses a function name from two different previous definitions.")) </output>

    rule <k> error(badUseFunName) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module uses a local function name that has been quantified.")) </output>

    rule <k> error(duplicateDeriving) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module has a type declaration that has derived with duplicate classes.")) </output>

    rule <k> error(ambiguousClassName) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module uses a class whose names are defined previously.")) </output>

    rule <k> error(messuseClassTypeName) ~> K:K => .K </k>
         <output> L:List (.List => ListItem("The module uses a type name in a class name position or a class name in a type name position.")) </output>

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

    rule exnExp(S:String) => error(S)

endmodule
