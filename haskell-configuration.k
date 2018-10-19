//configuration of haskell
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"

module HASKELL-CONFIGURATION
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX

    configuration 
        <T>
            <k> $PGM:ModuleList ~> startImportRecursion </k>
            <tempModule> .K </tempModule>
            <tempCode> .K </tempCode>
            <tempAlpha> .K </tempAlpha>
            <tempAlphaMap> .Map </tempAlphaMap>
            <tempT> .K </tempT>
            <importTree> .List </importTree>
            <modules> //static information about a module
                <module multiplicity="*">
                    <moduleName> .K </moduleName>
                    <moduleAlphaPlus> .K </moduleAlphaPlus>
                    <moduleBetaPlus> .K </moduleBetaPlus>
                    <moduleCompCode> .K </moduleCompCode>
                    //<imports> .Set </imports>
                    <classes> .Map </classes> //type classes
                </module>
              <classNameInMod> .Map </classNameInMod> //store all class names in a modules. 
              <typeNameInMod> .Map </typeNameInMod> //store all type names in a modules. 
              <constrNameInMod> .Map </constrNameInMod> //store all constructor names in a modules. 
              <importMap> .Map </importMap>
            </modules>
        </T>

endmodule
