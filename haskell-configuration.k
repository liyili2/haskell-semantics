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
                    <imports> .Set </imports>
                    <classes> //static information about a module
                        <class multiplicity="*">
                            <className> .K </className>
                        </class>
                    </classes>
                </module>
            </modules>
        </T>

endmodule
