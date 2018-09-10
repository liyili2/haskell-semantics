requires "haskell-syntax.k"

module HASKELL-CONFIGURATION
    imports HASKELL-SYNTAX

    syntax KItem ::= callInit(K)
    //syntax KItem ::= initPreModule(K) [function]
    //syntax KItem ::= tChecker(K) [function]

    configuration 
        <T>
            <k> $PGM:ModuleList </k>
            <tempModule> .K </tempModule>
            <tempCode> .K </tempCode>
            <tempAlpha> .K </tempAlpha>
            <tempAlphaMap> .Map </tempAlphaMap>
            <tempT> .K </tempT>
            <modules> //static information about a module
                <module multiplicity="*">
                    <moduleName> "" </moduleName>
                    <moduleAlphaPlus> "" </moduleAlphaPlus>
                    <moduleBetaPlus> "" </moduleBetaPlus>
                    <moduleCompCode> "" </moduleCompCode>
                    <imports> "" </imports>
                    <classes> //static information about a module
                        <class multiplicity="*">
                            <className> "" </className>
                        </class>
                    </classes>
                </module>
            </modules>
        </T>

endmodule
