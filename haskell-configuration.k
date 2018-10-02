requires "haskell-syntax.k"

module HASKELL-CONFIGURATION
    imports HASKELL-SYNTAX

    syntax KItem ::= "startImportRecursion"
    syntax KItem ::= callInit(K)
    //syntax KItem ::= initPreModule(K) [function]
    //syntax KItem ::= tChecker(K) [function]

    configuration 
        <T>
            <k> $PGM:ModuleList ~> startImportRecursion </k>
            <tempModule> .K </tempModule>
            <tempCode> .K </tempCode>
            <tempAlpha> .K </tempAlpha>
            <tempAlphaMap> .Map </tempAlphaMap>
            <tempT> .K </tempT>
            <tempGamma> .Map </tempGamma>
            <tempAlphaStar> .K </tempAlphaStar>
            <tempBetaStar> .K </tempBetaStar>
            <importTree> .List </importTree>
            <recurImportTree> .List </recurImportTree>
            <impTreeVMap> .Map </impTreeVMap>
            <modules> //static information about a module
                <module multiplicity="*">
                    <moduleName> .K </moduleName>
                    <moduleAlphaStar> .K </moduleAlphaStar>
                    <moduleBetaStar> .K </moduleBetaStar>
                    <moduleImpAlphas> .List </moduleImpAlphas>
                    <moduleImpBetas> .List </moduleImpBetas>
                    <moduleCompCode> .K </moduleCompCode>
                    <moduleTempCode> .K </moduleTempCode>
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
