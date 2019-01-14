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
            <tempBetaMap> .Map </tempBetaMap>
            <tempKindMap> .Map </tempKindMap>
            <tempT> .K </tempT>
            <tempExports> .Map </tempExports>
            <currModule> .K </currModule>
            <importTree> .List </importTree>
            <tempImports> .Map </tempImports>
            <kindVarCounter> 0 </kindVarCounter>
            <kindVarSet> .Set </kindVarSet>
            <genVarCounter> 0 </genVarCounter>
            <modules> //static information about a module
                <module multiplicity="*">
                    <moduleName> .K </moduleName>
                    <moduleAlphaPlus> .K </moduleAlphaPlus>
                    <moduleBetaPlus> .K </moduleBetaPlus>
                    <moduleCompCode> .K </moduleCompCode>
                    <exports> .Set </exports>
                    <importElemMap> .Map </importElemMap>
                </module>
              <typeNameInMod> .Map </typeNameInMod>
                   //store all type names in modules. from module name to type name+arity
              <constrNameInMod> .Map </constrNameInMod> //store all constructor names in modules. 
              <importMap> .Map </importMap>
            </modules>
            <classes>
              <classMethodNames> .Set </classMethodNames> //store all class method names in modules.
              <class multiplicity="*">
                <classModule> .K </classModule>
                <className> .K </className>
                <classTypeVar> .K </classTypeVar>
                <classContext> .Set </classContext>
                <classMethods> .Map </classMethods>
              </class>
            </classes>
            <output stream="stdout" color="DodgerBlue"> .List </output>
        </T>

endmodule
