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
            <unnamedModuleExp> .List </unnamedModuleExp>
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
                <moduleMethodNames> .Map </moduleMethodNames>
                <module multiplicity="*">
                    <moduleName> .K </moduleName>
                    <moduleAlphaPlus> .K </moduleAlphaPlus>
                    <moduleBetaPlus> .K </moduleBetaPlus>
                    <moduleCompCode> .K </moduleCompCode>
                    <exports> .Set </exports>
                    <imports> .Set </imports>
                    <defaultInt> Integer </defaultInt>
                    <defaultDouble> Double </defaultDouble>
                    <moduleMethods> .Map </moduleMethods>
                </module>
              <typeNameInMod> .Map </typeNameInMod>
                   //store all type names in modules. from module name to type name+arity
              <constrNameInMod> .Map </constrNameInMod> //store all constructor names in modules. 
              <importMap> .Map </importMap>
            </modules>
            <classes>
              <classNames> .Map </classNames>
                     //store all class names for each module
              <classMethodNames> .Map </classMethodNames>
              <class multiplicity="*">
                <classModule> .K </classModule>
                <className> .K </className>
                <classTypeVar> .K </classTypeVar>
                <classContext> .Set </classContext>
                <classMethods> .Map </classMethods>
              </class>
              <instance multiplicity="*">
                <instanceModule> .K </instanceModule>
                <instanceClass> .K </instanceClass>
                <instanceType> .K </instanceType>
                <instanceContext> .Set </instanceContext>
                <instanceMethods> .Map </instanceMethods>
              </instance>
            </classes>
            <output stream="stdout" color="DodgerBlue"> .List </output>
        </T>

endmodule
