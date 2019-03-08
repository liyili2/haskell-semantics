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
            <tempBetaMap> .Map </tempBetaMap>
            <tempT> .K </tempT>
            <tempExports> .K </tempExports>
            <currModule> .K </currModule>
            <importTree> .List </importTree>
            <kindVarCounter> 0 </kindVarCounter>
            <kindVarSet> .Set </kindVarSet>
            <genVarCounter> 0 </genVarCounter>
            <modules> //static information about a module
                <moduleMethodNames> .Map </moduleMethodNames>
                <moduleTypeNames> .Map </moduleTypeNames>
                 //all valid type names for each module generated from alpha/beta
                 //needs to generate from beta/alpha
                <moduleImportMap> .Map </moduleImportMap>
                <exports> .Map </exports>
                <module multiplicity="*">
                    <moduleName> .K </moduleName>
                    <moduleAlpha> .Map </moduleAlpha>
                    <moduleBeta> .Map </moduleBeta>
                    <moduleDefs> .Set </moduleDefs>
                    <kindMap> .Map </kindMap>
                       //a module storing all elements of operators that are possibly outputed
                    <imports> .Set </imports>
                    <importKindMap> .Map </importKindMap>
                      //a kind map for all imports
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
              <methodNamesByClass> .Map </methodNamesByClass>
              <classParentMap> .Map </classParentMap>
              <class multiplicity="*">
                <classModule> .K </classModule>
                <className> .K </className>
                <classTypeVar> .K </classTypeVar>
                <classKind> .K </classKind>
                <classContext> .Set </classContext>
                <classMethods> .Map </classMethods>
              </class>
              <instances>
                <instance multiplicity="*">
                   <instanceModule> .K </instanceModule>
                   <instanceClass> .K </instanceClass>
                   <instanceType> .K </instanceType>
                   <instanceContext> .Set </instanceContext>
                   <instanceMethods> .Map </instanceMethods>
                </instance>
              </instances>
            </classes>
            <output stream="stdout" color="DodgerBlue"> .List </output>
        </T>

endmodule
