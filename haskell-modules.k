//helper functions for the haskell semantics.
requires "haskell-syntax.k"
requires "haskell-abstract-syntax.k"
requires "haskell-helper.k"
requires "haskell-kindinfer.k"
requires "haskell-transformation.k"

module HASKELL-MODULES
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX
    imports HASKELL-HELPER
    imports HASKELL-KINDINFER
    imports HASKELL-TRANSFORMATION

    //a function to generate exports
    syntax Bool ::= hasVarInSet(K, K, Set) [function]
    rule hasVarInSet(A:K, .K, .Set) => false
    rule hasVarInSet(A:K, .K, SetItem(B:K) S:Set)
             => hasVarInSet(A:K, B, S)
    rule hasVarInSet(funName(A:K), funName(A:K), S:Set) => true
    rule hasVarInSet(funName(A:K),
                  fullName(Mod:K, funName(A:K)), S:Set) => true
    rule hasVarInSet(constrName(A:K), constrName(A:K), S:Set) => true
    rule hasVarInSet(constrName(A:K),
                  fullName(Mod:K, constrName(A:K)), S:Set) => true
    rule hasVarInSet(A:K, B:KItem, S:Set) => hasVarInSet(A, .K, S) [owise]

    syntax Bool ::= hasInstanceInList(K, List, Set) [function]
            //fun name, list of fun names or constrs,
           // set of vars/constrs in a class/type
    rule hasInstanceInList(A:K, .List, S:Set) => false
    rule hasInstanceInList(funName(A:K), ListItem(funName(A:K)) L:List, S:Set) => true
    rule hasInstanceInList(funName(A:K),
              ListItem(fullName(Mod:K, funName(A:K))) L:List, S:Set) => true
    rule hasInstanceInList(funName(A:K), ListItem(haveAll) L:List, S:Set)
            => hasVarInSet(funName(A:K), .K, S)
    rule hasInstanceInList(constrName(A:K),
              ListItem(fullName(Mod:K, constrName(A:K))) L:List, S:Set) => true
    rule hasInstanceInList(constrName(A:K), ListItem(constrName(A:K)) L:List, S:Set) => true
    rule hasInstanceInList(constrName(A:K), ListItem(haveAll) L:List, S:Set)
            => hasVarInSet(constrName(A:K), .K, S)
    rule hasInstanceInList(A:K, ListItem(B:K) L:List, S:Set)
           => hasInstanceInList(A, L, S) [owise]

/*
    syntax Bool ::= hasVarConInstance(K, K, Set, Set) [function]
    rule hasVarConInstance(A:K, .K, .Set, S:Set) => false
    rule hasVarConInstance(A:K, .K, SetItem(B:K) S:Set, S1:Set)
            => hasVarConInstance(A:K, B:K, S:Set, S1)
    rule hasVarConInstance(A:K, appExp(B:K, L:List), S:Set, S1:Set) => true
         requires hasInstanceInList(A, L, S1)
    rule hasVarConInstance(A:K, appExp(B:K, L:List), S:Set, S1:Set)
          => hasVarConInstance(A, .K, S, S1)
         requires notBool hasInstanceInList(A, L, S1)
    rule hasVarConInstance(A:K, fullName(Mod:K, A), S:Set, S1:Set) => true
    rule hasVarConInstance(A:KItem, A, S:Set, S1:Set) => true
    rule hasVarConInstance(A:KItem, B:KItem, S:Set, S1:Set)
             => hasVarConInstance(A, .K, S, S1) [owise]


    syntax Bool ::= hasTypeClassModInstance(K, K, Set) [function]
    rule hasTypeClassModInstance(A:K, .K, .Set) => false
    rule hasTypeClassModInstance(A:K, .K, SetItem(B:K) S:Set)
            => hasTypeClassModInstance(A:K, B:K, S:Set)
    rule hasTypeClassModInstance(className(A:K),
                   appExp(className(A:K), L:List), S:Set) => true
    rule hasTypeClassModInstance(typeName(A:K),
                     appExp(typeName(A:K), L:List), S:Set) => true
    rule hasTypeClassModInstance(moduleNameAst(A:K),
                     moduleNameAst(A), S:Set) => true
    rule hasTypeClassModInstance(A:KItem, B:KItem, S:Set)
           => hasTypeClassModInstance(A, .K, S) [owise]
*/
    syntax Set ::= allNamesFromModule(K, K, Map, Map) [function]
            //curr-mod, execute, mod-parent-set, class_names
                 | allNamesAux(Set, Map, Map) [function]

    rule allNamesFromModule(A:K, .K, .Map, M:Map) => .Set
    rule allNamesFromModule(A:K, .K, (A |-> B:K) M:Map, (A |-> C:K) M1:Map)
            => getRidWrapper(C) allNamesFromModule(A:K, B, M, M1)
    rule allNamesFromModule(A:K, resultSet(S:Set), M:Map, M1:Map)
            => allNamesAux(S, M, M1)
    rule allNamesAux(.Set, M:Map, M1:Map) => .Set
    rule allNamesAux(SetItem(A:K) S:Set, M:Map, M1:Map)
           => allNamesFromModule(A, .K, M, M1)
                 allNamesAux(S, M, M1)


    //first, simple translation of exports
/*
    syntax KItem ::= toExports(K, K) [function]

    syntax KItem ::= toExportsAux(K, List) [function]
    rule toExports(Mod:K, 'exportWrap(A:K,, B:K))
                 => toExports(Mod, A)
    rule toExports(Mod:K, .ExportList) => .Set
    rule toExports(Mod:K, 'exportCon(A:QVar,, B:ExportList))
           => toExports(Mod, B)
    rule toExports(Mod:K, 'exportCon('moduleName(A:K),, B:ExportList))
           => SetItem(moduleNameAst(A)) toExports(Mod, B)
    rule toExports(Mod:K, 'exportCon('exportTyCon(A:K,, B:K),, C:ExportList))
           => SetItem(toExportsAux(transVar(Mod, A), transCName(Mod, B))) toExports(Mod, C)

    rule toExportsAux(A:K, .List) => appExp(A, ListItem(absClass))
    rule toExportsAux(A:K, ListItem(B:K) L:List)
                  => appExp(A, ListItem(B:K) L:List)
*/

    syntax List ::= transCName(K, K) [function]
    rule transCName(Mod:K, 'allInclude(.KList)) => ListItem(haveAll)
    rule transCName(Mod:K, 'emptyOptCNameList(.KList)) => .List
    rule transCName(Mod:K, .CQList) => .List
    rule transCName(Mod:K, 'cnameCon(A:K,, B:K))
          => transCName(Mod:K, A) transCName(Mod:K, B)
    rule transCName(Mod:K, V:CQName) => transVar(Mod, V)

    //helper functions for generating import set
    //translate each type/fresh vars
    syntax KItem ::= transCNameCon(K, Set, Set) [function]
           //type-name, term, set of export, export-type-map, set of result
    rule transCNameCon('allInclude(.KList), S:Set, R:Set)
            => resultSet(S)
    rule transCNameCon('emptyOptCNameList(.KList), S:Set, R:Set)
            => resultSet(.Set)
    rule transCNameCon(.CQList, S:Set, R:Set) => resultSet(R)
    rule transCNameCon('cnameCon(X:Var,, B:K), S:Set, R:Set)
             => transCNameCon(B, S, SetItem(funName(pillVar(X))) R)
         requires funName(pillVar(X)) in S
    rule transCNameCon('cnameCon(X:Var,, B:K), S:Set, R:Set)
             => error(importFromNoSource)
         requires notBool funName(pillVar(X)) in S
    rule transCNameCon('cnameCon(X:Con,, B:K), S:Set, R:Set)
             => transCNameCon(B, S, SetItem(constrName(pillVar(X))) R)
         requires constrName(pillVar(X)) in S
    rule transCNameCon('cnameCon(X:Con,, B:K), S:Set, R:Set)
             => error(importFromNoSource)
         requires notBool constrName(pillVar(X)) in S
    rule transCNameCon('cnameCon(A:QVar,, B:K), S:Set, R:Set)
          => error(syntaxError)

    syntax KItem ::= transCNameClass(K, Set, Set) [function]
           //class-name, term, set of export, export-type-map, set of result
    rule transCNameClass('allInclude(.KList), S:Set, R:Set)
            => resultSet(S)
    rule transCNameClass('emptyOptCNameList(.KList), S:Set, R:Set)
            => resultSet(.Set)
    rule transCNameClass(.CQList, S:Set, R:Set) => resultSet(R)
    rule transCNameClass('cnameCon(X:Var,, B:K), S:Set, R:Set)
             => transCNameClass(B, S, SetItem(funName(pillVar(X))) R)
         requires funName(pillVar(X)) in S
    rule transCNameClass('cnameCon(X:Var,, B:K), S:Set, R:Set)
             => error(importFromNoSource)
         requires notBool funName(pillVar(X)) in S
    rule transCNameClass('cnameCon(X:Con,, B:K), S:Set, R:Set)
             => error(importFromNoSource)
    rule transCNameClass('cnameCon(A:QVar,, B:K), S:Set, R:Set)
          => error(syntaxError)

    //transformation of imports 
    syntax Bool ::= transQualified(K) [function]
    rule transQualified('emptyQualified(.KList)) => false
    rule transQualified(qualified) => true

    syntax KItem ::= getAsModId(K) [function]
    rule getAsModId('emptyOptAsModId(.KList)) => .K
    rule getAsModId('asModid(A:K)) => A

    syntax KItem ::= transImports(K, K) [function]
                   | transImportList(K, Set, Map, Set, Map) [function]
                    //term, target-export-set,target-export-map
                   // result-set, result-map
                   | transImportListAux(K, K, K, Set, Map, Set, Map) [function]
    rule transImports(A:K, resultSetMap(S:Set, M:Map))
           => transImportList(A, S, M, .Set, .Map)
    rule transImportList(.ImportList, S:Set, M:Map, S1:Set, M1:Map)
                => resultSetMap(S1, M1)
    rule transImportList('importCon(A:Var,, As:ImportList),
                  S:Set, M:Map, S1:Set, M1:Map)
             => transImportList(As, S, M, SetItem(funName(pillVar(A))) S1, M1)
         requires funName(pillVar(A)) in S
    rule transImportList('importCon(A:Var,, As:ImportList),
                  S:Set, M:Map, S1:Set, M1:Map) => error(importFromNoSource)
         requires notBool funName(pillVar(A)) in S
    rule transImportList('importCon('importTyCon(T:TyCon,, C:OptCQList),,
          As:ImportList), S:Set, (className(T) |-> Cs:K) M:Map, S1:Set, M1:Map)
             => transImportListAux(As, className(T),
                      transCNameClass(C, getRidWrapper(Cs), .Set),
                   S, (className(T) |-> Cs:K) M:Map, SetItem(className(T)) S1, M1)
         requires className(T) in S
    rule transImportList('importCon('importTyCon(T:TyCon,, C:OptCQList),,
          As:ImportList), S:Set, (typeName(T) |-> Cs:K) M:Map, S1:Set, M1:Map)
             => transImportListAux(As, typeName(T),
                      transCNameCon(C, getRidWrapper(Cs), .Set),
                   S, (typeName(T) |-> Cs:K) M:Map, SetItem(typeName(T)) S1, M1)
         requires typeName(T) in S
    rule transImportList('importCon('importTyCon(T:TyCon,, C:OptCQList),,
          As:ImportList), S:Set, M:Map, S1:Set, M1:Map) => error(importFromNoSource)
         requires notBool typeName(T) in S andBool notBool className(T) in S

    rule transImportListAux(As:K, A:K, error(B:K),
                  S:Set, M:Map, S1:Set, M1:Map) => error(B)
    rule transImportListAux(As:K, A:K, resultSet(L:Set),
            S:Set, M:Map, S1:Set, M1:Map)
            => transImportList(As, S, M, L S1, updateMapItem(M1, .K, A, L))

    //gen import set, get all imports, and then
    // check if all imports have valid parents in the original export list
    syntax KItem ::= genImportSet(K, Map, Set, Set) [function]
                  //term, export-map, set-of-imported-mods, set of results
                   | genImportSetAux(K, K, Map, Set, Set) [function]
                   | genImportSetNext(K, K, K, K, Map, Set, Set) [function]
                     //store-next, store-form, import-spec,
                    //import-mod, export-map, Set-of-imports, set-of-results
                   | genImportSetNext1(K, K, Map, K, Set, Set) [function]
                   | genImportSetNext2(K, K, Map, K, K, Set, Set) [function]

    rule genImportSet('bodyimpandtop(I:ImpDecls,, T:TopDecls), M:Map, Ps:Set, S:Set)
          => genImportSet(I, M, Ps, S)
    rule genImportSet('bodyimpdecls(I:ImpDecls),M:Map, Ps:Set, S:Set)
          => genImportSet(I, M, Ps, S)
    rule genImportSet('bodytopdecls(T:TopDecls), M:Map, Ps:Set, S:Set)
            => resultImportSet(Ps, S)
    rule genImportSet(.ImpDecls, M:Map, Ps:Set, S:Set) => resultImportSet(Ps, S)
    rule genImportSet('impDecls(I:ImpDecl,, Is:ImpDecls),M:Map,Ps:Set, S:Set)
            => genImportSetAux(I, Is,M, Ps, S)
    rule genImportSetAux('emptyImpDecl(.KList), Is:K,M:Map, Ps:Set, S:Set)
           => genImportSet(Is,M, Ps, S)
    rule genImportSetAux('impDecl(A:OptQualified,, B:ModId,,
                  C:OptAsModId,, D:OptImpSpec), Is:K, M:Map, Ps:Set, S:Set)
          => genImportSetNext(Is, importElem(B,
                getAsModId(C),transQualified(A), .Set, .Map), B, D,M,Ps SetItem(B), S)

    rule genImportSetNext(Is:K, A:K, 'emptyOptImpSpec(.KList),
                 B:K, M:Map,Ps:Set, S:Set)
            => genImportSet(Is,M,Ps:Set, SetItem(A) S)
    rule genImportSetNext(Is:K, X:K, 'impSpecKey(
            A:ImportList,, P:OptComma), B:K, (B |-> R:K) M:Map, Ps:Set, S:Set)
          => genImportSetNext1(Is, X,
                   (B |-> R:K) M:Map, transImports(A,R), Ps:Set, S)
    rule genImportSetNext(Is:K, X:K, 'hidingCon('impSpecKey(
            A:ImportList,, P:OptComma)),B:K, (B |-> R:K) M:Map, Ps:Set, S:Set)
          => genImportSetNext2(Is, X, (B |-> R:K) M:Map,
                     R, transImports(A, R),Ps:Set, S)

    rule genImportSetNext1(Is:K, X:K, B:Map, error(A:K),Ps:Set, S:Set) => error(A)
    rule genImportSetNext1(Is:K, importElem(
             X:K, Y:K, Z:K, As:Set, Ns:Map), B:Map,
                   resultSetMap(As':Set, Ns':Map),Ps:Set,S:Set)
           => genImportSet(Is, B, Ps:Set, S SetItem(importElem(X, Y, Z, As', Ns')))
    rule genImportSetNext2(Is:K, X:K,B:Map, R:K, error(A:K),Ps:Set, S:Set) => error(A)
    rule genImportSetNext2(Is:K, importElem(
             X:K, Y:K, Z:K, As:Set, Ns:Map),B:Map, resultSetMap(
               As1:Set, Ns1:Map), resultSetMap(As':Set, Ns':Map),Ps:Set, S:Set)
           => genImportSet(Is, B, Ps:Set, S SetItem(importElem(
                    X, Y, Z, setMinus(As', .K, As1), mapMinus(Ns', .K,.K, Ns1))))

    //collect all elements in a modules
    syntax Set ::= collectTypeNames(Set) [function]
    rule collectTypeNames(.Set) => .Set
    rule collectTypeNames(SetItem(A:K) S:Set)
             => SetItem(typeName(A)) collectTypeNames(S)

    syntax Set ::= collectFunNames(Set) [function]
    rule collectFunNames(.Set) => .Set
    rule collectFunNames(SetItem(A:K) S:Set)
           => SetItem(funName(A)) collectFunNames(S)

    syntax KItem ::= toClassName(K) [function]
    rule toClassName(fullName(Mod:K, A:K)) => className(A)

    syntax Set ::= toClassNames(Set) [function]
    rule toClassNames(.Set) => .Set
    rule toClassNames(SetItem(A:K) S:Set)
             => SetItem(toClassName(A)) toClassNames(S)

    syntax Set ::= collectPreBetaNamesAux(Set) [function]
    rule collectPreBetaNamesAux(.Set) => .Set
    rule collectPreBetaNamesAux(SetItem(A:K) S:Set)
           => SetItem(constrName(A)) collectPreBetaNamesAux(S)

    syntax Set ::= collectFieldNamesAux(List) [function]
    rule collectFieldNamesAux(.List) => .Set
    rule collectFieldNamesAux(ListItem(
            typeConst(fullName(Prelude, recordTypeAssign),
                    ListItem(tyVar(S:K, A:K)) Ls:List)) L:List)
             => SetItem(funName(A)) collectFieldNamesAux(L)

    syntax Set ::= collectFieldNames(List) [function]
    rule collectFieldNames(.List) => .Set
    rule collectFieldNames(ListItem(typeConst(fullName(Prelude, (->)),
            ListItem(typeConst(fullName(Prelude, recordType), AL:List))
                Ls:List)) L:List)
               => collectFieldNamesAux(AL) collectFieldNames(L)

    syntax Set ::= collectPreBetaNames(Map, K) [function]
    rule collectPreBetaNames(.Map, .K) => .Set
    rule collectPreBetaNames(M:Map (A:K |-> B:K), .K)
           => collectPreBetaNames(M, B)
    rule collectPreBetaNames(M:Map, preBetaEntry(A:Set, B:List, C:Map, D:Set))
           => collectPreBetaNamesAux(keys(C))
                collectFieldNames(values(C))
                   collectPreBetaNames(M, .K)

    //check if exports are all distinct.

    //check if a set of imports are contained in a set of exports
    syntax KItem ::= isExportContained(Set, K, Set) [function]
         //imports, execute, exports
   // rule isExportContained(.Set, .K, S:Set) => .K
    //rule 
 


endmodule
