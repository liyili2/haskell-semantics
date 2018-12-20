//
requires "haskell-syntax.k"
requires "haskell-configuration.k"
requires "haskell-abstract-syntax.k"
requires "haskell-helper.k"
requires "haskell-errors.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX
    imports HASKELL-ABSTRACT-SYNTAX
    imports HASKELL-CONFIGURATION
    imports HASKELL-HELPER
    imports HASKELL-ERRORS

/*
    //USER DEFINED LIST
    //definition of ElemList

    //syntax KItem ::= ElemList
    syntax ElemList ::= List{Element,","} [strict]
    syntax Int ::= lengthOfList(ElemList) [function]

    rule lengthOfList(.ElemList) => 0
    rule lengthOfList(val(K:K),L:ElemList) => 1 +Int lengthOfList(L)
    rule lengthOfList(valValue(K:K),L:ElemList) => 1 +Int lengthOfList(L)

    syntax Element ::= val(K) [strict]
    syntax ElementResult ::= valValue(K)
    syntax Element ::= ElementResult
    syntax KResult ::= ElementResult
    rule val(K:KResult) => valValue(K) [structural]

    //form ElemList
    syntax ElemList ::= formElemList(K) [function]

    //CONVERT ~> TO List
    //list convert
    syntax List ::= convertToList(K)  [function]
    rule convertToList(.K) => .List
    rule convertToList(A:KItem ~> B:K) => ListItem(A) convertToList(B)
*/

    rule <k> 'modListSingle('module(A:K,, B:K)) => dealWithImports(getImports(B)) ...</k>
         <currModule> _:K => A </currModule>
    (.Bag =>
          <module>...   //DOT DOT DOT MEANS OVERWRITE ONLY SOME OF THE DEFAULTS
    	    <moduleName> A </moduleName>
            <exports> SetItem(allExports) </exports>
       ...</module>
    )

    rule <k> 'modList('module(A:K,, B:K),, C:K) => dealWithImports(getImports(B)) ~> C ...</k>
         <currModule> _:K => A </currModule>
    (.Bag =>
          <module>...   //DOT DOT DOT MEANS OVERWRITE ONLY SOME OF THE DEFAULTS
    	    <moduleName> A </moduleName>
            <exports> SetItem(allExports) </exports>
       ...</module>
    )

    rule <k> 'modListSingle('moduleBody(B:K)) => dealWithImports(getImports(B)) ...</k>
         <currModule> _:K => noname </currModule>
    (.Bag =>
          <module>...   //DOT DOT DOT MEANS OVERWRITE ONLY SOME OF THE DEFAULTS
    	    <moduleName> noname </moduleName>
            <exports> SetItem(allExports) </exports>
       ...</module>
    )

    rule <k> 'modList('moduleBody(B:K),, C:K) => dealWithImports(getImports(B)) ~> C ...</k>
         <currModule> _:K => noname </currModule>
    (.Bag =>
          <module>...   //DOT DOT DOT MEANS OVERWRITE ONLY SOME OF THE DEFAULTS
    	    <moduleName> noname </moduleName>
            <exports> SetItem(allExports) </exports>
       ...</module>
    )

    rule <k> 'modListSingle('moduleExp(A:K,, B:K,, D:K))
               => dealWithImports(getImports(D)) ...</k>
         <tempExports> M:Map => M[A <- B] </tempExports>
         <currModule> _:K => A </currModule>
    (.Bag =>
          <module>...   //DOT DOT DOT MEANS OVERWRITE ONLY SOME OF THE DEFAULTS
    	    <moduleName> A </moduleName>
       ...</module>
    )

    rule <k> 'modList('moduleExp(A:K,, B:K,, D:K),, C:K)
                    => dealWithImports(getImports(D)) ~> C ...</k>
         <tempExports> M:Map => M[A <- B] </tempExports>
         <currModule> _:K => A </currModule>
    (.Bag =>
          <module>...   //DOT DOT DOT MEANS OVERWRITE ONLY SOME OF THE DEFAULTS
    	    <moduleName> A </moduleName>
       ...</module> )

    //select a module that does not have father. 
    rule <k> startPreprocessing => selectImport ...</k>
         <tempImports> .Map => M </tempImports>
         <importMap> M:Map </importMap>

    rule <k> selectImport => .K ...</k>
         <tempImports> M:Map => deleteImport(M, .K, .K,
                                selectNoFather(.K, .K, M)) </tempImports>
         <currModule> Curr:K => selectNoFather(.K, .K, M) </currModule>
         requires selectNoFather(.K, .K, M) =/=K none
 
    rule <k> selectImport => error(cyclicImports) ...</k>
         <tempImports> M:Map </tempImports>
         requires selectNoFather(.K, .K, M) ==K none

    

    //declare toExports

    rule dealWithImports(.ImpDecls) => .K
    rule dealWithImports('impDecls('emptyOptCNameList(.KList),, Es:ImpDecls))
             => dealWithImports(Es)

    rule <k> dealWithImports('impDecls(import A:OptQualified
                     N:ModId C:OptAsModId D:OptImpSpec,, Es:ImpDecls))
               ...</k>
         <currModule> Curr:K </currModule>
             <module>...
                  <moduleName> Curr </moduleName>
                  <importElemMap> IM:Map => IM[N <-
                 importElem(dealWithOpt(A), dealWithOpt(C), dealWithOpt(D))] </importElemMap>
              ...</module>
         <importMap> M:Map => updateMapItem(M, .K, Curr, N) </importMap>

    //rule dealWithImports(Mod:K, 

//    rule dealWithImports(Mod:K, A:K) => callInit(A)

//    rule <k> dealWithImports(Mod:K, A:K) => callInit(A) ...</k>

/*
    rule dealWithImports(Mod:K, 'bodyimpandtop(A:K,, B:K))
              => dealWithImportsAux(Mod, A) ~> callInit(Mod, B)

    rule dealWithImports(Mod:K, 'bodyimpdecls(A:K))
                => dealWithImportsAux(Mod, A)
    rule dealWithImports(Mod:K, 'bodytopdecls(A:K)) => callInit(Mod, A)

    //TODO: need to deal with option cases for import
    rule dealWithImportsAux(Mod:K, .ImpDecls) => .K
    rule dealWithImportsAux(Mod:K, 'impDecls('emptyImpDecl(.KList),, As:ImpDecls))
                 => dealWithImportsAux(Mod, As)
    rule <k> dealWithImportsAux(Mod:K, 'impDecls('impDecl(X:K,, V:K,, Y:K,, U:K),, As:ImpDecls))
                 => dealWithImportsAux(Mod, As) ...</k>
         <importMap> M:Map => updateMapItem(M, .K, Mod, V) </importMap>
*/
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    /*NEW TODO ALGORITHM
1. Construct tree for module inclusion
2. Check tree for cycles
3. Go to each leaf and recursively go up the tree and build alpha* and beta* for the types of the module and the children
(and specify scoping) (desugar the scope so that each type specifies the scope) */

    rule <k> startImportRecursion => checkImportCycle ...</k>

    syntax KItem ::= cycleCheck(K,Map,List,List) [function] //current node, map of all nodes to visited or not, stack, graph
    syntax Map ::= createVisitMap(List,Map) [function] //graph, visitmap
    syntax KItem ::= getUnvisitedNode(K,K, Map) [function] //visitmap
    syntax List ::= getNodeNeighbors(K,List) [function] //visitmap

    rule <k> checkImportCycle
             => cycleCheck(.K,createVisitMap(I, .Map),.List,I) ...</k>
         <importTree> I:List </importTree>

    rule createVisitMap(ListItem(impObject(A:K,B:K)) Rest:List, M:Map) 
             => createVisitMap(Rest, M[A <- unvisited][B <- unvisited])
    rule createVisitMap(.List, M:Map) => M

    rule getUnvisitedNode(.K, .K, .Map) => none
    rule getUnvisitedNode(.K, .K, (A:K |-> B:K) M:Map)
           => getUnvisitedNode(A, B, M)
    rule getUnvisitedNode(A:KItem, unvisited, M:Map) => A
    rule getUnvisitedNode(A:KItem, visited, M:Map)
            =>  getUnvisitedNode(.K, .K, M)

    rule cycleCheck(none, M:Map, .List, L:List) => .K
    rule cycleCheck(.K, M:Map, .List, I:List) => cycleCheck(getUnvisitedNode(.K, .K, M), M, .List, I)
    rule cycleCheck(.K, M:Map, ListItem(Node:K) S:List, I:List) => cycleCheck(Node, M, S, I)
    rule cycleCheck(Node:K, M:Map, S:List, I:List)
                 => cycleCheck(.K, M[Node <- visited], getNodeNeighbors(Node,I) S, I)
         requires Node =/=K .K andBool Node =/=K none

/*
    rule cycleCheck(A:K,.K,.K,I:K) => cycleCheck(A,createVisitMap(I,.Map),.List,I)



    rule cycleCheck(Node:K, M:Map, S:List, I:K) => cycleCheck(.K, M[Node <- visited], getNodeNeighbors(Node,I) S, I)

    rule cycleCheck(.K, M:Map, ListItem(Node:K) S:List, I:K) => cycleCheck(Node, M, S, I)
    //rule cycleCheck(.K, M:Map, .K, ListItem(impObject(A:K,B:K)) Rest:List) => cycleCheck(ListItem(impObject(A:K,B:K)) Rest:List)
*/
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //call before Checker Code
    rule <k> callInit(Mod:K, S:K) => countNames(Mod, S)
              ~> getPreModule(Mod, S,preModule(AList(.List),TList(.List))) ...</k>
         <tempModule> A:K => S </tempModule>
         <currModule> _:K => Mod </currModule>

    //start of Checker Code
    // STEP 1 CONSTRUCT T AND ALPHA 
    // alpha = type
    // T = newtype and data, temporary data structure

    //syntax KItem ::= initPreModule(K) [function]
    syntax KItem ::= makeT (K, K,K,K,K) [function]

    syntax KItem ::= fetchTypes (K,K,K,K,K) [function]

    syntax List ::= makeInnerT (K,K,K) [function] //LIST
    syntax List ::= getTypeVars(K) [function] //LIST

    syntax KItem ::= getCon(K) [function]
    syntax List ::= getArgSorts(K) [function] //LIST

//    rule initPreModule('module(I:ModuleName,, J:K)) => getPreModule(J,preModule(AList(.List),TList(.List)))
//    rule initPreModule('moduleExp(I:ModuleName,, L:K,, J:K)) => getPreModule(J,preModule(AList(.List),TList(.List)))
//    rule initPreModule('moduleBody(J:Body)) => getPreModule(J,preModule(AList(.List),TList(.List)))

    //first create a map name for every classname/type name
    rule countNames(Mod:K, 'bodytopdecls(I:K)) => countNames(Mod, I)
    rule countNames(Mod:K, .TopDecls) => .K
    rule <k> countNames(Mod:K, 'topdeclslist('class(A:K,, B:K,, C:K,, D:K),, Rest:K))
               => countNames(Mod, Rest) ...</k>
         <module>... <moduleName> Mod </moduleName>
                      <classes> M:Map => M[B <- none] </classes>
                ...</module>
         <classNameInMod> CM:Map => updateMapItem(CM, .K, Mod, B) </classNameInMod>

    rule getPreModule(Mod:K,'bodytopdecls(I:K), J:K) => getPreModule(Mod:K, I,J)
    rule getPreModule(Mod:K,'topdeclslist('type(A:K,, B:K),, Rest:K),J:K)
                   => fetchTypes(Mod, A,B,Rest,J) //constructalpha


    rule getPreModule(Mod:K,'topdeclslist('data(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K)
                   => makeT(Mod, B,C,Rest,J)
    rule getPreModule(Mod:K,'topdeclslist('newtype(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K)
                    => makeT(Mod, B,C,Rest,J)


    rule getPreModule(Mod:K,'topdeclslist('topdecldecl(A:K),, Rest:K),J:K) => getPreModule(Mod:K,Rest,J)
    rule getPreModule(Mod:K,'topdeclslist('class(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K)
             => dealWithClass('class(A:K,, B:K,, C:K,, D:K))
                         ~> getPreModule(Mod, Rest,J)
    rule getPreModule(Mod:K,'topdeclslist('instance(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K)
              => getPreModule(Mod:K,Rest,J)
    rule getPreModule(Mod:K,'topdeclslist('default(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K)
               => getPreModule(Mod:K,Rest,J)
    rule getPreModule(Mod:K,'topdeclslist('foreign(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K)
                   => getPreModule(Mod:K,Rest,J)
    rule getPreModule(Mod:K,.TopDecls,J:K) => J

    //a function to deal with a single class
    rule <k> dealWithClass('class('emptyContext(.KList),, B:K,, C:K,, D:K)) => .K ...</k>
         <module>... <moduleName> Mod </moduleName>
           <classes> M:Map
            => M[B <- typeClass(none, ListItem(C),
                     classContentToList(Mod, B, D, TM, CM, IM))] </classes>
                ...</module>
         <typeNameInMod> TM:Map </typeNameInMod>
          <constrNameInMod> CM:Map </constrNameInMod>
          <importMap> IM:Map </importMap>

    //rule getPreModule('module(I:ModuleName,L:K, J:K)) => preModule(J)

    rule fetchTypes(Mod:K, 'simpleTypeCon(I:TyCon,, H:TyVars),
               'atypeGTyCon(C:K), Rest:K, preModule(AList(M:List), L:K))
              => getPreModule(Mod, Rest,preModule(AList(ListItem(AObject(I,C)) M), L))

    rule makeT(Mod:K, 'simpleTypeCon(I:TyCon,, H:TyVars),
                   D:K, Rest:K, preModule(AList(M:List), TList(ListInside:List)))
                     => getPreModule(Mod, Rest,preModule(AList(M),
                           TList(ListItem(TObject(I,H,makeInnerT(I,H,D))) ListInside)))

    rule makeInnerT(A:K,B:K,'nonemptyConstrs(C:K)) => makeInnerT(A,B,C)
    rule makeInnerT(A:K,B:K,'singleConstr(C:K)) => ListItem(InnerTPiece(getCon(C),getTypeVars(C),getArgSorts(C),C,A))
    rule makeInnerT(A:K,B:K,'multConstr(C:K,, D:K)) => ListItem(InnerTPiece(getCon(C),getTypeVars(C),getArgSorts(C),C,A)) makeInnerT(A,B,D)

    rule getTypeVars('constrCon(A:K,, B:K)) => getTypeVars(B)
    rule getTypeVars('optBangATypes(A:K,, Rest:K)) => getTypeVars(A) getTypeVars(Rest)
    rule getTypeVars('optBangAType('emptyBang(.KList),, Rest:K)) => getTypeVars(Rest)
    rule getTypeVars('atypeGTyCon(A:K)) => .List
    rule getTypeVars('atypeTyVar(A:K)) => ListItem(A)
    rule getTypeVars(.OptBangATypes) => .List

    //rule getCon('emptyConstrs()) => .K
    //rule getCon('nonemptyConstrs(A:K)) => getCon(A)
    rule getCon('constrCon(A:K,, B:K)) => A

    //rule getArgSorts('constrCon(A:K,, B:K)) => B
    rule getArgSorts('constrCon(A:K,, B:K)) => getArgSorts(B)
    rule getArgSorts('optBangATypes(A:K,, Rest:K)) => getArgSorts(A) getArgSorts(Rest)
    rule getArgSorts('optBangAType('emptyBang(.KList),, Rest:K)) => getArgSorts(Rest)
    rule getArgSorts('atypeGTyCon(A:K)) => ListItem(A)
    rule getArgSorts('atypeTyVar(A:K)) => .List
    rule getArgSorts(.OptBangATypes) => .List

    // STEP 2 PERFORM CHECKS

    rule <k> preModule(A:K,T:K) => startChecks ...</k>
         <tempAlpha> OldAlpha:K => A </tempAlpha>
         <tempT> OldT:K => T </tempT>


/*    rule <k> performNextChecks
             => checkUseVars
                ~> (checkLabelUses
                ~> (checkBlockAddress(.K)
                ~> (checkNoNormalBlocksHavingLandingpad(.K, TNS -Set TES)
                ~> (checkAllExpBlocksHavingLandingpad(.K, TES)
                ~> (checkAllExpInFromInvoke(.K, TES)
                ~> (checkLandingpad
                ~> checkLandingDomResumes)))))) ...</k> */

    rule <k> startChecks
             => checkNoSameKey
                ~> (checkTypeConsDontCollide
                ~> (makeAlphaMap
                ~> (checkAlphaNoLoops
                ~> (checkArgSortsAreTargets
                ~> (checkParUsed))))) ...</k>

    rule <k> checkTypeConsDontCollide
             => tyConCollCheck(T,.List,.Set) ...</k>
         <tempT> T:K </tempT>

    //syntax KItem ::= tChecker(K) [function]
    syntax KItem ::= tyConCollCheck(K,K,K) [function] //(TList,List of Tycons,Set of Tycons) 
    syntax KItem ::= lengthCheck(K,K) [function]
    //syntax KItem ::= tyConCollCheck(K,K,K) [function]
    //syntax K ::= innerCollCheck(K) [function]
    //syntax K ::= tyConCollCheckPasser(K, K) [function]

    //rule tChecker(preModule(Alpha:Map,T:K,Mod:K)) => tyConCollCheck(innerCollCheck(T),preModule(Alpha,T,Mod))

    //rule tyConCollCheck(.K,preModule(Alpha:Map,H:K,Mod:K)) => tyConCollCheck(innerCollCheck(H),preModule(Alpha,H,Mod))

    rule tyConCollCheck(TList(ListItem(TObject(A:K,B:K,ListItem(InnerTPiece(Ty:K,E:K,F:K,H:K,G:K)) Inners:List)) Rest:List),J:List,D:Set) => 
                    tyConCollCheck(TList(ListItem(TObject(A,B,Inners)) Rest),ListItem(Ty) J, SetItem(Ty) D)
    rule tyConCollCheck(TList(ListItem(TObject(A:K,B:K,.List)) Rest:List),J:List,D:Set) => 
                    tyConCollCheck(TList(Rest),J,D)
    rule tyConCollCheck(TList(.List),J:List,D:Set) => 
                    lengthCheck(size(J),size(D))

    rule lengthCheck(A:Int, B:Int) => .K
                    requires A ==Int B

    rule lengthCheck(A:Int, B:Int) => error
                    requires A =/=Int B

    //rule tyConCollCheck(TList(TObject(A:K,B:K,C:K) ~> Rest:K),J:K) => tyConCollCheckPasser(TList(innerCollCheck(TObject(A:K,B:K,C:K)) ~> Rest:K),J:K)
    syntax KItem ::= keyCheck(K,K,K,K) [function] //(Alpha, T, List of names, Set of names)

    rule <k> checkNoSameKey
             => keyCheck(A, T, .Set, .List) ...</k>
         <tempAlpha> A:K </tempAlpha>
         <tempT> T:K </tempT>
    //rule <k> checkAlphaNoSameKey
    //         => akeyCheck(.K, .Set) ...</k>

    rule keyCheck(AList(ListItem(AObject(A:K,B:K)) C:List), T:K, D:Set, G:List) => keyCheck(AList(C), T, SetItem(A) D, ListItem(A) G)
    rule keyCheck(AList(.List), TList(ListItem(TObject(A:K,B:K,C:K)) Rest:List), D:Set, G:List) => keyCheck(AList(.List), TList(Rest), SetItem(A) D, ListItem(A) G)
    rule keyCheck(AList(.List), TList(.List), D:Set, G:List) => lengthCheck(size(G),size(D))



    //deal with alpha map, deal with renaming of type name
    rule <k> makeAlphaMap => makeAlphaM(S, .Map, .Map) ...</k>
         <tempModule> S:K </tempModule>

    rule <k> putAlphaMap(M:Map) => .K ...</k>
         <tempAlphaMap> _:Map => M </tempAlphaMap>

    //deal with beta map,
    rule <k> makePreBetaMap => makePreBetaFun(S, .Map, .Map) ...</k>
         <tempModule> S:K </tempModule>

/*
    rule <k> makeAlphaMap
             => makeAlphaM(A, .Map) ...</k>
         <tempAlpha> A:K </tempAlpha> 

    rule makeAlphaM(AList(ListItem(AObject(A:K,B:K)) C:List), M:Map) => makeAlphaM(AList(C), M[A <- B])
    rule makeAlphaM(AList(.List), M:Map) => tAlphaMap(M)

    rule <k> tAlphaMap(M:K) => .K ...</k>
         <tempAlphaMap> OldAlphaMap:K => M </tempAlphaMap>
*/

//    syntax KItem ::= tkeyCheck(K,K,K) [function] //(T,List of T,Set of T)

//    rule <k> checkTNoSameKey
//             => tkeyCheck(T, .Set, T) ...</k>
//         <tempT> T:K </tempT>

//    rule tkeyCheck(TList(ListItem(TObject(A:K,B:K,C:K)) Rest:List), D:Set, G:K) => tkeyCheck(TList(Rest), SetItem(A) D, G)
//    rule tkeyCheck(TList(.List), D:Set, TList(G:List)) => lengthCheck(size(G),size(D))

    syntax KItem ::= aloopCheck(K,K,K,K,K,K,K) [function] //(Alpha,List of Alpha,Set of Alpha,CurrNode,lengthcheck,T,BigSet)

    rule <k> checkAlphaNoLoops
             => aloopCheck(A,.List,.Set,.K,.K,T,.Set) ...</k>
         <tempAlphaMap> A:K </tempAlphaMap>
         <tempT> T:K </tempT>

    //aloopCheck set and list to check cycles
    rule aloopCheck(Alpha:Map (A:KItem |-> B:KItem), D:List, G:Set, .K, .K,T:K,S:Set) => aloopCheck(Alpha, ListItem(B) ListItem(A) D, SetItem(B) SetItem(A) G, B, .K,T,S)
    rule aloopCheck(Alpha:Map (H |-> B:KItem), D:List, G:Set, H:KItem, .K,T:K,S:Set) => aloopCheck(Alpha, ListItem(B) D, SetItem(B) G, B, .K,T,S)

    rule aloopCheck(Alpha:Map, D:List, G:Set, H:KItem, .K,T:K,S:Set) => aloopCheck(Alpha, .List, .Set, .K, lengthCheck(size(G),size(D)),T,G S) //type rename loop ERROR
         requires (notBool H in keys(Alpha)) andBool (H in typeSet(T, .Set) orBool H in S) 

    rule aloopCheck(Alpha:Map, D:List, G:Set, H:KItem, .K,T:K,S:Set) => error //terminal alpha rename is not in T ERROR
         requires (notBool H in keys(Alpha)) andBool (notBool (H in typeSet(T, .Set) orBool H in S))


    syntax Set ::= typeSet(K,K) [function] //(K, KSet)
    rule typeSet(TList(ListItem(TObject(A:K,B:K,C:K)) Rest:List), D:Set) => typeSet(TList(Rest), SetItem(A) D)
    rule typeSet(TList(.List), D:Set) => D

//    rule aloopCheck(Alpha:Map, D:List, G:Set, H:KItem, .K) => keys(Alpha) ~> H
//         requires notBool H in keys(Alpha)

    rule aloopCheck(.Map, .List, .Set, .K, .K,T:K, S:Set) => .K
//    rule aloopCheck(AList(Front:List ListItem(AObject(H,B:K)) C:List), D:List, G:Set, H:ConId) => aloopCheck(AList(C:List), ListItem(B) D, SetItem(B) G, B)


//    syntax KItem ::= TList(K) //list of T objects for every new type introduced by data and newtype
//    syntax KItem ::= TObject(K,K,K) //(type name, entire list of poly type vars, list of inner T pieces)
//    syntax KItem ::= InnerTPiece(K,K,K,K,K) //(type constructor, poly type vars, argument sorts, entire constr block, type name)

//Make sure argument sorts [U] [W,V] are in the set of keys of alpha and targets of T, (keys of T)

    syntax KItem ::= argSortCheck(K,K,K) [function] //(T,AlphaMap)

    rule <k> checkArgSortsAreTargets
             => argSortCheck(T,A,typeSet(T,.Set)) ...</k>
         <tempAlphaMap> A:K </tempAlphaMap>
         <tempT> T:K </tempT>
    
    rule argSortCheck(TList(ListItem(TObject(A:K,B:K,ListItem(InnerTPiece(C:K,D:K,ListItem(Arg:KItem) ArgsRest:List,E:K,F:K)) InnerRest:List)) TListRest:List),AlphaMap:Map,Tset:Set) => argSortCheck(TList(ListItem(TObject(A,B,ListItem(InnerTPiece(C,D,ArgsRest,E,F)) InnerRest)) TListRest),AlphaMap,Tset)
         requires ((Arg in keys(AlphaMap)) orBool (Arg in Tset))

    rule argSortCheck(TList(ListItem(TObject(A:K,B:K,ListItem(InnerTPiece(C:K,D:K,ListItem(Arg:KItem) ArgsRest:List,E:K,F:K)) InnerRest:List)) TListRest:List),AlphaMap:Map,Tset:Set) => error
         requires (notBool ((Arg in keys(AlphaMap)) orBool (Arg in Tset)))

    rule argSortCheck(TList(ListItem(TObject(A:K,B:K,ListItem(InnerTPiece(C:K,D:K,.List,E:K,F:K)) InnerRest:List)) TListRest:List),AlphaMap:Map,Tset:Set) => argSortCheck(TList(ListItem(TObject(A,B,InnerRest)) TListRest),AlphaMap,Tset)

    rule argSortCheck(TList(ListItem(TObject(A:K,B:K,.List)) TListRest:List),AlphaMap:Map,Tset:Set) => argSortCheck(TList(TListRest),AlphaMap,Tset)

    rule argSortCheck(TList(.List),AlphaMap:Map,Tset:Set) => .K

//NEED TO CHECK all the polymorphic parameters from right appear on left. RIGHT SIDE ONLY
//NEED TO CHECK UNIQUENESS FOR POLY PARAM ON LEFT SIDE ONLY

    syntax KItem ::= parCheck(K,K) [function] //(T,AlphaMap)
    syntax KItem ::= makeTyVarList(K,K,K) [function] //(TyVars, NewList)
    syntax KItem ::= lengthRet(K,K,K) [function]

    rule <k> checkParUsed
             => parCheck(T,.K) ...</k>
         <tempT> T:K </tempT>

    //rule makeParLists(TList(ListItem(TObject(A:K,ListItem(Arg:KItem) PolyList:List,C:K)) Rest:List),Tlist:List,Tset:Set) => makeParLists(TList(ListItem(TObject(A,PolyList,C)) Rest),ListItem(Arg) Tlist,SetItem(Arg) Tset)
    rule parCheck(TList(ListItem(TObject(A:K,B:K,C:K)) Rest:List),.K) => parCheck(TList(ListItem(TObject(A:K,B:K,C:K)) Rest:List),makeTyVarList(B,.List,.Set))

    rule parCheck(TList(ListItem(TObject(A:K,B:K,ListItem(InnerTPiece(C:K,ListItem(Par:KItem) ParRest:List,D:K,E:K,F:K)) InnerRest:List)) Rest:List),NewSet:Set) =>
         parCheck(TList(ListItem(TObject(A,B,ListItem(InnerTPiece(C,ParRest,D,E,F)) InnerRest)) Rest),NewSet)
            requires Par in NewSet

    rule parCheck(TList(ListItem(TObject(A:K,B:K,ListItem(InnerTPiece(C:K,ListItem(Par:KItem) ParRest:List,D:K,E:K,F:K)) InnerRest:List)) Rest:List),NewSet:Set) => error
            requires notBool (Par in NewSet)

    rule parCheck(TList(ListItem(TObject(A:K,B:K,ListItem(InnerTPiece(C:K,.List,D:K,E:K,F:K)) InnerRest:List)) Rest:List),NewSet:Set) =>
         parCheck(TList(ListItem(TObject(A,B,InnerRest)) Rest),NewSet)

    rule parCheck(TList(ListItem(TObject(A:K,B:K,.List)) Rest:List),NewSet:Set) =>
         parCheck(TList(Rest),NewSet)

    rule parCheck(TList(.List),NewSet:Set) => .K

    rule makeTyVarList('typeVars(A:K,,Rest:K),NewList:List,NewSet:Set) => makeTyVarList(Rest, ListItem(A) NewList, SetItem(A) NewSet)

    rule makeTyVarList(.TyVars,NewList:List,NewSet:Set) => lengthRet(size(NewList),size(NewSet),NewSet)

    rule lengthRet(A:Int, B:Int, C:K) => C
                    requires A ==Int B

    rule lengthRet(A:Int, B:Int, C:K) => error
                    requires A =/=Int B
    
    //rule argSortCheck(TList(ListItem(TObject(A:K,B:K,C:K)

    // STEP 3 Transform T into beta

endmodule
