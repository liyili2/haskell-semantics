//
requires "haskell-syntax.k"
requires "haskell-configuration.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX
    imports HASKELL-CONFIGURATION

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

    //call before Checker Code
    rule <k> callInit(S:K) => initPreModule(S) ...</k>
         <tempModule> A:K => S </tempModule>

    //start of Checker Code
    syntax KItem ::= Module(K, K)
    syntax KItem ::= preModule(K,K) //(alpha, T)

    // STEP 1 CONSTRUCT T AND ALPHA
    // alpha = type
    // T = newtype and data, temporary data structure

    syntax KItem ::= initPreModule(K) [function]
    syntax KItem ::= getPreModule(K, K) [function] //(Current term, premodule)
    syntax KItem ::= makeT (K,K,K,K) [function]

    syntax KItem ::= fetchTypes (K,K,K,K) [function]

    syntax List ::= makeInnerT (K,K,K) [function] //LIST
    syntax List ::= getTypeVars(K) [function] //LIST

    syntax KItem ::= getCon(K) [function]
    syntax List ::= getArgSorts(K) [function] //LIST

    syntax KItem ::= AList(K)
    syntax KItem ::= AObject(K,K) //(1st -> 2nd) map without idempotency

    syntax KItem ::= TList(K) //list of T objects for every new type introduced by data and newtype
    syntax KItem ::= TObject(K,K,K) //(type name, entire list of poly type vars, list of inner T pieces)
    syntax KItem ::= InnerTPiece(K,K,K,K,K) //(type constructor, poly type vars, argument sorts, entire constr block, type name)

    rule initPreModule('module(I:ModuleName,, J:K)) => getPreModule(J,preModule(AList(.List),TList(.List)))
    rule initPreModule('moduleExp(I:ModuleName,, L:K,, J:K)) => getPreModule(J,preModule(AList(.List),TList(.List)))
    rule initPreModule('moduleBody(J:Body)) => getPreModule(J,preModule(AList(.List),TList(.List)))

    rule getPreModule('bodytopdecls(I:K), J:K) => getPreModule(I,J)
    rule getPreModule('topdeclslist('type(A:K,, B:K),, Rest:K),J:K) => fetchTypes(A,B,Rest,J) //constructalpha


    rule getPreModule('topdeclslist('data(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => makeT(B,C,Rest,J)
    rule getPreModule('topdeclslist('newtype(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => makeT(B,C,Rest,J)


    rule getPreModule('topdeclslist('topdecldecl(A:K),, Rest:K),J:K) => getPreModule(Rest,J)
    rule getPreModule('topdeclslist('class(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => getPreModule(Rest,J)
    rule getPreModule('topdeclslist('instance(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => getPreModule(Rest,J)
    rule getPreModule('topdeclslist('default(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => getPreModule(Rest,J)
    rule getPreModule('topdeclslist('foreign(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => getPreModule(Rest,J)
    rule getPreModule(.TopDecls,J:K) => J

    //rule getPreModule('module(I:ModuleName,L:K, J:K)) => preModule(J)

    rule fetchTypes('simpleTypeCon(I:TyCon,, H:TyVars), C:K, Rest:K, preModule(AList(M:List), L:K)) => getPreModule(Rest,preModule(AList(ListItem(AObject(I,C)) M), L))

    rule makeT('simpleTypeCon(I:TyCon,, H:TyVars), D:K, Rest:K, preModule(AList(M:List), TList(ListInside:List))) => getPreModule(Rest,preModule(AList(M),TList(ListItem(TObject(I,H,makeInnerT(I,H,D))) ListInside)))

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

    syntax KItem ::= "error"

    syntax KItem ::= "startChecks"
    syntax KItem ::= "checkAlphaNoSameKey"
    syntax KItem ::= "checkAlphaNoLoops"
        //alpha check for no loops
    syntax KItem ::= "checkTypeConsDontCollide"
        //Make sure typeconstructors do not collide in T
    syntax KItem ::= "checkArgSortsAreTargets"
           //Make sure argument sorts [U] [W,V] are in the set of keys of alpha and targets of T, (keys of T)
//NEED TO CHECK all the polymorphic parameters are used in left side and right side (1 to 1)
//Keys of alpha and keys of T should be unique

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
             => checkTypeConsDontCollide
                ~> (checkAlphaNoSameKey
                ~> (checkAlphaNoLoops)) ...</k>

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
    syntax KItem ::= akeyCheck(K,K,K) [function] //(Alpha,List of Alpha,Set of Alpha)
    syntax KItem ::= aloopCheck(K) [function] //(Alpha,List of Alpha,Set of Alpha,CurrNode)

    rule <k> checkAlphaNoSameKey
             => akeyCheck(A, .Set, A) ...</k>
         <tempAlpha> A:K </tempAlpha>
    //rule <k> checkAlphaNoSameKey
    //         => akeyCheck(.K, .Set) ...</k>

    rule <k> checkAlphaNoLoops
             => aloopCheck(A) ...</k>
         <tempAlpha> A </tempAlpha>

    rule akeyCheck(AList(ListItem(AObject(A:K,B:K)) C:List), D:Set, G:K) => akeyCheck(AList(C), SetItem(A) D, G)
    rule akeyCheck(AList(.List), D:Set, AList(G:List)) => lengthCheck(size(G),size(D))

    //aloopCheck set and list to check cycles
    //rule aloopCheck(A:Map (B:K |-> C:K)) => aloopCheck(A)
    

    // STEP 3 Transform T into beta

endmodule
