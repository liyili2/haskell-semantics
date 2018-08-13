requires "haskell-syntax.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX

    configuration <k> tChecker(initPreModule($PGM:Module)) </k>

    syntax KItem ::= Module(K, K)

    //rule getPreModule(module I:ModId where J:Body) => preModule(J)
    //rule getPreModule({I:TopDecls}) => getPreModule(I)
    //rule getPreModule(data I:OptContext J K L) => preModule(I)

    // t Checker
    syntax KItem ::= tChecker(K) [function]

    rule tChecker(preModule(Alpha:K,T:K,Module:K)) //

    // First pass
    syntax KItem ::= fetchTypes (K,K,K,K) [function]
    syntax KItem ::= makeT (K,K,K,K) [function]
    syntax K ::= makeInnerT (K,K,K) [function]
    syntax KItem ::= getTypeVars (K) [function]

    syntax KItem ::= getCon(K) [function]
    syntax KItem ::= getArgSorts(K) [function]

    syntax K ::= getPreModule (K,K) [function]
    syntax K ::= initPreModule (K) [function]
    syntax KItem ::= preModule(Map,K,K) //(alpha, T, Source Code)

    syntax KItem ::= TList(KList) //list of T objects for every new type introduced by data and newtype
    syntax KItem ::= TObject(KList,KList,KList) //(type name, entire list of poly type vars, list of inner T pieces)
    syntax KItem ::= InnerTPiece(K,KList,KList,K,K) //(type constructor, poly type vars, argument sorts, entire constr block, type name)

    rule initPreModule('module(I:ModuleName,, J:K)) => getPreModule(J,preModule(.Map,TList(.K),J))
    rule initPreModule('moduleExp(I:ModuleName,, L:K,, J:K)) => getPreModule(J,preModule(.Map,TList(.K),J))
    rule initPreModule('moduleBody(J:Body)) => getPreModule(J,preModule(.Map,TList(.K),J))

    rule getPreModule('bodytopdecls(I:K), J:K) => getPreModule(I,J)


    rule getPreModule('topdeclslist('type(A:K,, B:K),, Rest:K),J:K) => fetchTypes(A,B,Rest,J) //constructalpha


    rule getPreModule('topdeclslist('data(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => makeT(B,C,Rest,J)
    rule getPreModule('topdeclslist('newtype(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => makeT(B,C,Rest,J)


    rule getPreModule('topdeclslist('topdecldecl(A:K),, Rest:K),J:K) => getPreModule(Rest,J)
    rule getPreModule('topdeclslist('class(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => fetchTypes(B,C,Rest,J)
    rule getPreModule('topdeclslist('instance(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => fetchTypes(B,C,Rest,J)
    rule getPreModule('topdeclslist('default(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => fetchTypes(B,C,Rest,J)
    rule getPreModule('topdeclslist('foreign(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => fetchTypes(B,C,Rest,J)
    rule getPreModule(.TopDecls,J:K) => J

    //rule getPreModule('module(I:ModuleName,L:K, J:K)) => preModule(J)

    rule fetchTypes('simpleTypeCon(I:TyCon,, H:TyVars), C:K, Rest:K, preModule(M:Map, L:K, J:K)) => getPreModule(Rest,preModule(M[I <- C],L,J))

    rule makeT('simpleTypeCon(I:TyCon,, H:TyVars), D:K, Rest:K, preModule(M:Map, TList(ListInside:K), J:K)) => getPreModule(Rest,preModule(M,TList( TObject(I,H,makeInnerT(I,H,D)) ~> ListInside),J))

    rule makeInnerT(A:K,B:K,'nonemptyConstrs(C:K)) => makeInnerT(A,B,C)
    rule makeInnerT(A:K,B:K,'singleConstr(C:K)) => InnerTPiece(getCon(C),getTypeVars(C),getArgSorts(C),C,A)
    rule makeInnerT(A:K,B:K,'multConstr(C:K,, D:K)) => InnerTPiece(getCon(C),getTypeVars(C),getArgSorts(C),C,A) ~> makeInnerT(A,B,D)

    rule getTypeVars('constrCon(A:K,, B:K)) => getTypeVars(B)
    rule getTypeVars('optBangATypes(A:K,, Rest:K)) => getTypeVars(A) ~> getTypeVars(Rest)
    rule getTypeVars('optBangAType('emptyBang(.KList),, Rest:K)) => getTypeVars(Rest)
    rule getTypeVars('atypeGTyCon(A:K)) => .K
    rule getTypeVars('atypeTyVar(A:K)) => A
    rule getTypeVars(.OptBangATypes) => .OptBangATypes

    //rule getCon('emptyConstrs()) => .K
    //rule getCon('nonemptyConstrs(A:K)) => getCon(A)
    rule getCon('constrCon(A:K,, B:K)) => A

    //rule getArgSorts('constrCon(A:K,, B:K)) => B
    rule getArgSorts('constrCon(A:K,, B:K)) => getArgSorts(B)
    rule getArgSorts('optBangATypes(A:K,, Rest:K)) => getArgSorts(A) ~> getArgSorts(Rest)
    rule getArgSorts('optBangAType('emptyBang(.KList),, Rest:K)) => getArgSorts(Rest)
    rule getArgSorts('atypeGTyCon(A:K)) => A
    rule getArgSorts('atypeTyVar(A:K)) => .K
    rule getArgSorts(.OptBangATypes) => .OptBangATypes
endmodule
