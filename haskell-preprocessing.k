requires "haskell-syntax.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX

    configuration <k> initPreModule($PGM:Module) </k>

    syntax KItem ::= Module(K, K)

    //rule getPreModule(module I:ModId where J:Body) => preModule(J)
    //rule getPreModule({I:TopDecls}) => getPreModule(I)
    //rule getPreModule(data I:OptContext J K L) => preModule(I)

    syntax KItem ::= fetchTypes (K,K,K,K) [function]
    syntax KItem ::= makeT (K,K,K,K) [function]
    syntax KItem ::= makeInnerT (K,K,K) [function]
    syntax KItem ::= getTypeVars (K) [function]

    syntax KItem ::= getCon(K) [function]
    syntax KItem ::= getArgSorts(K) [function]

    syntax K ::= getPreModule (K,K) [function]
    syntax K ::= initPreModule (K) [function]
    syntax KItem ::= preModule(Map,K,K)

    syntax KItem ::= TObject(KList,KList,KList)
    syntax KItem ::= InnerTPiece(K,KList,KList,K) //(type constructor, poly type vars, argument sorts, type name)

    rule initPreModule('module(I:ModuleName,, J:K)) => getPreModule(J,preModule(.Map,TObject(.K,.K,.K),J))
    rule initPreModule('moduleExp(I:ModuleName,, L:K,, J:K)) => getPreModule(J,preModule(.Map,TObject(.K,.K,.K),J))
    rule initPreModule('moduleBody(J:Body)) => getPreModule(J,preModule(.Map,TObject(.K,.K,.K),J))

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

    rule makeT('simpleTypeCon(I:TyCon,, H:TyVars), D:K, Rest:K, preModule(M:Map, TObject(A:K,B:K,C:K), J:K)) => getPreModule(Rest,preModule(M,TObject(I ~> A,getTypeVars(H) ~> B,makeInnerT(I,H,D) ~> C),J))

    rule makeInnerT(A:K,B:K,C:K) => InnerTPiece(getCon(C),getTypeVars(B),getArgSorts(C),A)

    rule getTypeVars(.TyVars) => .K
endmodule
