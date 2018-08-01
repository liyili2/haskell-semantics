requires "haskell-syntax.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX

    configuration <k> initPreModule($PGM:Module) </k>

    syntax KItem ::= Module(K, K)

    //rule getPreModule(module I:ModId where J:Body) => preModule(J)
    //rule getPreModule({I:TopDecls}) => getPreModule(I)
    //rule getPreModule(data I:OptContext J K L) => preModule(I)

    syntax KItem ::= fetchTypes (K,K,K,K) [function]
    syntax K ::= getPreModule (K,K) [function]
    syntax K ::= initPreModule (K) [function]
    syntax KItem ::= preModule(Map,K)
    rule initPreModule('module(I:ModuleName,, J:K)) => getPreModule(J,preModule(.Map,J))
    rule getPreModule('bodytopdecls(I:TopDecls), J:K) => getPreModule(I,J)
    rule getPreModule('_;_('data(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => fetchTypes(B,C,Rest,J)
    rule getPreModule('_;_('type(A:K,, B:K),, Rest:K),J:K) => fetchTypes(A,B,Rest,J)
    rule getPreModule('_;_('newtype(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => fetchTypes(B,C,Rest,J)
    rule getPreModule('_;_('topdecldecl(A:K),, Rest:K),J:K) => getPreModule(Rest,J)
    rule getPreModule(.TopDecls,J:K) => J
    //rule getPreModule('_;_('class(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => fetchTypes(B,C,Rest,J)
    //rule getPreModule('module(I:ModuleName,L:K, J:K)) => preModule(J)

    rule fetchTypes('simpleTypeCon(I:TyCon,, H:TyVars), C:K, Rest:K, preModule(M:Map, J:K)) => getPreModule(Rest,preModule(M[I <- C],J))
endmodule
