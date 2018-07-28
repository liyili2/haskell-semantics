requires "haskell-syntax.k"

module HASKELL-PREPROCESSING
    imports HASKELL-SYNTAX

    configuration <k> initPreModule($PGM:Module) </k>

    syntax KItem ::= Module(K, K)

    //rule getPreModule(module I:ModId where J:Body) => preModule(J)
    //rule getPreModule({I:TopDecls}) => getPreModule(I)
    //rule getPreModule(data I:OptContext J K L) => preModule(I)

    syntax KItem ::= fetchTypes (K,K,K) [function]
    syntax K ::= getPreModule (K,K) [function]
    syntax K ::= initPreModule (K) [function]
    syntax KItem ::= preModule(K, K)
    rule initPreModule('module(I:ModuleName,, J:K)) => getPreModule(J,preModule(.K,J))
    rule getPreModule('bodytopdecls(I:TopDecls), J:K) => getPreModule(I,J)
    rule getPreModule('_;_('data(A:K,, B:K,, C:K,, D:K),, Rest:K),J:K) => fetchTypes(B,Rest,J)
    //rule getPreModule('module(I:ModuleName,L:K, J:K)) => preModule(J)

    rule fetchTypes('simpleTypeCon(I:TyCon,, H:TyVars), Rest:K, preModule(L:K, J:K)) => getPreModule(Rest,preModule(I,J))
endmodule
