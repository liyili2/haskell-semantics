// Syntax from haskell 2010 Report
// https://www.haskell.org/onlinereport/haskell2010/haskellch10.html#x17-17500010

module HASKELL-SYNTAX
// Section 10.2
    //syntax Digit ::= AscDigit
    //syntax AscDigit ::= Token{[0-9]}   [onlyLabel]
    syntax Literal ::= Integer | String
    syntax VarSym ::= Token{[\! \# \$ \% \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~][\! \# \$ \% \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]*}   [onlyLabel]
    syntax ConSym ::= Token{[\:][\! \# \$ \% \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]*}   [onlyLabel]
//    syntax Symbol ::= AscSymbol
//    syntax AscSymbol ::= Token{[\! \# \$ \% \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]}   [onlyLabel]

//    syntax VarSym ::= Symbols //not true to haskell


//    syntax Symbols ::= List{Symbol, ""}

//    syntax VarSym ::= Token{~[\:] (~[\ ])*} [onlyLabel]
//    syntax ConSym ::= Token{[\:] (~[\ ])*} [onlyLabel]

//    syntax VarId ::= Token{[:]([\ ]~)*} [onlyLabel]
//    syntax ReservedId ::= "case" | "class" | "data" | "default" | "deriving" | "do" | "else" | "->" | "@" | "~" | "=>"

//    syntax ConSym ::= Token{"([;::)(]~)"} [onlyLabel]
//    syntax ReservedOp ::= ".." | ":" | "::" | "=" | "\\" | "|" | "<-" | "->" | "@" | "~" | "=>"

    syntax VarId ::= "size" [onlyLabel] | Token{[a-z][0-9 a-z A-Z \']*}   [onlyLabel]
    syntax ConId ::= Token{[A-Z][0-9 a-z A-Z \']*}   [onlyLabel]

    syntax TyVars ::= List{TyVar, ""} //used in SimpleType syntax
    syntax TyVar ::= VarId
    syntax TyCon ::= ConId
    syntax TyCls ::= ConId
    syntax ModId ::= ConId

    syntax QVarId ::= VarId | ModId "." VarId
    syntax QConId ::= ConId | ModId "." ConId
    syntax QTyCon ::= TyCon | ModId "." TyCon
    syntax QTyCls ::= TyCls | ModId "." TyCls
    syntax QVarSym ::= VarSym | ModId "." VarSym
    syntax QConSym ::= ConSym | ModId "." ConSym

//    syntax Integer ::= Token{[0-9]*}   [onlyLabel]

    syntax Integer ::= Int

//    syntax StringInside ::= Token{[0-9 a-z A-Z]*}   [onlyLabel]
//    syntax String ::= "\"" StringInside "\""
//    syntax String ::= Token{[\"][0-9 a-z A-Z]*[\"]}   [onlyLabel]

//  Section 10.5

    syntax Module ::= "module" ModId "where" Body
                    | "module" ModId Exports "where" Body
                    | Body

    syntax Body ::= "{" ImpDecls ";" TopDecls "}"
                  | "{" ImpDecls "}"
                  | "{" TopDecls "}"

//    syntax Body1 ::= ImpDecls ";" TopDecls

    syntax ImpDecls ::= List{ImpDecl, ";"}

    syntax Exports ::= "(" ExportList ")" //| "(" ExportList ",)"

    syntax ExportList ::= List{Export, ","}

    syntax Export ::= QVar | QTyCon

    syntax ImpDecl ::= "import" ModId

    syntax TopDecls ::= List{TopDecl, ";"}

//    syntax TopDecl ::= Decl // TEMPORARY

    syntax TopDecl ::= "type" SimpleType "=" Type
                     | "data" SimpleType
                     | "data" SimpleType "=" Constrs
//                     | "newtype" SimpleType "=" NewConstr
                     | "class" TyCls TyVar
//                     | "instance" QTycls Inst
//                     | "default" Types
//                     | "foreign" FDecl
                     | Decl

    syntax Decls ::= "{" DeclsList "}"
    syntax DeclsList ::= List{Decl, ";"}

    syntax Decl ::= GenDecl
                  | FunLhs Rhs
                  | Pat Rhs

    syntax GenDecl ::= Vars "::" Type
//                     | Vars "::" Context "=>" Type
//                     | Fixity Ops
//                     | Fixity Integer Ops

//    syntax Ops ::= List{Op, ","}
    syntax Vars ::= List{Var, ","}

    syntax Types ::= List{Type, ","}
    syntax Type ::= BType
                  | BType "->" Type

    syntax BType ::= AType
                   | BType AType

    syntax OptBangATypes ::= List{OptBangAType, ""}
    syntax OptBangAType ::= OptBang AType
    syntax OptBang ::= "!" | "" [onlyLabel, klabel('emptyBang)]
    syntax AType ::= GTyCon
                   | TyVar
                   | "(" Types ")"
                   | "[" Type "]"
                   | "(" Type ")"

    syntax GTyCon ::= QTyCon

    syntax Context ::= Class
                     | Classes

    syntax Classes ::= List{Class, ","}

    syntax Class ::= QTyCls TyVar
//                   | QTyCls Tyvar ATypes

    syntax SimpleType ::= TyCon TyVars
    syntax Constrs ::= List{Constr, "|"}
    syntax Constr ::= Con OptBangATypes // (arity con  =  k, k ≥ 0) 

    syntax FunLhs ::= Var APat APats
//                    | Pat VarOp Pat
                    | "(" FunLhs ")" APat APats

    syntax Rhs ::= "=" Exp
                 | "=" Exp "where" Decls

    syntax Exp ::= InfixExp "::" Type
                 | InfixExp "::" Context "=>" Type
                 | InfixExp

    syntax InfixExp ::= LExp QOp InfixExp
                      | "-" InfixExp
                      | LExp

    syntax LExp ::= "\\" APats "->" Exp
                  | "let" Decls "in" Exp
                  | "if" Exp OptSemicolon "then" Exp OptSemicolon "else" Exp
//                  | "case" Exp "of" "{" Alts "}"
//                  | "do" "{" Stmts "}"
                  | Fexp
    syntax Fexp ::= AExp | Fexp AExp

    syntax OptSemicolon ::= ";" | "" [onlyLabel, klabel('emptySemicolon)]

    syntax AExp ::= GCon
                  | Literal
                  | "(" InfixExp QOp ")"
                  | "(" QOp InfixExp ")"

    syntax Pats ::= List{Pat, ","}

    syntax Pat ::= LPat QConOp Pat
                 | LPat

    syntax LPat ::= APat
                  | "-" Integer
//                  | "-" Float
                  | GCon APats

    syntax APats ::= List{APat, ""}

    syntax APat ::= Var
                  | Var "@" APat
//                  | QCon FPats
                  | Literal
//                  _
                  | "(" Pat ")"
                  | "(" Pats ")"
                  | "[" Pats "]"
                  | "~" APat

    syntax GCon ::= "()"
                  | "[]"
                  | "(,{,})"
                  | QCon

    //syntax OpId ::= Token{[\'][0-9 a-z A-Z \_]*[\']}   [onlyLabel]

    syntax Var ::= VarId //| "(" VarSym ")"
    syntax QVar ::= QVarId
    syntax Con ::= ConId //| "(" ConSym ")"
    syntax QCon ::= QConId //| "(" GConSym ")"
    syntax QVarOp ::= QVarSym
    syntax QConOp ::= GConSym
    syntax QOp ::= QVarOp | QConOp
    syntax GConSym ::= ":" | QConSym

configuration <k> $PGM:Module </k>
endmodule
