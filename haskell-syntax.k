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

    syntax VarId ::= "size" [onlyLabel] | Token{[a-z \_][0-9 a-z A-Z \' \_]*}   [onlyLabel]
    
    syntax ConId ::= Token{[A-Z][0-9 a-z A-Z \' \_]*}   [onlyLabel]

    syntax TyVarTuple ::= TyVar "," TyVar | TyVar "," TyVarTuple
    syntax TyVars ::= List{TyVar, ""} //used in SimpleType syntax
    syntax TyVar ::= VarId
    syntax TyCon ::= ConId
    syntax TyCls ::= ConId
    
    syntax ModId ::= ConId | ConId "." ModId

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

    syntax ImpDecls ::= List{ImpDecl, ";"}

    syntax Exports ::= "(" ExportList ")" | "(" ExportList ",)"

    syntax ExportList ::= List{Export, ","}

    syntax Export ::= QVar | QTyCon

    syntax ImpDecl ::= "import" ModId

    syntax TopDecls ::= List{TopDecl, ";"}

    syntax TopDecl ::= "type" SimpleType "=" Type
                     | "data" OptContext SimpleType OptConstrs
                     | "newtype" OptContext SimpleType "=" NewConstr
                     | "class" TyCls TyVar
                     | "instance" QTyCls Inst
                     | "default" Types
                     | "foreign" FDecl
                     | Decl

    syntax Decls ::= "{" DeclsList "}"
    syntax DeclsList ::= List{Decl, ";"}

    syntax Decl ::= GenDecl
                  | FunLhs Rhs
                  | Pat Rhs

    syntax GenDecl ::= Vars "::" Type
                     | Vars "::" Context "=>" Type
//                     | Fixity Ops
//                     | Fixity Integer Ops

    syntax Ops ::= Op | Op "," Ops
    syntax Vars ::= Var | Var "," Vars

    syntax TypeTuple ::= Type "," Type | Type "," TypeTuple
    syntax Types ::= List{Type, ","}
    syntax Type ::= BType
                  | BType "->" Type

    syntax BType ::= AType
                   | BType AType

    syntax OptBangATypes ::= List{OptBangAType, ""}
    syntax OptBangAType ::= OptBang AType
    syntax OptBang ::= "!" | "" [onlyLabel, klabel('emptyBang)]
    
    syntax ATypes ::= AType | AType ATypes
    syntax ATypeList ::= List{AType, ""}
    syntax AType ::= GTyCon
                   | TyVar
                   | "(" TypeTuple ")"
                   | "[" Type "]"
                   | "(" Type ")"

    syntax GTyCon ::= QTyCon
                    | "()"
                    | "[]"
                    | "(->)"
                    | "(,{,})"

    syntax OptContext ::= Context "=>" | "" [onlyLabel, klabel('emptyContext)]
    syntax Context ::= Class
                     | Classes

    syntax Classes ::= List{Class, ","}

    syntax Class       ::= QTyCls TyVar
                         | QTyCls "(" TyVar ATypes ")"

    syntax SimpleClass ::= QTyCls TyVar

    syntax SimpleType  ::= TyCon TyVars
    syntax OptConstrs  ::= "=" Constrs | "" [onlyLabel, klabel('emptyConstrs)]
    syntax Constrs     ::= Constr | Constr "|" Constrs
    syntax SubConstr   ::= BType | "!" AType
    syntax Constr      ::= Con OptBangATypes // (arity con  =  k, k ≥ 0) 
                         | SubConstr ConOp SubConstr
                         | Con "{" FieldDeclList "}"
    
    syntax NewConstr   ::= Con AType
                         | Con "{" Var "::" Type "}"
                         
    syntax FieldDeclList ::= List{FieldDecl, ","}
    
    syntax FieldDecl ::= Vars "::" Type
                       | Vars "::" "!" AType
                       
    syntax Deriving ::= "deriving" DClass
                      | "deriving" DClassList
    syntax DClassList ::= List{DClass, ","}
    syntax DClass ::= QTyCls
                       
    syntax Inst        ::= GTyCon
                         | "(" GTyCon TyVars ")"
                         | "(" TyVarTuple ")"
                         | "[" TyVar "]"
                         | "(" TyVar "->" TyVar ")"
    
    syntax FDecl ::= "import" CallConv Impent Var "::" FType
                   | "import" CallConv Safety Impent Var "::" FType
                   | "export" CallConv Safety Expent Var "::" FType
                   
    syntax CallConv ::= "ccall" | "stdcall" | "cplusplus" | "jvm" | "dotnet"
    
    syntax Impent ::= "IMPENT" // temporary
    syntax Expent ::= "EXPENT" // temporary
    
    syntax Safety ::= "unsafe" | "safe"
    
    syntax FType ::= FrType
                   | FaType "->" FType // unsure about this one syntax is ambiguous
    
    syntax FrType ::= FaType
                    | "()"
                    
    syntax FaType ::= QTyCon ATypeList

    syntax FunLhs ::= Var APat APats
//                    | Pat VarOp Pat
                    | "(" FunLhs ")" APat APats

    syntax Rhs ::= "=" Exp
                 | "=" Exp "where" Decls

    syntax ExpList ::= Exp | Exp "," ExpList
    syntax ExpTuple ::= Exp "," Exp | Exp "," ExpTuple

    syntax Exp ::= InfixExp "::" Type
                 | InfixExp "::" Context "=>" Type
                 | InfixExp

    syntax InfixExp ::= LExp QOp InfixExp
                      | "-" InfixExp
                      | LExp

    syntax LExp ::= "\\" APats "->" Exp
                  | "let" Decls "in" Exp
                  | "if" Exp OptSemicolon "then" Exp OptSemicolon "else" Exp
                  | "case" Exp "of" "{" Alts "}"
                  | "do" "{" Stmts "}"
                  | Fexp
    syntax Fexp ::= AExp | Fexp AExp

    syntax OptSemicolon ::= ";" | "" [onlyLabel, klabel('emptySemicolon)]

//    syntax OptWhereDecls ::= "where" Decls | ""

    syntax AExp ::= QVar
                  | GCon
                  | Literal
                  | "(" Exp ")"
                  | "(" ExpTuple ")"
                  | "[" ExpList "]"
                  | "(" InfixExp QOp ")"
                  | "(" QOp InfixExp ")"

    syntax Alts ::= Alt | Alt ";" Alts

    syntax Alt ::= Pat "->" Exp
                 | Pat "->" Exp "where" Decls
                 
    syntax Stmts ::= StmtList Exp OptSemicolon
    syntax StmtList ::= List{Stmt, ""}
    syntax Stmt ::= Exp ";"
                  | Pat "<-" Exp ";"
                  | "let" Decls ";"
                  | ";"

    syntax PatTuple ::= Pat "," Pat | Pat "," PatTuple
    syntax PatList ::= Pat | Pat "," PatList

    syntax Pat ::= LPat QConOp Pat
                 | LPat

    syntax LPat ::= APat
                  | "-" Integer
//                  | "-" Float
                  | GCon APatList

    syntax APatList ::= APat | APat APatList
    syntax APats ::= List{APat, ""}

    syntax APat ::= Var
                  | Var "@" APat
                  | GCon
//                  | QCon FPats
                  | Literal
//                  _
                  | "(" Pat ")"
                  | "(" PatTuple ")"
                  | "[" Pat "]"
                  | "[" PatList "]"
                  | "~" APat
    
    syntax FPats ::= List{FPat, ","}
    syntax FPat ::= QVar "=" Pat

    syntax GCon ::= "()"
                  | "[]"
                  | "(,{,})"
                  | QCon

    //syntax OpId ::= Token{[\'][0-9 a-z A-Z \_]*[\']}   [onlyLabel]

    syntax Var ::= VarId | "(" VarSym ")"
    syntax QVar ::= QVarId | "(" QVarSym ")"
    syntax Con ::= ConId | "(" ConSym ")"
    syntax QCon ::= QConId | "(" GConSym ")"
    syntax VarOp ::= VarSym | "`" VarId "`"
    syntax QVarOp ::= QVarSym | "`" QVarId "`"
    syntax ConOp ::= ConSym | "`" ConId "`"
    syntax QConOp ::= GConSym | "`" QConId "`"
    syntax Op ::= VarOp | ConOp
    syntax QOp ::= QVarOp | QConOp
    syntax GConSym ::= ":" | QConSym

configuration <k> $PGM:Module </k>
endmodule
