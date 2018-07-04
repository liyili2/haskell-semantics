// Syntax from haskell 2010 Report
// https://www.haskell.org/onlinereport/haskell2010/haskellch10.html#x17-17500010

module HASKELL-SYNTAX
// Section 10.2
    //syntax Digit ::= AscDigit
    //syntax AscDigit ::= Token{[0-9]}   [onlyLabel]
    syntax LiteralInner ::= Integer | String | CusFloat
    syntax Literal ::= LiteralInner | LiteralInner "#" | LiteralInner "##"
    syntax VarSym ::= Token{[\! \# \$ \% \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~][\! \# \$ \% \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]*}   [onlyLabel] | "-"
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

    syntax VarIdInner ::= "size" [onlyLabel]
                        | Token{[a-z \_][0-9 a-z A-Z \' \_]*}   [onlyLabel]

    syntax VarId ::= VarIdInner | VarIdInner "#" | VarIdInner "##"
    
    syntax ConIdInner ::= Token{[A-Z][0-9 a-z A-Z \' \_]*}   [onlyLabel]

    syntax ConId ::= ConIdInner | ConIdInner "#" | ConIdInner "##"

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
    syntax CusFloat ::= Token{([0-9]+[\.][0-9]+([e E][\+ \-]?[0-9]+)?)|([0-9]+[e E][\+ \-]?[0-9]+)} [onlyLabel]
//    syntax CusFloat ::= Float

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

    syntax Export ::= QVar 
                    | QTyCon OptCNameList
		                | QTyCls OptQVarList
                    | "module" ModId

    syntax ImpDecl ::= "import" OptQualified ModId OptAsModId OptImpSpec
                     | "" [onlyLabel, klabel('emptyImpDecl)]
    syntax OptQualified ::= "qualified" | "" [onlyLabel, klabel('emptyQualified)]
    syntax OptAsModId ::= "as" ModId | "" [onlyLabel, klabel('emptyOptAsModId)]

    syntax OptImpSpec ::= ImpSpec | "" [onlyLabel, klabel('emptyOptImpSpec)]

    syntax ImpSpec ::= "(" ImportList OptComma ")"
                     | "hiding" "(" ImportList OptComma ")"

    syntax ImportList ::= List{Import, ","}

    syntax Import ::= Var
                    | TyCon OptCNameList
		                | TyCls OptVarList

    syntax OptCNameList ::= "(..)" | "(" CNameList ")" | "" [onlyLabel, klabel('emptyOptCNameList)]
    syntax CNameList ::= List{CName, ","}

    syntax CName ::= Var | Con

    syntax TopDecls ::= List{TopDecl, ";"}

    syntax TopDecl ::= "type" SimpleType "=" Type
                     | "data" OptContext SimpleType OptConstrs OptDeriving
                     | "newtype" OptContext SimpleType "=" NewConstr OptDeriving
                     | "class" OptSContext TyCls TyVar OptCDecls
                     | "instance" OptSContext QTyCls Inst OptIDecls
                     | "default" Types
                     | "foreign" FDecl
                     | Decl

    syntax OptDecls ::= "where" Decls | "" [onlyLabel, klabel('emptyOptDecls)]
    syntax Decls ::= "{" DeclsList "}"
    syntax DeclsList ::= List{Decl, ";"}

    syntax Decl ::= GenDecl
                  | FunLhs Rhs
                  | Pat Rhs

    syntax OptCDecls ::= "where" CDecls | "" [onlyLabel, klabel('emptyOptCDecls)]
    syntax CDecls ::= "{" CDeclsList "}"
    syntax CDeclsList ::= List{CDecl, ";"}

    syntax CDecl ::= GenDecl
                   | FunLhs Rhs
                   | Var Rhs

    syntax OptIDecls ::= "where" IDecls | "" [onlyLabel, klabel('emptyOptIDecls)]
    syntax IDecls ::= "{" IDeclsList "}"
    syntax IDeclsList ::= List{IDecl, ";"}

    syntax IDecl ::= FunLhs Rhs
                   | Var Rhs
                   | "" [onlyLabel, klabel('emptyIDecl)]

    syntax GenDecl ::= Vars "::" Type
                     | Vars "::" Context "=>" Type
                     | Fixity Ops
                     | Fixity Integer Ops
                     | "" [onlyLabel, klabel('emptyGenDecl)]

    syntax Ops ::= Op | Op "," Ops
    syntax Vars ::= Var | Var "," Vars
    syntax Fixity ::= "infixl" | "infixr" | "infix"

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
    
    syntax OptSContext ::= SContext "=>" | "" [onlyLabel, klabel('emptySContext)]
    syntax SContext ::= SimpleClass
                      | SimpleClassList
    
    syntax SimpleClassList ::= List{SimpleClass, ","}

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

    syntax OptDeriving ::= Deriving | "" [onlyLabel, klabel('emptyDeriving)]
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

    syntax FunLhs ::= Var APatList
                    | Pat VarOp Pat
                    | "(" FunLhs ")" APatList

    syntax Rhs ::= "=" Exp OptDecls
                 | GdRhs OptDecls

    syntax GdRhs ::= Guards "=" Exp
                   | Guards "=" Exp GdRhs

    syntax Guards ::= "|" GuardList
    syntax GuardList ::= Guard | Guard "," GuardList
    syntax Guard ::= Pat "<-" InfixExp
                   | "let" Decls
                   | InfixExp

    syntax ExpList ::= Exp | Exp "," ExpList
    syntax ExpTuple ::= Exp "," Exp | Exp "," ExpTuple

    syntax OptExpComma ::= "," Exp | "" [onlyLabel, klabel('emptyExpComma)]
    syntax OptExp ::= Exp | "" [onlyLabel, klabel('emptyExp)]

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
    syntax Fexp ::= AExp | "(" Fexp ")" AExp

    syntax OptSemicolon ::= ";" | "" [onlyLabel, klabel('emptySemicolon)]
    syntax OptComma ::= "," | "" [onlyLabel, klabel('emptyComma)]

//    syntax OptWhereDecls ::= "where" Decls | ""

    syntax AExp ::= QVar
                  | GCon
                  | Literal
                  | "(" Exp ")"
                  | "(" ExpTuple ")"
                  | "[" ExpList "]"
                  | "[" Exp OptExpComma ".." OptExp "]"
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

    syntax LPat ::= AAPat
                  | "-" Integer
                  | "-" CusFloat
                  | GCon APatList

//    syntax APatList ::= APat | APat APatList
    syntax APatList ::= AAPat APats
    syntax APats ::= List{AAPat, ""}

    syntax AAPat ::= "(" APat ")" [bracket]

    syntax APat ::= Var
                  | Var "@" AAPat
                  | GCon
                  | QCon "{" FPats "}"
                  | Literal
//                  _
                  | "(" Pat ")"
                  | "(" PatTuple ")"
                  | "[" Pat "]"
                  | "[" PatList "]"
                  | "~" AAPat
    
    syntax FPats ::= List{FPat, ","}
    syntax FPat ::= QVar "=" Pat

    syntax GCon ::= "()"
                  | "[]"
                  | "(,{,})"
                  | QCon

    //syntax OpId ::= Token{[\'][0-9 a-z A-Z \_]*[\']}   [onlyLabel]
    syntax OptVarList ::= "(..)" | "(" VarList ")"
    syntax VarList ::= List{Var, ","}
    syntax OptQVarList ::= "(..)" | "(" QVarList ")"
    syntax QVarList ::= List{QVar, ","}

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
