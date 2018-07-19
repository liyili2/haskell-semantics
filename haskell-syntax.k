// Syntax from haskell 2010 Report
// https://www.haskell.org/onlinereport/haskell2010/haskellch10.html#x17-17500010

module HASKELL-SYNTAX
// Section 10.2
    //syntax Digit ::= AscDigit
    //syntax AscDigit ::= Token{[0-9]}   [onlyLabel]
/*
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
*/

    syntax Integer ::= Token{([0-9]+)
                | (([0][o]|[0][O])[0-7]+) 
                | (([0][x] | [0][X])[0-9 a-f A-F]+)}   [onlyLabel]

    syntax CusFloat ::= Token{([0-9]+[\.][0-9]+([e E][\+ \-]?[0-9]+)?)
                                 |([0-9]+[e E][\+ \-]?[0-9]+)} [onlyLabel]
    syntax CusChar ::= Token{[\'](~[\' \\ \&])[\']} [onlyLabel]
    syntax CusString ::= Token{[\'](~[\" \\]*)[\']} [onlyLabel]

    syntax VarId ::= Token{[a-z \_][a-z A-Z \_ 0-9 \']*} [onlyLabel]
    syntax ConId ::= Token{[A-Z][a-z A-Z \_ 0-9 \']*} [onlyLabel]
    syntax VarSym ::= Token{
   ([\! \# \$ \% \& \* \+ \/ \> \? \^][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]*)
  |[\-] | [\.]
  |([\.][\! \# \$ \% \& \* \+ \/ \< \= \> \? \@ \\ \^ \| \- \~ \:][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]*)
  | ([\-][\! \# \$ \% \& \* \+ \. \/ \< \= \? \@ \\ \^ \| \~ \:][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \~ \:]*)
  | ([\@][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]+)
  | ([\~][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]+)
  | ([\\][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]+)
  | ([\|][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]+)
  | ([\:][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]*)
  | ([\<][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \~ \:][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]*)
  | ([\=][\! \# \$ \% \& \* \+ \. \/ \< \= \? \@ \\ \^ \| \~ \:][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]*)} [onlyLabel]
    syntax ConSym ::= Token{[\:][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~][\! \# \$ \% \& \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]*}   [onlyLabel]

    syntax Literal ::= Integer | CusFloat | CusChar | CusString
    syntax TyCon ::= ConId
    syntax ModId ::= ConId | ConId "." ModId  [klabel('conModId)]
    syntax QTyCon ::= TyCon | ModId "." TyCon [klabel('conTyCon)]
    syntax QVarId ::= VarId | ModId "." VarId [klabel('qVarIdCon)]
    syntax QVarSym ::= VarSym | ModId "." VarSym  [klabel('qVarSymCon)]
    syntax QConSym ::= ConSym | ModId "." ConSym  [klabel('qConSymCon)]
/*    syntax QTyCls ::= QTyCon
    syntax TyCls ::= ConId
*/
    syntax TyVars ::= List{TyVar, ""} //used in SimpleType syntax
    syntax TyVar ::= VarId
    syntax TyVarTuple ::= TyVar "," TyVar      [klabel('twoTypeVarTuple)]
                        | TyVar "," TyVarTuple [klabel('typeVarTupleCon)]

    syntax Con ::= ConId | "(" ConSym ")"   [klabel('conSymBracket)]
    syntax Var ::= VarId | "(" VarSym ")"   [klabel('varSymBracket)]
    syntax QVar ::= QVarId | "(" QConSym ")" [klabel('qVarBracket)]
    syntax QCon ::= QTyCon | "(" GConSym ")"  [klabel('gConBracket)]

    syntax QConOp ::= GConSym | "`" QTyCon "`"    [klabel('qTyConQuote)]
    syntax QVarOp ::= QVarSym | "`" QVarId "`"    [klabel('qVarIdQuote)]
    syntax VarOp ::= VarSym   | "`" VarId "`"     [klabel('varIdQuote)]
    syntax ConOp ::= ConSym   | "`" ConId "`"     [klabel('conIdQuote)]

    syntax GConSym ::= ":" | QConSym
    syntax Vars ::= Var
                  | Var "," Vars  [klabel('varCon)]
    syntax VarsType ::= Vars "::" Type
    syntax Ops ::= Op
                 | Op "," Ops  [klabel('opCon)]
    syntax Fixity ::= "infixl" | "infixr" | "infix"
    syntax Op ::= VarOp | ConOp

    /* syntax QConId ::= ConId | ModId "." ConId */

    syntax QOp ::= QVarOp | QConOp

//  Section 10.5

    syntax Module ::= "module" ModId "where" Body   [klabel('module)]
                    | "module" ModId Exports "where" Body  [klabel('moduleExp)]
                    | Body

    syntax Body ::= "{" ImpDecls ";" TopDecls "}"
                  | "{" ImpDecls "}"
                  | "{" TopDecls "}"

    syntax ImpDecls ::= List{ImpDecl, ";"}

    syntax Exports ::= "(" ExportList ")" | "(" ExportList "," ")"

    syntax ExportList ::= List{Export, ","}

    syntax Export ::= QVar 
/*
                    | QTyCon OptCNameList
		                | QTyCls OptQVarList
                    | "module" ModId */

    syntax ImpDecl ::= /* "import" OptQualified ModId OptAsModId OptImpSpec
                     | */ "" [onlyLabel, klabel('emptyImpDecl)]
    //syntax OptQualified ::= "qualified" | "" [onlyLabel, klabel('emptyQualified)]
    //syntax OptAsModId ::= "as" ModId | "" [onlyLabel, klabel('emptyOptAsModId)]

    //syntax OptImpSpec ::= ImpSpec | "" [onlyLabel, klabel('emptyOptImpSpec)]

   // syntax ImpSpec ::= "(" ImportList OptComma ")"
//| "hiding" "(" ImportList OptComma ")"

    //syntax ImportList ::= List{Import, ","}

    /*syntax Import ::= Var
                    | TyCon OptCNameList
		                | TyCls OptVarList

    syntax OptCNameList ::= "(..)" | "(" CNameList ")" | "" [onlyLabel, klabel('emptyOptCNameList)]
    syntax CNameList ::= List{CName, ","}

    syntax CName ::= Var | Con
*/
    syntax TopDecls ::= List{TopDecl, ";"}

    syntax TopDecl ::= "type" SimpleType "=" Type
                     | "data" OptContext SimpleType OptConstrs OptDeriving
                     | "newtype" OptContext SimpleType "=" NewConstr OptDeriving
                     | "class" OptContext ConId TyVar OptCDecls
                              //place a check on this to check if the optContext is a SContext
                     | "instance" OptContext QTyCon Inst OptIDecls
                              //place a check on this to check if the optContext is a SContext
                     | "default" Types
                     | "foreign" FDecl
                     | Decl

    //optional decls
    syntax FDecl ::= "import" CallConv CusString Var "::" FType
                   | "import" CallConv Safety CusString Var "::" FType
                   | "export" CallConv Safety CusString Var "::" FType
    //fdecl needs to use special function in preprocessing
    // to get the actually elements from the impent and expent from the CusString
    //did string analysis
    
    syntax Safety ::= "unsafe" | "safe"
                   
    syntax CallConv ::= "ccall" | "stdcall" | "cplusplus" | "jvm" | "dotnet"
    syntax FType ::= FrType
                   | FaType "->" FType // unsure about this one syntax is ambiguous UNFINISHED
    
    syntax FrType ::= FaType
                    | "()"
                    
    syntax FaType ::= QTyCon ATypeList

    //define declaration.
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

    syntax GenDecl ::= VarsType
                     | Vars "::" Context "=>" Type
                     | Fixity Ops
                     | Fixity Integer Ops
                     | "" [onlyLabel, klabel('emptyGenDecl)]

    //three optional data type for the TopDecl data operator. 
    //deriving data type
    syntax OptDeriving ::= Deriving | "" [onlyLabel, klabel('emptyDeriving)]
    syntax Deriving ::= "deriving" DClass
                      | "deriving" "(" DClassList ")"
    syntax DClassList ::= List{DClass, ","}
    syntax DClass ::= QTyCon

    syntax FunLhs ::= Var APatList
                    | Pat VarOp Pat
                    | "(" FunLhs ")" APatList

    syntax Rhs ::= "=" Exp OptDecls
                 | GdRhs OptDecls

    syntax GdRhs ::= Guards "=" Exp
                   | Guards "=" Exp GdRhs
    syntax Guards ::= "|" GuardList
    syntax GuardList ::= Guard | Guard "," GuardList  [klabel('guardListCon)]
    syntax Guard ::= Pat "<-" InfixExp
                   | "let" Decls
                   | InfixExp

    //definition of exp
    syntax Exp ::= InfixExp "::" Type
                 | InfixExp "::" Context "=>" Type
                 | InfixExp

    syntax InfixExp ::= LExp QOp InfixExp
                      | "-" InfixExp   [klabel('minusInfix)]
                      | LExp

    syntax LExp ::= "\\" APatList "->" Exp
                  | "let" Decls "in" Exp
                  | "if" Exp OptSemicolon "then" Exp OptSemicolon "else" Exp
                  | "case" Exp "of" "{" Alts "}"
                  | "do" "{" Stmts "}"
                  | Fexp
    syntax Fexp ::= AExp | "(" Fexp ")" AExp

    syntax OptSemicolon ::= ";" | "" [onlyLabel, klabel('emptySemicolon)]
    syntax OptComma ::= "," | ""     [onlyLabel, klabel('emptyComma)]

//    syntax OptWhereDecls ::= "where" Decls | ""

    syntax AExp ::= QVar
                  | GCon
                  | Literal
                  | "(" Exp ")"
                  | "(" ExpTuple ")"
                  | "[" ExpList "]"
                  | "[" Exp OptExpComma ".." OptExp "]"
                  | "[" Exp "|" Quals "]"
                  | "(" InfixExp QOp ")"
                  | "(" QOp InfixExp ")" //qop cannot be - (minus) UNFINISHED
                           //place a check here to check if QOp is a minus
                  | QCon "{" FBindList "}"
                  | AExp "{" FBindList "}" //aexp cannot be qcon UNFINISHED
                          //first, does not understand the syntax, it is the Qcon {FBindlist}
                          //or QCon? Second, place a check in preprosssing.
                          //and also check the Fbindlist here must be at least one argument

    syntax OptExpComma ::= "," Exp | "" [onlyLabel, klabel('emptyExpComma)]
    syntax OptExp ::= Exp | "" [onlyLabel, klabel('emptyExp)]

    syntax ExpList ::= Exp | Exp "," ExpList
    syntax ExpTuple ::= Exp "," Exp [klabel('twoExpTuple)]
                      | Exp "," ExpTuple  [klabel('expTupleCon)]

    //constr datatypes
    syntax OptConstrs  ::= "=" Constrs | "" [onlyLabel, klabel('emptyConstrs)]
    syntax Constrs     ::= Constr | Constr "|" Constrs
    syntax Constr      ::= Con OptBangATypes [klabel('constrCon)] // (arity con  =  k, k ≥ 0) UNFINISHED
                         | SubConstr ConOp SubConstr
                         | Con "{" FieldDeclList "}"

    syntax NewConstr   ::= Con AType [klabel('newConstrCon)]
                         | Con "{" Var "::" Type "}"

    syntax SubConstr   ::= BType | "!" AType
    syntax FieldDeclList ::= List{FieldDecl, ","}
    syntax FieldDecl ::= VarsType
                       | Vars "::" "!" AType


    syntax OptBangATypes ::= List{OptBangAType, " "}
    syntax OptBangAType ::= OptBang AType
    syntax OptBang ::= "!" | "" [onlyLabel, klabel('emptyBang)]

    syntax OptContext ::= Context "=>" | "" [onlyLabel, klabel('emptyContext)]
    syntax Context ::= Class
                     | "(" Classes ")"

    syntax Classes ::= List{Class, ","}

    syntax SimpleClass ::= QTyCon TyVar  [klabel('classCon)]

    syntax Class       ::= SimpleClass
                         | QTyCon "(" TyVar ATypeList ")"
                              //a check in preprossing to check if the Atype list is empty
                              //it must have at least one item

    //define type and simple type
    syntax SimpleType  ::= TyCon TyVars  [klabel('simpleTypeCon)]
    syntax Type ::= BType
                  | BType "->" Type  [klabel('typeArrow)]
    syntax BType ::= AType
                   | BType AType [klabel('baTypeCon)]

    syntax ATypeList ::= List{AType, ""}

    syntax AType ::= GTyCon
                   | TyVar
                   | "(" TypeTuple ")"
                   | "[" Type "]" [klabel('tyList)]
                   | "(" Type ")"
    syntax TypeTuple ::= Type "," Type [right,klabel('twoTypeTuple)]
                       | Type "," TypeTuple [klabel('typeTupleCon)]
    syntax Types ::= List{Type, ","}

    syntax GConCommon ::= "()" | "[]" | "(,{,})"
    syntax GTyCon ::= QTyCon
                    | GConCommon
                    | "(->)"

    syntax GCon ::= GConCommon
                  | QCon

    //inst definition
    syntax Inst  ::= GTyCon
                   | "(" GTyCon TyVars ")" //TyVars must be distinct UNFINISHED
                   | "(" TyVarTuple ")" //TyVars must be distinct
                   | "[" TyVar "]"  [klabel('tyVarList)]
                   | "(" TyVar "->" TyVar ")" //TyVars must be distinct
    //pat definition
    syntax Pat ::= LPat QConOp Pat
                 | LPat

    syntax LPat ::= APat
                  | "-" Integer    [klabel('minusInt)]
                  | "-" CusFloat   [klabel('minusFloat)]
                  | GCon APatList  [klabel('lpatCon)]//arity gcon = k UNFINISHED

    syntax APatList ::= APat | APat APatList [klabel('apatCon)]

    syntax APat ::= Var
                  | Var "@" APat
                  | GCon
                  | QCon "{" FPats "}"
                  | Literal
                  | "_"
                  | "(" Pat ")"
                  | "(" PatTuple ")"
                  | "[" PatList "]"
                  | "~" APat

    syntax PatTuple ::= Pat "," Pat         [klabel('twoPatTuple)]
                      | Pat "," PatTuple    [klabel('patTupleCon)]
    syntax PatList ::= Pat
                      | Pat "," PatList     [klabel('patListCon)]

    syntax FPats ::= List{FPat, ","}
    syntax FPat ::= QVar "=" Pat

    //definition of quals
    syntax Quals ::= Qual | Qual "," Quals  [klabel('qualCon)]

    syntax Qual ::= Pat "<-" Exp
                  | "let" Decls
                  | Exp

    //definition of alts
    syntax Alts ::= Alt | Alt ";" Alts

    syntax Alt ::= Pat "->" Exp  [klabel('altArrow)]
                 | Pat "->" Exp "where" Decls
                 | "" [onlyLabel, klabel('emptyAlt)]

    //definition of stmts
    syntax Stmts ::= StmtList Exp OptSemicolon
    syntax StmtList ::= List{Stmt, ""}
    syntax Stmt ::= Exp ";"
                  | Pat "<-" Exp ";"
                  | "let" Decls ";"
                  | ";"

     //definition of fbind
    syntax FBindList ::= List{FBind, ","}
    syntax FBind ::= QVar "=" Exp


      /*

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
                     | "(" Classes ")"

    syntax Classes ::= List{Class, ","}

    syntax Class       ::= QTyCls TyVar
                         | QTyCls "(" TyVar ATypes ")"
    
    syntax OptSContext ::= SContext "=>" | "" [onlyLabel, klabel('emptySContext)]
    syntax SContext ::= SimpleClass
                      | "(" SimpleClassList ")"
    
    syntax SimpleClassList ::= List{SimpleClass, ","}

    syntax SimpleClass ::= QTyCls TyVar

    syntax SimpleType  ::= TyCon TyVars
    syntax OptConstrs  ::= "=" Constrs | "" [onlyLabel, klabel('emptyConstrs)]
    syntax Constrs     ::= Constr | Constr "|" Constrs
    syntax SubConstr   ::= BType | "!" AType
    syntax Constr      ::= Con OptBangATypes // (arity con  =  k, k ≥ 0) UNFINISHED
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
                         | "(" GTyCon TyVars ")" //TyVars must be distinct UNFINISHED
                         | "(" TyVarTuple ")" //TyVars must be distinct
                         | "[" TyVar "]"
                         | "(" TyVar "->" TyVar ")" //TyVars must be distinct
    
    syntax FDecl ::= "import" CallConv Impent Var "::" FType
                   | "import" CallConv Safety Impent Var "::" FType
                   | "export" CallConv Safety Expent Var "::" FType
                   
    syntax CallConv ::= "ccall" | "stdcall" | "cplusplus" | "jvm" | "dotnet"
    
    syntax Impent ::= "IMPENT" // temporary UNFINISHED
    syntax Expent ::= "EXPENT" // temporary
    
    syntax Safety ::= "unsafe" | "safe"
    
    syntax FType ::= FrType
                   | FaType "->" FType // unsure about this one syntax is ambiguous UNFINISHED
    
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
                  | "[" Exp "|" Quals "]"
                  | "(" InfixExp QOp ")"
                  | "(" QOp InfixExp ")" //qop cannot be - (minus) UNFINISHED
                  | QCon "{" FBindList "}"
                  | AExp "{" FBinds "}" //aexp cannot be qcon UNFINISHED

    syntax Quals ::= Qual | Qual "," Quals

    syntax Qual ::= Pat "<-" Exp
                  | "let" Decls
                  | Exp

    syntax Alts ::= Alt | Alt ";" Alts

    syntax Alt ::= Pat "->" Exp
                 | Pat "->" Exp "where" Decls
                 | "" [onlyLabel, klabel('emptyAlt)]
                 
    syntax Stmts ::= StmtList Exp OptSemicolon
    syntax StmtList ::= List{Stmt, ""}
    syntax Stmt ::= Exp ";"
                  | Pat "<-" Exp ";"
                  | "let" Decls ";"
                  | ";"

    syntax FBinds ::= FBind | FBind "," FBinds
    syntax FBindList ::= List{FBind, ","}
    syntax FBind ::= QVar "=" Exp

    syntax PatTuple ::= Pat "," Pat | Pat "," PatTuple
    syntax PatList ::= Pat | Pat "," PatList

    syntax Pat ::= LPat QConOp Pat
                 | LPat

    syntax LPat ::= AAPat
                  | "-" Integer
                  | "-" CusFloat
                  | GCon APatList //arity gcon = k UNFINISHED

//    syntax APatList ::= APat | APat APatList
    syntax APatList ::= AAPat APats
    syntax APats ::= List{AAPat, ""}

    syntax AAPat ::= "(" APat ")" [bracket]

    syntax APat ::= Var
                  | Var "@" AAPat
                  | GCon
                  | QCon "{" FPats "}"
                  | Literal
                  | "_"
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
    syntax GConSym ::= ":" | QConSym*/
configuration <k> getPreModule($PGM:Module) </k>
    syntax KItem ::= getPreModule (K) [function]
    syntax KItem ::= preModule(K)
    rule getPreModule('module(I:ModId,, J:Body)) => preModule(J)

endmodule
