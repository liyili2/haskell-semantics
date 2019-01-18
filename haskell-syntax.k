// Syntax from haskell 2010 Report
// https://www.haskell.org/onlinereport/haskell2010/haskellch10.html#x17-17500010

module HASKELL-SYNTAX

    syntax Integer ::= Token{([0-9]+)
                | (([0][o]|[0][O])[0-7]+) 
                | (([0][x] | [0][X])[0-9a-fA-F]+)}   [onlyLabel]

    syntax CusFloat ::= Token{([0-9]+[\.][0-9]+([e E][\+\-]?[0-9]+)?)
                                 |([0-9]+[e E][\+\-]?[0-9]+)} [onlyLabel]
    syntax CusChar ::= Token{[\'](~[\'\\\&])[\']} [onlyLabel]
    syntax CusString ::= Token{[\"](~[\"\\]*)[\"]} [onlyLabel]

    syntax VarId ::= Token{[a-z\_][a-z A-Z\_0-9\']*} [onlyLabel] | "size" [onlyLabel]
    syntax ConId ::= Token{[A-Z][a-zA-Z \_0-9\']*} [onlyLabel]
                   | "Integer"        [prefer]
                   | "Double"         [prefer]
                   | "Prelude"        [prefer]
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
                    | "-" [klabel('minusCon), onlyLabel, prefer]

    syntax IntFloat ::= "(" Integer ")"  [bracket] //NOT OFFICIAL SYNTAX
                      | "(" CusFloat ")" [bracket]

    syntax Literal ::= IntFloat | CusChar | CusString
    syntax TyCon ::= ConId
    syntax ModId ::= ConId | ConId "." ModId  [klabel('conModId)]
    syntax QTyCon ::= TyCon | ModId "." TyCon [klabel('conTyCon)]
    syntax QVarId ::= VarId | ModId "." VarId [klabel('qVarIdCon)]
    syntax QVarSym ::= VarSym | ModId "." VarSym  [klabel('qVarSymCon)]
    syntax QConSym ::= ConSym | ModId "." ConSym  [klabel('qConSymCon)]
/*    syntax QTyCls ::= QTyCon
    syntax TyCls ::= ConId
*/
    syntax TyVars ::= List{TyVar, ""} [klabel('typeVars)] //used in SimpleType syntax
    syntax TyVar ::= VarId
    syntax TyVarTuple ::= TyVar "," TyVar      [klabel('twoTypeVarTuple)]
                        | TyVar "," TyVarTuple [klabel('typeVarTupleCon)]

    syntax Con ::= ConId | "(" ConSym ")"   [klabel('conSymBracket), onlyLabel]
    syntax Var ::= VarId | "(" VarSym ")"   [klabel('varSymBracket), onlyLabel]
    syntax QVar ::= QVarId | "(" QConSym ")" [klabel('qVarBracket), onlyLabel]
    syntax QCon ::= QTyCon | "(" GConSym ")"  [klabel('gConBracket), onlyLabel]

    syntax QConOp ::= GConSym | "`" QTyCon "`"    [klabel('qTyConQuote), onlyLabel]
    syntax QVarOp ::= QVarSym | "`" QVarId "`"    [klabel('qVarIdQuote), onlyLabel]
    syntax VarOp ::= VarSym   | "`" VarId "`"     [klabel('varIdQuote), onlyLabel]
    syntax ConOp ::= ConSym   | "`" ConId "`"     [klabel('conIdQuote), onlyLabel]

    syntax GConSym ::= ":" [klabel('colon), onlyLabel] | QConSym
    syntax Vars ::= Var
                  | Var "," Vars  [klabel('varCon)]
    syntax VarsType ::= Vars "::" Type  [klabel('varAssign)]
    syntax Ops ::= Op
                 | Op "," Ops  [klabel('opCon)]
    syntax Fixity ::= "infixl" | "infixr" | "infix"
    syntax Op ::= VarOp | ConOp
    syntax CQName ::= Var | Con | QVar

    /* syntax QConId ::= ConId | ModId "." ConId */

    syntax QOp ::= QVarOp | QConOp

//  CUSTOM SYNTAX NOT PART OF OFFICAL HASKELL

    syntax ModuleList ::= Module [klabel('modListSingle)]
                        | Module "<NEXTMODULE>" ModuleList [klabel('modList)]

//  Section 10.5

    syntax ModuleName ::= "module" ModId [klabel('moduleName)]

    syntax Module ::= ModuleName "where" Body          [klabel('module)]
                    | ModuleName Exports "where" Body  [klabel('moduleExp)]
                    | Body                             [klabel('moduleBody)]

    syntax Body ::= "{" ImpDecls ";" TopDecls "}" [klabel('bodyimpandtop)]
                  | "{" ImpDecls "}" [klabel('bodyimpdecls)]
                  | "{" TopDecls "}" [klabel('bodytopdecls)]

    syntax ImpDecls ::= List{ImpDecl, ";"} [klabel('impDecls)]

    syntax Exports ::= "(" ExportList OptComma ")"
    syntax ExportList ::= List{Export, ","}

    syntax Export ::= QVar 
                    | QTyCon OptCQList 
                    | ModuleName

    //optional cname list
    syntax OptCQList ::= "(..)"
                       | "(" CQList ")"   [klabel('cqListBracket)]
                          //Liyi: a check needs to place in preprocessing to check
                          //if the CQList is a cname list or a qvar list.
                       | "" [onlyLabel, klabel('emptyOptCNameList)]
    syntax CQList ::= List{CQName, ","}

    syntax ImpDecl ::= "import" OptQualified ModId OptAsModId OptImpSpec [klabel('impDecl)]
                     | "" [onlyLabel, klabel('emptyImpDecl)]
    syntax OptQualified ::= "qualified"
                          | ""  [onlyLabel, klabel('emptyQualified)]
    syntax OptAsModId ::= "as" ModId
                        | ""    [onlyLabel, klabel('emptyOptAsModId)]

    syntax OptImpSpec ::= ImpSpec
                        | ""    [onlyLabel, klabel('emptyOptImpSpec)]

    syntax ImpSpecKey ::= "(" ImportList OptComma ")"
    syntax ImpSpec ::= ImpSpecKey
                     | "hiding" ImpSpecKey

    syntax ImportList ::= List{Import, ","}

    syntax Import ::= Var
                    | TyCon CQList
                     //Liyi: a check to check if the import cqlist elements are within cnames
                     //or are within vars. in the preprossing.

    //definition of top decls
    syntax TopDecls ::= List{TopDecl, ";"} [klabel('topdeclslist)]

    syntax TopDecl ::= Decl
                     > "type" SimpleType "=" Type [klabel('atype)]
                     | "data" OptContext SimpleType OptConstrs OptDeriving  [klabel('data)]
                     | "newtype" OptContext SimpleType "=" NewConstr OptDeriving [klabel('newtype)]
                     | "class" OptContext ConId TyVar OptCDecls [klabel('class)]
                              //Liyi: place a check on this to check if the optContext is a SContext
                     | "instance" OptContext QTyCon Inst OptIDecls [klabel('instance)]
                              //Liyi: place a check on this to check if the optContext is a SContext
                     | "default" Types [klabel('default)]
                     | "foreign" FDecl [klabel('foreign)]

    //optional decls
    syntax FDecl ::= "import" CallConv CusString Var "::" FType
                   | "import" CallConv Safety CusString Var "::" FType
                   | "export" CallConv Safety CusString Var "::" FType
    //Liyi: fdecl needs to use special function in preprocessing
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
    syntax OptDecls ::= "where" Decls [onlyLabel, klabel('whereDecls)]
                      | "" [onlyLabel, klabel('emptyOptDecls)]
    syntax Decls ::= "{" DeclsList "}" [klabel('decls)]
    syntax DeclsList ::= List{Decl, ";"} [klabel('declsCon)]

    syntax Decl ::= GenDecl
                  | FunLhs Rhs [klabel('declFunLhsRhs), onlyLabel]
                  | Pat Rhs [klabel('declPatRhs), onlyLabel]

    syntax OptCDecls ::= "where" CDecls [klabel('cdeclWhere), onlyLabel]
                       | "" [onlyLabel, klabel('emptyOptCDecls)]
    syntax CDecls ::= "{" CDeclsList "}" [klabel('cdeclBracket), onlyLabel]
    syntax CDeclsList ::= List{CDecl, ";"}   [klabel('cdeclCon)]

    syntax CDecl ::= GenDecl
                   | FunLhs Rhs  [klabel('cdeclFunLhsRhs), onlyLabel]
                   | Var Rhs [klabel('cdeclVarRhs), onlyLabel]

    syntax OptIDecls ::= "where" IDecls  [klabel('ideclWhere), onlyLabel]
                       | "" [onlyLabel, klabel('emptyOptIDecls)]
    syntax IDecls ::= "{" IDeclsList "}"   [klabel('ideclBracket), onlyLabel]
    syntax IDeclsList ::= List{IDecl, ";"} [klabel('ideclsCon)]

    syntax IDecl ::= FunLhs Rhs [klabel('ideclFunLhsRhs), onlyLabel]
                   | Var Rhs [klabel('ideclVarRhs), onlyLabel]
                   | "" [onlyLabel, klabel('emptyIDecl)]

    syntax GenDecl ::= VarsType
                     | Vars "::" Context "=>" Type   [klabel('genAssignContext)]
                     | Fixity Ops
                     | Fixity Integer Ops
                     | "" [onlyLabel, klabel('emptyGenDecl)]

    //three optional data type for the TopDecl data operator. 
    //deriving data type
    syntax OptDeriving ::= Deriving | "" [onlyLabel, klabel('emptyDeriving)]
    syntax Deriving ::= "deriving" DClass
                      | "deriving" "(" DClassList ")"
    syntax DClassList ::= List{DClass, ","}  [klabel('dclassCon)]
    syntax DClass ::= QTyCon

    syntax FunLhs ::= Var APatList             [klabel('normalLhs), onlyLabel]
                    | Pat VarOp Pat            [klabel('binLhs), onlyLabel]
                    | "(" FunLhs ")" APatList  [klabel('groupLhs), onlyLabel]

    syntax Rhs ::= "=" Exp OptDecls  [klabel('normalRhs), onlyLabel]
                 | GdRhs OptDecls    [klabel('guardRhs), onlyLabel]

    syntax GdRhs ::= Guards "=" Exp        [klabel('guardSingle), onlyLabel]
                   | Guards "=" Exp GdRhs  [klabel('guardCon), onlyLabel]
    syntax Guards ::= "|" GuardList        [klabel('startGuardCons), onlyLabel]
    syntax GuardList ::= Guard | Guard "," GuardList  [klabel('guardListCon), onlyLabel]
    syntax Guard ::= Pat "<-" InfixExp     [klabel('guardAssign), onlyLabel]
                   | "let" Decls           [klabel('guardLet), onlyLabel]
                   | InfixExp

    //definition of exp
    syntax Exp ::= InfixExp
                 > InfixExp "::" Type  [klabel('expAssign)]
                 | InfixExp "::" Context "=>" Type  [klabel('expAssignContext)]

    syntax InfixExp ::= LExp
                      > "-" InfixExp   [klabel('minusInfix), onlyLabel]
                      > LExp QOp InfixExp  [klabel('binInfixExp), onlyLabel]

    syntax LExp ::= AExp
                  > "\\" APatList "->" Exp  [klabel('lambdaExp), onlyLabel]
                  | "let" Decls "in" Exp    [klabel('letInExp), onlyLabel]
                  | "if" Exp OptSemicolon "then" Exp OptSemicolon "else" Exp
                                            [klabel('ifElseExp), onlyLabel]
                  | "case" Exp "of" "{" Alts "}"    [klabel('caseExp), onlyLabel]
                  | "do" "{" Stmts "}"              [klabel('doExp), onlyLabel]

    syntax OptSemicolon ::= ";" | "" [onlyLabel, klabel('emptySemicolon)]
    syntax OptComma ::= "," | ""     [onlyLabel, klabel('emptyComma)]

//    syntax OptWhereDecls ::= "where" Decls | ""

    syntax AExp ::= QVar
                  | GCon
                  | Literal
                  > AExp AExp [left, klabel('funApp), onlyLabel]
                  > AExp "{" FBindList "}" [klabel('recordExp), onlyLabel]
                          //aexp cannot be qcon UNFINISHED
                          //Liyi: first, does not understand the syntax, it is the Qcon {FBindlist}
                          //or QCon? Second, place a check in preprosssing.
                          //and also check the Fbindlist here must be at least one argument
                  > "(" Exp ")"             [bracket]
                  | "(" ExpTuple ")"    [klabel('expTuple), onlyLabel]
                  | "[" ExpList "]"     [klabel('expList), onlyLabel]
                  | "[" Exp OptExpComma ".." OptExp "]"  [klabel('expSeq), onlyLabel]
                  | "[" Exp "|" Quals "]"    [klabel('listComprehension), onlyLabel]
                  | "(" InfixExp QOp ")"     [klabel('leftSection), onlyLabel]
                  | "(" QOp InfixExp ")"     [klabel('rightSection), onlyLabel] 
                            //qop cannot be - (minus) UNFINISHED
                           //Liyi: place a check here to check if QOp is a minus

    syntax OptExpComma ::= "," Exp [onlyLabel, klabel('dotExp)]
                         | "" [onlyLabel, klabel('emptyExpComma)]
    syntax OptExp ::= Exp | "" [onlyLabel, klabel('emptyExp)]

    syntax ExpList ::= Exp | Exp "," ExpList  [right, klabel('expListCon), onlyLabel]
    syntax ExpTuple ::= Exp "," Exp           [right, klabel('twoExpTuple), onlyLabel]
                      | Exp "," ExpTuple      [right, klabel('expTupleCon), onlyLabel]

    //constr datatypes
    syntax OptConstrs  ::= "=" Constrs [klabel('nonemptyConstrs)] | "" [onlyLabel, klabel('emptyConstrs)]
    syntax Constrs     ::= Constr | Constr "|" Constrs [klabel('multConstr)]
    syntax Constr      ::= Con OptBangATypes [klabel('constrCon)] // (arity con  =  k, k ≥ 0) UNFINISHED
                         | SubConstr ConOp SubConstr
                         | Con "{" FieldDeclList "}"

    syntax NewConstr   ::= Con AType [klabel('newConstrCon), onlyLabel]
                         | Con "{" Var "::" Type "}"  [klabel('newConField), onlyLabel]

    syntax SubConstr   ::= BType | "!" AType
    syntax FieldDeclList ::= List{FieldDecl, ","}  [klabel('fieldCon)]
    syntax FieldDecl ::= VarsType
                       | Vars "::" "!" AType


    syntax OptBangATypes ::= List{OptBangAType, " "} [klabel('optBangATypes)]
    syntax OptBangAType ::= OptBang AType [klabel('optBangAType), onlyLabel]
    syntax OptBang ::= "!" | "" [onlyLabel, klabel('emptyBang)]

    syntax OptContext ::= Context "=>" | "" [onlyLabel, klabel('emptyContext)]
    syntax Context ::= Class
                     | "(" Classes ")" [klabel('contextClass)]

    syntax Classes ::= List{Class, ","}      [klabel('classesCon)]

    syntax SimpleClass ::= QTyCon TyVar  [klabel('classCon), onlyLabel]

    syntax Class ::= SimpleClass
                   | QTyCon "(" TyVar ATypeList ")" [klabel('multiClass)]
                              //Liyi: a check in preprossing to check if the Atype list is empty
                              //it must have at least one item

    //define type and simple type
    syntax SimpleType ::= TyCon TyVars  [klabel('simpleTypeCon), onlyLabel]
    syntax Type ::= BType
                  | BType "->" Type  [klabel('typeArrow)]
    syntax BType ::= AType
                   | AType BType [klabel('baTypeCon), onlyLabel]

    syntax ATypeList ::= List{AType, ""} [klabel('atypeList)]

    syntax AType ::= GTyCon                     
                   | TyVar                      
                   | "(" TypeTuple ")"          [klabel('tupleCover)]
                   | "[" Type "]"               [klabel('tyList)]
                   | "(" Type ")"               [klabel('group)]           
    syntax TypeTuple ::= Type "," Type          [right,klabel('twoTypeTuple), onlyLabel]
                       | Type "," TypeTuple     [klabel('typeTupleCon), onlyLabel]
    syntax Types ::= List{Type, ","}            [klabel('typeCon)]

    syntax GConCommas ::= ","            [klabel('dotInTuple)]
                       | "," GConCommas  [klabel('dotCon)]
    syntax GConCommon ::= "()" [klabel('unitType)] | "[]"
                        | "(" GConCommas ")"  [klabel('tupleFun)]//was incorrect syntax
    syntax GTyCon ::= QTyCon
                    | GConCommon
                    | "(->)"

    syntax GCon ::= GConCommon
                  | QCon

    //inst definition
    syntax Inst ::= GTyCon
                  | "(" GTyCon TyVars ")" [klabel('instAppType), onlyLabel]
                    //TyVars must be distinct UNFINISHED
                  | "(" TyVarTuple ")" [klabel('instTupleCover), onlyLabel]
                      //TyVars must be distinct
                  | "[" TyVar "]"  [klabel('tyVarList), onlyLabel]
                  | "(" TyVar "->" TyVar ")" [klabel('typeVarFun), onlyLabel]
                     //TyVars must be distinct
    //pat definition
    syntax Pat ::= LPat QConOp Pat  [klabel('binPattern), onlyLabel]
                 | LPat

    syntax LPat ::= APat
                  | "-" IntFloat    [klabel('minusPat)]
                  | GCon APatList  [klabel('lpatCon), onlyLabel]//arity gcon = k UNFINISHED

    syntax APatList ::= APat | APat APatList [klabel('apatCon), onlyLabel]

    syntax APat ::= Var
                  | Var "@" APat
                  | GCon
                  | QCon "{" FPats "}"  [klabel('recordPat), onlyLabel]
                  | Literal [klabel('apatLiteral)]
                  | "_"     [klabel('underscore), onlyLabel]
                  | "(" Pat ")"   [bracket]
                  | "(" PatTuple ")"  [klabel('patTuple), onlyLabel]
                  | "[" PatList "]"   [klabel('patList), onlyLabel]
                  | "~" APat  [klabel('irrefutablePat)]

    syntax PatTuple ::= Pat "," Pat         [klabel('twoPatTuple)]
                      | Pat "," PatTuple    [klabel('patTupleCon)]
    syntax PatList ::= Pat
                      | Pat "," PatList     [klabel('patListCon)]

    syntax FPats ::= List{FPat, ","}  [klabel('fpatCon)]
    syntax FPat ::= QVar "=" Pat      [klabel('recordConAssign), onlyLabel]

    //definition of quals
    syntax Quals ::= Qual | Qual "," Quals  [klabel('qualCon)]

    syntax Qual ::= Pat "<-" Exp  [klabel('qualAssign), onlyLabel]
                  | "let" Decls   [klabel('qualLet), onlyLabel]
                  | Exp

    //definition of alts
    syntax Alts ::= Alt
                  | Alt ";" Alts [klabel('altCon), onlyLabel]

    syntax Alt ::= Pat "->" Exp  [klabel('altArrow), onlyLabel]
                 | Pat "->" Exp "where" Decls
                 | "" [onlyLabel, klabel('emptyAlt), onlyLabel]

    //definition of stmts
    syntax Stmts ::= StmtList Exp OptSemicolon  [klabel('stmtMain), onlyLabel]
    syntax StmtList ::= List{Stmt, ""}          [klabel('stmtCon)]
    syntax Stmt ::= Exp ";"           [klabel('expStmt), onlyLabel]
                  | Pat "<-" Exp ";"  [klabel('patExpStmt), onlyLabel]
                  | "let" Decls ";"   [klabel('letStmt), onlyLabel]
                  | ";"               [klabel('emptyStmt), onlyLabel]

     //definition of fbind
    syntax FBindList ::= List{FBind, ","}  [klabel('fbCon)]
    syntax FBind ::= QVar "=" Exp   [klabel('fbConAssign), onlyLabel]

endmodule
