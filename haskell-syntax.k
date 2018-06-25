module HASKELL-SYNTAX
    //syntax Digit ::= AscDigit
    //syntax AscDigit ::= Token{[0-9]}   [onlyLabel]
    syntax Literal ::= Integer
//    syntax VarSym ::= Symbol
//    syntax ConSym ::= Symbol
//    syntax Symbol ::= AscSymbol
//    syntax AscSymbol ::= Token{[\! \# \$ \% \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]}   [onlyLabel]
    syntax Integer ::= Token{[0-9]*}   [onlyLabel]

//    syntax VarSym ::= Symbols //not true to haskell


//    syntax Symbols ::= List{Symbol, ""}

//    syntax VarSym ::= Token{~[\:] (~[\ ])*} [onlyLabel]
    syntax ConSym ::= Token{[\:] (~[\ ])*} [onlyLabel]

    syntax VarId ::= Token{[a-z][0-9 a-z A-Z \']*}   [onlyLabel]
    syntax ConId ::= Token{[A-Z][0-9 a-z A-Z \']*}   [onlyLabel]

//    syntax VarId ::= Token{[:]([\ ]~)*} [onlyLabel]
//    syntax ReservedId ::= "case" | "class" | "data" | "default" | "deriving" | "do" | "else" | "->" | "@" | "~" | "=>"

//    syntax ConSym ::= Token{"([;::)(]~)"} [onlyLabel]
    syntax ReservedOp ::= ".." | ":" | "::" | "=" | "\\" | "|" | "<-" | "->" | "@" | "~" | "=>"

    syntax Module ::= "module" ModId "where" Body
                    | "module" ModId Exports "where" Body
                    | Body

    syntax Exp ::= InfixExp
    syntax InfixExp ::= LExp QOp InfixExp
                      | LExp

    syntax LExp ::= "\\" Apats "->" Exp
//                  | "let" Decls "in" Exp
                  | "if" Exp OptComma "then" Exp OptComma "else" Exp
//                  | "case" Exp "of" "{" Alts "}"
//                  | "do" "{" Stmts "}"
//                  | Fexp
//    syntax Fexp ::= AExp | Fexp AExp

    syntax OptComma ::= ";" | "" [onlyLabel, klabel('emptyComma)]

    syntax Apats ::= List{Apat, ""}

    syntax AExp ::= Literal
                  | "(" InfixExp QOp ")"
                  | "(" QOp InfixExp ")"

    syntax Apat ::= Literal

    syntax OpId ::= Token{[\'][0-9 a-z A-Z \_]*[\']}   [onlyLabel]
    syntax QVarOp ::= OpId
    syntax QConOp ::= OpId
    syntax QOp ::= QVarOp | QConOp
endmodule
