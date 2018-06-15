module HASKELL-SYNTAX
    //syntax Digit ::= AscDigit
    //syntax AscDigit ::= Token{[0-9]}   [onlyLabel]
    syntax Literal ::= Integer
    syntax VarSym ::= Symbol
    syntax ConSym ::= Symbol
    syntax Symbol ::= AscSymbol
    syntax AscSymbol ::= Token{[\! \# \$ \% \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]}   [onlyLabel]
    syntax Integer ::= Token{[0-9]*}   [onlyLabel]

    syntax APat ::= Literal
    //syntax Exp ::= InfixExp
    syntax InfixExp ::= LExp QOp InfixExp
                      | LExp

    syntax LExp ::= "\" Apt_list "->" Exp
                  | "let" Decls "in" Exp
                  | "if" Exp OptComma "then" Exp OptComma "else" Exp
                  | "case" Exp "of" "{" Alts "}"
                  | "do" "{" Stmts "}"
                  | Fexp
    syntax Fexp ::= AExp | Fexp AExp

    syntax OptComma ::= ";" | "" [onlyLabel, klabel('emptyComma)]

    syntax Apt_list ::= List{Apt, ""}

    syntax AExp ::= Literal
                  | "(" InfixExp Qop ")"
                  | "(" Qop InfixExp ")"
endmodule
