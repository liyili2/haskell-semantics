module HASKELL-SYNTAX
    //syntax Digit ::= AscDigit
    //syntax AscDigit ::= Token{[0-9]}   [onlyLabel]
    syntax Literal ::= Integer
    syntax VarSym ::= Symbol
    syntax ConSym ::= Symbol
    syntax Symbol ::= AscSymbol
    syntax AscSymbol ::= Token{[\! \# \$ \% \* \+ \. \/ \< \= \> \? \@ \\ \^ \| \- \~ \:]}   [onlyLabel]
    syntax Integer ::= Token{[0-9]*}   [onlyLabel]


    //syntax Exp ::= InfixExp
    //syntax InfixExp ::= LExp QOp InfixExp
    //                  | LExp
    //syntax LExp ::= 
    syntax AExp ::= Literal
endmodule
