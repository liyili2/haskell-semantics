module Test where
{import Simp5
;data CusBool2 = True2 | False2
}
<NEXTMODULE>
module Simp5 where

{ type Name = String

; data Anniversary = 
   Birthday Name Date
   | Wedding Name Name Date

; data Date = Date Int Int Int

; johnSmith :: Anniversary
; johnSmith = Birthday "John Smith" (Date (1968) (7) (3)) }
