module Test where
{import Simp5
;data CusBool2 = True3 | False3
}
<NEXTMODULE>
module Simp5 where
{data CusBool = True2 | False2
;z y = let {x = Simp5.True2} in \y -> x}
