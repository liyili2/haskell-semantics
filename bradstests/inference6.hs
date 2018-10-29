module Test where
{import Simp5
;data CusBool2 = True3 | False3
}
<NEXTMODULE>
module Simp5 where
{data CusBool = True2 | False2
;z h = \y -> (let {f = \x -> x y} in (f (\x -> Simp5.True2)))}
