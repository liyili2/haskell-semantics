module Test where
{import Lib
;data CusBool2 = True2 | False2
}
<NEXTMODULE>
module Lib where
{data CusBool = True | False
;data NewType a b = Newfoo a | Newbar b
;type CustomBool = Cusbool
;data Stack a = Empty  
             | MkStack a (Stack a)  
}
<NEXTMODULE>
module Test2 where
{import Test
}
