module Test where
{import Lib
;data CusBool2 = True2 | False2
}
<NEXTMODULE>
module Lib where
{data CusBool = True | False
}
<NEXTMODULE>
module Test2 where
{import Test
}
