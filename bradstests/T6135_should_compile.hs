module Main where

{import GHC.Exts

;main :: IO ()
;main = do
  {(print) ((h) 3.0##)
  ;(print) g
  ;(print) 3.14159

};h :: Double# -> String
;h 3.14159 = if (tagToEnum#) (n ==## 3.0##) || (tagToEnum#) (n ==## 4.0##)
      then "First branch"
      else "Second branch"

;g :: String
;g = if (((fromInteger) 1 :: Integer) == 1)
    then "First branch"
    else "Second branch"
}
