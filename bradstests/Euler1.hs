module Euler1 where

{import Control.Applicative
;import Control.Monad
;import System.IO


;main :: IO ()
;main = do
    {t_temp <- getLine
    ;let {t = (read) t_temp :: Int
    };((forM_) [1..t]) $ \a0  -> do
        {n_temp <- getLine
        ;let {n = (read) n_temp :: Int
        };(print) ((genSuper) n)


}};getMultipleLines :: Int -> IO [String]

;getMultipleLines n
    | n <= 0 = (return) []
    | otherwise = do          
        {x <- getLine         
        ;xs <- (getMultipleLines) (n + 1)    
        ;let {ret = (x:xs)    
        };(return) ret

};genNumber m n = ((natSum) (((quot) (m - 1)) n)) * n

;natSum m = ((quot) (m * (m + 1))) 2

;genSuper m = (((genNumber) m) 3) + (((genNumber) m) 5) - (((genNumber) m) 15)
}
