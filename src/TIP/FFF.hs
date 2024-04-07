module TIP.FFF where

data L a = N | C a (L a)
{-@ data L [llen] a = N | C {lhd :: a, ltl :: L a }  @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs