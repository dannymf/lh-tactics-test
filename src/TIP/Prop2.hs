{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop2 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop2 @-}
prop2 :: N -> ListN -> ListN -> Bool
prop2 n xs ys = addN (countListN n xs) (countListN n ys) == countListN n (concatListN xs ys)

return []

{-@ automatic-instances prop2_proof @-}
{-@
prop2_proof :: n:N -> xs:ListN -> ys:ListN -> {prop2 n xs ys}
@-}
-- [tactic|
-- prop2_proof :: N -> ListN -> ListN -> Proof
-- prop2_proof n xs ys = induct xs
-- |]
-- %tactic:begin:prop2_proof
prop2_proof :: N -> ListN -> ListN -> Proof
prop2_proof = \n -> \xs -> \ys -> case xs of
                                      Data.Nil -> trivial
                                      Data.Cons n_0 listN_1 -> prop2_proof n listN_1 ys
-- %tactic:end:prop2_proof
