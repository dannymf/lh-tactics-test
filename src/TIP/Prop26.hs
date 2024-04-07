{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop26 where

import Data
import Proof
import Tactic.Core.Quote

-- prop26

{-@ reflect prop26 @-}
prop26 :: N -> ListN -> ListN -> Bool
prop26 x xs ys = 
  implies
    (elemListN x xs)
    (elemListN x (concatListN xs ys))

return []

{-@ automatic-instances prop26_proof @-}
{-@
prop26_proof :: x:N -> xs:ListN -> ys:ListN -> {prop26 x xs ys}
@-}
-- [tactic|
-- prop26_proof :: N -> ListN -> ListN -> Proof
-- prop26_proof x xs ys = induct xs
-- |]
-- %tactic:begin:prop26_proof
prop26_proof :: N -> ListN -> ListN -> Proof
prop26_proof = \x -> \xs -> \ys -> case xs of
                                       Data.Nil -> trivial
                                       Data.Cons n_0 listN_1 -> prop26_proof x listN_1 ys
-- %tactic:end:prop26_proof
