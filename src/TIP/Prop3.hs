{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop3 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop3 @-}
prop3 :: N -> ListN -> ListN -> Bool
prop3 n xs ys = leqN (countListN n xs) (countListN n (concatListN xs ys))

return []

{-@ automatic-instances prop3_proof @-}
{-@
prop3_proof :: n:N -> xs:ListN -> ys:ListN -> {prop3 n xs ys}
@-}
-- [tactic|
-- prop3_proof :: N -> ListN -> ListN -> Proof
-- prop3_proof n xs ys =
--   use {leqN_addN (countListN n xs) (countListN n ys)};
--   use {addN_countListN_concatListN n xs ys}
-- |]
-- %tactic:begin:prop3_proof
prop3_proof :: N -> ListN -> ListN -> Proof
prop3_proof = \n -> \xs -> \ys -> leqN_addN (countListN n xs) (countListN n ys) &&& (addN_countListN_concatListN n xs ys &&& trivial)
-- %tactic:end:prop3_proof
-- %tactic:begin:prop3_proof
-- prop3_proof :: N -> ListN -> ListN -> Proof
-- prop3_proof = \n -> \xs -> \ys -> leqN_addN (countListN n xs) (countListN n ys) &&& (addN_countListN_concatListN n xs ys &&& trivial)
-- -- %tactic:end:prop3_proof

{-@ automatic-instances leqN_addN @-}
{-@ 
assume leqN_addN :: m:N -> n:N -> {leqN m (addN m n)}
@-}
leqN_addN :: N -> N -> Proof
leqN_addN m n = trivial

{-@ automatic-instances addN_countListN_concatListN @-}
{-@
assume addN_countListN_concatListN :: n:N -> xs:ListN -> ys:ListN -> {countListN n (concatListN xs ys) == addN (countListN n xs) (countListN n ys)}
@-}
addN_countListN_concatListN :: N -> ListN -> ListN -> Proof
addN_countListN_concatListN n xs ys = trivial

