{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop13 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect dropList @-}
dropList :: N -> List a -> List a
dropList _ LNil  = LNil
dropList Z as = as
dropList (S n) (LCons a as) = dropList n as

{-@ reflect prop @-}
prop n x xs = dropList (S n) (LCons x xs) == dropList n xs

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> x:N -> xs:List N -> {prop n x xs}
@-}
-- [tactic|
-- proof :: N -> N -> List N -> Proof
-- proof n x xs = induct xs
-- |]
-- %tactic:begin:proof
proof :: N -> N -> List N -> Proof
proof = \n -> \x -> \xs -> case xs of
                               Data.LNil -> trivial
                               Data.LCons x_0 x_1 -> trivial
-- %tactic:end:proof
