{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop33 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop :: (Ord a, Num a) => a -> a -> Bool
prop a b = (min a b == a) == (a <= b)

return []

{-@ automatic-instances proof @-}
{-@
proof :: a:N -> b:N -> {prop a b}
@-}
[tactic|
proof :: N -> N -> Proof
proof a b = induct a; induct b
|]

-- %tactic:begin:proof
-- proof :: N -> N -> Proof
-- proof = \a -> \b -> case a of
--                         Data.Z -> case b of
--                                       Data.Z -> trivial
--                                       Data.S n_0 -> trivial
--                         Data.S n_0 -> case b of
--                                           Data.Z -> trivial
--                                           Data.S n_1 -> proof n_0 n_1
-- %tactic:end:proof
