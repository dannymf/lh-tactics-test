{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop19 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n xs = lengthListN (dropListN n xs) == subN (lengthListN xs) n

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> xs:ListN -> {prop n xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof n xs = induct n; induct xs
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \n -> \xs -> case n of
                         Data.Z -> case xs of
                                       Data.Nil -> trivial
                                       Data.Cons n_0 listN_1 -> trivial
                         Data.S n_0 -> case xs of
                                           Data.Nil -> trivial
                                           Data.Cons n_1 listN_2 -> proof n_0 listN_2
-- %tactic:end:proof
