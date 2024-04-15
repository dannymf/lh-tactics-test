{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}

module TIP.FunctorList where

import Prelude hiding (fmap, id)

-- import ProofCombinators
import Tactic.Core.Quote
import TIP.FFF
import Proof

-- | Functor Laws :
-- | fmap-id fmap id == id
-- | fmap-distrib forall g h . fmap (g x h) == fmap g o fmap h

{-@ reflect fmap @-}
fmap :: (a -> b) -> L a -> L b
fmap _ N        = N 
fmap f (C x xs) = C (f x) (fmap f xs)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ 
fmap_id :: xs:L a -> { fmap id xs == id xs } 
@-}
-- [tactic|
-- fmap_id :: L a -> Proof
-- fmap_id xs = 
--   induct xs
-- |]
-- %tactic:begin:fmap_id
fmap_id :: L a -> Proof
fmap_id
  = \ xs
      -> case xs of
           N -> trivial
           C x_0 x_1 -> fmap_id x_1
-- %tactic:end:fmap_id
-- %tactic:begin:proof
-- 
-- %tactic:end:proof
-- %tactic:begin:proof
-- proof :: L a -> Proof
-- proof
--   = \ xs
--       -> case xs of
--            N -> trivial
--            C x_0 x_1 -> proof x_1
-- %tactic:end:proof

-- fmap_id :: L a -> Proof
-- fmap_id N
--   = trivial 
-- fmap_id (C x xs)
--   = fmap_id (xs)

-- | Distribution

-- %tactic:begin:fmap_distrib
{-@ 
fmap_distrib :: f:(a -> a) -> g:(a -> a) -> xs:L a
               -> { fmap (compose f g) xs == compose (fmap f) (fmap g) xs } 
@-}
-- [tactic|
-- fmap_distrib :: (a -> a) -> (a -> a) -> L a -> Proof
-- fmap_distrib f g xs =
--   induct xs
-- |]
-- %tactic:begin:fmap_distrib
fmap_distrib :: (a -> a) -> (a -> a) -> L a -> Proof
fmap_distrib
  = \ f
      -> \ g
           -> \ xs
                -> case xs of
                     N -> trivial
                     C x_0 x_1
                       -> (((fmap_distrib f) f) x_1
                             &&&
                               (((fmap_distrib f) g) x_1
                                  &&& (((fmap_distrib g) f) x_1 &&& ((fmap_distrib g) g) x_1)))
-- %tactic:end:fmap_distrib

-- fmap_distrib :: (a -> a) -> (a -> a) -> L a -> Proof
-- fmap_distrib
--   = \ f
--       -> \ g
--            -> \ xs
--                 -> case xs of
--                      N -> trivial
--                      C x_0 x_1 -> fmap_distrib f g x_1
-- %tactic:end:fmap_distrib

-- fmap_distrib :: (a -> a) -> (a -> a) -> L a -> Proof
-- fmap_distrib f g N
--   = trivial 
-- fmap_distrib f g (C x xs)
--   = fmap_distrib f g xs

