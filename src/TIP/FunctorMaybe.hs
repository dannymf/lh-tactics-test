{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes #-}

module TIP.FunctorMaybe where

import Prelude hiding (fmap, id)

import Tactic.Core.Quote
import Proof

-- | Functor Laws :
-- | fmap-id fmap id == id
-- | fmap-distrib forall g h . fmap (g o h) == fmap g o fmap h


{-@ reflect fmap @-}
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap f Nothing  = Nothing
fmap f (Just x) = Just (f x)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


-- CHANGE TO PERMIT DESTRUCT AS WELL
{-@ 
fmap_id :: xs:Maybe a -> { fmap id xs == id xs } 
@-}
-- [tactic|
-- fmap_id :: Maybe a -> Proof
-- fmap_id xs  = destruct xs 
-- |]
-- %tactic:begin:fmap_id
fmap_id :: Maybe a -> Proof
fmap_id
  = \ xs
      -> case xs of
           Nothing -> trivial
           Just x_0 -> trivial
-- %tactic:end:fmap_id

-- | Distribution


{-@ fmap_distrib :: f:(b -> c) -> g:(a -> b) -> xs:Maybe a
               -> { fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
-- [tactic|
-- fmap_distrib :: (b -> c) -> (a -> b) -> Maybe a -> Proof
-- fmap_distrib f g xs = induct xs 
-- |]
-- %tactic:begin:fmap_distrib
fmap_distrib :: (b -> c) -> (a -> b) -> Maybe a -> Proof
fmap_distrib
  = \ f
      -> \ g
           -> \ xs
                -> case xs of
                     Nothing -> trivial
                     Just x_0 -> trivial
-- %tactic:end:fmap_distrib

-- data Maybe a = Nothing | Just a
-- {-@ data Maybe a = Nothing | Just a @-}
