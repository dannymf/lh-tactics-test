{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-con" @-}
-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple" @-}

module Map where

import Proof

import Prelude hiding (map, filter)

{-@ data Map k v = Node { key   :: k
                        , value :: v
                        , left  :: ML k v key
                        , right :: MR k v key }
                 | Tip
  @-}
data Map k v = Node { key   :: k
                        , value :: v
                        , left  :: Map k v
                        , right :: Map k v }
                 | Tip


{-@ type ML a b X = Map {v:a | v < X} b           @-}
{-@ type MR a b X = Map {v:a | X < v} b         @-}

-- {-@ reflect lambda @-}
-- lambda :: Eq k => (k -> Bool) -> k -> k -> Bool
-- lambda set k' k = if k == k' then True else set k

{-@ type Set k = (Int, k -> Bool) @-}
type Set k = (Int, k -> Bool)

{-@ reflect contains @-}
contains :: Eq k => Set k -> k -> Bool 
contains (_, keys) = keys

{-@ reflect addHelper @-}
addHelper keys k k' = if k == k' then True else keys k'

{-@ reflect add @-}
add :: Eq k => Set k -> k -> Set k
add set@(size, keys) k = if keys k then set else (size + 1, addHelper keys k)

{-@ reflect mergeHelper @-}
mergeHelper set1 set2 k = if set1 k then True else set2 k

{-@ reflect merge @-}
merge :: Eq k => Set k -> Set k -> Set k
merge (size1, set1) (size2, set2) = (size1 + size2, mergeHelper set1 set2)

{-@ reflect emptyHelper @-}
emptyHelper k = False

{-@ reflect empty @-}
empty :: Set k
empty = (0, emptyHelper)

{-@ reflect singletonHelper @-}
singletonHelper k k' = k == k'

{-@ reflect singleton @-}
singleton :: Eq k => k -> Set k
singleton k = (1, singletonHelper k)

{-@ reflect append @-}
append :: [a] -> [a] -> [a]
append [] bs = bs
append (a:as) bs = a : append as bs

{-@ reflect keys @-}
keys                :: (Ord k) => Map k v -> Set k
keys Map.Tip            = empty
keys (Node k _ l r) = ks `merge` kl `merge` kr
  where
    kl              = keys l
    kr              = keys r
    ks              = singleton k

{-@ reflect emp @-}
emp :: Map k v
emp     = Map.Tip

{-@ reflect set @-}
{-@ set :: (Ord k) => k:k -> v -> m:Map k v
                   -> n: Map k v @-}
set :: Ord k => k -> v -> Map k v -> Map k v
set k' v' (Node k v l r)
  | k' == k   = Node k v' l r
  | k' <  k   = set k' v' l
  | otherwise = set k' v' r
set k' v' Tip = Node k' v' Tip Tip

-- {-@ die :: {v:String | false} -> a  @-}
-- die :: String -> a
-- die = error
-- {-@ lemma_notMem :: key:k
--                  -> m:Map {k:k | k /= key} v
--                  -> {v:Bool | not (HasKey key m)}
--   @-}
-- lemma_notMem :: k -> Map k v -> Bool
-- lemma_notMem _   Tip            = True
-- lemma_notMem key (Node _ _ l r) = lemma_notMem key l &&
--                                   lemma_notMem key r

assert :: a -> b -> a
assert = const

{-@ reflect get @-}
{-@ get :: (Ord k) => k:k -> m:Map k v -> Maybe v @-}
get :: Ord k => k -> Map k v -> Maybe v
get k' (Node k v l r)
  | k' == k   = Just v
  | k' <  k   = get k' l
  | otherwise = get k' r
get k Tip     = Nothing

{-@ predicate HasKey K M = contains (keys M) K @-}

{-@ reflect member @-}
{-@ member :: (Ord k, Eq k) => k:k -> m:Map k v -> Bool @-}
member :: (Ord k, Eq k) => k -> Map k v -> Bool
member k' (Node k v l r)
  | k' == k   = True
  | k' <  k   = member k' l
  | otherwise = member k' r
member k Tip     = False

{-@ lemma1 :: Eq k => k:k -> m:{m : Map k v | m == Tip} -> {not (HasKey k m) && not (member k m)}@-}
lemma1 :: Eq k => k -> Map k v -> Proof
lemma1 _ Tip = trivial 
lemma1 _ (Node {}) = error "false"

{-@ lemma :: (Ord k) => key:k -> m:Map k v
                   -> {w:_ | w <=> member key m} @-}
lemma :: Ord k => k -> Map k v -> Bool
lemma k' (Node k _ l r)
  | k' == k   = True
  | k' <  k   = lemma k' l
  | otherwise = lemma k' r
lemma _ Tip     = False

{-@ reflect prop2 @-}
prop2 :: (Ord k, Eq v) => k -> v -> Map k v -> Bool
prop2 k v map = get k (set k v map) == Just v

-- IDEMPTOENCE
{-@ proof2 :: (Ord k, Eq v) => key:k -> val:v -> map:Map k v -> {prop2 key val map} @-}
proof2 :: (Ord k, Eq v) => k -> v -> Map k v -> Proof
proof2 k v Tip = trivial
proof2 k v (Node root _ l r) 
  | k == root = trivial 
  | k < root = proof2 k v l 
  | otherwise = proof2 k v r

{-@ reflect prop3 @-}
prop3 :: Ord k => k -> Bool
prop3 k = not (member k emp)

{-@ proof3 :: Ord a => n:a -> m:{m:Map a b | m == Tip} -> {prop3 n} @-}
proof3 :: Ord a => a -> Map a b -> Proof
proof3 n _ = trivial

-- {-@ reflect proof5 @-}
-- proof5 :: (Ord k, Eq v) => k -> k -> v -> Map k v -> Bool
-- proof5 key key' v' map = get key (set key' v' map) == get key map

-- {-@ prop5 :: key:k -> {key':k|key' /= key} -> v':v -> map:Map k v -> {proof5 key key' v' map} @-}
-- prop5 :: (Ord k, Eq v) => k -> k -> v -> Map k v -> Proof
-- prop5 k k' v' Tip = trivial
-- prop5 k k' v' map@(Node k'' v'' l r) 
--   | k == k' = trivial -- doesn't happen bc of refinement
--   | k' == k'' && v' == v'' = trivial
--   | not (member k map) = trivial
--   | k < k'' && k' < k'' = prop5 k k' v' l
--   | k > k'' && k' > k'' = prop5 k k' v' r
--   | k < k'' && k' == k'' = prop5 k k' v' l
--   | k > k'' && k' == k'' = prop5 k k' v' r
--   | k == k'' && k' == k'' = trivial
--   | k == k'' && k' < k'' = prop5 k k' v' l
--   | k == k'' && k' > k'' = prop5 k k' v' r
--   | otherwise = trivial

-- {-@ prop4 :: key:k -> map:{map:Map k v|member key map} -> {HasKey key map} @-}
-- prop4 :: Ord k => k -> Map k v -> Proof 
-- prop4 k Tip = trivial -- should fail
-- prop4 k (Node k' _ l r)
--   | k == k' = trivial 
--   | k < k' = prop4 k l
--   | otherwise = prop4 k r 

map :: Map Int Bool 
map = Node 5 True Tip Tip

{-@ filter' :: f:(k -> Bool) -> Map k v -> [({key:k | f key}, v)] @-}
filter' :: (k -> Bool) -> Map k v -> [(k,v)]
filter' f Tip = []
filter' f (Node k v l r) = if f k 
  then filter' f l `append` [(k, v)] `append` filter' f r 
  else filter' f l `append` filter' f r

