{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}

{-|
This module implements data types and monadic operations to build, modify and query disjoint int sets in a monadic way
(such as through ST). Keep in mind that that this module assumes your int set is 0 based, i.e has no negatives, and is
contiguous from zero. Storage space required is two machine integers per int in the set.

For more information see the <https://en.wikipedia.org/wiki/Disjoint_sets Disjoint Sets> article on wikipedia, noting that
this modules only deals with disjoint sets with elements of type 'Int', in particular contiguous and starting at 0.
-}
module Data.DisjointSet.Int.Monadic (
  DisjointIntSetMonadic(DisjointIntSetMonadicFixed, DisjointIntSetMonadicVariable),
  DisjointIntSet(DisjointIntSet),
  newDisjointIntSetFixed,
  newDisjointIntSetVariable,
  union,
  find,
  count,
  findAndCount,
  numSets,
  size,
  nextInSet,
  setToList,
  unsafeFreeze,
  freeze,
  runDisjointIntSet
  )
where

import qualified Data.DisjointSet.Int.Monadic.Impl as Impl

import Data.DisjointSet.Int.Monadic.Impl (MVectorT)

import Prelude (
  Int, (+), (-), (*), negate,
  ($),
  return,
  Monad, (>>),
  Bool(True, False),
  (<), (>=), (==), (>), (/=), (<=),
  mapM_,
  max,
  pred, succ,
  undefined,
  minBound,
  div,
  Maybe,
  Foldable,
  (.),
  (>>=),
  (<$>),
  Show
  )

import Data.Vector.Unboxed.Mutable (
  MVector,
  new,
  unsafeRead, unsafeWrite,
  unsafeGrow
  )

import qualified Data.Vector.Unboxed
import qualified Data.Vector.Unboxed.Mutable

import Data.Vector.Unboxed (
  Vector
  )

import Control.Monad.Primitive (
  PrimState, PrimMonad
  )

import Control.Monad.ST (
  ST, runST
  )

import Control.Monad.Ref (
  MonadRef, Ref, newRef,
  readRef, writeRef, modifyRef'
  )

import Control.Monad (
  when
  )

data Size = Variable | Fixed

{-|
There are two sorts of monadic int sets, one of fixed size and one of variable size. The variable sized one automatically expands
but is presumably a bit slower due to the extra indirection and time taken for copies when resizing.

Note that when the variable sized int set expands, it expands to at least twice it's current size, so you won't get @O(n^2)@ behaviour due to
frequent resizings.

Whilst the following is implementation details, it might be interesting to know. Each int set has two vectors of Ints. The first either contains a
positive or negative number, if it's positive, it's a pointer which eventually points to the representative set. However, if it's negative,
this element is the representative set, and the absolute value of it is the number of elements in the set.

The second set maintains a circular linked lists for each set. This allows one to iterate though elements of a set quickly.

For more information on the algorithms, the <https://en.wikipedia.org/wiki/Disjoint-set_data_structure disjoint set data structure page on Wikipedia>
is a good start.
-}
data DisjointIntSetMonadic m where
  DisjointIntSetMonadicFixed :: (Monad m) => (MVectorT m) -> (MVectorT m) -> (Ref m Int) -> Int -> DisjointIntSetMonadic m
  DisjointIntSetMonadicVariable :: (Monad m) => (Ref m (MVectorT m)) -> (Ref m (MVectorT m)) -> (Ref m Int) -> (Ref m Int) -> DisjointIntSetMonadic m

{-|
This is the non-monadic disjoint int set. It can be created by using the monadic operations and then calling
'freeze', 'unsafeFreeze' or 'runDisjointIntSet' as appropriate.

Alternatively 'Data.DisjointSet.Int.create' can create a disjoint set
directly from any 'Foldable' structure of int pairs, e.g. and @[(Int, Int)]@.

There's not a variable and fixed length version of this because well, you can't modify the non-monadic version anyway.
-}
data DisjointIntSet = DisjointIntSet (Vector Int) (Vector Int) Int Int deriving Show

type MonadT m = (MonadRef m, PrimMonad m)

runMonadicIntSetFunc ::(MonadT m) => DisjointIntSetMonadic m -> ((?v :: MVectorT m, ?set_v :: MVectorT m, ?numElems :: Int, ?numSets :: Int, ?numSets_ref :: Ref m Int) => m b) -> m b
runMonadicIntSetFunc (DisjointIntSetMonadicVariable v_ref set_v_ref numSets_ref numElems_ref) f = do
  v <- readRef v_ref
  set_v <- readRef set_v_ref
  numElems <- readRef numElems_ref
  numSets <- readRef numSets_ref
  let
    ?v = v
    ?set_v = set_v
    ?numElems = numElems
    ?numSets = numSets
    ?numSets_ref = numSets_ref
    in f
runMonadicIntSetFunc (DisjointIntSetMonadicFixed v set_v numSets_ref numElems) f =
  do
    numSets <- readRef numSets_ref
    let
      ?v = v
      ?set_v = set_v
      ?numElems = numElems
      ?numSets = numSets
      ?numSets_ref = numSets_ref
      in f

{-|
Merges the two elements passed into one set.
-}
union :: (MonadT m) => DisjointIntSetMonadic m -> Int -> Int -> m Bool
union x@(DisjointIntSetMonadicFixed _ _ _ _) i1 i2 = runMonadicIntSetFunc x (Impl.union (i1, i2))
union x@(DisjointIntSetMonadicVariable v_ref set_v_ref numSets_ref numElems_ref) i1 i2 = do
  let
    ?v_ref = v_ref
    ?set_v_ref = set_v_ref
    ?numSets_ref = numSets_ref
    ?numElems_ref = numElems_ref
    in do
      Impl.resize (max i1 i2)
      runMonadicIntSetFunc x (Impl.union (i1,i2))

{-|
Finds the representative set for that element.
-}
find :: (MonadT m) => DisjointIntSetMonadic m -> Int -> m Int
find x i = runMonadicIntSetFunc x (Impl.find i)

{-|
Gives how many elements in this element's set.
-}
count :: (MonadT m) => DisjointIntSetMonadic m -> Int -> m Int
count x i = runMonadicIntSetFunc x (Impl.count i)

{-|
Both 'find' and 'count', but in one operation, so in theory faster than running them separately.
-}
findAndCount :: (MonadT m) => DisjointIntSetMonadic m -> Int -> m (Int, Int)
findAndCount x i = runMonadicIntSetFunc x (Impl.findAndCount i)

{-|
How many distinct sets. Note for fixed size disjoint sets this starts at the size, all ints are assumed to be in
separate sets.
-}
numSets :: (MonadT m) => DisjointIntSetMonadic m -> m Int
numSets (DisjointIntSetMonadicFixed _ _ numSets_ref _) = readRef numSets_ref
numSets (DisjointIntSetMonadicVariable _ _ numSets_ref _) = readRef numSets_ref

{-|
How many elements in this disjoint set. Note for fixed size disjoint sets this is always the size
they are created with, regardless of whether these elements have been assigned to sets.
-}
size :: (MonadT m) => DisjointIntSetMonadic m -> m Int
size (DisjointIntSetMonadicFixed _ _ _ numElems) = return numElems
size (DisjointIntSetMonadicVariable _ _ _ numElems_ref) = readRef numElems_ref

{-|
Creates a new disjoint set of fixed size.
-}
newDisjointIntSetFixed :: (PrimMonad m, MonadRef m) => Int -> m (DisjointIntSetMonadic m)
newDisjointIntSetFixed size = let ?size = size; ?array_size = size in do
  v <- Impl.new_count
  set_v <- Impl.new_set
  n <- newRef size
  return (DisjointIntSetMonadicFixed v set_v n size)

{-|
Creates a new disjoint set of variable size.
-}
newDisjointIntSetVariable :: (PrimMonad m, MonadRef m) => m (DisjointIntSetMonadic m)
newDisjointIntSetVariable = let ?size = 0; ?array_size = 1024 in do
  v <- Impl.new_count
  set_v <- Impl.new_set
  v_ref <- newRef v
  set_v_ref <- newRef set_v
  zero <- newRef 0
  n <- newRef 0
  return (DisjointIntSetMonadicVariable v_ref set_v_ref zero n)

{-|
Repeated calls iterates through the circular linked list of elements in this set
-}
nextInSet :: (MonadT m) => DisjointIntSetMonadic m -> Int -> m Int
nextInSet x i =  runMonadicIntSetFunc x (Impl.nextInSet i)

{-|
Repeatedly calls nextInSet to generate a list of elements in this set.
-}
setToList :: forall m. (MonadT m) => DisjointIntSetMonadic m -> Int -> m [Int]
setToList x i = do
  n <- count x i
  go n i where
    go :: Int -> Int -> m [Int]
    go n i = case n of
      0 -> return []
      _ -> do
        next_i <- nextInSet x i
        rest <- go (n - 1) next_i
        return (i:rest)


{-|
Freezes the disjoint int set into a non-mondaic set, but without copying. You should not modify the
monadic disjoint int set after this operation.
-}
unsafeFreeze :: (MonadT m) => DisjointIntSetMonadic m -> m DisjointIntSet
unsafeFreeze (DisjointIntSetMonadicFixed v set_v numSets_ref numElems) = do
  v_frozen <- Data.Vector.Unboxed.unsafeFreeze v
  set_v_frozen <- Data.Vector.Unboxed.unsafeFreeze set_v
  numSets <- readRef numSets_ref
  return (DisjointIntSet v_frozen set_v_frozen numSets numElems)
unsafeFreeze (DisjointIntSetMonadicVariable v_ref set_v_ref numSets_ref numElems_ref) = do
  numSets <- readRef numSets_ref
  numElems <- readRef numElems_ref
  v <- readRef v_ref
  set_v <- readRef set_v_ref
  v_frozen <- Data.Vector.Unboxed.unsafeFreeze v
  set_v_frozen <- Data.Vector.Unboxed.unsafeFreeze set_v
  return (DisjointIntSet v_frozen set_v_frozen numSets numElems)

{-|
Safely freezes the disjoint int set into a non-mondaic set by doing a full copy. You should not modify the
monadic disjoint int set after this operation.
-}
freeze :: (MonadT m) => DisjointIntSetMonadic m -> m DisjointIntSet
freeze (DisjointIntSetMonadicFixed v set_v numSets_ref numElems) = do
  v_frozen <- Data.Vector.Unboxed.freeze (Data.Vector.Unboxed.Mutable.slice 0 numElems v)
  set_v_frozen <- Data.Vector.Unboxed.freeze (Data.Vector.Unboxed.Mutable.slice 0 numElems set_v)
  numSets <- readRef numSets_ref
  return (DisjointIntSet v_frozen set_v_frozen numSets numElems)
freeze (DisjointIntSetMonadicVariable v_ref set_v_ref numSets_ref numElems_ref) = do
  numSets <- readRef numSets_ref
  numElems <- readRef numElems_ref
  v <- readRef v_ref
  set_v <- readRef set_v_ref
  v_frozen <- Data.Vector.Unboxed.freeze (Data.Vector.Unboxed.Mutable.slice 0 numElems v)
  set_v_frozen <- Data.Vector.Unboxed.freeze (Data.Vector.Unboxed.Mutable.slice 0 numElems set_v)
  return (DisjointIntSet v_frozen set_v_frozen numSets numElems)

{-|
A bit like 'runST', runs the ST action which must have the result of 'DisjointIntSetMonadic', but then
returns a non monadic 'DisjointIntSet'. It uses 'unsafeFreeze' interally, but this is perfectly safe as
nothing is done to the monadic disjoint int set after 'unsafeFreeze'.
-}
runDisjointIntSet :: (forall s. ST s (DisjointIntSetMonadic (ST s))) -> DisjointIntSet
runDisjointIntSet actions = runST (actions >>= unsafeFreeze)

{-|
This package has a separate interface for working with non-monadic disjoint int sets ('DisjointIntSet').
Naturally you can't do modifications unless you're in the monad, but you can do queries outside it.

If you're written a function that does work on a non-monadic int set (i.e. 'DisjointIntSet') but you want to
run it inside the monad, this is a way of doing it safely.
-}
runPure :: (MonadT m) => DisjointIntSetMonadic m -> (DisjointIntSet -> a) -> m a
runPure x f = f <$> (unsafeFreeze x)

{-|
Much like 'runPure', but incase you want to return a monadic result back to the monad. Can't imagine many
situations where this is useful but it's provided for completeness.
-}
runMonad :: (MonadT m) => DisjointIntSetMonadic m -> (DisjointIntSet -> m a) -> m a
runMonad x f = (unsafeFreeze x) >>= f
