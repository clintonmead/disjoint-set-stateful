{-# LANGUAGE NoImplicitPrelude #-}

{-|
This module contains non-monadic functions for querying disjoint int sets. See "Data.DisjointSet.Int.Monadic" for information about
how to create and modify disjoint int sets.

There are two other disjoint int set packages on hackage, namely:

* "disjoint-set"
* "disjoint-sets-st"

The first is a pure disjoint int set implementation, so as it doesn't do in place array updates in ST it will presumably
be somewhat slower, with the data structure used likely taking more space and having log(n) access speed.

This package does not include a pure implementation, you're better off using "disjoint-set" for that.

"disjoint-sets-st" does offer an implementation in IO, however, it's missing two features:

1) The ability to "freeze" a disjoint set, and then query it in a pure way.
2) Maintaining a circular linked list of each set so one can quickly discover all the elements of one set without
quering through the entire structure.

This package implements both of the above features.
-}
module Data.DisjointSet.Int (
  find,
  count,
  findAndCount,
  numSets,
  size,
  nextInSet,
  setToList
)
where

import Data.Vector.Unboxed (Vector, (!))
import Data.DisjointSet.Int.Monadic (DisjointIntSet(DisjointIntSet))
import Data.DisjointSet.Int.Monadic.Impl (PointerOrCount(Pointer, Count), isPointer)

import Prelude (
  Int,
  Bool (True, False),
  negate,
  fst,
  snd,
  (/=),
  Maybe (Just, Nothing),
  (.)
  )

import Data.List (unfoldr)

type VectorT = Vector Int

read :: VectorT -> Int -> PointerOrCount
read v i =
  let
    r = v ! i
  in
    case (isPointer r) of
      True -> Pointer r
      False -> Count (negate r)

{-|
Both 'find' and 'count', but in one operation, so in theory faster than running them separately.
-}
findAndCount :: DisjointIntSet -> Int -> (Int, Int)
findAndCount (DisjointIntSet v _ _ _) i = go i where
  go i = case (read v i) of
    Pointer next_i -> go next_i
    Count c -> (i, c)

{-|
Finds the representative set for that element.
-}
find :: DisjointIntSet -> Int -> Int
find v i = fst (findAndCount v i)

{-|
Gives how many elements in this element's set.
-}
count :: DisjointIntSet -> Int -> Int
count v i = snd (findAndCount v i)

{-|
How many distinct sets.
-}
numSets :: DisjointIntSet -> Int
numSets (DisjointIntSet _ _ numSets _) = numSets

{-|
How many elements in this disjoint set.
-}
size ::  DisjointIntSet -> Int
size (DisjointIntSet _ _ _ size) = size

{-|
Gets the next element in the current set. This is a circular list, so if you iterate on this you'll get back to the
element you started with in the end.
-}
nextInSet :: DisjointIntSet -> Int -> Int
nextInSet (DisjointIntSet _ set_v _ _) i = set_v ! i

{-|
Returns a list of the elements in the selected set.
-}
setToList :: DisjointIntSet -> Int -> [Int]
setToList ds i = i:(unfoldr f i) where
  f curr_i = let next_i = nextInSet ds curr_i in if next_i /= i then Just (next_i, next_i) else Nothing

