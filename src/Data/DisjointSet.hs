{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Data.DisjointSet where


import Prelude (
  Int, (+), (-), negate,
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
  (.)
  )

import Data.Vector.Unboxed.Mutable (
  MVector,
  new,
  unsafeRead, unsafeWrite,
  unsafeGrow
  )

import qualified Data.Vector.Unboxed.Mutable as Vector

import Data.Vector.Unboxed (
  Vector,
  unsafeFreeze
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

type MVectorT m = MVector (PrimState m) Int

data Size = Variable | Fixed

data DisjointIntSetMonadic m (s :: Size) where
  DisjointIntSetMonadicFinite :: (MVectorT m) -> (Ref m Int) -> DisjointIntSetMonadic m Fixed
  DisjointIntSetMonadicInfinite :: (Ref m (MVectorT m)) -> (Ref m Int) -> (Ref m Int) -> DisjointIntSetMonadic m Variable

data DisjointIntSet = DisjointIntSet (Vector Int) (Vector Int)

unionM :: (MonadRef m, PrimMonad m) => DisjointIntSetMonadic m a -> (Int,Int) -> m Bool
unionM (DisjointIntSetMonadicFinite v numSets_ref) arg = unionMWithCountChange v numSets_ref arg
unionM (DisjointIntSetMonadicInfinite v_ref numSets_ref numElems_ref) arg@(x,y) = do
  v <- readRef v_ref
  resize v_ref v numElems_ref numSets_ref (max x y)
  unionMWithCountChange v numSets_ref arg

findM :: (MonadRef m, PrimMonad m) => DisjointIntSetMonadic m a -> Int -> m Int
findM (DisjointIntSetMonadicFinite v _) i = findM' v i
findM (DisjointIntSetMonadicInfinite v_ref _ numElems_ref) i = do
  numElems <- readRef numElems_ref
  case (i < numElems) of
    True -> do
      v <- readRef v_ref
      findM' v i
    False ->
      return i

countM :: (MonadRef m, PrimMonad m) => DisjointIntSetMonadic m a -> Int -> m Int
countM (DisjointIntSetMonadicFinite v _) i = countM' v i
countM (DisjointIntSetMonadicInfinite v_ref _ numElems_ref) i = do
  numElems <- readRef numElems_ref
  case (i < numElems) of
    True -> do
      v <- readRef v_ref
      countM' v i
    False ->
      return 1
findAndCountM :: (MonadRef m, PrimMonad m) => DisjointIntSetMonadic m a -> Int -> m (Int, Int)
findAndCountM (DisjointIntSetMonadicFinite v _) i = findAndCountM' v i
findAndCountM (DisjointIntSetMonadicInfinite v_ref _ numElems_ref) i = do
  numElems <- readRef numElems_ref
  case (i < numElems) of
    True -> do
      v <- readRef v_ref
      findAndCountM' v i
    False ->
      return (i, 1)

numSetsM :: (MonadRef m, PrimMonad m) => DisjointIntSetMonadic m a -> m Int
numSetsM (DisjointIntSetMonadicFinite _ numSets_ref) = readRef numSets_ref
numSetsM (DisjointIntSetMonadicInfinite _ numSets_ref _) = readRef numSets_ref

freeze :: (MonadRef m, PrimMonad m) => DisjointIntSetMonadic m a -> m DisjointIntSet
freeze (DisjointIntSetMonadicFinite v numSets_ref) = do
  numSets <- readRef numSets_ref
  freeze' v v numSets (Vector.length v)
freeze (DisjointIntSetMonadicInfinite v_ref numSets_ref numElems_ref) = do
  v <- readRef v_ref
  numSets <- readRef numSets_ref
  numElems <- readRef numElems_ref
  target_v <- new numElems
  freeze' v target_v numSets numElems

resize :: (MonadRef m, PrimMonad m) => Ref m (MVectorT m) -> MVectorT m -> Ref m Int -> Ref m Int -> Int -> m ()
resize v_ref v numElems_ref numSets_ref i = do
  numElems <- readRef numElems_ref
  let new_numElems = i+1
  let addedElems = new_numElems - numElems
  when (addedElems > 0) $ do
    modifyRef' numSets_ref (+addedElems)
    writeRef numElems_ref new_numElems
    when (new_numElems > Vector.length v) $ do
      new_v <- unsafeGrow v new_numElems
      writeRef v_ref new_v
    mapM_ (\i -> unsafeWrite v i (-1)) [new_numElems..i]

halfNegativeMax = minBound `div` 2

isCount = (<0)
isPointer = (>=0)
isNonCanonical = (<= halfNegativeMax)
toCanonical x = (x - minBound)
fromCanonical x = (x + minBound)

freeze' :: (MonadRef m, PrimMonad m) => MVectorT m -> MVectorT m -> Int -> Int -> m DisjointIntSet
freeze' v target_v numSets numElems = do
  currSet_ref <- newRef 0
  set_v <- new numSets
  mapM_ (finalCollapse set_v v target_v currSet_ref) [0..(numElems-1)]
  result_v <- unsafeFreeze target_v
  set_result_v <- unsafeFreeze set_v
  return (DisjointIntSet result_v set_result_v)

unionMWithCountChange :: (MonadRef m, PrimMonad m) => MVectorT m -> Ref m Int -> (Int,Int) -> m Bool
unionMWithCountChange v numSets_ref i = do
  setsCombined <- unionM' v i
  when setsCombined (modifyRef' numSets_ref pred)
  return setsCombined


collapse :: (PrimMonad m, ?v :: MVectorT m) => Int -> Int -> m ()
collapse target_i = collapse' where
  collapse' current_i = do
    next_i <- read current_i
    when (target_i /= next_i) $ do
      write current_i target_i
      collapse' next_i

findAndRemoveCount :: (PrimMonad m, ?v :: MVectorT m) => Int -> m Int
findAndRemoveCount i = do
  r <- read i
  case (isPointer r) of
    True ->
      case (r == i) of
        True -> return i
        False -> findAndRemoveCount r
    False -> do
      write i i
      return i

removeCountAndCollapse :: (PrimMonad m) => MVectorT m -> Int -> m ()
removeCountAndCollapse v i = let ?v = v in do
  final_i <- findAndRemoveCount i
  collapse final_i i

read :: (PrimMonad m, ?v :: MVectorT m) => Int -> m Int
read = read' ?v

read' :: (PrimMonad m) => MVectorT m -> Int -> m Int
read' = unsafeRead

write :: (PrimMonad m, ?v :: MVectorT m) => Int -> Int -> m ()
write = write' ?v

write' ::  (PrimMonad m) => MVectorT m -> Int -> Int -> m ()
write' = unsafeWrite

findAndCount :: (PrimMonad m, ?v :: MVectorT m) => Int -> m (Int,Int)
findAndCount i = do
  r <- read i
  case (isPointer r) of
    True -> findAndCount r
    False -> return (i, r)

findAndCountAndCollapse :: (PrimMonad m, ?v :: MVectorT m) => Int -> m (Int,Int)
findAndCountAndCollapse i = do
  r@(final_i, _) <- findAndCount i
  collapse final_i i
  return r

unionM' :: PrimMonad m => MVectorT m -> (Int,Int) -> m Bool
unionM' v (x_i, y_i) = let ?v = v in  go x_i y_i where
  go x_i y_i = do
    (x_count_i, x_count) <- findAndCount x_i
    (y_count_i, y_count) <- findAndCount y_i
    let new_count = x_count + y_count
    (target_i, change) <-
      case (x_count_i == y_count_i) of
        True -> return (x_count_i, False)
        False -> do
          final_i <-
            case (x_count < y_count) of -- This is actually where x >= y, as counts are stored as negative integers
              True ->
                do
                  write x_count_i new_count
                  write y_count_i x_count_i
                  return x_count_i
              False ->
                do
                  write y_count_i new_count
                  write x_count_i y_count_i
                  return y_count_i
          return (final_i, True)
          where
            new_count = x_count + y_count
    collapse target_i x_i
    collapse target_i y_i
    return change

findM' :: PrimMonad m => MVectorT m -> Int -> m Int
findM' v i = let ?v = v in do
  (final_i, _) <- findAndCountAndCollapse i
  return final_i


countM' :: PrimMonad m => MVectorT m -> Int -> m Int
countM' v i =  let ?v = v in do
  (_, count) <- findAndCountAndCollapse i
  return (negate count)

findAndCountM' :: PrimMonad m => MVectorT m -> Int -> m (Int, Int)
findAndCountM' v i = let ?v = v in do
 (count, final_i) <- findAndCountAndCollapse i
 return (negate count, final_i)

collapseM :: PrimMonad m => MVectorT m -> Int -> m ()
collapseM v i = let ?v = v in findAndCountAndCollapse i >> return ()

newDisjointSetFixed :: (PrimMonad m, MonadRef m) => Int -> m (DisjointIntSetMonadic m Fixed)
newDisjointSetFixed size = do
  v <- new size
  Vector.set v (-1)
  n <- newRef size
  return (DisjointIntSetMonadicFinite v n)

newDisjointSetVariable :: (PrimMonad m, MonadRef m) => m (DisjointIntSetMonadic m Variable)
newDisjointSetVariable = do
  v <- new 1024
  v_ref <- newRef v
  zero <- newRef 0
  n <- newRef 0
  return (DisjointIntSetMonadicInfinite v_ref zero n)

finalCollapse :: forall m. (MonadRef m, PrimMonad m) => MVectorT m -> MVectorT m -> MVectorT m -> Ref m Int -> Int -> m ()
finalCollapse set_v old_v new_v set_i_ref i =
  let
    read_old = read' old_v
    read_new = read' new_v

    write_old = write' old_v
    write_new = write' new_v

    write_set = write' set_v

    orig_i = i
    init = do
      r <- read_old i
      case (isPointer r) of
        True -> go r
        False -> case (isNonCanonical r) of
          True -> write_new i (toCanonical r)
          False -> do
            set_i <- readRef set_i_ref
            writeRef set_i_ref (succ set_i)
            write_new i set_i
            write_set set_i (-r)
    go i = do
      case (i >= orig_i) of
        True -> do
          r <- read_old i
          case (isPointer r) of
            True -> go r
            False -> case (isNonCanonical r) of
              True -> collapseCanonical (toCanonical r) r i
              False -> do
                set_i <- readRef set_i_ref
                writeRef set_i_ref (succ set_i)
                let nonCanonical = fromCanonical set_i
                write_set set_i (-r)
                write_old i nonCanonical
                collapseCanonical set_i nonCanonical i
        False -> do
          r <- read_new i
          collapseCanonical r (fromCanonical r) i

    collapseCanonical canonical_r non_canonical_r last_i = do
      next_i <- read_old orig_i
      write_new orig_i canonical_r
      (let ?v = old_v in collapse last_i next_i) :: m () -- Signature due to potentual GHC bug #13006
  in
    init
