{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Data.DisjointSet.Int.Monadic.Impl where


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
  (.)
  )

import Data.Vector.Unboxed.Mutable (
  MVector,
  new,
  unsafeRead, unsafeWrite, unsafeSwap,
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

initNewElem :: (PrimMonad m, ?v :: MVectorT m, ?set_v :: MVectorT m) => Int -> m ()
initNewElem i = do
  init_count i
  init_set i


resize :: (
  MonadRef m,
  PrimMonad m,
  PrimMonad m,
  ?v_ref :: Ref m (MVectorT m),
  ?set_v_ref :: Ref m (MVectorT m),
  ?numElems_ref :: Ref m Int,
  ?numSets_ref :: Ref m Int
  ) =>  Int -> m ()
resize i = do
  numElems <- readRef ?numElems_ref
  let new_numElems = i+1
  let addedElems = new_numElems - numElems
  when (addedElems > 0) $ do
    v <- readRef ?v_ref
    set_v <- readRef ?set_v_ref
    modifyRef' ?numSets_ref (+addedElems)
    writeRef ?numElems_ref new_numElems
    if (new_numElems > Vector.length v)
    then
      do
        new_v <- unsafeGrow v new_numElems
        writeRef ?v_ref new_v
        new_set_v <- unsafeGrow set_v new_numElems
        writeRef ?set_v_ref new_set_v
        let
          ?v = new_v
          ?set_v = new_set_v
          in
            init_range numElems new_numElems
    else
      do
        let
          ?v = v
          ?set_v = set_v
          in
            init_range numElems new_numElems



isCount = (<0)
isPointer = (>=0)
--isNonCanonical = (<= halfNegativeMax)
--toCanonical x = (x - minBound)
--fromCanonical x = (x + minBound
{-
freeze' :: (MonadRef m, PrimMonad m) => MVectorT m -> MVectorT m -> Int -> Int -> m DisjointIntSet
freeze' v target_v numSets numElems = do
  currSet_ref <- newRef 0
  set_v <- new numSets
  mapM_ (finalCollapse set_v v target_v currSet_ref) [0..(numElems-1)]
  result_v <- unsafeFreeze target_v
  set_result_v <- unsafeFreeze set_v
  return (DisjointIntSet result_v set_result_v)
-}


collapse :: (PrimMonad m, ?v :: MVectorT m) => Int -> Int -> m ()
collapse target_i current_i = when (target_i /= current_i) $ collapse' current_i where
  collapse' current_i = do
    next_i <- read_absolute current_i
    when (target_i /= next_i) $ do
      write current_i target_i
      collapse' next_i

data PointerOrCount = Pointer Int | Count Int


read :: (PrimMonad m, ?v :: MVectorT m) => Int -> m PointerOrCount
read i =
  do
    r <- read_absolute i
    return (if (isPointer r) then (Pointer r) else (Count (negate r)))

read_absolute :: (PrimMonad m, ?v :: MVectorT m) => Int -> m Int
read_absolute i = unsafeRead ?v i

write ::  (PrimMonad m, ?v :: MVectorT m) => Int -> Int -> m ()
write = unsafeWrite ?v

write_count :: (PrimMonad m, ?v :: MVectorT m) => Int -> Int -> m ()
write_count i x = write i (-x)


read_set ::  (PrimMonad m, ?set_v :: MVectorT m) => Int -> m Int
read_set = unsafeRead ?set_v


swap_set :: (PrimMonad m, ?set_v :: MVectorT m) => Int -> Int -> m ()
swap_set = unsafeSwap ?set_v


mapM_zeroToN :: (Monad m) => Int -> (Int -> m ()) -> m ()
mapM_zeroToN = mapM_nToN 0

mapM_nToN :: (Monad m) => Int -> Int -> (Int -> m ()) -> m ()
mapM_nToN start_n end_n f = mapM_ f [start_n..(end_n-1)]

new_count :: (PrimMonad m, ?size :: Int, ?array_size :: Int) => m (MVectorT m)
new_count = do
  v <- new ?array_size
  let ?v = v in mapM_zeroToN ?size init_count
  return v

init_count :: (PrimMonad m, ?v :: MVectorT m) => Int -> m ()
init_count i = write_count i 1

init_count_range :: (PrimMonad m, ?v :: MVectorT m) => Int -> Int -> m ()
init_count_range start_i end_i = mapM_nToN start_i end_i init_count

init_set :: (PrimMonad m, ?set_v :: MVectorT m) => Int -> m ()
init_set i = unsafeWrite ?set_v i i

init_set_range :: (PrimMonad m, ?set_v :: MVectorT m) => Int -> Int -> m ()
init_set_range start_i end_i = mapM_nToN start_i end_i init_set

init_range :: (PrimMonad m, ?v :: MVectorT m, ?set_v :: MVectorT m) => Int -> Int -> m ()
init_range start_i end_i = do
  init_count_range start_i end_i
  init_set_range start_i end_i

new_set :: (PrimMonad m, ?size :: Int, ?array_size :: Int)  => m (MVectorT m)
new_set = do
  set_v <- new ?array_size
  let ?set_v = set_v in mapM_zeroToN ?size init_set
  return set_v

{-
new_next_set :: (PrimMonad m, ?size :: Int, ?array_size :: Int) => m (MVectorT m)
new_next_set = do
  next_set_v <- new ?array_size
  when (?size /= 0) $ do
    mapM_zeroToN (?size - 1) (\i -> unsafeWrite next_set_v i (i+1))
    unsafeWrite next_set_v (?size - 1) 0
  return next_set_v

init_next_set_range :: (PrimMonad m, ?next_set_v :: MVectorT m, ?v :: MVectorT m) => Int -> Int -> m ()
init_next_set_range start_i end_i = do
  zero_i <- find 0
  one_i <- unsafeRead ?next_set_v zero_i
  unsafeWrite ?next_set_v zero_i start_i
  mapM_nToN start_i (end_i-1) (\i -> unsafeWrite ?next_set_v i (i+1))
  unsafeWrite ?next_set_v end_i one_i
-}


union :: forall m. (MonadRef m, PrimMonad m, ?v :: MVectorT m, ?set_v :: MVectorT m, ?numSets_ref :: Ref m Int) =>  (Int,Int) -> m Bool
union (x_i, y_i) = go x_i y_i where
  go :: (?v :: MVectorT m) => Int -> Int -> m Bool
  go x_i y_i = do
    (x_count_i, x_count) <- findAndCountNoCollapse x_i
    (y_count_i, y_count) <- findAndCountNoCollapse y_i
    let new_count = x_count + y_count
    (target_i, result) <-
      case (x_count_i /= y_count_i) of
        True -> do
          final_i <-
            case (x_count > y_count) of
              True ->
                do
                  write_count x_count_i new_count
                  write y_count_i x_count_i
                  return x_count_i
              False ->
                do
                  write_count y_count_i new_count
                  write x_count_i y_count_i
                  return y_count_i
          swap_set x_count_i y_count_i
          modifyRef' ?numSets_ref pred
          return (final_i, True)
        False -> return (x_count_i, False)
    collapse target_i x_i
    collapse target_i y_i
    return result

equivalent :: (PrimMonad m, ?set_v :: MVectorT m) => (a -> Int -> m a) -> a -> Int -> m a
equivalent f init i = go init i where
  go acc i' = do
    p <- read_set i'
    r <- f acc i'
    if (p /= i) then go r p else return r

find :: (PrimMonad m, ?v :: MVectorT m) =>  Int -> m Int
find i = do
  (final_i, _) <- findAndCount i
  return final_i


count :: (PrimMonad m, ?v :: MVectorT m) =>  Int -> m Int
count i =  do
  (_, count) <- findAndCount i
  return count

findAndCountNoCollapse :: (PrimMonad m, ?v :: MVectorT m) => Int -> m (Int,Int)
findAndCountNoCollapse i = do
  r <- read i
  case r of
    Pointer p -> findAndCountNoCollapse p
    Count c -> return (i, c)

findAndCount :: (PrimMonad m, ?v :: MVectorT m) => Int -> m (Int,Int)
findAndCount i = do
  r@(final_i, _) <- findAndCountNoCollapse i
  collapse final_i i
  return r

nextInSet :: (PrimMonad m, ?set_v :: MVectorT m) => Int -> m Int
nextInSet = read_set






{-
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
-}