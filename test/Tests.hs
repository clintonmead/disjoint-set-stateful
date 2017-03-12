module Main where

import Data.DisjointSet.Int
import qualified Data.DisjointSet.Int.Monadic as M

import Data.List (nub, sort)

import Test.Hspec (hspec, it, shouldBe)

ds t =
  M.runDisjointIntSet (do
    ds <- case t of
      Just n -> M.newDisjointIntSetFixed n
      Nothing -> M.newDisjointIntSetVariable
    M.union ds 0 1
    M.union ds 3 2
    M.union ds 1 2
    M.union ds 8 9
    M.union ds 8 3
    M.union ds 7 4
    return ds
  )

allEqual (x:xs) = all (==x) xs

testds x = do
  it "check set1" $ allEqual [find x 0, find x 1, find x 2, find x 3, find x 8, find x 9] `shouldBe` True
  it "check set2" $ allEqual [find x 4, find x 7] `shouldBe` True
  it "check different" $ length (nub [find x 0, find x 4, find x 5, find x 6]) `shouldBe` 4
  it "check count" $ map (count x) [0..9] `shouldBe` [6,6,6,6,2,1,1,2,6,6]
  it "check size" $ size x `shouldBe` 10
  it "check num_sets" $ numSets x `shouldBe` 4
  it "check setToList" $ [sort (setToList x 8), sort (setToList x 4), setToList x 5, setToList x 6] `shouldBe` [[0,1,2,3,8,9], [4,7], [5], [6]]


main = hspec $ do
  testds (ds (Just 10))
  testds (ds Nothing)