{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}

module Test.Machine.Heap.GarbageCollection (tests) where



import qualified Data.Map                           as M
import           Data.Monoid
import qualified Data.Set                           as S
import           Data.Text                          (Text)
import qualified Data.Text                          as T
import           Test.Tasty
import           Test.Tasty.HUnit

import           Stg.Language.Prettyprint
import           Stg.Machine.Heap
import           Stg.Machine.Heap.GarbageCollection
import           Stg.Machine.Types
import           Stg.Parser

import           Test.Orphans                       ()



tests :: TestTree
tests = testGroup "Garbage collection"
    [ minimal
    ]

prettyIndented :: PrettyAnsi a => a -> Text
prettyIndented = T.unlines . map ("    " <>) . T.lines . prettyprintAnsi

minimal :: TestTree
minimal = testGroup "Minimal example"
    [ unusedIsCollected
    , usedIsNotCollected
    , heapSplit
    ]
  where
    (~>) = (,)
    dirtyHeap = Heap
        [ MemAddr 0 ~> Closure [stg| (used1) \n () -> Used (used1) |]
                               [Addr (MemAddr 1)]
        , MemAddr 1 ~> Closure [stg| (used2, prim) \n () -> Used (used2, prim) |]
                               [Addr (MemAddr 2), PrimInt 1]
        , MemAddr 2 ~> Closure [stg| () \n () -> Used ()   |] []
        , MemAddr 3 ~> Closure [stg| () \n () -> Unused () |] [] ]
    globals = Globals
        [ "main"  ~> Addr (MemAddr 0) ]

    errorMsg cleanHeap = T.unlines
        [ "Globals:"
        , prettyIndented globals
        , "Dirty heap:"
        , prettyIndented dirtyHeap
        , "Clean heap:"
        , prettyIndented cleanHeap ]

    unusedIsCollected = testCase "Dead address is found" test
      where
        expectedDead = S.singleton (MemAddr 3)
        (Dead actualDead, _alive, cleanHeap) = garbageCollect globals dirtyHeap
        test = assertEqual (T.unpack (errorMsg cleanHeap)) expectedDead actualDead

    usedIsNotCollected = testCase "Alives are kept" test
      where
        expectedHeap = let Heap h = dirtyHeap
                       in Heap (M.delete (MemAddr 3) h)
        (_dead, _alive, cleanHeap) = garbageCollect globals dirtyHeap
        test = assertEqual (T.unpack (errorMsg cleanHeap)) expectedHeap cleanHeap

    heapSplit = testCase "dead+alive contain all previous addresses" test
      where
        expected = let Heap h = dirtyHeap in M.keysSet h
        actual = dead <> alive
        (Dead dead, Alive alive, cleanHeap) = garbageCollect globals dirtyHeap
        test = assertEqual (T.unpack (errorMsg cleanHeap)) expected actual
