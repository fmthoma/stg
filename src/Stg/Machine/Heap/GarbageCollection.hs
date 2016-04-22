{-# LANGUAGE LambdaCase #-}

-- | Remove unused heap objects.
module Stg.Machine.Heap.GarbageCollection (
    garbageCollect,
    Dead(..),
    Alive(..),
) where



import           Data.Map          (Map)
import qualified Data.Map          as M
import           Data.Maybe
import           Data.Monoid
import           Data.Set          (Set)
import qualified Data.Set          as S

import           Stg.Language
import           Stg.Machine.Types



-- | Alive memory addresses.
newtype Alive = Alive (Set MemAddr)

-- | Dead memory addresses that have been eliminated by garbage collection.
newtype Dead = Dead (Set MemAddr)

-- | Simple tracing garbage collector.
--
-- 1. Get the addresses of all globals.
-- 2. Collect all the addresses contained in the closures the global addresses
--    map to on the heap.
-- 3. Drop all addresses from the heap that weren't found in the process.
garbageCollect
    :: Globals -- ^ Root elements (unconditionally alive).
    -> Heap
    -> (Dead, Alive, Heap)
garbageCollect globals heap = (Dead dead, Alive alive, cleanHeap)
  where
    alive = aliveAddresses globals heap
    dead = let Heap h = heap
           in M.keysSet h `S.difference` alive
    (cleanHeap, _dropped) = let isAlive addr _ = S.member addr alive
                            in M.partitionWithKey isAlive heap

-- | Find all alive addresses in the heap, starting at the values of the
-- globals, which are considered alive.
aliveAddresses :: Globals -> Heap -> Set MemAddr
aliveAddresses (Globals globals) (Heap heap) = foldMap addrs globalClosures
  where
    globalAddrs = [ addr | (_, Addr addr) <- M.toList globals ]
    globalClosures = mapMaybe (\addr -> M.lookup addr heap) globalAddrs



-- | Collect all mentioned addresses in a syntax element.
class Addresses ast where
    addrs :: ast -> Set MemAddr

instance Addresses ast => Addresses [ast] where
    addrs = foldMap addrs

instance Addresses ast => Addresses (Map k ast) where
    addrs = foldMap addrs

instance Addresses Closure where
    addrs (Closure lf free) = addrs lf <> addrs free

instance Addresses LambdaForm where
    addrs (LambdaForm _free _upd _bound expr) = addrs expr

instance Addresses Value where
    addrs = \case
        Addr s     -> S.singleton s
        PrimInt _i -> mempty

instance Addresses Expr where
    addrs = \case
        Let _rec binds expr -> addrs binds <> addrs expr
        Case scrutinee alts -> addrs scrutinee <> addrs alts
        AppF _fun args      -> addrs args
        AppC _con args      -> addrs args
        AppP _f _x _y       -> mempty
        Lit _i              -> mempty

instance Addresses Binds where
    addrs (Binds bs) = foldMap addrs bs

instance Addresses Alts where
    addrs = \case
        Algebraic alts -> addrs alts
        Primitive alts -> addrs alts

instance Addresses AlgebraicAlts where
    addrs (AlgebraicAlts alts defaultAlt) = addrs alts <> addrs defaultAlt

instance Addresses PrimitiveAlts where
    addrs (PrimitiveAlts alts defaultAlt) = addrs alts <> addrs defaultAlt

instance Addresses AlgebraicAlt where
    addrs (AlgebraicAlt _con _vars expr) = addrs expr

instance Addresses PrimitiveAlt where
    addrs (PrimitiveAlt _prim expr) = addrs expr

instance Addresses DefaultAlt where
    addrs = \case
        DefaultNotBound expr -> addrs expr
        DefaultBound _  expr -> addrs expr

instance Addresses Atom where
    addrs = mempty
