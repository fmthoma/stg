{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}

-- | A simple stack type. Very similar to an ordinary list, but with a more
-- specialized API.
module Stack (
    Stack(..),
    popN,
    (<>>),
    fromList,
) where



import           Data.Foldable                as F
import           Data.Monoid
import qualified GHC.Exts                     as OverloadedLists
import           Text.PrettyPrint.ANSI.Leijen hiding (list, (<>))



-- | The usual stack data structure.
data Stack a = Empty | a :< Stack a
    deriving (Eq, Ord)

instance Show a => Show (Stack a) where
    show = show . toList

instance Pretty a => Pretty (Stack a) where
    pretty = prettyList . toList

instance Functor Stack where
    fmap _ Empty = Empty
    fmap f (x :< xs) = f x :< fmap f xs

instance Foldable Stack where
    foldMap _ Empty = mempty
    foldMap f (x :< xs) = f x <> foldMap f xs

instance Monoid (Stack a) where
    mempty = Empty
    Empty `mappend` s = s
    (x :< xs) `mappend` ys = x :< (xs <> ys)

instance OverloadedLists.IsList (Stack a) where
    type Item (Stack a) = a
    fromList = fromList
    toList = F.toList

-- | Push a list of items onto the stack. The first item will be at the
-- top of the stack.
(<>>) :: [a] -> Stack a -> Stack a
list <>> stack = fromList list <> stack

-- | Pop exactly n elements off the stack; fail if not enough elements are
-- present.
popN :: Int -> Stack a -> Maybe ([a], Stack a)
popN n _ | n < 0 = Nothing
popN 0 stack = Just ([], stack)
popN _ Empty = Nothing
popN n (x :< xs) = case popN (n-1) xs of
    Nothing -> Nothing
    Just (pops, rest) -> Just (x:pops, rest)

-- | Create a stack from a list. The first item will be the top of the stack.
fromList :: [a] -> Stack a
fromList = foldr (:<) Empty
