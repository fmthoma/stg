{-# LANGUAGE LambdaCase  #-}
{-# LANGUAGE QuasiQuotes #-}

module Main (main) where



import           Data.Foldable
import qualified Data.Text                as T
import qualified Data.Text.IO             as T
import           System.Console.ANSI      (hSupportsANSI)
import           System.IO                (stdout)

import           Stg.Language.Prettyprint
import           Stg.Machine
import           Stg.Parser



main :: IO ()
main = do
    let prog = [stg|
        -- one = () \n () -> 1#;
        -- add = () \n (x, y) -> +# x y;
        -- -- INVALID: three = () \u () -> +# 1# 2#;
        -- -- ... because only variables may be on the RHS ..?
        -- main = () \u () -> add (2#, 1#)

        -- main = () \u () -> case Just () of
        --     Just () -> Yes ();
        --     Nothing () -> Maybe ();
        --     default -> No ()

        main = () \u () -> case tuple (fst, snd) of
            default -> Tuple (fst, snd);

        fst = () \n () -> Fst ();
        snd = () \n () -> Snd ();
        tuple = () \n (x,y) -> Tuple (x,y)
        |]
        initial = initialState "main" prog
        steps = iterate evalStep initial
    ppr <- hSupportsANSI stdout >>= \case
        True  -> pure prettyprintAnsi
        False -> pure prettyprint
    for_ steps (\state -> do
        T.putStrLn (ppr state)
        T.putStrLn (T.replicate 80 "=") )
