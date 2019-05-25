{-# LANGUAGE MultiParamTypeClasses #-}
module Aenderung where

import qualified Data.Map as M
import Data.List (nub)
import Data.Maybe (mapMaybe)

import Test.HUnit (Test(..), assertEqual)

-- diffing worlds.
-- Im Unterschied zu Data.Generic.Diff will ich keinen editscript der die Gleichheit betont,
-- ich suche nur die Unterschiede und will den Ausgangszustand wegabstrahieren.

-- Person kann sein: natürliche Person, juristische Person, ein Tier, die Umwelt an sich, ....

data Aenderung person etwas = Verliert person etwas | Gewinnt person etwas
    deriving (Ord, Eq)
-- brauche noch Vorbedingung fuer ein Delta von Handlungen?

instance (Show person, Show etwas) => Show (Aenderung person etwas) where
    show (Verliert p e) = show p ++ " verliert " ++ show e
    show (Gewinnt p e) = show p ++ " gewinnt " ++ show e

data Auswirkung world person etwas = Auswirkung (world -> world -> [Aenderung person etwas])


-- Deltas, d.h. Unterschiede Zwischen Welten.
--
-- Man könnte eine class Delta world einführen, mit einer delta-Funtion
--   :: welt -> welt -> [Aenderung person etwas]
-- Diese Klasse würde dann Welten mit Personen und Etwas in Relation setzen.
-- Dafür bräuchte es MultiParamTypeClasses. Eine simple Funktion ist da einfacher.

type Delta world person etwas = world -> world -> [Aenderung person etwas]

delta_num :: (Ord etwas, Num etwas) => person -> etwas -> etwas -> Maybe (Aenderung person etwas)
delta_num p i1 i2
    | i1 == i2 = Nothing
    | i1 > i2 = Just $ Verliert p (i1 - i2)
    | i1 < i2 = Just $ Gewinnt  p (i2 - i1)

delta_num_map :: Ord person => (Ord etwas, Num etwas) => Delta (M.Map person etwas) person etwas
delta_num_map vorher nachher = mapMaybe (\p -> delta_num p (lookup p vorher) (lookup p nachher)) personen
    where personen = nub $ (M.keys vorher) ++ (M.keys nachher) --TODO nub is O(n^2), use sets
          lookup = M.findWithDefault 0

-- Tests and properties

tests = [
    TestCase (assertEqual "eq"
        Nothing
        (delta_num "X" 4 4)
        ),
    TestCase (assertEqual "geben"
        (Just (Verliert "X" 3))
        (delta_num "X" 4 1)
        ),
    TestCase (assertEqual "nehmen"
        (Just (Gewinnt "X" 6))
        (delta_num "X" 4 10)
        ),
    TestCase (assertEqual "negativ"
        (Just (Verliert "X" 8))
        (delta_num "X" 4 (-4))
        )
    ] ++ [
    TestCase (assertEqual "map"
        [Verliert "Alice" 3, Gewinnt "Bob" 8]
        (delta_num_map (M.fromList [("Alice", 3)]) (M.fromList [("Bob", 8)]))
        ),
    TestCase (assertEqual "map"
        [Gewinnt "Alice" 5]
        (delta_num_map (M.fromList [("Bob", 42), ("Alice", 3)]) (M.fromList [("Alice", 8), ("Bob", 42)]))
        )
    ]

-- Die Zahlen bei Gewinnt oder Verliert sind immer positiv.
prop_positive :: Integer -> Integer -> Bool
prop_positive i1 i2 = case delta_num "X" i1 i2 of
                        Just a -> (number a) > 0
                        Nothing -> i1 == i2
                      where number (Gewinnt _ n) = n
                            number (Verliert _ n) = n

-- Es kann maximal so viele Änderungen geben, wie es Personen gibt.
prop_max_aenderungen :: M.Map String Integer -> M.Map String Integer -> Bool
prop_max_aenderungen m1 m2 = length (delta_num_map m1 m2) <= length (M.keys m1) + length (M.keys m2)
