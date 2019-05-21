{-# LANGUAGE MultiParamTypeClasses #-}
module Aenderung where

import qualified Data.Map as M
import Data.List (nub)
import Data.Maybe (mapMaybe)

-- diffing worlds.
-- Im Unterschied zu Data.Generic.Diff will ich keinen editscript der die Gleichheit betont,
-- ich suche nur die Unterschiede und will den Ausgangszustand wegabstrahieren.

-- person kann sein: natürliche Person, juristische Person, ein Tier, die Umwelt an sich, ....

data Aenderung person etwas = Verliert person etwas | Gewinnt person etwas
-- brauche noch Vorbedingung fuer einen Diff von Handlungen?

instance (Show person, Show etwas) => Show (Aenderung person etwas) where
    show (Verliert p e) = show p ++ " verliert " ++ show e
    show (Gewinnt p e) = show p ++ " gewinnt " ++ show e

--TODO world, person, etwas relaten!!!! MultiParamTypeClasses?
data Auswirkung world person etwas = Auswirkung (world -> world -> [Aenderung person etwas])

diff_num :: (Ord etwas, Num etwas) => person -> etwas -> etwas -> Maybe (Aenderung person etwas)
diff_num p i1 i2
    | i1 == i2 = Nothing
    | i1 > i2 = Just $ Verliert p (i1 - i2)
    | i1 < i2 = Just $ Gewinnt  p (i2 - i1)

diff_num_map :: Ord person => (Ord etwas, Num etwas) => M.Map person etwas -> M.Map person etwas -> [Aenderung person etwas]
diff_num_map vorher nachher = mapMaybe (\p -> diff_num p (lookup p vorher) (lookup p nachher)) personen --TODO
    where personen = nub $ (M.keys vorher) ++ (M.keys nachher) --TODO nub is O(n^2), use sets
          lookup = M.findWithDefault 0

-- diff_num_map (M.fromList [("Alice", 3)]) (M.fromList [("Bob", 8)])

--TODO test

