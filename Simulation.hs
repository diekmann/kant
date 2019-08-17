{-# LANGUAGE FlexibleContexts  #-}
--TODO can I do without FlexibleContexts?

module Simulation where

import qualified Gesetz as G
import qualified Handlung as H
import qualified Kant

import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen


data Optionen person world a b = Optionen {
    person :: person, -- handelnde Person

    moeglich :: H.Handlung world -> Bool, -- Ist eine Handlung möglich?
    
    maxime :: Kant.Maxime person world,
    allgemeines_gesetz_ableiten :: Kant.AllgemeinesGesetzAbleiten world a b
}


-- simulate one HandlungF
simulateHandlungF :: (Ord a, Ord b) => (Enum person, Bounded person) => (Eq world) =>
  Optionen person world a b
  -> H.HandlungF person world       -- Beabsichtigte Handlung
  -> world                          -- Initialwelt.
  -> G.Gesetz Integer a b             -- Initialgesetz
  -> (world, G.Gesetz Integer a b)
simulateHandlungF so h welt g | not ((moeglich so) (H.handeln (person so) welt h)) = (welt, g)
simulateHandlungF so h welt g =
  let (sollensanordnung, g') = Kant.kategorischer_imperativ (person so) welt h (maxime so ) (allgemeines_gesetz_ableiten so) g in
  let w' = (if sollensanordnung == G.Erlaubnis && ((moeglich so) (H.handeln (person so) welt h))
            then
              H.nachher (H.handeln (person so) welt h)
            else
              welt
           ) in
  (w', g')


-- simulate one HandlungF
simulateOne :: (Ord a, Ord b) => (Enum person, Bounded person) => (Eq world) =>
  Optionen person world a b
  -> Int                            -- maximale Anzahl Iterationen (Simulationen)
  -> H.HandlungF person world       -- Beabsichtigte Handlung
  -> world                          -- Initialwelt.
  -> G.Gesetz Integer a b             -- Initialgesetz
  -> G.Gesetz Integer a b
simulateOne _  i _ _    g | i <= 0 = g -- iteration vorbei
simulateOne so i h welt g =
  let (w', g') = simulateHandlungF so h welt g in
  if welt == w' then
    g'
  else
    simulateOne so (i-1) h w' g'


gesetzbuch_generator :: (Ord a, Ord b) => (Enum person, Bounded person) => (Eq world) =>
  (Arbitrary (H.HandlungF person world)) =>
  Optionen person world a b
  -> Int
  -> world
  -> G.Gesetz Integer a b
  -> Gen (G.Gesetz Integer a b)
-- TODO: liste mit Historie was passiert ist und zu welchem Gesetz fuehrte.
gesetzbuch_generator _  i _    g | i <= 0 = return g
gesetzbuch_generator so i welt g = do
    h <- arbitrary
    let (w', g') = simulateHandlungF so h welt g
    gesetzbuch_generator so (i-1) w' g'

gesetzbuch_inferieren so welt = generate $ gesetzbuch_generator so 10 welt G.leer
