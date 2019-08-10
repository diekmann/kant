module Simulation where

import Gesetz
import qualified Handlung as H
import qualified Kant


data Optionen person world a b = Optionen {
    person :: person, -- handelnde Person

    moeglich :: H.Handlung world -> Bool, -- Ist eine Handlung möglich?
    
    maxime :: Kant.Maxime person world,
    allgemeines_gesetz_ableiten :: Kant.AllgemeinesGesetzAbleiten world a b
}


--TODO:handlung arbitrary

-- simulate one HandlungF
simulateOne :: (Ord a, Ord b) => (Enum person, Bounded person) => (Eq world) =>
  Optionen person world a b
  -> Int                            -- maximale Anzahl Iterationen (Simulationen)
  -> H.HandlungF person world       -- Beabsichtigte Handlung
  -> world                          -- Initialwelt.
  -> Gesetz Integer a b             -- Initialgesetz
  -> Gesetz Integer a b
-- liste mit Historie was passiert ist und zu welchem Gesetz fuehrte.
simulateOne _  i _ _    g | i <= 0 = g -- iteration vorbei
simulateOne so _ h welt g | not ((moeglich so) (H.handeln (person so) welt h)) = g
simulateOne so i h welt g =
  let (sollensanordnung, g') = Kant.kategorischer_imperativ (person so) welt h (maxime so ) (allgemeines_gesetz_ableiten so) g in
  let w' = (if sollensanordnung == Erlaubnis && ((moeglich so) (H.handeln (person so) welt h))
            then
              H.nachher (H.handeln (person so) welt h)
            else
              welt
           ) in
  if welt == w' then
    g'
  else
    simulateOne so (i-1) h w' g'
