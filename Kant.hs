{-# LANGUAGE ScopedTypeVariables #-}

module Kant where

import qualified Gesetz as G
import qualified Action as A

-- Describes if an Action (for a given world) is good or bad.
-- Personal ethics.
newtype Maxime person world = Maxime (person -> A.Action world -> Bool)
--                                    I (me) -> Impact         -> good/bad


-- Beispiel
maxime_mir_ist_alles_recht = Maxime (\_ _ -> True)

-- TODO: in einer Maxime darf keine konkrete Person hardcoded sein.
-- Verboten: Maxime (\ich _ -> if ich == "konkrete Person" then ...)


-- We test:
--   * What if everyone would act like this?
--   * What if everyone would judge by that maxime?
--     Example: robbing - potentially good for the thief
--                        but the thief would not like to be the victim.
-- Essentially: cross-product       Population x Population
--              where each person   acts       x is affected
teste_maxime :: forall person world. (Enum person, Bounded person) =>
  world                       -- World in its current state
  -> A.ActionF person world   -- Action we judge
  -> Maxime person world
  -> Bool
teste_maxime world action (Maxime maxime) =
  all being_affected population
    where
      population :: [person]
      population = [minBound..maxBound]

      everyone_acts :: [A.Action world]
      everyone_acts = [A.act acting_person world action | acting_person <- population]

      being_affected :: person -> Bool
      being_affected affected_person = all (maxime affected_person) everyone_acts


-- Deriving a universal law.
type AllgemeinesGesetzAbleiten world a b =
  A.Action world -> G.Sollensanordnung -> G.Rechtsnorm a b

-- Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
-- dass sie ein allgemeines Gesetz werde.
kategorischer_imperativ ::
  Ord a => Ord b =>
  Enum person => Bounded person =>
  person                       -- acting Person
  -> world                     -- current state of the world
  -> A.ActionF person world    -- action we examine
  -> Maxime person world       -- personal ethics
  -> AllgemeinesGesetzAbleiten world a b
  -> G.Gesetz Integer a b
  -- Result
  -> (G.Sollensanordnung,    -- Are we allowed to act?
      G.Gesetz Integer a b)  -- Updated law.
kategorischer_imperativ ich welt handlung maxime gesetz_ableiten gesetz =
  -- TODO: missing "will"
  -- TODO: only Erlaubnis/Verbot support.
  let should_act = if teste_maxime welt handlung maxime
                     then
                       G.Erlaubnis
                     else
                       G.Verbot in
  (
    should_act,
    G.hinzufuegen (gesetz_ableiten (A.act ich welt handlung) should_act) gesetz
  )


beispiel_kategorischer_imperativ =
  kategorischer_imperativ
    ()  -- ich  (ein Bounded type der nicht so groß ist)
    0   -- Welt
    (A.ActionF (\_ n-> n+1)) -- die Welt inkrementieren
    maxime_mir_ist_alles_recht
    (\_ _ -> G.Rechtsnorm (G.Tatbestand "tb") (G.Rechtsfolge "yolo")) -- AllgemeinesGesetzAbleiten
    G.leer

