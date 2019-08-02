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
--   * Was if everyone would judge by that maxime?
--     Example: robbing - potentially good for the thief
--                        but the thief would not like to be the victim.
-- Essentially: cross-product       Population x Population
--              where each person   acts       x is affected
teste_maxime :: forall person world. (Enum person, Bounded person) =>
  world                       -- Welt in ihrem aktuellen Zustand
  -> A.ActionF person world -- Zu untersuchende Action
  -> Maxime person world
  -> Bool
teste_maxime welt handlung (Maxime maxime) =
  all was_wenn_jeder_so_handelt_aus_sicht_von bevoelkerung
    where
      bevoelkerung :: [person]
      bevoelkerung = [minBound..maxBound]

      wenn_jeder_so_handelt :: [A.Action world]
      wenn_jeder_so_handelt = [A.act acting_person welt handlung
                               | acting_person <- bevoelkerung]

      was_wenn_jeder_so_handelt_aus_sicht_von :: person -> Bool
      was_wenn_jeder_so_handelt_aus_sicht_von betroffene_person =
        all (maxime betroffene_person) wenn_jeder_so_handelt


-- Versuch ein allgemeines Gesetz abzuleiten:
-- TODO: Nur aus einer von außen betrachteten Action
--       und einer Entscheidung ob diese Action ausgeführt werden soll
--       wird es schwer ein allgemeines Gesetz abzuleiten.
type AllgemeinesGesetzAbleiten world a b =
  A.Action world -> G.Sollensanordnung -> G.Rechtsnorm a b

-- Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
-- dass sie ein allgemeines Gesetz werde.
-- TODO: unterstütze viele Maximen, wobei manche nicht zutreffen können?
kategorischer_imperativ ::
  Ord a => Ord b =>
  Enum person => Bounded person =>
  person                       -- actde Person
  -> world                     -- Die Welt in ihrem aktuellen Zustand
  -> A.ActionF person world  -- Eine mögliche Action,
                               -- über die wir entscheiden wollen ob wir sie ausführen sollten.
  -> Maxime person world       -- Persönliche Ethik?
  -> AllgemeinesGesetzAbleiten world a b -- (wenn man keinen Plan hat wie man sowas implementiert,
                                         --  einfach als Eingabe annehmen)
  -> G.Gesetz Integer a b      -- Allgemeines Gesetz (für alle Menschen)
  -- Ergebnis:
  -> (G.Sollensanordnung,    -- Sollen wir die Action ausführen?
      G.Gesetz Integer a b)  -- Soll das allgemeine Gesetz entsprechend angepasst werden?
  --TODO: Wenn unsere Maximen perfekt und die Maximen aller Menschen konsisten sind,
  --      soll das Gesetz nur erweitert werden.
kategorischer_imperativ ich welt handlung maxime gesetz_ableiten gesetz =
  -- Es fehlt: "Wollen"
  -- TODO: Wir unterstützen nur Erlaubnis/Verbot.
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

