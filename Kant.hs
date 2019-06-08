{-# LANGUAGE ScopedTypeVariables #-}

module Kant where

import qualified Gesetz as G
import qualified Handlung as H

-- Beschreibt ob eine Handlung in einer gegebenen Welt gut ist.
-- Passt nicht so ganz auf die Definition von Maxime?
-- TODO: ich sollte Maxime als axiom betrachten.
newtype Maxime person world = Maxime (person -> H.Handlung world -> Bool)
--                                    ich    -> Auswirkung       -> gut/böse

-- Beispiel
maxime_mir_ist_alles_recht = Maxime (\_ _ -> True)

-- TODO: in einer Maxime darf keine konkrete Person hardcoded sein.
-- Verboten: Maxime (\ich _ -> if ich == "konkrete Person" then ...)


-- Wir testen:
--   * Was wenn jeder so handeln würde?
--   * Was wenn jeder diese maxime hätte? Bsp: stehlen und bestohlen werden.
-- Faktisch: Kreuzprodukt Bevölkerung x Bevölkerung,
--           wobei jeder einmal als handelnde Person auftritt
--           und einmal als betroffene Person (durch Auswertung der Maxime).
teste_maxime :: forall person world. (Enum person, Bounded person) =>
  world                       -- Welt in ihrem aktuellen Zustand
  -> H.HandlungF person world -- Zu untersuchende Handlung
  -> Maxime person world
  -> Bool
teste_maxime welt handlung (Maxime maxime) =
  all was_wenn_jeder_so_handelt_aus_sicht_von bevoelkerung
    where
      bevoelkerung :: [person]
      bevoelkerung = [minBound..maxBound]

      wenn_jeder_so_handelt :: [H.Handlung world]
      wenn_jeder_so_handelt = [H.handeln handelnde_person welt handlung
                               | handelnde_person <- bevoelkerung]

      was_wenn_jeder_so_handelt_aus_sicht_von :: person -> Bool
      was_wenn_jeder_so_handelt_aus_sicht_von betroffene_person =
        all (maxime betroffene_person) wenn_jeder_so_handelt


-- Versuch ein allgemeines Gesetz abzuleiten:
-- TODO: Nur aus einer von außen betrachteten Handlung
--       und einer Entscheidung ob diese Handlung ausgeführt werden soll
--       wird es schwer ein allgemeines Gesetz abzuleiten.
type AllgemeinesGesetzAbleiten world a b =
  H.Handlung world -> G.Sollensanordnung -> G.Rechtsnorm a b

-- Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
-- dass sie ein allgemeines Gesetz werde.
-- TODO: unterstütze viele Maximen, wobei manche nicht zutreffen können?
kategorischer_imperativ ::
  Ord a => Ord b =>
  Enum person => Bounded person =>
  person                       -- handelnde Person
  -> world                     -- Die Welt in ihrem aktuellen Zustand
  -> H.HandlungF person world  -- Eine mögliche Handlung,
                               -- über die wir entscheiden wollen ob wir sie ausführen sollten.
  -> Maxime person world       -- Persönliche Ethik?
  -> AllgemeinesGesetzAbleiten world a b -- (wenn man keinen Plan hat wie man sowas implementiert,
                                         --  einfach als Eingabe annehmen)
  -> G.Gesetz Integer a b      -- Allgemeines Gesetz (für alle Menschen)
  -- Ergebnis:
  -> (G.Sollensanordnung,    -- Sollen wir die Handlung ausführen?
      G.Gesetz Integer a b)  -- Soll das allgemeine Gesetz entsprechend angepasst werden?
  --TODO: Wenn unsere Maximen perfekt und die Maximen aller Menschen konsisten sind,
  --      soll das Gesetz nur erweitert werden.
kategorischer_imperativ ich welt handlung maxime gesetz_ableiten gesetz =
  -- Es fehlt: ich muss nach allgemeinem Gesetz handeln.
  --           Wenn das Gesetz meinen Fall nicht abdeckt,
  --           dann muss meine Maxime zum Gesetz erhoben werden.
  -- Es fehlt: "Wollen"
  -- TODO: Wir unterstützen nur Erlaubnis/Verbot.
  let soll_handeln = if teste_maxime welt handlung maxime
                     then
                       G.Erlaubnis
                     else
                       G.Verbot in
  (
    soll_handeln,
    G.hinzufuegen (gesetz_ableiten (H.handeln ich welt handlung) soll_handeln) gesetz
  )


beispiel_kategorischer_imperativ =
  kategorischer_imperativ
    ()  -- ich  (ein Bounded type der nicht so groß ist)
    0   -- Welt
    (H.HandlungF (\_ n-> n+1)) -- die Welt inkrementieren
    maxime_mir_ist_alles_recht
    (\_ _ -> G.Rechtsnorm (G.Tatbestand "tb") (G.Rechtsfolge "yolo")) -- AllgemeinesGesetzAbleiten
    G.leer

