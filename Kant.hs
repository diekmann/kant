{-# LANGUAGE ScopedTypeVariables #-}

module Kant where

import qualified Gesetz as G
import qualified Handlung as H

-- Beschreibt ob eine Handlung in einer gegebenen Welt gut ist.
-- Passt nicht so ganz auf die Definition von Maxime?
-- TODO: ich sollte Maxime als axiom betrachten.
-- TODO: in einer maxime darf keine konkrete Person hardcoded sein.
newtype Maxime person world = Maxime (person -> H.Handlung world -> Bool)
--TODO: Maxime

maxime_mir_ist_alles_recht = Maxime (\_ _ -> True)

-- Verboten: Maxime (\ich _ -> if ich == "konkrete Person" then ...)

-- Wir testen: was wenn jeder so handeln wuerde.
-- TODO: was wenn jeder diese maxime haette? Betroffene Person. Bsp: stehlen und bestohlen werden.
teste_maxime :: forall person world. Enum person => Bounded person => world -> H.HandlungF person world -> Maxime person world -> Bool
teste_maxime welt handlung (Maxime maxime) = all was_wenn_jeder_so_handelt_aus_sicht_von bevoelkerung
    where
      bevoelkerung :: [person]
      bevoelkerung = [minBound..maxBound]

      wenn_jeder_so_handelt :: [H.Handlung world]
      wenn_jeder_so_handelt = [H.handeln handelnde_person welt handlung | handelnde_person <- bevoelkerung]

      was_wenn_jeder_so_handelt_aus_sicht_von :: person -> Bool
      was_wenn_jeder_so_handelt_aus_sicht_von betroffene_person = all (maxime betroffene_person) wenn_jeder_so_handelt


--TODO: Name passt nicht ganz
--verallgemeinern :: Maxime world -> S.Set (Rechtsnorm a b)
--verallgemeinern = undefined

--type gesetz_ableiten = world -> world -> Rechtsnorm a b


-- uebertraegt einen Tatbestand woertlich ins Gesetz
case_law_ableiten :: H.Handlung world -> G.Sollensanordnung -> G.Rechtsnorm (world, world) G.Sollensanordnung
case_law_ableiten (H.Handlung vorher nachher) erlaubt = G.Rechtsnorm (G.Tatbestand (vorher, nachher)) (G.Rechtsfolge erlaubt)

-- Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst, dass sie ein allgemeines Gesetz werde.
-- TODO unterstütze viele Maximen, wobei manche nicht zutreffen können?
kategorischer_imperativ ::
    Ord a => Ord b =>
    Enum person => Bounded person =>
    person                       -- handelnde Person
    -> world                     -- Die Welt in ihrem aktuellen Zustand
    -> H.HandlungF person world  -- Eine mögliche Handlung, über die wir entscheiden wollen ob wir sie ausführen sollten.
    -> Maxime person world  -- Persönliche Ethik?
    -> (H.Handlung world -> G.Sollensanordnung -> G.Rechtsnorm a b) -- allgemeines Gesetz ableiten. TODO: so wird das nicht allgemein.
    -> G.Gesetz Integer a b      -- Allgemeines Gesetz (für alle Menschen)
    -- Ergebnis:
    -> (G.Sollensanordnung, -- Sollen wir die Handlung ausführen?
        G.Gesetz Integer a b)       -- Soll das allgemeine Gesetz entsprechend angepasst werden?
    --TODO: Wenn unsere Maximen perfekt und die Maximen aller Menschen konsisten sind, soll das Gesetz nur erweitert werden (append only)?
kategorischer_imperativ ich welt handlung maxime gesetz_ableiten gesetz =
    -- Es fehlt: ich muss nach allgemeinem Gesetz handeln. Wenn das Gesetz meinen Fall nicht abdeckt, dann muss meine Maxime zum Gesetz erhoben werden.
    -- Es fehlt: Wollen. Was will will? Was WILL ich für ein allgemeines Gesetz? Es soll für ALLE Menschen fair und gerecht sein.
    let soll_handeln = (if teste_maxime welt handlung maxime then
          --Wenn (bewerten handlung) für alle Menschen True ist muss es ein Gebot werden?
          G.Erlaubnis
        else
          --Nur ein Verbot wenn (bewerten handlung) für alle Menschen False ist.
          G.Verbot) in
    --TODO gesetz erweitern, für alle Welten?
    --TODO gesetz muss fuer alle gelten!
    (soll_handeln, add (gesetz_ableiten (H.handeln ich welt handlung) soll_handeln) gesetz)
      where add rn g = G.hinzufuegen rn g

beispiel_kategorischer_imperativ = kategorischer_imperativ 'I' 0 (H.HandlungF (\_ n-> n+1)) maxime_mir_ist_alles_recht case_law_ableiten G.leer
