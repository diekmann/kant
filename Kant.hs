module Kant where

import qualified Gesetz as G

-- Beschreibt Handlungen als Änderung der Welt.
newtype Handlung world = Handlung (world -> world)

handeln :: world -> Handlung world -> world
handeln welt (Handlung h) = h welt

-- Beispiel, für eine Welt die nur aus einer Zahl besteht.
-- Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
beispiel_handlung = Handlung $ \n -> if n < 9000 then n+1 else n

-- Beschreibt ob eine Handlung in einer gegebenen Welt gut ist.
-- Passt nicht so ganz auf die Definition von Maxime?
newtype Maxime world = Maxime (world -> Handlung world -> Bool)
--TODO: Maxime

maxime_mir_ist_alles_recht = Maxime (\_ _ -> True)

--TODO: Name passt nicht ganz
--verallgemeinern :: Maxime world -> S.Set (Rechtsnorm a b)
--verallgemeinern = undefined

--type gesetz_ableiten = world -> world -> Rechtsnorm a b

-- Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst, dass sie ein allgemeines Gesetz werde.
-- TODO unterstütze viele Maximen, wobei manche nicht zutreffen können?
kategorischer_imperativ ::
    Ord a => Ord b =>
    world              -- Die Welt in ihrem aktuellen Zustand
    -> Handlung world  -- Eine mögliche Handlung, über die wir entscheiden wollen ob wir sie ausführen sollten.
    -> Maxime world    -- Persönliche Ethik?
    -> (world -> world -> G.Rechtsnorm a b) -- allgemeines Gesetz ableiten. TODO: so wird das nicht allgemein.
    -> G.Gesetz a b      -- Allgemeines Gesetz (für alle Menschen)
    -- Ergebnis:
    -> (G.Sollensanordnung, -- Sollen wir die Handlung ausführen?
        G.Gesetz a b)       -- Soll das allgemeine Gesetz entsprechend angepasst werden?
    --TODO: Wenn unsere Maximen perfekt und die Maximen aller Menschen konsisten sind, soll das Gesetz nur erweitert werden (append only)?
kategorischer_imperativ welt handlung maxime gesetz_ableiten gesetz =
    -- Es fehlt: ich muss nach allgemeinem Gesetz handeln. Wenn das Gesetz meinen Fall nicht abdeckt, dann muss meine Maxime zum Gesetz erhoben werden.
    -- Es fehlt: Wollen. Was will will? Was WILL ich für ein allgemeines Gesetz? Es soll für ALLE Menschen fair und gerecht sein.
    let Maxime bewerten = maxime in
    if bewerten welt handlung then
        --TODO gesetz erweitern, für alle Welten?
        --Wenn (bewerten handlung) für alle Menschen True ist muss es ein Gebot werden?
        (G.Erlaubnis, add (gesetz_ableiten welt (handeln welt handlung)) gesetz)
    else
        --Nur ein Verbot wenn (bewerten handlung) für alle Menschen False ist.
        (G.Verbot, gesetz)
      where add rn g = G.hinzufuegen (G.Paragraph "0") rn g

beispiel_kategorischer_imperativ = kategorischer_imperativ 0 (Handlung (\n-> n+1)) maxime_mir_ist_alles_recht G.case_law_ableiten G.leer
