module Kant where

import qualified Gesetz as G
import qualified Handlung as H


-- Beschreibt ob eine Handlung in einer gegebenen Welt gut ist.
-- Passt nicht so ganz auf die Definition von Maxime?
newtype Maxime person world = Maxime (world -> H.Handlung person world -> Bool)
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
    person                      -- handelnde Person
    -> world                    -- Die Welt in ihrem aktuellen Zustand
    -> H.Handlung person world  -- Eine mögliche Handlung, über die wir entscheiden wollen ob wir sie ausführen sollten.
    -> Maxime person world  -- Persönliche Ethik?
    -> (world -> world -> G.Sollensanordnung -> G.Rechtsnorm a b) -- allgemeines Gesetz ableiten. TODO: so wird das nicht allgemein.
    -> G.Gesetz Integer a b      -- Allgemeines Gesetz (für alle Menschen)
    -- Ergebnis:
    -> (G.Sollensanordnung, -- Sollen wir die Handlung ausführen?
        G.Gesetz Integer a b)       -- Soll das allgemeine Gesetz entsprechend angepasst werden?
    --TODO: Wenn unsere Maximen perfekt und die Maximen aller Menschen konsisten sind, soll das Gesetz nur erweitert werden (append only)?
kategorischer_imperativ ich welt handlung maxime gesetz_ableiten gesetz =
    -- Es fehlt: ich muss nach allgemeinem Gesetz handeln. Wenn das Gesetz meinen Fall nicht abdeckt, dann muss meine Maxime zum Gesetz erhoben werden.
    -- Es fehlt: Wollen. Was will will? Was WILL ich für ein allgemeines Gesetz? Es soll für ALLE Menschen fair und gerecht sein.
    let Maxime bewerten = maxime in
    let soll_handeln = (if bewerten welt handlung then
          --Wenn (bewerten handlung) für alle Menschen True ist muss es ein Gebot werden?
          G.Erlaubnis
        else
          --Nur ein Verbot wenn (bewerten handlung) für alle Menschen False ist.
          G.Verbot) in
    --TODO gesetz erweitern, für alle Welten?
    (soll_handeln, add (gesetz_ableiten welt (H.handeln ich welt handlung) soll_handeln) gesetz)
      where add rn g = G.hinzufuegen rn g

beispiel_kategorischer_imperativ = kategorischer_imperativ "ich" 0 (H.Handlung (\_ n-> n+1)) maxime_mir_ist_alles_recht G.case_law_ableiten G.leer
