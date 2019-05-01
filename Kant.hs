module Kant where

import qualified Data.Set as S

newtype Tatbestand = Tatbestand String
  deriving (Eq, Ord, Show)
newtype Rechtsfolge = Rechtsfolge String
  deriving (Eq, Ord, Show)

newtype Rechtsnorm = Rechtsnorm (Tatbestand, Rechtsfolge)
  deriving (Eq, Ord, Show)

newtype Paragraph = Paragraph String
  deriving (Eq, Ord, Show)

newtype Gesetz = Gesetz (S.Set (Paragraph, Rechtsnorm))
  deriving (Eq, Ord, Show)

-- https://de.wikipedia.org/wiki/Rechtsfolge
beispiel_gesetz = Gesetz $ S.fromList [
  (Paragraph "§ 823 BGB",
   Rechtsnorm
     (Tatbestand "Wer vorsätzlich oder fahrlässig das Leben, den Körper, die Gesundheit, (...), das Eigentum oder (...) eines anderen widerrechtlich verletzt,",
      Rechtsfolge "ist dem anderen zum Ersatz des daraus entstehenden Schadens verpflichtet."
     )
  ),
  (Paragraph "§ 985 BGB",
   Rechtsnorm
     (Tatbestand "Der Eigentümer einer Sache kann von dem Besitzer",
      Rechtsfolge "die Herausgabe der Sache verlangen"
     )
  ),
  (Paragraph "§ 303 StGB",
   Rechtsnorm
     (Tatbestand "Wer rechtswidrig eine fremde Sache beschädigt oder zerstört,",
      Rechtsfolge "wird mit Freiheitsstrafe bis zu zwei Jahren oder mit Geldstrafe bestraft."
     )
  )
  ]

-- Beschreibt eine Handlung als Änderung der Welt.
newtype Handlung world = Handlung (world -> world)

-- ob eine Handlung ausgeführt werden muss, darf, kann, nicht muss.
data Sollensanordnung = Gebot | Verbot | Erlaubnis | Freistellung
  deriving (Eq, Ord, Show, Enum)

newtype Maxime world = Maxime (Handlung world -> Bool)

maxime_mir_ist_alles_recht = Maxime (\_ -> True)

--TODO: Name passt nicht ganz
verallgemeinern :: Maxime world -> S.Set Rechtsnorm
verallgemeinern = undefined

-- Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst, dass sie ein allgemeines Gesetz werde.
-- TODO nterstütze viele Maximen, wobei manche nicht zutreffen können?
kategorischer_imperativ :: 
    Handlung world  -- Eine mögliche Handlung, über die wir entscheiden wollen ob wir sie ausführen sollten.
    -> Maxime world -- Persönliche Ethik?
    -> Gesetz       -- Allgemeines Gesetz (für alle Menschen)
    -- Ergebnis:
    -> (Sollensanordnung, -- Sollen wir die Handlung ausführen?
        Gesetz)           -- Soll das allgemeine Gesetz entsprechend angepasst werden?
    --TODO: Wenn unsere Maximen perfekt und die Maximen aller Menschen konsisten sind, soll das Gesetz nur erweitert werden (append only)?
kategorischer_imperativ handlung maxime gesetz =
    let Maxime bewerten = maxime in
    if bewerten handlung then
        --TODO gesetz erweitern
        --Wenn (bewerten handlung) für alle Menschen True ist muss es ein Gebot werden?
        (Erlaubnis, gesetz)
    else
        --Nur ein Verbot wenn (bewerten handlung) für alle Menschen False ist.
        (Verbot, gesetz)

beispiel_kategorischer_imperativ = kategorischer_imperativ (Handlung (\n-> n+1)) maxime_mir_ist_alles_recht beispiel_gesetz
