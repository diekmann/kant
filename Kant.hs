module Kant where

import qualified Data.Set as S

newtype Tatbestand a = Tatbestand a
  deriving (Eq, Ord, Show)
newtype Rechtsfolge a = Rechtsfolge a
  deriving (Eq, Ord, Show)

data Rechtsnorm a b = Rechtsnorm (Tatbestand a) (Rechtsfolge b)
  deriving (Eq, Ord, Show)

newtype Paragraph = Paragraph String
  deriving (Eq, Ord, Show)

newtype Gesetz a b = Gesetz (S.Set (Paragraph, Rechtsnorm a b))
  deriving (Eq, Ord, Show)

-- https://de.wikipedia.org/wiki/Rechtsfolge
beispiel_gesetz :: Gesetz String String
beispiel_gesetz = Gesetz $ S.fromList [
  (Paragraph "§ 823 BGB",
   Rechtsnorm
     (Tatbestand "Wer vorsätzlich oder fahrlässig das Leben, den Körper, die Gesundheit, (...), das Eigentum oder (...) eines anderen widerrechtlich verletzt,")
     (Rechtsfolge "ist dem anderen zum Ersatz des daraus entstehenden Schadens verpflichtet.")
  ),
  (Paragraph "§ 985 BGB",
   Rechtsnorm
     (Tatbestand "Der Eigentümer einer Sache kann von dem Besitzer")
     (Rechtsfolge "die Herausgabe der Sache verlangen")
  ),
  (Paragraph "§ 303 StGB",
   Rechtsnorm
     (Tatbestand "Wer rechtswidrig eine fremde Sache beschädigt oder zerstört,")
     (Rechtsfolge "wird mit Freiheitsstrafe bis zu zwei Jahren oder mit Geldstrafe bestraft.")
  )
  ]

-- Beschreibt Handlungen als Änderung der Welt.
newtype Handlung world = Handlung (world -> world)

handeln :: world -> Handlung world -> world
handeln welt (Handlung h) = h welt

-- Beispiel, für eine Welt die nur aus einer Zahl besteht.
-- Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
beispiel_handlung = Handlung $ \n -> if n < 9000 then n+1 else n

-- ob eine Handlung ausgeführt werden muss, darf, kann, nicht muss.
data Sollensanordnung = Gebot | Verbot | Erlaubnis | Freistellung
  deriving (Eq, Ord, Show, Enum)

-- Beschreibt ob eine Handlung in einer gegebenen Welt gut ist.
-- Passt nicht so ganz auf die Definition von Maxime?
newtype Maxime world = Maxime (world -> Handlung world -> Bool)
--TODO: Maxime

maxime_mir_ist_alles_recht = Maxime (\_ _ -> True)

--TODO: Name passt nicht ganz
--verallgemeinern :: Maxime world -> S.Set (Rechtsnorm a b)
--verallgemeinern = undefined


-- Wenn die welt nur eine Zahl ist, ...
-- Resourcen sind endlich.
data Zahlenwelt = Zahlenwelt Integer -- verbleibendResourcen
                             Integer -- welt
  deriving (Eq, Ord, Show)

zahl :: Zahlenwelt -> Integer
zahl (Zahlenwelt _ i) = i

abbauen :: Integer -> Zahlenwelt -> Zahlenwelt
abbauen i (Zahlenwelt verbleibend w) | verbleibend-i > 0 = Zahlenwelt (verbleibend-i) (w+i)
abbauen _ w = w -- Welt ist verbraucht. 

fortschritt :: Zahlenwelt -> Zahlenwelt -> Bool
fortschritt (Zahlenwelt _ w1) (Zahlenwelt _ w2) = w2 > w1

-- Eigentlich wollen wir Fortschritt in ALLEN möglichen Welten.
maxime_zahlenfortschritt = Maxime $ \w (Handlung h) -> fortschritt w (h w)

type CaseLaw world = Gesetz (world, world) (Sollensanordnung)

show_CaseLaw :: Show world => CaseLaw world -> String
show_CaseLaw (Gesetz g) = S.foldl (\s p-> s ++ show_paragraph p ++ "; ") "" g
  where
    show_paragraph (Paragraph p, rechtsnorm) = p ++ ": " ++ show_rechtsnorm rechtsnorm
    show_rechtsnorm (Rechtsnorm (Tatbestand (a,b)) (Rechtsfolge f)) = "Wenn die welt " ++ show a ++ " ist und wir die welt nach " ++
                                                                       show b ++ " aendern wollen, dann " ++ show f

zahlengesetz_beispiel :: CaseLaw Zahlenwelt
zahlengesetz_beispiel = Gesetz $ S.singleton ((Paragraph "Paragraph 42"), (Rechtsnorm (Tatbestand (Zahlenwelt 0 1, Zahlenwelt 0 2)) (Rechtsfolge Verbot)))

--type gesetz_ableiten = world -> world -> Rechtsnorm a b

-- Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst, dass sie ein allgemeines Gesetz werde.
-- TODO unterstütze viele Maximen, wobei manche nicht zutreffen können?
kategorischer_imperativ ::
    Ord a => Ord b =>
    world              -- Die Welt in ihrem aktuellen Zustand
    -> Handlung world  -- Eine mögliche Handlung, über die wir entscheiden wollen ob wir sie ausführen sollten.
    -> Maxime world    -- Persönliche Ethik?
    -> (world -> world -> Rechtsnorm a b)
    -> Gesetz a b      -- Allgemeines Gesetz (für alle Menschen)
    -- Ergebnis:
    -> (Sollensanordnung, -- Sollen wir die Handlung ausführen?
        Gesetz a b)       -- Soll das allgemeine Gesetz entsprechend angepasst werden?
    --TODO: Wenn unsere Maximen perfekt und die Maximen aller Menschen konsisten sind, soll das Gesetz nur erweitert werden (append only)?
kategorischer_imperativ welt handlung maxime gesetz_ableiten gesetz =
    -- Es fehlt: ich muss nach allgemeinem Gesetz handeln. Wenn das Gesetz meinen Fall nicht abdeckt, dann muss meine Maxime zum Gesetz erhoben werden.
    -- Es fehlt: Wollen. Was will will? Was WILL ich für ein allgemeines Gesetz? Es soll für ALLE Menschen fair und gerecht sein.
    let Maxime bewerten = maxime in
    if bewerten welt handlung then
        --TODO gesetz erweitern, für alle Welten?
        --Wenn (bewerten handlung) für alle Menschen True ist muss es ein Gebot werden?
        (Erlaubnis, add (gesetz_ableiten welt (handeln welt handlung)) gesetz)
    else
        --Nur ein Verbot wenn (bewerten handlung) für alle Menschen False ist.
        (Verbot, gesetz)
      where add rn (Gesetz g) = Gesetz $ S.insert (Paragraph "0", rn) g

case_law_ableiten w1 w2 = Rechtsnorm (Tatbestand (w1, w2)) (Rechtsfolge Erlaubnis)

beispiel_kategorischer_imperativ = kategorischer_imperativ 0 (Handlung (\n-> n+1)) maxime_mir_ist_alles_recht case_law_ableiten (Gesetz S.empty)
beispiel2_kategorischer_imperativ = kategorischer_imperativ (Zahlenwelt 9000 0) (Handlung (abbauen 5)) maxime_zahlenfortschritt case_law_ableiten (Gesetz S.empty)
