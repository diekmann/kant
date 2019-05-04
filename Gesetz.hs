module Gesetz where

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

leer :: Gesetz a b
leer = Gesetz S.empty

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

hinzufuegen :: Ord a => Ord b => Paragraph -> Rechtsnorm a b -> Gesetz a b -> Gesetz a b
hinzufuegen p rn (Gesetz g) = Gesetz $ S.insert (p, rn) g


-- ob eine Handlung ausgeführt werden muss, darf, kann, nicht muss.
data Sollensanordnung = Gebot | Verbot | Erlaubnis | Freistellung
  deriving (Eq, Ord, Show, Enum)


-- Gesetz beschreibt: (wenn vorher, wenn nachher) dann Erlaubt/Verboten, wobei vorher/nachher die Welt beschreiben.
type CaseLaw world = Gesetz (world, world) Sollensanordnung

-- uebertraegt einen Tatbestand woertlich als Erlaubnis ins Gesetz
case_law_ableiten :: w -> w -> Rechtsnorm (w, w) Sollensanordnung
case_law_ableiten vorher nachher = Rechtsnorm (Tatbestand (vorher, nachher)) (Rechtsfolge Erlaubnis)

show_CaseLaw :: Show w => CaseLaw w -> String
show_CaseLaw (Gesetz g) = S.foldl (\s p-> s ++ show_paragraph p ++ "; ") "" g
  where
    show_paragraph (Paragraph p, rechtsnorm) = p ++ ": " ++ show_rechtsnorm rechtsnorm
    show_rechtsnorm (Rechtsnorm (Tatbestand (a,b)) (Rechtsfolge f)) = "Wenn die welt " ++ show a ++ " ist und wir die welt nach " ++
                                                                       show b ++ " aendern wollen, dann " ++ show f

