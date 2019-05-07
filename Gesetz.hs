module Gesetz where

import qualified Data.Set as S

newtype Tatbestand a = Tatbestand a
  deriving (Eq, Ord, Show)
newtype Rechtsfolge a = Rechtsfolge a
  deriving (Eq, Ord, Show)

data Rechtsnorm a b = Rechtsnorm (Tatbestand a) (Rechtsfolge b)
  deriving (Eq, Ord, Show)

newtype Paragraph p = Paragraph p
  deriving (Eq, Ord, Show)

newtype Gesetz p a b = Gesetz (S.Set (Paragraph p, Rechtsnorm a b))
  deriving (Eq, Ord, Show)

leer :: Gesetz p a b
leer = Gesetz S.empty

-- https://de.wikipedia.org/wiki/Rechtsfolge
beispiel_gesetz :: Gesetz String String String
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

neuer_paragraph :: Gesetz Integer a b -> Paragraph Integer
neuer_paragraph (Gesetz g) = let ps = S.map (\ (Paragraph i, _) -> i) g;
                                 max = S.findMax ps in
                             Paragraph (max+1)

-- Fuegt eine Rechtsnorm als neuen Paragraphen hinzu.
hinzufuegen :: Ord a => Ord b => Rechtsnorm a b -> Gesetz Integer a b -> Gesetz Integer a b
hinzufuegen rn (Gesetz g) | S.member rn rechtsnormen = Gesetz g -- Rechtsnorm existiert bereits
    where rechtsnormen = S.map snd g
hinzufuegen rn (Gesetz g) = Gesetz $ S.insert (neuer_paragraph (Gesetz g), rn) g


-- ob eine Handlung ausgeführt werden muss, darf, kann, nicht muss.
data Sollensanordnung = Gebot | Verbot | Erlaubnis | Freistellung
  deriving (Eq, Ord, Show, Enum)


-- Gesetz beschreibt: (wenn vorher, wenn nachher) dann Erlaubt/Verboten, wobei vorher/nachher die Welt beschreiben.
-- Paragraphen sind einfach Integer
type CaseLaw world = Gesetz Integer (world, world) Sollensanordnung

show_CaseLaw :: Show w => CaseLaw w -> String
show_CaseLaw (Gesetz g) = S.foldl (\s p-> s ++ show_paragraph p ++ "\n") "" g
  where
    show_paragraph (Paragraph p, rechtsnorm) = "§" ++ show p ++ ": " ++ show_rechtsnorm rechtsnorm
    show_rechtsnorm (Rechtsnorm (Tatbestand (a,b)) (Rechtsfolge f)) = "Wenn die welt " ++ show a ++ " ist und wir die welt nach " ++
                                                                       show b ++ " aendern wollen, dann " ++ show f

-- uebertraegt einen Tatbestand woertlich ins Gesetz
case_law_ableiten :: w -> w -> Sollensanordnung -> Rechtsnorm (w, w) Sollensanordnung
case_law_ableiten vorher nachher erlaubt = Rechtsnorm (Tatbestand (vorher, nachher)) (Rechtsfolge erlaubt)

