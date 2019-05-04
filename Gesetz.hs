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

-- ob eine Handlung ausgeführt werden muss, darf, kann, nicht muss.
data Sollensanordnung = Gebot | Verbot | Erlaubnis | Freistellung
  deriving (Eq, Ord, Show, Enum)

