module Gesetz where

import qualified Data.Set as S

import Test.HUnit (Test(..), assertEqual)

newtype Tatbestand a = Tatbestand a
  deriving (Eq, Ord, Show)
newtype Rechtsfolge a = Rechtsfolge a
  deriving (Eq, Ord, Show)

data Rechtsnorm a b = Rechtsnorm (Tatbestand a) (Rechtsfolge b)
  deriving (Eq, Ord, Show)

newtype Paragraph p = Paragraph p
  deriving (Eq, Ord)

newtype Gesetz p a b = Gesetz (S.Set (Paragraph p, Rechtsnorm a b))
  deriving (Eq, Ord)

instance Show p => Show (Paragraph p) where
    show (Paragraph p) = "§" ++ show p

instance (Show p, Show a, Show b) => Show (Gesetz p a b) where
    show (Gesetz g) = S.foldl (\s p-> s ++ show_paragraph p ++ "\n") "" g
      where
        show_paragraph (p, rechtsnorm) = show p ++ ": " ++ show_rechtsnorm rechtsnorm
        show_rechtsnorm (Rechtsnorm t f) = "Wenn " ++ show t ++ ", dann " ++ show f

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
neuer_paragraph (Gesetz g) | (S.null g) = Paragraph 1
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


-- Tests

tests = [
    TestCase (assertEqual "leer"
        (Paragraph 1)
        (neuer_paragraph leer)
        ),
    TestCase (assertEqual "zwei"
        (Paragraph 2)
        (neuer_paragraph (Gesetz (S.singleton (Paragraph 1, rn))))
        ),
    TestCase (assertEqual "vier"
        (Paragraph 4)
        (neuer_paragraph (Gesetz (S.fromList [(Paragraph 1, rn), (Paragraph 3, rn)])))
        ),
    TestCase (assertEqual "vier ungeordnet"
        (Paragraph 4)
        (neuer_paragraph (Gesetz (S.fromList [(Paragraph 3, rn), (Paragraph 1, rn)])))
        ),
    TestCase (assertEqual "hinzufuegen leer"
        (Gesetz (S.singleton (Paragraph 1, rn)))
        (hinzufuegen rn leer)
        ),
    TestCase (assertEqual "hinzufuegen id"
        (Gesetz (S.singleton (Paragraph 1, rn)))
        (hinzufuegen rn (hinzufuegen rn leer))
        ),
    TestCase (assertEqual "zwei hinzufuegen"
        (Gesetz (S.fromList [(Paragraph 1, rn), (Paragraph 2, Rechtsnorm (Tatbestand "tb") (Rechtsfolge Verbot))]))
        (hinzufuegen (Rechtsnorm (Tatbestand "tb") (Rechtsfolge Verbot)) (hinzufuegen rn leer))
        )
    ]
    where rn = Rechtsnorm (Tatbestand "tb") (Rechtsfolge Erlaubnis)
