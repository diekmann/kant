module Zahlenwelt where

import Gesetz
import qualified Kant
import qualified Data.Set as S

-- Wenn die welt nur eine Zahl ist, ...
-- Resourcen sind endlich.
data Zahlenwelt = Zahlenwelt Integer -- verbleibendResourcen
                             Integer -- welt
  deriving (Eq, Ord)

instance Show Zahlenwelt where
    show (Zahlenwelt resourcen welt) = "verbleibendeResourcen:"++show resourcen++";welt:"++show welt

zahl :: Zahlenwelt -> Integer
zahl (Zahlenwelt _ i) = i

abbauen :: Integer -> Zahlenwelt -> Zahlenwelt
abbauen i (Zahlenwelt verbleibend w) = Zahlenwelt (verbleibend-i) (w+i)

-- Eine Handlung ist nur physikalisch moeglich, solange es noch Resourcen gibt.
moeglich :: Zahlenwelt -> Kant.Handlung Zahlenwelt -> Bool
moeglich (Zahlenwelt verbleibend welt) h =
  let (Zahlenwelt v w) = Kant.handeln (Zahlenwelt verbleibend welt) h in
  v >= 0

-- Mehr ist mehr gut.
fortschritt :: Zahlenwelt -> Zahlenwelt -> Bool
fortschritt (Zahlenwelt _ w1) (Zahlenwelt _ w2) = w2 > w1

-- TODO: Eigentlich wollen wir Fortschritt in ALLEN möglichen Welten.
maxime_zahlenfortschritt = Kant.Maxime $ \w (Kant.Handlung h) -> fortschritt w (h w)

zahlengesetz_beispiel :: CaseLaw Zahlenwelt
zahlengesetz_beispiel = Gesetz $ S.singleton ((Paragraph 42), (Rechtsnorm (Tatbestand (Zahlenwelt 0 1, Zahlenwelt 0 2)) (Rechtsfolge Verbot)))

beispiel_kategorischer_imperativ = Kant.kategorischer_imperativ (Zahlenwelt 9000 0) (Kant.Handlung (abbauen 5)) maxime_zahlenfortschritt case_law_ableiten leer

make_case_law :: Kant.Handlung Zahlenwelt -> Zahlenwelt -> CaseLaw Zahlenwelt -> CaseLaw Zahlenwelt
make_case_law h w g =
  if not (moeglich w h) then
    g
  else
  let (s,g') = Kant.kategorischer_imperativ w h maxime_zahlenfortschritt case_law_ableiten g in
  let w' = (if s == Erlaubnis then Kant.handeln w h else w) in
  make_case_law h w' g'

beispiel = make_case_law (Kant.Handlung (abbauen 5)) (Zahlenwelt 42 0) zahlengesetz_beispiel
--putStrLn $ show_CaseLaw  beispiel



