module Zahlenwelt where

import Gesetz
import qualified Kant
import qualified Data.Set as S

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
maxime_zahlenfortschritt = Kant.Maxime $ \w (Kant.Handlung h) -> fortschritt w (h w)

type CaseLaw world = Gesetz (world, world) (Sollensanordnung)

show_CaseLaw :: Show world => CaseLaw world -> String
show_CaseLaw (Gesetz g) = S.foldl (\s p-> s ++ show_paragraph p ++ "; ") "" g
  where
    show_paragraph (Paragraph p, rechtsnorm) = p ++ ": " ++ show_rechtsnorm rechtsnorm
    show_rechtsnorm (Rechtsnorm (Tatbestand (a,b)) (Rechtsfolge f)) = "Wenn die welt " ++ show a ++ " ist und wir die welt nach " ++
                                                                       show b ++ " aendern wollen, dann " ++ show f

zahlengesetz_beispiel :: CaseLaw Zahlenwelt
zahlengesetz_beispiel = Gesetz $ S.singleton ((Paragraph "Paragraph 42"), (Rechtsnorm (Tatbestand (Zahlenwelt 0 1, Zahlenwelt 0 2)) (Rechtsfolge Verbot)))

beispiel_kategorischer_imperativ = Kant.kategorischer_imperativ (Zahlenwelt 9000 0) (Kant.Handlung (abbauen 5)) maxime_zahlenfortschritt Kant.case_law_ableiten (Gesetz S.empty)

