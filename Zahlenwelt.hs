module Zahlenwelt where

import Gesetz
import Handlung
import qualified Kant
import qualified Data.Set as S
import qualified Data.Map as M

import Debug.Trace

data Person = Alice | Bob | Carl
    deriving (Eq, Ord, Show, Enum, Bounded)

-- Wenn die welt nur eine Zahl ist, ...
-- Resourcen sind endlich.
data Zahlenwelt = Zahlenwelt { verbleibend :: Integer, -- verbleibendResourcen
                               besitz :: M.Map Person Integer -- Besitz jeder Person
                             }
  deriving (Eq, Ord)

instance Show Zahlenwelt where
    show (Zahlenwelt resourcen welt) = "verbleibendeResourcen:"++show resourcen++";welt:"++show welt

abbauen :: Integer -> Person -> Zahlenwelt -> Zahlenwelt
abbauen i p (Zahlenwelt verbleibend besitz) = Zahlenwelt (verbleibend-i) (M.adjust (+i) p besitz)

-- Eine Handlung ist nur physikalisch moeglich, solange es noch Resourcen gibt.
moeglich :: Person -> Zahlenwelt -> Handlung Person Zahlenwelt -> Bool
moeglich person welt h = (verbleibend nach_handlung) >= 0
    where nach_handlung = handeln person welt h 

-- Mehr ist mehr gut.
globaler_fortschritt :: Zahlenwelt -> Zahlenwelt -> Bool
-- Groesser (>) anstelle (>=) ist hier echt spannend! Es sagt, dass wir nicht handeln duerfen, wenn andere nicht die moeglichkeit haben!!
globaler_fortschritt (Zahlenwelt _ vorher) (Zahlenwelt _ nachher) = (gesamtbesitz nachher) >= (gesamtbesitz vorher) -- kein strenger Fortschritt, eher kein Rueckschritt
    where gesamtbesitz = M.foldl' (+) 0
-- Dieser globale Fortschritt sollte eigentlich allgemeines Gesetz werden und die Maxime sollte individuelle Bereicherung sein (und die unsichtbare Hand macht den Rest. YOLO).


individueller_fortschritt :: Person -> Zahlenwelt -> Zahlenwelt -> Bool
individueller_fortschritt p vorher nachher = (meins nachher) >= (meins vorher)
    where meins welt = M.findWithDefault 0 p (besitz welt)


-- TODO: Eigentlich wollen wir Fortschritt in ALLEN möglichen Welten.
maxime_zahlenfortschritt = Kant.Maxime $ \person welt h -> individueller_fortschritt person welt (handeln person welt h)

zahlengesetz_beispiel :: CaseLaw Zahlenwelt
zahlengesetz_beispiel = Gesetz $ S.singleton (
    (Paragraph 42),
    (Rechtsnorm (Tatbestand (Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 0 },
                             Zahlenwelt { verbleibend = 90000, besitz = M.singleton Alice 1}))
                (Rechtsfolge Verbot)))

beispiel_kategorischer_imperativ = Kant.kategorischer_imperativ Alice
    (Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 0 }) (Handlung (abbauen 5)) maxime_zahlenfortschritt case_law_ableiten leer

-- max i iterations
make_case_law :: Int -> Handlung Person Zahlenwelt -> Zahlenwelt -> CaseLaw Zahlenwelt -> CaseLaw Zahlenwelt
make_case_law i _ _ g | i <= 0 = g
make_case_law i h w g =
  --TODO: alles fuer Alice hardcoded
  if not (moeglich Alice w h) then
    g
  else
  let (s,g') = Kant.kategorischer_imperativ Alice w h maxime_zahlenfortschritt case_law_ableiten g in
  let w' = (if s == Erlaubnis then handeln Alice w h else w) in
  make_case_law (i-1) h w' g'

beispiel = make_case_law 100 (Handlung (abbauen 10)) (Zahlenwelt { verbleibend = 42, besitz = M.singleton Alice 5 }) zahlengesetz_beispiel
--putStrLn $ show_CaseLaw  beispiel



