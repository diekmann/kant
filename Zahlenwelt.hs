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

stehlen :: Integer -> Person -> Person -> Zahlenwelt -> Zahlenwelt
stehlen _ opfer _ welt | M.notMember opfer (besitz welt) = welt -- Wenn das Opfer nichts hat kann auch nichts gestohlen werden.
stehlen i opfer dieb (Zahlenwelt r besitz) = Zahlenwelt r neuer_besitz
    where neuer_besitz = case M.lookup opfer besitz of
                           Nothing -> besitz
                           Just _ ->  M.insertWith (+) dieb i (M.adjust (\x -> x-i) opfer besitz)

-- Eine Handlung ist nur physikalisch moeglich, solange es noch Resourcen gibt.
moeglich :: Person -> Zahlenwelt -> HandlungF Person Zahlenwelt -> Bool
moeglich person welt h = (verbleibend nach_handlung) >= 0
    where nach_handlung = nachher $ handeln person welt h 

-- Mehr ist mehr gut.
-- Globaler Fortschritt erlaubt stehlen, solange dabei nichts vernichtet wird.
globaler_fortschritt :: Handlung Zahlenwelt -> Bool
-- Groesser (>) anstelle (>=) ist hier echt spannend! Es sagt, dass wir nicht handeln duerfen, wenn andere nicht die moeglichkeit haben!!
globaler_fortschritt (Handlung vorher nachher) = (gesamtbesitz nachher) >= (gesamtbesitz vorher) -- kein strenger Fortschritt, eher kein Rueckschritt
    where gesamtbesitz w = M.foldl' (+) 0 (besitz w)
-- Dieser globale Fortschritt sollte eigentlich allgemeines Gesetz werden und die Maxime sollte individuelle Bereicherung sein (und die unsichtbare Hand macht den Rest. YOLO).


individueller_fortschritt :: Person -> Handlung Zahlenwelt -> Bool
individueller_fortschritt p (Handlung vorher nachher) = (meins nachher) >= (meins vorher)
    where meins welt = M.findWithDefault 0 p (besitz welt)

debug_maxime :: (Person -> Handlung Zahlenwelt -> Bool) -> (Person -> Handlung Zahlenwelt -> Bool)
--debug_maxime f = \ich welt -> trace ("maxime aus sicht von " ++ show ich ++ " für " ++ show welt) $ f ich welt
debug_maxime f ich welt = do_trace ("aus sicht von " ++ show ich ++ " für " ++ show welt) $ f ich welt
    where ergebnis = f ich welt
          do_trace str = if not ergebnis then trace ("verletzte maxime "++str) else id

-- TODO: Eigentlich wollen wir Fortschritt in ALLEN möglichen Welten.
-- TODO: hard-coded alice. Eine Maxime braucht ein Aus-Sicht-Von!
maxime_zahlenfortschritt = Kant.Maxime $ debug_maxime (\ich -> individueller_fortschritt ich)

zahlengesetz_beispiel :: CaseLaw Zahlenwelt
zahlengesetz_beispiel = Gesetz $ S.singleton (
    (Paragraph 42),
    (Rechtsnorm (Tatbestand (Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 0 },
                             Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 1}))
                (Rechtsfolge Verbot)))

beispiel_kategorischer_imperativ = Kant.kategorischer_imperativ Alice
    (Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 0 }) (HandlungF (abbauen 5)) maxime_zahlenfortschritt Kant.case_law_ableiten leer

-- max i iterations
make_case_law :: Int -> HandlungF Person Zahlenwelt -> Zahlenwelt -> CaseLaw Zahlenwelt -> CaseLaw Zahlenwelt
make_case_law i _ _ g | i <= 0 = g
make_case_law i h w g =
  --TODO: alles fuer Alice hardcoded
  if not (moeglich Alice w h) then
    g
  else
  let (s,g') = Kant.kategorischer_imperativ Alice w h maxime_zahlenfortschritt Kant.case_law_ableiten g in
  let w' = (if s == Erlaubnis then nachher (handeln Alice w h) else w) in
  make_case_law (i-1) h w' g'

initialwelt = Zahlenwelt {
                verbleibend = 42,
                besitz = M.fromList [(Alice, 5), (Bob, 10)]
              }

beispiel1 = make_case_law 10 (HandlungF (abbauen 5)) initialwelt zahlengesetz_beispiel
beispiel2 = make_case_law 10 (HandlungF (stehlen 5 Bob)) initialwelt zahlengesetz_beispiel
beispiel3 = make_case_law 10 (HandlungF (stehlen 2 Alice)) initialwelt zahlengesetz_beispiel
--putStrLn $ show_CaseLaw  beispiel



