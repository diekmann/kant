module Zahlenwelt where

import Gesetz
import qualified Handlung as H
import qualified Aenderung
import qualified Kant
import qualified Gesetze
import qualified Data.Set as S
import qualified Data.Map as M

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

-- Eine Handlung ist nur physikalisch möglich, solange es noch Resourcen gibt.
moeglich :: Person -> Zahlenwelt -> H.HandlungF Person Zahlenwelt -> Bool
moeglich person welt h = (verbleibend nach_handlung) >= 0
    where nach_handlung = H.nachher $ H.handeln person welt h

-- Mehr ist mehr gut.
-- Globaler Fortschritt erlaubt stehlen, solange dabei nichts vernichtet wird.
globaler_fortschritt :: H.Handlung Zahlenwelt -> Bool
-- Groesser (>) anstelle (>=) ist hier echt spannend! Es sagt, dass wir nicht handeln duerfen, wenn andere nicht die moeglichkeit haben!!
globaler_fortschritt (H.Handlung vorher nachher) = (gesamtbesitz nachher) >= (gesamtbesitz vorher) -- kein strenger Fortschritt, eher kein Rueckschritt
    where gesamtbesitz w = M.foldl' (+) 0 (besitz w)
-- Dieser globale Fortschritt sollte eigentlich allgemeines Gesetz werden und die Maxime sollte individuelle Bereicherung sein (und die unsichtbare Hand macht den Rest. YOLO).


individueller_fortschritt :: Person -> H.Handlung Zahlenwelt -> Bool
individueller_fortschritt p (H.Handlung vorher nachher) = (meins nachher) >= (meins vorher)
    where meins welt = M.findWithDefault 0 p (besitz welt)


-- TODO: Eigentlich wollen wir Fortschritt in ALLEN möglichen Welten.
-- TODO: hard-coded alice. Eine Maxime braucht ein Aus-Sicht-Von!
maxime_zahlenfortschritt = Kant.Maxime $ Kant.debug_maxime (\ich -> individueller_fortschritt ich)

zahlengesetz_beispiel :: Gesetze.CaseLaw Zahlenwelt
zahlengesetz_beispiel = Gesetz $ S.singleton (
    (Paragraph 42),
    (Rechtsnorm (Tatbestand (Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 0 },
                             Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 1}))
                (Rechtsfolge Verbot)))

beispiel_kategorischer_imperativ = Kant.kategorischer_imperativ Alice
    (Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 0 }) (H.HandlungF (abbauen 5)) maxime_zahlenfortschritt
    Gesetze.case_law_ableiten leer


--TODO beispie sowohl fuer case_law_ableiten als auch case_law_relativ_ableiten

delta_zahlenwelt :: Aenderung.Delta Zahlenwelt Person Integer
delta_zahlenwelt vorher nachher = Aenderung.delta_num_map (besitz vorher) (besitz nachher) --TODO wer braucht schon Natur und verbleibende Resourcen?


-- max i iterations
make_case_law :: (Ord a, Ord b) => Kant.AllgemeinesGesetzAbleiten Zahlenwelt a b
                 -> Int                            -- maximale Anzahl Iterationen (Simulationen)
                 -> H.HandlungF Person Zahlenwelt  -- Beabsichtigte Handlung
                 -> Zahlenwelt                     -- Initialwelt
                 -> Gesetz Integer a b             -- Initialgesetz
                 -> Gesetz Integer a b
make_case_law _ i _ _ g | i <= 0 = g
make_case_law ableiten i h w g =
  --TODO: alles fuer Alice hardcoded
  let (s,g') = Kant.kategorischer_imperativ Alice w h maxime_zahlenfortschritt ableiten g in
  let w' = (if s == Erlaubnis && (moeglich Alice w h) then H.nachher (H.handeln Alice w h) else w) in
  if w == w' then
    g'
  else
    make_case_law ableiten (i-1) h w' g'

initialwelt = Zahlenwelt {
                verbleibend = 42,
                besitz = M.fromList [(Alice, 5), (Bob, 10)]
              }

beispiel1 :: Gesetze.CaseLaw Zahlenwelt
beispiel1 = make_case_law Gesetze.case_law_ableiten 10 (H.HandlungF (abbauen 5)) initialwelt leer
beispiel1' :: Gesetze.CaseLawRelativ Person Integer
beispiel1' = make_case_law (Gesetze.case_law_relativ_ableiten delta_zahlenwelt) 10 (H.HandlungF (abbauen 5)) initialwelt leer
beispiel2 = make_case_law (Gesetze.case_law_relativ_ableiten delta_zahlenwelt) 10 (H.HandlungF (stehlen 5 Bob)) initialwelt leer
beispiel3 = make_case_law (Gesetze.case_law_relativ_ableiten delta_zahlenwelt) 10 (H.HandlungF (stehlen 2 Alice)) initialwelt leer
--putStrLn $ Gesetze.show_CaseLaw  beispiel


