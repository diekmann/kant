{-# LANGUAGE FlexibleInstances #-}
--TODO move Arbitrary and FlexibleInstances into smaller module

module Zahlenwelt where

import Gesetz
import qualified Handlung as H
import qualified Aenderung
import qualified Kant
import qualified Gesetze
import qualified DebugMaxime as Debug
import qualified Simulation
import qualified Data.Set as S
import qualified Data.Map as M

import Test.QuickCheck



data Person = Alice | Bob | Carl
    deriving (Eq, Ord, Show, Enum, Bounded)

-- Wenn die Welt sich durch eine Zahl darstellen lässt, ...
data Zahlenwelt = Zahlenwelt {
        verbleibend :: Integer, -- Ressourcen sind endlich. Verbleibende Ressourcen in der Welt.
        besitz :: M.Map Person Integer -- Besitz jeder Person.
      }
  deriving (Eq, Ord, Show)

abbauen :: Integer -> Person -> Zahlenwelt -> Zahlenwelt
abbauen i p (Zahlenwelt verbleibend besitz) = Zahlenwelt (verbleibend-i) (M.adjust (+i) p besitz)

stehlen :: Integer -> Person -> Person -> Zahlenwelt -> Zahlenwelt
stehlen _ opfer _ welt | M.notMember opfer (besitz welt) =
    welt -- Wenn das Opfer nichts hat kann auch nichts gestohlen werden.
stehlen i opfer dieb (Zahlenwelt r besitz) = Zahlenwelt r neuer_besitz
    where neuer_besitz = case M.lookup opfer besitz of
                           Nothing -> besitz
                           Just _ ->  M.insertWith (+) dieb i (M.adjust (\x -> x-i) opfer besitz)

wegwerfen :: Integer -> Person -> Zahlenwelt -> Zahlenwelt
wegwerfen i p (Zahlenwelt verbleibend besitz) = Zahlenwelt verbleibend (M.adjust (\x -> x-i) p besitz)

recyclen :: Integer -> Person -> Zahlenwelt -> Zahlenwelt
recyclen i p (Zahlenwelt verbleibend besitz) = Zahlenwelt (verbleibend+i) (M.adjust (\x -> x-i) p besitz)


-- Eine Handlung ist nur physikalisch möglich, solange es noch Resourcen gibt.
moeglich :: H.Handlung Zahlenwelt -> Bool
moeglich (H.Handlung vorher nachher) = (verbleibend nachher) >= 0

-- Mehr ist mehr gut.
-- Globaler Fortschritt erlaubt stehlen, solange dabei nichts vernichtet wird.
globaler_fortschritt :: H.Handlung Zahlenwelt -> Bool
-- Groesser (>) anstelle (>=) ist hier echt spannend! Es sagt, dass wir nicht handeln duerfen, wenn andere nicht die möglichkeit haben!!
globaler_fortschritt (H.Handlung vorher nachher) = (gesamtbesitz nachher) >= (gesamtbesitz vorher) -- kein strenger Fortschritt, eher kein Rueckschritt
    where gesamtbesitz w = M.foldl' (+) 0 (besitz w)
-- Dieser globale Fortschritt sollte eigentlich allgemeines Gesetz werden und die Maxime sollte individuelle Bereicherung sein (und die unsichtbare Hand macht den Rest. YOLO).


individueller_fortschritt :: Person -> H.Handlung Zahlenwelt -> Bool
individueller_fortschritt p (H.Handlung vorher nachher) = (meins nachher) >= (meins vorher)
    where meins welt = M.findWithDefault 0 p (besitz welt)


-- TODO: Eigentlich wollen wir Fortschritt in ALLEN möglichen Welten.
maxime_zahlenfortschritt = Debug.debug_maxime $ Kant.Maxime (\ich -> individueller_fortschritt ich)
-- Interessant: hard-coded Alice anstelle von 'ich'.

zahlengesetz_beispiel :: Gesetze.CaseLaw Zahlenwelt
zahlengesetz_beispiel = Gesetz $ S.singleton (
    (Paragraph 42),
    (Rechtsnorm (Tatbestand (Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 0 },
                             Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 1}))
                (Rechtsfolge Verbot)))

beispiel_kategorischer_imperativ = Kant.kategorischer_imperativ Alice
    (Zahlenwelt { verbleibend = 9000, besitz = M.singleton Alice 0 })
    (H.HandlungF (abbauen 5))
    maxime_zahlenfortschritt
    Gesetze.case_law_ableiten
    leer


delta_zahlenwelt :: Aenderung.Delta Zahlenwelt Person Integer
delta_zahlenwelt vorher nachher = Aenderung.delta_num_map (besitz vorher) (besitz nachher)
  --TODO wer braucht schon Natur und verbleibende Resourcen?

so = Simulation.Optionen {
    Simulation.person = Alice,

    Simulation.moeglich = moeglich,

    Simulation.maxime = maxime_zahlenfortschritt,
    Simulation.allgemeines_gesetz_ableiten = Gesetze.case_law_ableiten 
}

so_besser = so { Simulation.allgemeines_gesetz_ableiten = Gesetze.case_law_relativ_ableiten delta_zahlenwelt }

initialwelt = Zahlenwelt {
                verbleibend = 42,
                besitz = M.fromList [(Alice, 5), (Bob, 10)]
              }

beispiel_CaseLaw :: H.HandlungF Person Zahlenwelt -> Gesetze.CaseLaw Zahlenwelt
beispiel_CaseLaw h = Simulation.simulateOne so 20 h initialwelt leer

beispiel_CaseLawRelativ :: H.HandlungF Person Zahlenwelt -> Gesetze.CaseLawRelativ Person Integer
beispiel_CaseLawRelativ h = Simulation.simulateOne so_besser 20 h initialwelt leer

beispiel1 = beispiel_CaseLaw (H.HandlungF (abbauen 5))
beispiel1' = beispiel_CaseLawRelativ (H.HandlungF (abbauen 5))
--putStrLn $ Gesetze.show_CaseLaw  beispiel1

beispiel2 = beispiel_CaseLaw (H.HandlungF (stehlen 5 Bob))
beispiel2' = beispiel_CaseLawRelativ (H.HandlungF (stehlen 5 Bob))

beispiel3 = beispiel_CaseLaw (H.HandlungF (stehlen 2 Alice))
beispiel3' = beispiel_CaseLawRelativ (H.HandlungF (stehlen 2 Alice))

beispiel4 = beispiel_CaseLaw (H.HandlungF (abbauen 0))
beispiel4' = beispiel_CaseLawRelativ (H.HandlungF (abbauen 0))

instance Arbitrary Person where
    arbitrary = elements [minBound..maxBound]

instance Arbitrary (H.HandlungF Person Zahlenwelt) where
  arbitrary = do
    i <- arbitrary
    opfer <- arbitrary
    f <- elements [abbauen i, stehlen i opfer, wegwerfen i, recyclen i]
    return (H.HandlungF f)

beispiel_sim1 = Simulation.gesetzbuch_inferieren so initialwelt
beispiel_sim1' = Simulation.gesetzbuch_inferieren so_besser initialwelt
