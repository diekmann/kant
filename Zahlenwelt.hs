module Zahlenwelt where

import Gesetz
import qualified Action as A
import qualified Aenderung
import qualified Kant
import qualified Gesetze
import qualified DebugMaxime as Debug
import qualified Data.Set as S
import qualified Data.Map as M

data Person = Alice | Bob | Carl
    deriving (Eq, Ord, Show, Enum, Bounded)

-- Wenn die Welt sich durch eine Zahl darstellen lässt, ...
data Zahlenwelt = Zahlenwelt {
        remaining :: Integer,            -- Resources are finite.
        property :: M.Map Person Integer -- Estate of each person.
      }
  deriving (Eq, Ord, Show)

abbauen :: Integer -> Person -> Zahlenwelt -> Zahlenwelt
abbauen i p (Zahlenwelt remaining property) = Zahlenwelt (remaining-i) (M.adjust (+i) p property)

stehlen :: Integer -> Person -> Person -> Zahlenwelt -> Zahlenwelt
stehlen _ opfer _ welt | M.notMember opfer (property welt) =
    welt -- Wenn das Opfer nichts hat kann auch nichts gestohlen werden.
stehlen i opfer dieb (Zahlenwelt r property) = Zahlenwelt r neuer_property
    where neuer_property = case M.lookup opfer property of
                           Nothing -> property
                           Just _ ->  M.insertWith (+) dieb i (M.adjust (\x -> x-i) opfer property)

-- Eine Action ist nur physikalisch möglich, solange es noch Resourcen gibt.
moeglich :: Person -> Zahlenwelt -> A.ActionF Person Zahlenwelt -> Bool
moeglich person welt h = (remaining nach_handlung) >= 0
    where nach_handlung = A.after $ A.act person welt h

-- Mehr ist mehr gut.
global_progress :: A.Action Zahlenwelt -> Bool
global_progress (A.Action before after) = (total after) >= (total before)
    where total w = M.foldl' (+) 0 (property w)

-- Allows e.g., stealing, as long as we don't destroy resources.
--
-- Interesting: use (>) instead of (>=)


individual_progress :: Person -> A.Action Zahlenwelt -> Bool
individual_progress p (A.Action before after) = (mine after) >= (mine before)
    where mine world = M.findWithDefault 0 p (property world)


maxime_zahlenfortschritt = Debug.debug_maxime $ Kant.Maxime (\me -> individual_progress me)

-- Interesting: hard-code Alice instead of 'me'.


delta_zahlenwelt :: Aenderung.Delta Zahlenwelt Person Integer
delta_zahlenwelt before after = Aenderung.delta_num_map (property before) (property after)
  --yolo: who needs nature and consider remaining resources?


simulate :: (Ord a, Ord b) =>
  Person
  -> Kant.Maxime Person Zahlenwelt
  -> Kant.AllgemeinesGesetzAbleiten Zahlenwelt a b
  -> Int                            -- maximale Anzahl Iterationen (Simulationen)
  -> A.ActionF Person Zahlenwelt    -- Beabsichtigte Action
  -> Zahlenwelt                     -- Initialwelt
  -> Gesetz Integer a b             -- Initialgesetz
  -> Gesetz Integer a b
simulate _      _      _        i _ _    g | i <= 0 = g -- iteration vorbei
simulate person _      _        i h welt g | not (moeglich person welt h) = g
simulate person maxime ableiten i h welt g =
  let (sollensanordnung, g') = Kant.kategorischer_imperativ person welt h maxime ableiten g in
  let w' = (if sollensanordnung == Erlaubnis && (moeglich person welt h)
            then
              A.after (A.act person welt h)
            else
              welt
           ) in
  if welt == w' then
    g'
  else
    simulate person maxime ableiten (i-1) h w' g'

initialwelt = Zahlenwelt {
                remaining = 42,
                property = M.fromList [(Alice, 5), (Bob, 10)]
              }

-- Now we hard-code Alice as acting person in our examples (the maxim remains generic)
 
beispiel_CaseLaw :: A.ActionF Person Zahlenwelt -> Gesetze.CaseLaw Zahlenwelt
beispiel_CaseLaw h = simulate Alice maxime_zahlenfortschritt Gesetze.case_law_ableiten 10 h initialwelt leer

beispiel_CaseLawRelativ :: A.ActionF Person Zahlenwelt -> Gesetze.CaseLawRelativ Person Integer
beispiel_CaseLawRelativ h = simulate Alice maxime_zahlenfortschritt (Gesetze.case_law_relativ_ableiten delta_zahlenwelt) 20 h initialwelt leer

beispiel1 = beispiel_CaseLaw (A.ActionF (abbauen 5))
beispiel1' = beispiel_CaseLawRelativ (A.ActionF (abbauen 5))

beispiel2 = beispiel_CaseLaw (A.ActionF (stehlen 5 Bob))
beispiel2' = beispiel_CaseLawRelativ (A.ActionF (stehlen 5 Bob))

beispiel3 = beispiel_CaseLaw (A.ActionF (stehlen 2 Alice))
beispiel3' = beispiel_CaseLawRelativ (A.ActionF (stehlen 2 Alice))


