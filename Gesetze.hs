module Gesetze where

import qualified Gesetz as G
import qualified Action as A
import qualified Aenderung
import qualified Kant
import qualified Data.Set as Set

-- Case Law

-- Gesetz beschreibt: (wenn before, wenn after) dann Erlaubt/Verboten,
--                    wobei before/after die Welt beschreiben.
-- Paragraphen sind einfache Integer
type CaseLaw world = G.Gesetz Integer (world, world) G.Sollensanordnung

-- Übertraegt einen Tatbestand wörtlich ins Gesetz.
-- Nicht sehr allgemein.
case_law_ableiten :: Kant.AllgemeinesGesetzAbleiten world (world, world) G.Sollensanordnung
case_law_ableiten (A.Action before after) sollensanordnung =
    G.Rechtsnorm
        (G.Tatbestand (before, after))
        (G.Rechtsfolge sollensanordnung)

show_CaseLaw :: Show w => CaseLaw w -> String
show_CaseLaw (G.Gesetz g) = Set.foldl (\s p-> s ++ show_paragraph p ++ "\n") "" g
  where
    show_paragraph (p, rechtsnorm) = show p ++ ": " ++ show_rechtsnorm rechtsnorm
    show_rechtsnorm (G.Rechtsnorm (G.Tatbestand (a,b)) (G.Rechtsfolge f)) =
        "Wenn die welt " ++ show a ++ " ist und wir die welt nach " ++ show b ++
        " aendern wollen, dann " ++ show f

-- Case Law etwas besser

-- Für Zahlenwelt
type CaseLawRelativ person etwas = G.Gesetz Integer [Aenderung.Aenderung person etwas] G.Sollensanordnung

case_law_relativ_ableiten
  :: (world -> world -> [Aenderung.Aenderung person etwas])
     -> Kant.AllgemeinesGesetzAbleiten world [Aenderung.Aenderung person etwas] G.Sollensanordnung
case_law_relativ_ableiten delta (A.Action before after) erlaubt =
  G.Rechtsnorm (G.Tatbestand (delta before after)) (G.Rechtsfolge erlaubt)

