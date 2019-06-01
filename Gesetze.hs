module Gesetze where

import qualified Gesetz as G
import qualified Handlung as H
import qualified Aenderung
import qualified Kant
import qualified Data.Set as Set

-- Case Law --

-- Gesetz beschreibt: (wenn vorher, wenn nachher) dann Erlaubt/Verboten, wobei vorher/nachher die Welt beschreiben.
-- Paragraphen sind einfach Integer
type CaseLaw world = G.Gesetz Integer (world, world) G.Sollensanordnung

-- uebertraegt einen Tatbestand woertlich ins Gesetz.
-- Nicht sehr allgemein.
case_law_ableiten :: Kant.AllgemeinesGesetzAbleiten world (world, world) G.Sollensanordnung
case_law_ableiten (H.Handlung vorher nachher) sollensanordnung =
    G.Rechtsnorm
        (G.Tatbestand (vorher, nachher))
        (G.Rechtsfolge sollensanordnung)

show_CaseLaw :: Show w => CaseLaw w -> String
show_CaseLaw (G.Gesetz g) = Set.foldl (\s p-> s ++ show_paragraph p ++ "\n") "" g
  where
    show_paragraph (G.Paragraph p, rechtsnorm) = "§" ++ show p ++ ": " ++ show_rechtsnorm rechtsnorm
    show_rechtsnorm (G.Rechtsnorm (G.Tatbestand (a,b)) (G.Rechtsfolge f)) =
        "Wenn die welt " ++ show a ++ " ist und wir die welt nach " ++ show b ++
        " aendern wollen, dann " ++ show f

-- Case Law etwas besser --

-- Fuer zahlenwelt
type CaseLawRelativ person etwas = G.Gesetz Integer [Aenderung.Aenderung person etwas] G.Sollensanordnung

case_law_relativ_ableiten
    :: (world -> world -> [Aenderung.Aenderung person etwas])
        -> Kant.AllgemeinesGesetzAbleiten world [Aenderung.Aenderung person etwas] G.Sollensanordnung
case_law_relativ_ableiten delta (H.Handlung vorher nachher) erlaubt = G.Rechtsnorm (G.Tatbestand (delta vorher nachher)) (G.Rechtsfolge erlaubt)

