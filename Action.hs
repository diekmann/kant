module Action where

-- Describes Actions as snapshots of the world. Independent of acting person.
-- Allows to observes actions externally.
data Action world = Action {before::world, after::world}

instance Show world => Show (Action world) where
  show (Action before after) =
    "(Action before:" ++ show before ++ " after:" ++ show after ++ ")"

-- Action als Funktion gewrapped.
-- Was ist das? Abstrakte Action? Plan zu act? Absicht?
-- Von Außen können wir Funktionen nur extensional betrachten, d.h. Eingabe und Ausgabe anschauen.
-- Die Absicht die sich in einer Funktion verstecken kann ist schwer zu erkennen.
-- Eine ActionF kann nicht geprinted werden!
newtype ActionF person world = ActionF (person -> world -> world)

act :: person -> world -> ActionF person world -> Action world
act acting_person world (ActionF h) = Action {before = world,
                                              after = h acting_person world}

-- Beispiel, für eine Welt die nur aus einer Zahl besteht.
-- Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
beispiel_handlungf = ActionF $ \p n -> if n < 9000 then n+1 else n

