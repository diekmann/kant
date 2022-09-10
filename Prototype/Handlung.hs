module Handlung where

-- Beschreibt Handlungen als Änderung der Welt. Unabhängig von der handelnden Person.
-- Beschreibt vergangene Handlung.
--
-- Handlungen können Leute betreffen.
-- Handlungen können aus Sicht Anderer wahrgenommen werden.
-- Ich brauche nur Welt vorher und Welt nachher.
-- So kann ich handelnde Person und beobachtende Person trennen.
data Handlung world = Handlung {vorher::world, nachher::world}

instance Show world => Show (Handlung world) where
  show (Handlung vorher nachher) =
    "(Handlung vorher:" ++ show vorher ++ " nachher:" ++ show nachher ++ ")"

-- Handlung als Funktion gewrapped.
-- Was ist das? Abstrakte Handlung? Plan zu handeln? Absicht?
-- Von Außen können wir Funktionen nur extensional betrachten, d.h. Eingabe und Ausgabe anschauen.
-- Die Absicht die sich in einer Funktion verstecken kann ist schwer zu erkennen.
-- Eine HandlungF kann nicht geprinted werden!
newtype HandlungF person world = HandlungF (person -> world -> world)

handeln :: person -> world -> HandlungF person world -> Handlung world
handeln handelnde_person welt (HandlungF h) = Handlung {vorher = welt,
                                                        nachher = h handelnde_person welt}

-- Beispiel, für eine Welt die nur aus einer Zahl besteht.
-- Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
beispiel_handlungf = HandlungF $ \p n -> if n < 9000 then n+1 else n

