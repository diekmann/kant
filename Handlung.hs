module Handlung where

-- Beschreibt Handlungen als Änderung der Welt. Unabhängig von der handelnden Person.
-- Beschreibt vergangene Handlung.
data Handlung world = Handlung {vorher::world, nachher::world}

-- Was ist das? Abstrakte Handlung? Plan zu handeln?
newtype HandlungF person world = HandlungF (person -> world -> world)

handeln :: person -> world -> HandlungF person world -> Handlung world
handeln handelnde_person welt (HandlungF h) = Handlung {vorher = welt,
                                                        nachher = h handelnde_person welt}

-- Beispiel, für eine Welt die nur aus einer Zahl besteht.
-- Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
beispiel_handlungf = HandlungF $ \p n -> if n < 9000 then n+1 else n


-- Handlungen können Leute betreffen.
-- Handlungen können aus Sicht Anderer wahrgenommen werden.
--
-- ich brauche nur welt vorher und welt nachher. so kann ich handelnde person und beobachtende person trennen
