module Handlung where

-- Beschreibt Handlungen für eine handelnde Person als Änderung der Welt.
newtype Handlung person world = Handlung (person -> world -> world)

handeln :: person -> world -> Handlung person world -> world
handeln handelnde_person welt (Handlung h) = h handelnde_person welt

-- Beispiel, für eine Welt die nur aus einer Zahl besteht.
-- Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
beispiel_handlung = Handlung $ \p n -> if n < 9000 then n+1 else n
