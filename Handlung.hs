module Handlung where


-- Beschreibt Handlungen als Änderung der Welt.
newtype Handlung world = Handlung (world -> world)

handeln :: world -> Handlung world -> world
handeln welt (Handlung h) = h welt

-- Beispiel, für eine Welt die nur aus einer Zahl besteht.
-- Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
beispiel_handlung = Handlung $ \n -> if n < 9000 then n+1 else n
