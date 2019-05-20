{-# LANGUAGE MultiParamTypeClasses #-}
module Handlung where

-- Beschreibt Handlungen als Änderung der Welt. Unabhängig von der handelnden Person.
-- Beschreibt vergangene Handlung.
--
-- Handlungen können Leute betreffen.
-- Handlungen können aus Sicht Anderer wahrgenommen werden.
-- Ich brauche nur welt vorher und welt nachher. so kann ich handelnde person und beobachtende person trennen
data Handlung world = Handlung {vorher::world, nachher::world}

instance Show world => Show (Handlung world) where
    show (Handlung vorher nachher) = "(Handlung vorher:"++show vorher++" nachher:"++show nachher++")"

-- Was ist das? Abstrakte Handlung? Plan zu handeln?
newtype HandlungF person world = HandlungF (person -> world -> world)

handeln :: person -> world -> HandlungF person world -> Handlung world
handeln handelnde_person welt (HandlungF h) = Handlung {vorher = welt,
                                                        nachher = h handelnde_person welt}

-- Beispiel, für eine Welt die nur aus einer Zahl besteht.
-- Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
beispiel_handlungf = HandlungF $ \p n -> if n < 9000 then n+1 else n



-- diffing worlds.
-- Im Unterschied zu Data.Generic.Diff will ich keinen editscript der die Gleichheit betont,
-- ich suche nur die Unterschiede und will den Ausgangszustand wegabstrahieren.

-- person kann sein: natürliche Person, juristische Person, ein Tier, die Umwelt an sich, ....

data Aenderung person etwas = Geben person person etwas | Nehmen person person etwas
-- brauche noch Vorbedingung fuer einen Diff von Handlungen?

--TODO world, person, etwas relaten!!!! MultiParamTypeClasses?
class Diff world person etwas where
    diff :: world -> world -> [Aenderung person etwas]

--TODO person should be generic?
instance Diff Integer () Integer where
    diff i1 i2
        | i1 == i2 = []
        | i1 > i2 = [Geben () () (i1 - i2)]
        | i1 < i2 = [Nehmen () () (i2 - i1)]

--TODO test

