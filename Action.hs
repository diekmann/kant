module Action where

-- Describes an action as snapshots of the world.
-- Independent of acting person.
-- Allows to observes actions externally.
data Action world = Action {before::world, after::world}

instance Show world => Show (Action world) where
  show (Action before after) =
    "(Action before:" ++ show before ++ " after:" ++ show after ++ ")"


-- Action wrapped as function.
-- What's this? Abstract action? Intent to act? Aim? Plan? Purpose?
newtype ActionF person world = ActionF (person -> world -> world)

-- Note: We can only observe an ActionF extensional, by observing input/output.
-- We cannot print it.



act :: person -> world -> ActionF person world -> Action world
act acting_person world (ActionF h) = Action {before = world,
                                              after = h acting_person world}


-- Beispiel, für eine Welt die nur aus einer Zahl besteht.
-- Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
beispiel_ActionF = ActionF $ \p n -> if n < 9000 then n+1 else n

