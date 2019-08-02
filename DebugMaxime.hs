module DebugMaxime (debug_maxime) where

import qualified Kant
import qualified Action as A
import qualified Debug.Trace (trace)

-- debug_maxime gibt Details aus wenn die Maxime verletzt wurde.
debug_maxime :: (Show person, Show world) =>
  Kant.Maxime person world
  -> Kant.Maxime person world
debug_maxime (Kant.Maxime f) = Kant.Maxime (debug_maxime_f f)

-- debug_maxime_f wrapped die Funktion in einer Maxime.
debug_maxime_f :: (Show person, Show world) =>
  (person -> A.Action world -> Bool) -> (person -> A.Action world -> Bool)
debug_maxime_f f ich welt =
  do_trace ("aus Sicht von " ++ show ich ++ " für " ++ show welt) $ ergebnis
    where ergebnis = f ich welt
          do_trace str = if not ergebnis
                         then Debug.Trace.trace ("\nverletzte maxime "++str)
                         else id
