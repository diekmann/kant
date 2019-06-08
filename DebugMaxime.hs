module DebugMaxime where

import qualified Handlung as H
import qualified Debug.Trace (trace)

-- debug_maxime gibt Details aus wenn die Maxime verletzt wurde.
debug_maxime :: (Show person, Show world) =>
  (person -> H.Handlung world -> Bool) -> (person -> H.Handlung world -> Bool)
debug_maxime f ich welt =
  do_trace ("aus Sicht von " ++ show ich ++ " für " ++ show welt) $ ergebnis
    where ergebnis = f ich welt
          do_trace str = if not ergebnis
                         then Debug.Trace.trace ("\nverletzte maxime "++str)
                         else id
