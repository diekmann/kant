import Test.HUnit
import Test.QuickCheck
import qualified Aenderung
import qualified Gesetz
import qualified DebugMaximeTest

tests = TestList $ Aenderung.tests ++ Gesetz.tests

qcArgs = stdArgs{maxSuccess = 1000}

main = do
    runTestTT tests
    quickCheckWith qcArgs Aenderung.prop_positive
    quickCheck Aenderung.prop_max_aenderungen
    -- TODO: Debug.Trace schreibt auf STDERR.
    quickCheck DebugMaximeTest.prop_debug_maxime_id_executable
