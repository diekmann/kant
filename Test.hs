import Test.HUnit
import Test.QuickCheck
import qualified Aenderung
import qualified Gesetz

tests = TestList $ Aenderung.tests ++ Gesetz.tests

qcArgs = stdArgs{maxSuccess = 1000}

main = do
    runTestTT tests
    quickCheckWith qcArgs Aenderung.prop_positive
    quickCheck Aenderung.prop_max_aenderungen
