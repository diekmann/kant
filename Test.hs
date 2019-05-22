import Test.HUnit
import Test.QuickCheck
import qualified Aenderung
import qualified Gesetz

tests = TestList $ Aenderung.tests ++
        [
        TestCase (assertEqual "test1"
            (Gesetz.Paragraph 1)
            (Gesetz.neuer_paragraph Gesetz.leer)
            )
        ]

qcArgs = stdArgs{maxSuccess = 1000}

main = do
    runTestTT tests
    quickCheckWith qcArgs Aenderung.prop_positive
    quickCheck Aenderung.prop_max_aenderungen
