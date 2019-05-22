import Test.HUnit
import qualified Aenderung
import qualified Gesetz

tests = TestList $ Aenderung.tests ++
        [
        TestCase (assertEqual "test1"
            (Gesetz.Paragraph 1)
            (Gesetz.neuer_paragraph Gesetz.leer)
            )
        ]

main = runTestTT tests
