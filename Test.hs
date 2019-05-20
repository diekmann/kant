import Test.HUnit
import qualified Gesetz

tests = TestList [
    TestCase (assertEqual "test1"
        (Gesetz.Paragraph 1)
        (Gesetz.neuer_paragraph Gesetz.leer)
        )
    ]

main = runTestTT tests
