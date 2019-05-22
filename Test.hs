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

props = Aenderung.props

main = do
    runTestTT tests
    mapM quickCheck props
