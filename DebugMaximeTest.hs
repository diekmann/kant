{-# LANGUAGE FlexibleInstances  #-}
module DebugMaximeTest where

import qualified Kant
import qualified Action as H
import qualified DebugMaxime as Debug

import Test.QuickCheck.Arbitrary

-- Property: debug_maxime verändert die Maxime nicht. Es ist equivalent zur Identityfunktion.
--
-- Zwei (totale, pure) Funktionen (sprich: Maximen) sind equivalent,
-- wenn sie für alle Eingaben equivalent sind.
prop_debug_maxime_id :: (Arbitrary person, Show person, Arbitrary world, Show world) =>
  Kant.Maxime person world
  -> person
  -> A.Action world
  -> Bool
prop_debug_maxime_id maxime person world =
    let Kant.Maxime f_orig = maxime
        Kant.Maxime f_debug = Debug.debug_maxime maxime
    in
    f_debug person world == f_orig person world

-- YOLO: irgendwas, damit quickcheck das ausführen kann.
prop_debug_maxime_id_executable :: Kant.Maxime String Integer -> String -> A.Action Integer -> Bool
prop_debug_maxime_id_executable = prop_debug_maxime_id

instance Arbitrary (Kant.Maxime String Integer) where
  arbitrary = do
    ergebnis <- arbitrary
    return $ Kant.Maxime (\_ _ -> ergebnis)

instance Show (Kant.Maxime String Integer) where
  show _ = "Dummy show Kant.Maxime String Integer for quickcheck"

instance Arbitrary (A.Action Integer) where
  arbitrary = do
    v <- arbitrary
    n <- arbitrary
    return (A.Action v n)
