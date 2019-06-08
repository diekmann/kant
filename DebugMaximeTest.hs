{-# LANGUAGE FlexibleInstances  #-}
module DebugMaximeTest where

import qualified Kant
import qualified Handlung as H
import qualified DebugMaxime as Debug

import Test.QuickCheck.Arbitrary

prop_debug_maxime_id :: (Arbitrary person, Show person, Arbitrary world, Show world) =>
  person
  -> H.Handlung world
  -> Bool
prop_debug_maxime_id person world =
    let Kant.Maxime f_orig = Kant.maxime_mir_ist_alles_recht in
    let Kant.Maxime f_debug = Debug.debug_maxime2 Kant.maxime_mir_ist_alles_recht in
    f_debug person world == f_orig person world

prop_debug_maxime_id_executable :: String -> H.Handlung Integer -> Bool
prop_debug_maxime_id_executable = prop_debug_maxime_id

instance Arbitrary (H.Handlung Integer) where
  arbitrary = do
    v <- arbitrary
    n <- arbitrary
    return (H.Handlung v n)
