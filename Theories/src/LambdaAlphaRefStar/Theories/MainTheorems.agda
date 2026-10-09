module LambdaAlphaRefStar.Theories.MainTheorems where

-- The scope safety theorem for the gradual language
open import LambdaAlphaRefStar.Theories.ScopeSafety using (scope-safety)

-- The scope safety corollary for the static sister language
open import LambdaAlphaRefStar.Theories.StaticScopeSafety using (static-scope-safety)

-- The space efficiency theorem
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.SpaceEfficient using (space-consumption-elab)
