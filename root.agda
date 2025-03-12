{-# OPTIONS --cubical --allow-unsolved-metas #-}

module root where

  -- Utilities
  open import CategoryTheory
  open import ContainersPlus

  -- Monad container and directed container definitions
  open import MndContainer
  open import MndContainerMorphism
  open import DirectedContainer
  open import MndContainerToMonad

  -- Distributive law definitions
  open import MndDistributiveLaw
  open import DirectedDistributiveLaw
  open import MndDirectedDistributiveLaw
  open import DirectedMndDistributiveLaw

  -- Examples
  open import ContainerExamples
  open import DistributiveLawExamples

  -- Compatible composite proofs
  open import MndCompatibleComposite
  open import MndDistrLawToCompatibleComposite

  
-- use agda --html --html-dir=htmlcode root.agda in directory Cubical-final
