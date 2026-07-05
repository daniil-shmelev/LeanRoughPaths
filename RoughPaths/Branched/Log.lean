/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Branched.Basic

/-!
# Branched Log-Signatures

This file defines truncated convolution logarithms of rooted-forest characters.
These are the Hopf-algebraic log-signatures associated with branched rough path
increments.
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z

noncomputable section

/-- A branched signature is a character on the rooted-forest algebra. -/
abbrev BranchedSignature (R : Type u) [CommSemiring R] :=
  ForestAlgebra.Character R

/-- A labelled branched signature is a character on the labelled rooted-forest algebra. -/
abbrev LabelledBranchedSignature (α : Type u) (R : Type v) [CommSemiring R] :=
  LForestAlgebra.Character α R

namespace BranchedSignature

variable {R : Type u} [Field R]

/-- The truncated branched log-signature of a forest character. -/
def logTruncated (χ : BranchedSignature R) (n : Nat) :
    ForestAlgebra.LinearFunctional R :=
  ForestAlgebra.LinearFunctional.logCharacterTruncated χ n

@[simp]
theorem logTruncated_zero (χ : BranchedSignature R) :
    logTruncated χ 0 = 0 := by
  simp [logTruncated]

@[simp]
theorem logTruncated_unit (n : Nat) :
    logTruncated (ForestAlgebra.Character.unit R) n = 0 := by
  rw [logTruncated, ForestAlgebra.LinearFunctional.logCharacterTruncated]
  have haug :
      ForestAlgebra.LinearFunctional.augmentationPart (ForestAlgebra.Character.unit R) = 0 := by
    rw [ForestAlgebra.LinearFunctional.augmentationPart]
    simp
  rw [haug]
  simp [ForestAlgebra.LinearFunctional.convolution_zero_left]

theorem logTruncated_evalForest
    (χ : BranchedSignature R) (n : Nat) (φ : RootedForest) :
    ForestAlgebra.LinearFunctional.evalForest (logTruncated χ n) φ =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          ForestAlgebra.LinearFunctional.evalForest
            (ForestAlgebra.LinearFunctional.convolutionPower
              (ForestAlgebra.LinearFunctional.augmentationPart χ) k) φ).sum :=
  ForestAlgebra.LinearFunctional.logCharacterTruncated_evalForest χ n φ

theorem logTruncated_evalTree
    (χ : BranchedSignature R) (n : Nat) (τ : RootedTree) :
    ForestAlgebra.LinearFunctional.evalForest
        (logTruncated χ n) (RootedForest.singleton τ) =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          ForestAlgebra.LinearFunctional.evalForest
            (ForestAlgebra.LinearFunctional.convolutionPower
              (ForestAlgebra.LinearFunctional.augmentationPart χ) k)
            (RootedForest.singleton τ)).sum :=
  logTruncated_evalForest χ n (RootedForest.singleton τ)

end BranchedSignature

namespace LabelledBranchedSignature

variable {α : Type u} {R : Type v} [Field R]

/-- The truncated labelled branched log-signature of a labelled forest character. -/
def logTruncated (χ : LabelledBranchedSignature α R) (n : Nat) :
    LForestAlgebra.LinearFunctional α R :=
  LForestAlgebra.LinearFunctional.logCharacterTruncated χ n

@[simp]
theorem logTruncated_zero (χ : LabelledBranchedSignature α R) :
    logTruncated χ 0 = 0 := by
  simp [logTruncated]

@[simp]
theorem logTruncated_unit (n : Nat) :
    logTruncated (LForestAlgebra.Character.unit α R) n = 0 := by
  rw [logTruncated, LForestAlgebra.LinearFunctional.logCharacterTruncated]
  have haug :
      LForestAlgebra.LinearFunctional.augmentationPart (LForestAlgebra.Character.unit α R) =
        0 := by
    rw [LForestAlgebra.LinearFunctional.augmentationPart]
    simp
  rw [haug]
  simp [LForestAlgebra.LinearFunctional.convolution_zero_left]

theorem logTruncated_evalForest
    (χ : LabelledBranchedSignature α R) (n : Nat) (φ : LRootedForest α) :
    LForestAlgebra.LinearFunctional.evalForest (logTruncated χ n) φ =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          LForestAlgebra.LinearFunctional.evalForest
            (LForestAlgebra.LinearFunctional.convolutionPower
              (LForestAlgebra.LinearFunctional.augmentationPart χ) k) φ).sum :=
  LForestAlgebra.LinearFunctional.logCharacterTruncated_evalForest χ n φ

theorem logTruncated_evalTree
    (χ : LabelledBranchedSignature α R) (n : Nat) (τ : LRootedTree α) :
    LForestAlgebra.LinearFunctional.evalForest
        (logTruncated χ n) (LRootedForest.singleton τ) =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          LForestAlgebra.LinearFunctional.evalForest
            (LForestAlgebra.LinearFunctional.convolutionPower
              (LForestAlgebra.LinearFunctional.augmentationPart χ) k)
            (LRootedForest.singleton τ)).sum :=
  logTruncated_evalForest χ n (LRootedForest.singleton τ)

theorem logTruncated_comapMapLabels {β : Type w} (f : α → β)
    (χ : LabelledBranchedSignature β R) (n : Nat) :
    logTruncated (LForestAlgebra.Character.comapMapLabels f χ) n =
      LForestAlgebra.LinearFunctional.comapMapLabels f (logTruncated χ n) :=
  LForestAlgebra.LinearFunctional.logCharacterTruncated_comapMapLabels f χ n

theorem logTruncated_comapEraseLabels
    (χ : BranchedSignature R) (n : Nat) :
    logTruncated (LForestAlgebra.Character.comapEraseLabels (α := α) χ) n =
      LForestAlgebra.LinearFunctional.comapEraseLabels (α := α)
        (BranchedSignature.logTruncated χ n) :=
  LForestAlgebra.LinearFunctional.logCharacterTruncated_comapEraseLabels χ n

theorem logTruncated_comapConstLabel
    (a : α) (χ : LabelledBranchedSignature α R) (n : Nat) :
    BranchedSignature.logTruncated (LForestAlgebra.Character.comapConstLabel a χ) n =
      LForestAlgebra.LinearFunctional.comapConstLabel a (logTruncated χ n) :=
  LForestAlgebra.LinearFunctional.logCharacterTruncated_comapConstLabel a χ n

end LabelledBranchedSignature

namespace AlgebraicBranchedRoughPath

variable {T : Type u} {R : Type v} [Field R]

/-- Truncated branched log-signature of a rough path increment. -/
def logIncrementTruncated (X : AlgebraicBranchedRoughPath T R)
    (s t : T) (n : Nat) : ForestAlgebra.LinearFunctional R :=
  BranchedSignature.logTruncated (X.character s t) n

@[simp]
theorem logIncrementTruncated_zero
    (X : AlgebraicBranchedRoughPath T R) (s t : T) :
    logIncrementTruncated X s t 0 = 0 := by
  simp [logIncrementTruncated, BranchedSignature.logTruncated]

@[simp]
theorem logIncrementTruncated_self
    (X : AlgebraicBranchedRoughPath T R) (t : T) (n : Nat) :
    logIncrementTruncated X t t n = 0 := by
  rw [logIncrementTruncated, X.character_self]
  exact BranchedSignature.logTruncated_unit n

theorem logIncrementTruncated_evalForest
    (X : AlgebraicBranchedRoughPath T R)
    (s t : T) (n : Nat) (φ : RootedForest) :
    ForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated X s t n) φ =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          ForestAlgebra.LinearFunctional.evalForest
            (ForestAlgebra.LinearFunctional.convolutionPower
              (ForestAlgebra.LinearFunctional.augmentationPart (X.character s t)) k)
            φ).sum :=
  BranchedSignature.logTruncated_evalForest (X.character s t) n φ

theorem logIncrementTruncated_evalTree
    (X : AlgebraicBranchedRoughPath T R)
    (s t : T) (n : Nat) (τ : RootedTree) :
    ForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated X s t n) (RootedForest.singleton τ) =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          ForestAlgebra.LinearFunctional.evalForest
            (ForestAlgebra.LinearFunctional.convolutionPower
              (ForestAlgebra.LinearFunctional.augmentationPart (X.character s t)) k)
            (RootedForest.singleton τ)).sum :=
  logIncrementTruncated_evalForest X s t n (RootedForest.singleton τ)

theorem AgreeUpToOrder.logIncrementTruncated
    {X Y : AlgebraicBranchedRoughPath T R} {m n : Nat}
    (h : AgreeUpToOrder X Y n) (s t : T) :
    ForestAlgebra.LinearFunctional.AgreeUpToOrder
      (AlgebraicBranchedRoughPath.logIncrementTruncated X s t m)
      (AlgebraicBranchedRoughPath.logIncrementTruncated Y s t m) n :=
  ForestAlgebra.LinearFunctional.agreeUpToOrder_logCharacterTruncated
    (fun φ hφ => by
      rw [AlgebraicBranchedRoughPath.character_evalForest,
        AlgebraicBranchedRoughPath.character_evalForest]
      exact h s t φ hφ)

theorem AgreeUpToOrder.logIncrementTruncated_evalForest
    {X Y : AlgebraicBranchedRoughPath T R} {m n : Nat}
    (h : AgreeUpToOrder X Y n) (s t : T) (φ : RootedForest)
    (hφ : RootedForest.order φ ≤ n) :
    ForestAlgebra.LinearFunctional.evalForest
        (AlgebraicBranchedRoughPath.logIncrementTruncated X s t m) φ =
      ForestAlgebra.LinearFunctional.evalForest
        (AlgebraicBranchedRoughPath.logIncrementTruncated Y s t m) φ :=
  (h.logIncrementTruncated (m := m) s t) φ hφ

end AlgebraicBranchedRoughPath

namespace AlgebraicLabelledBranchedRoughPath

variable {T : Type u} {α : Type v} {R : Type w} [Field R]

/-- Truncated labelled branched log-signature of a rough path increment. -/
def logIncrementTruncated (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : T) (n : Nat) : LForestAlgebra.LinearFunctional α R :=
  LabelledBranchedSignature.logTruncated (X.lcharacter s t) n

@[simp]
theorem logIncrementTruncated_zero
    (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : T) :
    logIncrementTruncated X s t 0 = 0 := by
  simp [logIncrementTruncated, LabelledBranchedSignature.logTruncated]

@[simp]
theorem logIncrementTruncated_self
    (X : AlgebraicLabelledBranchedRoughPath T α R) (t : T) (n : Nat) :
    logIncrementTruncated X t t n = 0 := by
  rw [logIncrementTruncated, lcharacter_self X]
  exact LabelledBranchedSignature.logTruncated_unit n

theorem logIncrementTruncated_evalForest
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : T) (n : Nat) (φ : LRootedForest α) :
    LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated X s t n) φ =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          LForestAlgebra.LinearFunctional.evalForest
            (LForestAlgebra.LinearFunctional.convolutionPower
              (LForestAlgebra.LinearFunctional.augmentationPart (X.lcharacter s t)) k)
            φ).sum :=
  LabelledBranchedSignature.logTruncated_evalForest (X.lcharacter s t) n φ

theorem logIncrementTruncated_evalTree
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : T) (n : Nat) (τ : LRootedTree α) :
    LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated X s t n) (LRootedForest.singleton τ) =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          LForestAlgebra.LinearFunctional.evalForest
            (LForestAlgebra.LinearFunctional.convolutionPower
              (LForestAlgebra.LinearFunctional.augmentationPart (X.lcharacter s t)) k)
            (LRootedForest.singleton τ)).sum :=
  logIncrementTruncated_evalForest X s t n (LRootedForest.singleton τ)

theorem AgreeUpToOrder.logIncrementTruncated
    {X Y : AlgebraicLabelledBranchedRoughPath T α R} {m n : Nat}
    (h : AgreeUpToOrder X Y n) (s t : T) :
    LForestAlgebra.LinearFunctional.AgreeUpToOrder
      (AlgebraicLabelledBranchedRoughPath.logIncrementTruncated X s t m)
      (AlgebraicLabelledBranchedRoughPath.logIncrementTruncated Y s t m) n :=
  LForestAlgebra.LinearFunctional.agreeUpToOrder_logCharacterTruncated
    (fun φ hφ => by
      rw [AlgebraicLabelledBranchedRoughPath.lcharacter_evalForest,
        AlgebraicLabelledBranchedRoughPath.lcharacter_evalForest]
      exact h s t φ hφ)

theorem AgreeUpToOrder.logIncrementTruncated_evalForest
    {X Y : AlgebraicLabelledBranchedRoughPath T α R} {m n : Nat}
    (h : AgreeUpToOrder X Y n) (s t : T) (φ : LRootedForest α)
    (hφ : LRootedForest.order φ ≤ n) :
    LForestAlgebra.LinearFunctional.evalForest
        (AlgebraicLabelledBranchedRoughPath.logIncrementTruncated X s t m) φ =
      LForestAlgebra.LinearFunctional.evalForest
        (AlgebraicLabelledBranchedRoughPath.logIncrementTruncated Y s t m) φ :=
  (h.logIncrementTruncated (m := m) s t) φ hφ

theorem logIncrementTruncated_comapMapLabels {β : Type z} (f : α → β)
    (X : AlgebraicLabelledBranchedRoughPath T β R)
    (s t : T) (n : Nat) :
    logIncrementTruncated (AlgebraicLabelledBranchedRoughPath.comapMapLabels f X) s t n =
      LForestAlgebra.LinearFunctional.comapMapLabels f
        (logIncrementTruncated X s t n) := by
  rw [logIncrementTruncated, logIncrementTruncated,
    AlgebraicLabelledBranchedRoughPath.lcharacter_comapMapLabels]
  exact LabelledBranchedSignature.logTruncated_comapMapLabels f
    (X.lcharacter s t) n

theorem logIncrementTruncated_comapMapLabels_evalForest {β : Type z} (f : α → β)
    (X : AlgebraicLabelledBranchedRoughPath T β R)
    (s t : T) (n : Nat) (φ : LRootedForest α) :
    LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated
          (AlgebraicLabelledBranchedRoughPath.comapMapLabels f X) s t n) φ =
      LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated X s t n) (LRootedForest.mapLabels f φ) := by
  rw [logIncrementTruncated_comapMapLabels]
  exact LForestAlgebra.LinearFunctional.evalForest_comapMapLabels f
    (logIncrementTruncated X s t n) φ

theorem logIncrementTruncated_comapMapLabels_evalTree {β : Type z} (f : α → β)
    (X : AlgebraicLabelledBranchedRoughPath T β R)
    (s t : T) (n : Nat) (τ : LRootedTree α) :
    LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated
          (AlgebraicLabelledBranchedRoughPath.comapMapLabels f X) s t n)
        (LRootedForest.singleton τ) =
      LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated X s t n) (LRootedForest.singleton (LRootedTree.map f τ)) := by
  rw [logIncrementTruncated_comapMapLabels_evalForest]
  simp [LRootedForest.mapLabels_singleton]

theorem logIncrementTruncated_comapEraseLabels
    (X : AlgebraicBranchedRoughPath T R)
    (s t : T) (n : Nat) :
    logIncrementTruncated
        (AlgebraicLabelledBranchedRoughPath.comapEraseLabels (α := α) X) s t n =
      LForestAlgebra.LinearFunctional.comapEraseLabels (α := α)
        (AlgebraicBranchedRoughPath.logIncrementTruncated X s t n) := by
  rw [logIncrementTruncated, AlgebraicBranchedRoughPath.logIncrementTruncated,
    AlgebraicLabelledBranchedRoughPath.lcharacter_comapEraseLabels]
  exact LabelledBranchedSignature.logTruncated_comapEraseLabels
    (X.character s t) n

theorem logIncrementTruncated_comapEraseLabels_evalForest
    (X : AlgebraicBranchedRoughPath T R)
    (s t : T) (n : Nat) (φ : LRootedForest α) :
    LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated
          (AlgebraicLabelledBranchedRoughPath.comapEraseLabels (α := α) X) s t n) φ =
      ForestAlgebra.LinearFunctional.evalForest
        (AlgebraicBranchedRoughPath.logIncrementTruncated X s t n)
        (LRootedForest.erase φ) := by
  rw [logIncrementTruncated_comapEraseLabels]
  exact LForestAlgebra.LinearFunctional.evalForest_comapEraseLabels
    (AlgebraicBranchedRoughPath.logIncrementTruncated X s t n) φ

theorem logIncrementTruncated_comapEraseLabels_evalTree
    (X : AlgebraicBranchedRoughPath T R)
    (s t : T) (n : Nat) (τ : LRootedTree α) :
    LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated
          (AlgebraicLabelledBranchedRoughPath.comapEraseLabels (α := α) X) s t n)
        (LRootedForest.singleton τ) =
      ForestAlgebra.LinearFunctional.evalForest
        (AlgebraicBranchedRoughPath.logIncrementTruncated X s t n)
        (RootedForest.singleton (LRootedTree.erase τ)) := by
  rw [logIncrementTruncated_comapEraseLabels_evalForest]
  simp [LRootedForest.erase_singleton]

theorem logIncrementTruncated_comapConstLabel
    (a : α) (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : T) (n : Nat) :
    AlgebraicBranchedRoughPath.logIncrementTruncated
        (AlgebraicLabelledBranchedRoughPath.comapConstLabel a X) s t n =
      LForestAlgebra.LinearFunctional.comapConstLabel a
        (logIncrementTruncated X s t n) := by
  rw [AlgebraicBranchedRoughPath.logIncrementTruncated, logIncrementTruncated,
    AlgebraicLabelledBranchedRoughPath.character_comapConstLabel]
  exact LabelledBranchedSignature.logTruncated_comapConstLabel a
    (X.lcharacter s t) n

theorem logIncrementTruncated_comapConstLabel_evalForest
    (a : α) (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : T) (n : Nat) (φ : RootedForest) :
    ForestAlgebra.LinearFunctional.evalForest
        (AlgebraicBranchedRoughPath.logIncrementTruncated
          (AlgebraicLabelledBranchedRoughPath.comapConstLabel a X) s t n) φ =
      LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated X s t n) (LRootedForest.constLabel a φ) := by
  rw [logIncrementTruncated_comapConstLabel]
  exact LForestAlgebra.LinearFunctional.evalForest_comapConstLabel a
    (logIncrementTruncated X s t n) φ

theorem logIncrementTruncated_comapConstLabel_evalTree
    (a : α) (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : T) (n : Nat) (τ : RootedTree) :
    ForestAlgebra.LinearFunctional.evalForest
        (AlgebraicBranchedRoughPath.logIncrementTruncated
          (AlgebraicLabelledBranchedRoughPath.comapConstLabel a X) s t n)
        (RootedForest.singleton τ) =
      LForestAlgebra.LinearFunctional.evalForest
        (logIncrementTruncated X s t n)
        (LRootedForest.singleton (LRootedTree.constLabel a τ)) := by
  rw [logIncrementTruncated_comapConstLabel_evalForest]
  simp [LRootedForest.constLabel_singleton]

end AlgebraicLabelledBranchedRoughPath

end

end RoughPaths
