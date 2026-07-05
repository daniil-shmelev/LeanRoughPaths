/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.CharacterConvolution
import HopfAlgebras.Combinatorial.BCK
import HopfAlgebras.Combinatorial.LBCK
import RoughPaths.HopfRoughPath.Basic
import HopfAlgebras.Hopf.LabelledCharacterConvolution

/-!
# Algebraic Branched Rough Paths

This file defines the algebraic part of branched rough paths using the
rooted-forest Hopf algebra already formalised in the library. Increments are
characters on the forest algebra and Chen's identity is character convolution.

Analytic regularity conditions, such as finite `p`-variation, are not included
here.

## Main definitions

* `AlgebraicBranchedRoughPath` - unlabelled branched signature increments
* `AlgebraicLabelledBranchedRoughPath` - labelled branched signature increments
* `AlgebraicBranchedRoughPath.increment_convolution_reverse` - reverse increments
  convolve to the unit

## References

* Massimiliano Gubinelli, *Ramification of rough paths*
* Christian Brouder, Alessandra Frabetti, Christian Krattenthaler,
  *Non-commutative Hopf algebra of formal diffeomorphisms*
* Peter Friz, Nicolas Victoir, *Multidimensional Stochastic Processes as Rough Paths*
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z y

/-- A branched rough path **is** a Hopf rough path over the
Butcher–Connes–Kreimer bialgebra: increments are characters on rooted
forests and Chen's identity is convolution in the character monoid. -/
abbrev AlgebraicBranchedRoughPath (T : Type u) (R : Type v)
    [CommSemiring R] : Type (max u v) :=
  HopfRoughPath bckBialg T R

namespace AlgebraicBranchedRoughPath

noncomputable section

variable {T : Type u} {R : Type v} [CommSemiring R]

/-- The constant identity branched rough path. -/
abbrev unit (T : Type u) (R : Type v) [CommSemiring R] :
    AlgebraicBranchedRoughPath T R :=
  HopfRoughPath.unit bckBialg T R

/-- Pull a branched rough path back along a map of time domains. -/
abbrev comapTime {S : Type w} (f : S → T)
    (X : AlgebraicBranchedRoughPath T R) : AlgebraicBranchedRoughPath S R :=
  HopfRoughPath.comapTime f X

/-- Coordinate of an increment on a rooted tree. -/
def treeCoeff (X : AlgebraicBranchedRoughPath T R) (s t : T)
    (τ : RootedTree) : R :=
  X.coeff s t (RootedForest.singleton τ)

/-- The increment as an algebra character of the forest algebra, via
the `AddMonoidAlgebra.lift` bridge `bckCharacter`. -/
def character (X : AlgebraicBranchedRoughPath T R) (s t : T) :
    ForestAlgebra.Character R :=
  bckCharacter (X.increment s t).1 (X.increment s t).2

@[simp]
theorem character_evalForest (X : AlgebraicBranchedRoughPath T R)
    (s t : T) (φ : RootedForest) :
    (X.character s t).evalForest φ = X.coeff s t φ :=
  evalForest_bckCharacter _ _ φ

@[ext]
theorem ext {X Y : AlgebraicBranchedRoughPath T R}
    (h : ∀ s t φ, X.coeff s t φ = Y.coeff s t φ) : X = Y :=
  HopfRoughPath.ext_coeff h

@[simp]
theorem coeff_comapTime {S : Type w} (f : S → T)
    (X : AlgebraicBranchedRoughPath T R) (s t : S) (φ : RootedForest) :
    (comapTime f X).coeff s t φ = X.coeff (f s) (f t) φ :=
  rfl

@[simp]
theorem treeCoeff_comapTime {S : Type w} (f : S → T)
    (X : AlgebraicBranchedRoughPath T R) (s t : S) (τ : RootedTree) :
    treeCoeff (comapTime f X) s t τ = treeCoeff X (f s) (f t) τ :=
  rfl

@[simp]
theorem comapTime_id (X : AlgebraicBranchedRoughPath T R) :
    comapTime id X = X :=
  rfl

theorem comapTime_comp {S : Type w} {U : Type y} (f : S → T) (g : U → S)
    (X : AlgebraicBranchedRoughPath T R) :
    comapTime g (comapTime f X) = comapTime (f ∘ g) X :=
  rfl

@[simp]
theorem comapTime_unit {S : Type w} (f : S → T) :
    comapTime f (unit T R) = unit S R :=
  rfl

@[simp]
theorem coeff_empty (X : AlgebraicBranchedRoughPath T R) (s t : T) :
    X.coeff s t RootedForest.empty = 1 :=
  X.coeff_one s t

@[simp]
theorem coeff_zero (X : AlgebraicBranchedRoughPath T R) (s t : T) :
    X.coeff s t 0 = 1 :=
  X.coeff_one s t

@[simp]
theorem coeff_add (X : AlgebraicBranchedRoughPath T R) (s t : T)
    (φ ψ : RootedForest) :
    X.coeff s t (φ + ψ) = X.coeff s t φ * X.coeff s t ψ :=
  X.coeff_mul_single rfl s t

/-- Two algebraic branched rough paths agree through forest order `n`. -/
abbrev AgreeUpToOrder (X Y : AlgebraicBranchedRoughPath T R) (n : Nat) :
    Prop :=
  HopfRoughPath.AgreeUpTo RootedForest.order X Y n

theorem agreeUpToOrder_refl (X : AlgebraicBranchedRoughPath T R) (n : Nat) :
    AgreeUpToOrder X X n :=
  HopfRoughPath.agreeUpTo_refl _ X n

theorem agreeUpToOrder_iff_coeff
    (X Y : AlgebraicBranchedRoughPath T R) (n : Nat) :
    AgreeUpToOrder X Y n ↔
      ∀ s t φ, RootedForest.order φ ≤ n → X.coeff s t φ = Y.coeff s t φ := Iff.rfl

theorem eq_of_agreeUpToOrder_all {X Y : AlgebraicBranchedRoughPath T R}
    (h : ∀ n, AgreeUpToOrder X Y n) : X = Y :=
  HopfRoughPath.eq_of_agreeUpTo_all h

theorem agreeUpToOrder_all_iff_eq {X Y : AlgebraicBranchedRoughPath T R} :
    (∀ n, AgreeUpToOrder X Y n) ↔ X = Y := by
  constructor
  · exact eq_of_agreeUpToOrder_all
  · intro h n
    cases h
    exact agreeUpToOrder_refl X n

@[simp]
theorem character_self (X : AlgebraicBranchedRoughPath T R) (t : T) :
    X.character t t = ForestAlgebra.Character.unit R :=
  ForestAlgebra.Character.ext fun φ => by
    rw [character_evalForest, ForestAlgebra.Character.unit_evalForest]
    exact (X.coeff_diagonal t φ).trans
      (BCK.counitCoeff_eq_boolIte φ).symm

theorem coeff_self (X : AlgebraicBranchedRoughPath T R)
    (t : T) (φ : RootedForest) :
    X.coeff t t φ = ForestAlgebra.counitCoeff (R := R) φ :=
  (X.coeff_diagonal t φ).trans (BCK.counitCoeff_eq_boolIte φ).symm

/-- Chen's identity for the lifted algebra characters. -/
theorem chen_eq (X : AlgebraicBranchedRoughPath T R) (s t u : T) :
    X.character s u =
      ForestAlgebra.Character.convolution (X.character s t) (X.character t u) :=
  ForestAlgebra.Character.ext fun φ => by
    rw [character_evalForest, convolution_evalForest_conv,
      HopfRoughPath.chen_coeff X s t u φ]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    rw [character_evalForest, character_evalForest]

theorem increment_convolution_reverse (X : AlgebraicBranchedRoughPath T R) (s t : T) :
    ForestAlgebra.Character.convolution (X.character s t) (X.character t s) =
      ForestAlgebra.Character.unit R := by
  rw [← X.chen_eq s t s, X.character_self s]

theorem reverse_convolution_increment (X : AlgebraicBranchedRoughPath T R) (s t : T) :
    ForestAlgebra.Character.convolution (X.character t s) (X.character s t) =
      ForestAlgebra.Character.unit R := by
  rw [← X.chen_eq t s t, X.character_self t]

theorem chen_coeff (X : AlgebraicBranchedRoughPath T R)
    (s t u : T) (φ : RootedForest) :
    X.coeff s u φ =
      RootedForest.convolutionCoeff (X.character s t) (X.character t u) φ := by
  rw [← ForestAlgebra.Character.convolution_evalForest, ← X.chen_eq s t u,
    character_evalForest]

theorem chen_treeCoeff (X : AlgebraicBranchedRoughPath T R)
    (s t u : T) (τ : RootedTree) :
    treeCoeff X s u τ =
      RootedTree.convolutionCoeff (X.character s t) (X.character t u) τ := by
  rw [treeCoeff, chen_coeff X s t u]
  exact (RootedTree.convolutionCoeff_eq_singleton (X.character s t) (X.character t u) τ).symm

theorem unit_coeff (s t : T) (φ : RootedForest) :
    (unit T R).coeff s t φ = ForestAlgebra.counitCoeff (R := R) φ :=
  (BCK.counitCoeff_eq_boolIte φ).symm

end

end AlgebraicBranchedRoughPath

/-- A labelled branched rough path **is** a Hopf rough path over the
labelled BCK bialgebra of decorated rooted forests. -/
abbrev AlgebraicLabelledBranchedRoughPath
    (T : Type u) (α : Type v) (R : Type w) [CommSemiring R] :
    Type (max u v w) :=
  HopfRoughPath (lbckBialg α) T R

namespace AlgebraicLabelledBranchedRoughPath

noncomputable section

variable {T : Type u} {α : Type v} {R : Type w} [CommSemiring R]

/-- The constant identity labelled branched rough path. -/
abbrev unit (T : Type u) (α : Type v) (R : Type w) [CommSemiring R] :
    AlgebraicLabelledBranchedRoughPath T α R :=
  HopfRoughPath.unit (lbckBialg α) T R

/-- Pull a labelled branched rough path back along a map of time domains. -/
abbrev comapTime {S : Type z} (f : S → T)
    (X : AlgebraicLabelledBranchedRoughPath T α R) :
    AlgebraicLabelledBranchedRoughPath S α R :=
  HopfRoughPath.comapTime f X

@[simp]
theorem comapTime_increment {S : Type z} (f : S → T)
    (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : S) :
    (comapTime f X).increment s t = X.increment (f s) (f t) :=
  rfl

/-- Coordinate of an increment on a labelled rooted tree. -/
def treeCoeff (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : T)
    (τ : LRootedTree α) : R :=
  X.coeff s t (LRootedForest.singleton τ)

/-- The increment as an algebra character of the labelled forest
algebra, via the `AddMonoidAlgebra.lift` bridge `lbckCharacter`. -/
def lcharacter (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : T) :
    LForestAlgebra.Character α R :=
  lbckCharacter (X.increment s t).1 (X.increment s t).2

@[simp]
theorem lcharacter_evalForest (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : T) (φ : LRootedForest α) :
    (X.lcharacter s t).evalForest φ = X.coeff s t φ :=
  evalForest_lbckCharacter _ _ φ

@[simp]
theorem lcharacter_self (X : AlgebraicLabelledBranchedRoughPath T α R)
    (t : T) :
    X.lcharacter t t = LForestAlgebra.Character.unit α R :=
  LForestAlgebra.Character.ext fun φ => by
    rw [lcharacter_evalForest, LForestAlgebra.Character.unit_evalForest]
    exact (X.coeff_diagonal t φ).trans
      (LBCK.counitCoeff_eq_boolIte φ).symm

/-- Chen's identity for the lifted labelled algebra characters. -/
theorem lchen_eq (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t u : T) :
    X.lcharacter s u =
      LForestAlgebra.Character.convolution (X.lcharacter s t)
        (X.lcharacter t u) :=
  LForestAlgebra.Character.ext fun φ => by
    rw [lcharacter_evalForest, convolution_evalForest_lconv,
      HopfRoughPath.chen_coeff X s t u φ]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    rw [lcharacter_evalForest, lcharacter_evalForest]

/-- Pull a labelled branched rough path back along a relabelling map. -/
def comapMapLabels {β : Type z} (f : α → β)
    (X : AlgebraicLabelledBranchedRoughPath T β R) :
    AlgebraicLabelledBranchedRoughPath T α R where
  increment s t :=
    ⟨(LForestAlgebra.Character.comapMapLabels f (X.lcharacter s t)).evalForest,
      evalForest_lbckIsCharacter _⟩
  identity t := by
    have hchar : LForestAlgebra.Character.comapMapLabels f
        (X.lcharacter t t) = LForestAlgebra.Character.unit α R := by
      rw [lcharacter_self,
        LForestAlgebra.Character.unit_eq_counit (α := β) (R := R),
        LForestAlgebra.Character.unit_eq_counit (α := α) (R := R)]
      exact LForestAlgebra.Character.comapMapLabels_counit (R := R) f
    exact CombBialg.Character.ext fun φ => by
      show (LForestAlgebra.Character.comapMapLabels f
        (X.lcharacter t t)).evalForest φ = _
      rw [hchar, LForestAlgebra.Character.unit_evalForest]
      exact LBCK.counitCoeff_eq_boolIte φ
  chen s t u := by
    have hchar : LForestAlgebra.Character.comapMapLabels f
        (X.lcharacter s u) =
        LForestAlgebra.Character.convolution
          (LForestAlgebra.Character.comapMapLabels f (X.lcharacter s t))
          (LForestAlgebra.Character.comapMapLabels f (X.lcharacter t u)) := by
      rw [lchen_eq X s t u]
      exact (LForestAlgebra.Character.convolution_comapMapLabels f
        (X.lcharacter s t) (X.lcharacter t u)).symm
    exact CombBialg.Character.ext fun φ => by
      show (LForestAlgebra.Character.comapMapLabels f
        (X.lcharacter s u)).evalForest φ = _
      rw [hchar, convolution_evalForest_lconv]
      rfl

@[simp]
theorem coeff_comapMapLabels {β : Type z} (f : α → β)
    (X : AlgebraicLabelledBranchedRoughPath T β R) (s t : T)
    (φ : LRootedForest α) :
    (comapMapLabels f X).coeff s t φ =
      X.coeff s t (LRootedForest.mapLabels f φ) := by
  show (LForestAlgebra.Character.comapMapLabels f
    (X.lcharacter s t)).evalForest φ = _
  rw [LForestAlgebra.Character.comapMapLabels_evalForest,
    lcharacter_evalForest]

@[ext]
theorem ext {X Y : AlgebraicLabelledBranchedRoughPath T α R}
    (h : ∀ s t φ, X.coeff s t φ = Y.coeff s t φ) : X = Y :=
  HopfRoughPath.ext_coeff h

@[simp]
theorem coeff_comapTime {S : Type z} (f : S → T)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : S) (φ : LRootedForest α) :
    (comapTime f X).coeff s t φ = X.coeff (f s) (f t) φ :=
  rfl

@[simp]
theorem treeCoeff_comapTime {S : Type z} (f : S → T)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : S) (τ : LRootedTree α) :
    treeCoeff (comapTime f X) s t τ = treeCoeff X (f s) (f t) τ :=
  rfl

@[simp]
theorem comapTime_id (X : AlgebraicLabelledBranchedRoughPath T α R) :
    comapTime id X = X :=
  rfl

theorem comapTime_comp {S : Type z} {U : Type y} (f : S → T) (g : U → S)
    (X : AlgebraicLabelledBranchedRoughPath T α R) :
    comapTime g (comapTime f X) = comapTime (f ∘ g) X :=
  rfl

@[simp]
theorem comapTime_unit {S : Type z} (f : S → T) :
    comapTime f (unit T α R) = unit S α R :=
  rfl

@[simp]
theorem coeff_empty (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : T) :
    X.coeff s t LRootedForest.empty = 1 :=
  X.coeff_one s t

@[simp]
theorem coeff_zero (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : T) :
    X.coeff s t 0 = 1 :=
  X.coeff_one s t

@[simp]
theorem coeff_add (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : T)
    (φ ψ : LRootedForest α) :
    X.coeff s t (φ + ψ) = X.coeff s t φ * X.coeff s t ψ := by
  have h : X.coeff s t φ * X.coeff s t ψ =
      (([φ + ψ] : List (LRootedForest α)).map
        (X.increment s t : LRootedForest α → R)).sum :=
    (X.increment s t).2.2 φ ψ
  rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at h
  exact h.symm

/-- Two algebraic labelled branched rough paths agree through forest order `n`. -/
abbrev AgreeUpToOrder
    (X Y : AlgebraicLabelledBranchedRoughPath T α R) (n : Nat) : Prop :=
  HopfRoughPath.AgreeUpTo LRootedForest.order X Y n

theorem agreeUpToOrder_refl
    (X : AlgebraicLabelledBranchedRoughPath T α R) (n : Nat) :
    AgreeUpToOrder X X n :=
  HopfRoughPath.agreeUpTo_refl _ X n

theorem agreeUpToOrder_iff_coeff
    (X Y : AlgebraicLabelledBranchedRoughPath T α R) (n : Nat) :
    AgreeUpToOrder X Y n ↔
      ∀ s t φ, LRootedForest.order φ ≤ n → X.coeff s t φ = Y.coeff s t φ := Iff.rfl

theorem eq_of_agreeUpToOrder_all
    {X Y : AlgebraicLabelledBranchedRoughPath T α R}
    (h : ∀ n, AgreeUpToOrder X Y n) : X = Y := by
  ext s t φ
  exact h (LRootedForest.order φ) s t φ le_rfl

theorem agreeUpToOrder_all_iff_eq
    {X Y : AlgebraicLabelledBranchedRoughPath T α R} :
    (∀ n, AgreeUpToOrder X Y n) ↔ X = Y := by
  constructor
  · exact eq_of_agreeUpToOrder_all
  · intro h n
    cases h
    exact agreeUpToOrder_refl X n

theorem AgreeUpToOrder.comapMapLabels {β : Type z} (f : α → β)
    {X Y : AlgebraicLabelledBranchedRoughPath T β R} {n : Nat}
    (h : AgreeUpToOrder X Y n) :
    AgreeUpToOrder (comapMapLabels f X) (comapMapLabels f Y) n := by
  intro s t φ hφ
  rw [coeff_comapMapLabels, coeff_comapMapLabels]
  exact h s t (LRootedForest.mapLabels f φ) (by simpa using hφ)

theorem treeCoeff_comapMapLabels {β : Type z} (f : α → β)
    (X : AlgebraicLabelledBranchedRoughPath T β R)
    (s t : T) (τ : LRootedTree α) :
    treeCoeff (comapMapLabels f X) s t τ =
      treeCoeff X s t (LRootedTree.map f τ) := by
  rw [treeCoeff, coeff_comapMapLabels, treeCoeff, LRootedForest.mapLabels_singleton]

@[simp]
theorem comapMapLabels_id (X : AlgebraicLabelledBranchedRoughPath T α R) :
    comapMapLabels id X = X := by
  ext s t φ
  rw [coeff_comapMapLabels]
  simp

theorem comapMapLabels_comp {β : Type z} {γ : Type y}
    (f : α → β) (g : β → γ)
    (X : AlgebraicLabelledBranchedRoughPath T γ R) :
    comapMapLabels f (comapMapLabels g X) = comapMapLabels (g ∘ f) X := by
  ext s t φ
  rw [coeff_comapMapLabels, coeff_comapMapLabels, coeff_comapMapLabels]
  simp [LRootedForest.mapLabels_comp, Function.comp_def]

@[simp]
theorem comapMapLabels_unit {β : Type z} (f : α → β) :
    comapMapLabels f (unit T β R) = unit T α R := by
  ext s t φ
  rw [coeff_comapMapLabels]
  exact (LBCK.counitCoeff_eq_boolIte _).symm.trans
    ((LForestAlgebra.counitCoeff_mapLabels (R := R) f φ).trans
      (LBCK.counitCoeff_eq_boolIte φ))

/-- Pull an unlabelled branched rough path back by forgetting labels. -/
def comapEraseLabels (X : AlgebraicBranchedRoughPath T R) :
    AlgebraicLabelledBranchedRoughPath T α R where
  increment s t :=
    ⟨(LForestAlgebra.Character.comapEraseLabels (α := α)
        (X.character s t)).evalForest,
      evalForest_lbckIsCharacter _⟩
  identity t := by
    have hchar : LForestAlgebra.Character.comapEraseLabels (α := α)
        (X.character t t) = LForestAlgebra.Character.unit α R := by
      rw [AlgebraicBranchedRoughPath.character_self,
        ForestAlgebra.Character.unit_eq_counit,
        LForestAlgebra.Character.unit_eq_counit (α := α) (R := R)]
      exact LForestAlgebra.Character.comapEraseLabels_counit
        (α := α) (R := R)
    exact CombBialg.Character.ext fun φ => by
      show (LForestAlgebra.Character.comapEraseLabels (α := α)
        (X.character t t)).evalForest φ = _
      rw [hchar, LForestAlgebra.Character.unit_evalForest]
      exact LBCK.counitCoeff_eq_boolIte φ
  chen s t u := by
    have hchar : LForestAlgebra.Character.comapEraseLabels (α := α)
        (X.character s u) =
        LForestAlgebra.Character.convolution
          (LForestAlgebra.Character.comapEraseLabels (α := α)
            (X.character s t))
          (LForestAlgebra.Character.comapEraseLabels (α := α)
            (X.character t u)) := by
      rw [X.chen_eq s t u]
      exact (LForestAlgebra.Character.convolution_comapEraseLabels
        (α := α) (X.character s t) (X.character t u)).symm
    exact CombBialg.Character.ext fun φ => by
      show (LForestAlgebra.Character.comapEraseLabels (α := α)
        (X.character s u)).evalForest φ = _
      rw [hchar, convolution_evalForest_lconv]
      rfl

/-- Pull a labelled branched rough path back along constant labelling. -/
def comapConstLabel (a : α) (X : AlgebraicLabelledBranchedRoughPath T α R) :
    AlgebraicBranchedRoughPath T R where
  increment s t :=
    ⟨(LForestAlgebra.Character.comapConstLabel a
        (X.lcharacter s t)).evalForest,
      evalForest_isCharacter _⟩
  identity t := by
    have hchar : LForestAlgebra.Character.comapConstLabel a
        (X.lcharacter t t) = ForestAlgebra.Character.unit R := by
      rw [lcharacter_self,
        LForestAlgebra.Character.unit_eq_counit (α := α) (R := R),
        ForestAlgebra.Character.unit_eq_counit]
      exact LForestAlgebra.Character.comapConstLabel_counit (R := R) a
    exact CombBialg.Character.ext fun φ => by
      show (LForestAlgebra.Character.comapConstLabel a
        (X.lcharacter t t)).evalForest φ = _
      rw [hchar, ForestAlgebra.Character.unit_evalForest]
      exact BCK.counitCoeff_eq_boolIte φ
  chen s t u := by
    have hchar : LForestAlgebra.Character.comapConstLabel a
        (X.lcharacter s u) =
        ForestAlgebra.Character.convolution
          (LForestAlgebra.Character.comapConstLabel a (X.lcharacter s t))
          (LForestAlgebra.Character.comapConstLabel a (X.lcharacter t u)) := by
      rw [lchen_eq X s t u]
      exact (LForestAlgebra.Character.convolution_comapConstLabel a
        (X.lcharacter s t) (X.lcharacter t u)).symm
    exact CombBialg.Character.ext fun φ => by
      show (LForestAlgebra.Character.comapConstLabel a
        (X.lcharacter s u)).evalForest φ = _
      rw [hchar, convolution_evalForest_conv]
      rfl

theorem coeff_comapEraseLabels (X : AlgebraicBranchedRoughPath T R)
    (s t : T) (φ : LRootedForest α) :
    (comapEraseLabels (α := α) X).coeff s t φ =
      X.coeff s t (LRootedForest.erase φ) := by
  show (LForestAlgebra.Character.comapEraseLabels (α := α)
    (X.character s t)).evalForest φ = _
  exact (LForestAlgebra.Character.comapEraseLabels_evalForest
    (X.character s t) φ).trans
    (AlgebraicBranchedRoughPath.character_evalForest X s t _)

theorem AgreeUpToOrder.comapEraseLabels
    {X Y : AlgebraicBranchedRoughPath T R} {n : Nat}
    (h : AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n) :
    AgreeUpToOrder (comapEraseLabels (α := α) X) (comapEraseLabels (α := α) Y) n := by
  intro s t φ hφ
  rw [coeff_comapEraseLabels, coeff_comapEraseLabels]
  exact h s t (LRootedForest.erase φ) (by simpa using hφ)

theorem treeCoeff_comapEraseLabels (X : AlgebraicBranchedRoughPath T R)
    (s t : T) (τ : LRootedTree α) :
    treeCoeff (comapEraseLabels (α := α) X) s t τ =
      AlgebraicBranchedRoughPath.treeCoeff X s t (LRootedTree.erase τ) := by
  rw [treeCoeff, coeff_comapEraseLabels, AlgebraicBranchedRoughPath.treeCoeff,
    LRootedForest.erase_singleton]

theorem coeff_comapConstLabel (a : α)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : T) (φ : RootedForest) :
    (comapConstLabel a X).coeff s t φ =
      X.coeff s t (LRootedForest.constLabel a φ) := by
  show (LForestAlgebra.Character.comapConstLabel a
    (X.lcharacter s t)).evalForest φ = _
  exact (LForestAlgebra.Character.comapConstLabel_evalForest a
    (X.lcharacter s t) φ).trans (lcharacter_evalForest X s t _)

theorem AgreeUpToOrder.comapConstLabel (a : α)
    {X Y : AlgebraicLabelledBranchedRoughPath T α R} {n : Nat}
    (h : AgreeUpToOrder X Y n) :
    AlgebraicBranchedRoughPath.AgreeUpToOrder (comapConstLabel a X) (comapConstLabel a Y) n := by
  intro s t φ hφ
  rw [coeff_comapConstLabel, coeff_comapConstLabel]
  exact h s t (LRootedForest.constLabel a φ) (by simpa using hφ)

theorem treeCoeff_comapConstLabel (a : α)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t : T) (τ : RootedTree) :
    AlgebraicBranchedRoughPath.treeCoeff (comapConstLabel a X) s t τ =
      treeCoeff X s t (LRootedTree.constLabel a τ) := by
  rw [AlgebraicBranchedRoughPath.treeCoeff, coeff_comapConstLabel, treeCoeff,
    LRootedForest.constLabel_singleton]

theorem comapConstLabel_comapEraseLabels
    (a : α) (X : AlgebraicBranchedRoughPath T R) :
    comapConstLabel a (comapEraseLabels (α := α) X) = X := by
  apply AlgebraicBranchedRoughPath.ext
  intro s t φ
  rw [coeff_comapConstLabel, coeff_comapEraseLabels]
  rw [LRootedForest.erase_constLabel]

@[simp]
theorem comapEraseLabels_unit :
    comapEraseLabels (α := α) (AlgebraicBranchedRoughPath.unit T R) = unit T α R := by
  ext s t φ
  rw [coeff_comapEraseLabels]
  exact (BCK.counitCoeff_eq_boolIte _).symm.trans
    ((LForestAlgebra.counitCoeff_erase (R := R) φ).trans
      (LBCK.counitCoeff_eq_boolIte φ))

@[simp]
theorem comapConstLabel_unit (a : α) :
    comapConstLabel a (unit T α R) = AlgebraicBranchedRoughPath.unit T R := by
  apply AlgebraicBranchedRoughPath.ext
  intro s t φ
  rw [coeff_comapConstLabel]
  have h :=
    LForestAlgebra.counitCoeff_erase (R := R) (LRootedForest.constLabel a φ)
  rw [LRootedForest.erase_constLabel] at h
  exact (LBCK.counitCoeff_eq_boolIte _).symm.trans
    (h.symm.trans (BCK.counitCoeff_eq_boolIte φ))

/-- A labelled branched rough path whose increments only depend on unlabelled forests. -/
def LabelInvariant (X : AlgebraicLabelledBranchedRoughPath T α R) : Prop :=
  ∀ s t : T, LForestAlgebra.Character.LabelInvariant (X.lcharacter s t)

theorem LabelInvariant.lcharacter {X : AlgebraicLabelledBranchedRoughPath T α R}
    (h : LabelInvariant X) (s t : T) :
    LForestAlgebra.Character.LabelInvariant (X.lcharacter s t) :=
  h s t

theorem LabelInvariant.coeff_eq {X : AlgebraicLabelledBranchedRoughPath T α R}
    (h : LabelInvariant X) {s t : T} {φ ψ : LRootedForest α}
    (hφψ : LRootedForest.erase φ = LRootedForest.erase ψ) :
    X.coeff s t φ = X.coeff s t ψ := by
  have hh := h s t φ ψ hφψ
  rwa [lcharacter_evalForest, lcharacter_evalForest] at hh

theorem lcharacter_comapEraseLabels (X : AlgebraicBranchedRoughPath T R)
    (s t : T) :
    (comapEraseLabels (α := α) X).lcharacter s t =
      LForestAlgebra.Character.comapEraseLabels (α := α)
        (X.character s t) :=
  LForestAlgebra.Character.ext fun φ => by
    rw [lcharacter_evalForest, coeff_comapEraseLabels]
    exact ((LForestAlgebra.Character.comapEraseLabels_evalForest
      (X.character s t) φ).trans
      (AlgebraicBranchedRoughPath.character_evalForest X s t _)).symm

theorem lcharacter_comapMapLabels {β : Type z} (f : α → β)
    (X : AlgebraicLabelledBranchedRoughPath T β R) (s t : T) :
    (comapMapLabels f X).lcharacter s t =
      LForestAlgebra.Character.comapMapLabels f (X.lcharacter s t) :=
  LForestAlgebra.Character.ext fun φ => by
    rw [lcharacter_evalForest, coeff_comapMapLabels]
    exact ((LForestAlgebra.Character.comapMapLabels_evalForest f
      (X.lcharacter s t) φ).trans (lcharacter_evalForest X s t _)).symm

theorem character_comapConstLabel (a : α)
    (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : T) :
    (comapConstLabel a X).character s t =
      LForestAlgebra.Character.comapConstLabel a (X.lcharacter s t) :=
  ForestAlgebra.Character.ext fun φ => by
    rw [AlgebraicBranchedRoughPath.character_evalForest,
      coeff_comapConstLabel]
    exact ((LForestAlgebra.Character.comapConstLabel_evalForest a
      (X.lcharacter s t) φ).trans (lcharacter_evalForest X s t _)).symm

theorem labelInvariant_comapEraseLabels (X : AlgebraicBranchedRoughPath T R) :
    LabelInvariant (comapEraseLabels (α := α) X) := by
  intro s t
  rw [lcharacter_comapEraseLabels]
  exact LForestAlgebra.Character.labelInvariant_comapEraseLabels (X.character s t)

theorem labelInvariant_unit : LabelInvariant (unit T α R) := by
  rw [← comapEraseLabels_unit (α := α) (T := T) (R := R)]
  exact labelInvariant_comapEraseLabels (α := α) (AlgebraicBranchedRoughPath.unit T R)

theorem LabelInvariant.comapMapLabels {β : Type z}
    {X : AlgebraicLabelledBranchedRoughPath T β R} (h : LabelInvariant X)
    (f : α → β) : LabelInvariant (comapMapLabels f X) := by
  intro s t
  rw [lcharacter_comapMapLabels]
  exact (h s t).comapMapLabels f

theorem LabelInvariant.comapConstLabel_eq
    {X : AlgebraicLabelledBranchedRoughPath T α R} (h : LabelInvariant X)
    (x y : α) : comapConstLabel x X = comapConstLabel y X := by
  apply AlgebraicBranchedRoughPath.ext
  intro s t φ
  rw [coeff_comapConstLabel, coeff_comapConstLabel]
  exact h.coeff_eq (by simp)

theorem LabelInvariant.comapEraseLabels_comapConstLabel
    {X : AlgebraicLabelledBranchedRoughPath T α R} (h : LabelInvariant X)
    (x : α) :
    comapEraseLabels (α := α) (comapConstLabel x X) = X := by
  ext s t φ
  rw [coeff_comapEraseLabels, coeff_comapConstLabel]
  exact h.coeff_eq (by simp)

/-- Unlabelled branched rough paths are equivalent to label-invariant labelled ones. -/
noncomputable def labelInvariantEquiv [Nonempty α] :
    AlgebraicBranchedRoughPath T R ≃
      {X : AlgebraicLabelledBranchedRoughPath T α R // LabelInvariant X} where
  toFun X := ⟨comapEraseLabels (α := α) X, labelInvariant_comapEraseLabels X⟩
  invFun X := comapConstLabel (Classical.choice (inferInstance : Nonempty α)) X.1
  left_inv X :=
    comapConstLabel_comapEraseLabels
      (Classical.choice (inferInstance : Nonempty α)) X
  right_inv X := by
    cases X with
    | mk X hX =>
        apply Subtype.ext
        exact hX.comapEraseLabels_comapConstLabel
          (Classical.choice (inferInstance : Nonempty α))

@[simp]
theorem labelInvariantEquiv_apply [Nonempty α] (X : AlgebraicBranchedRoughPath T R) :
    (labelInvariantEquiv (α := α) X).1 = comapEraseLabels (α := α) X :=
  rfl

@[simp]
theorem labelInvariantEquiv_symm_apply [Nonempty α]
    (X : {X : AlgebraicLabelledBranchedRoughPath T α R // LabelInvariant X}) :
    (labelInvariantEquiv (α := α) (T := T) (R := R)).symm X =
      comapConstLabel (Classical.choice (inferInstance : Nonempty α)) X.1 :=
  rfl

theorem labelInvariantEquiv_unit [Nonempty α] :
    labelInvariantEquiv (α := α) (T := T) (R := R)
        (AlgebraicBranchedRoughPath.unit T R) =
      ⟨unit T α R, labelInvariant_unit⟩ := by
  apply Subtype.ext
  exact comapEraseLabels_unit (α := α) (T := T) (R := R)

theorem labelInvariantEquiv_symm_unit [Nonempty α] :
    (labelInvariantEquiv (α := α) (T := T) (R := R)).symm
        ⟨unit T α R, labelInvariant_unit⟩ =
      AlgebraicBranchedRoughPath.unit T R :=
  comapConstLabel_unit (Classical.choice (inferInstance : Nonempty α))

theorem labelInvariant_iff_exists_comapEraseLabels [Nonempty α]
    (X : AlgebraicLabelledBranchedRoughPath T α R) :
    LabelInvariant X ↔
      ∃ Y : AlgebraicBranchedRoughPath T R, comapEraseLabels (α := α) Y = X := by
  constructor
  · intro hX
    let x := Classical.choice (inferInstance : Nonempty α)
    exact ⟨comapConstLabel x X, hX.comapEraseLabels_comapConstLabel x⟩
  · rintro ⟨Y, rfl⟩
    exact labelInvariant_comapEraseLabels (α := α) Y

theorem agreeUpToOrder_of_comapEraseLabels
    {X Y : AlgebraicBranchedRoughPath T R} {n : Nat} (x : α)
    (h : AgreeUpToOrder (comapEraseLabels (α := α) X)
      (comapEraseLabels (α := α) Y) n) :
    AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n := by
  intro s t φ hφ
  have hlabel := h s t (LRootedForest.constLabel x φ) (by simpa using hφ)
  rw [coeff_comapEraseLabels, coeff_comapEraseLabels,
    LRootedForest.erase_constLabel] at hlabel
  exact hlabel

theorem agreeUpToOrder_comapEraseLabels_iff [Nonempty α]
    {X Y : AlgebraicBranchedRoughPath T R} {n : Nat} :
    AgreeUpToOrder (comapEraseLabels (α := α) X)
        (comapEraseLabels (α := α) Y) n ↔
      AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n := by
  constructor
  · exact agreeUpToOrder_of_comapEraseLabels
      (Classical.choice (inferInstance : Nonempty α))
  · exact AgreeUpToOrder.comapEraseLabels

theorem agreeUpToOrder_all_comapEraseLabels_iff [Nonempty α]
    {X Y : AlgebraicBranchedRoughPath T R} :
    (∀ n, AgreeUpToOrder (comapEraseLabels (α := α) X)
        (comapEraseLabels (α := α) Y) n) ↔
      ∀ n, AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n := by
  constructor
  · intro h n
    exact (agreeUpToOrder_comapEraseLabels_iff (α := α) (n := n)).1 (h n)
  · intro h n
    exact AgreeUpToOrder.comapEraseLabels (α := α) (h n)

theorem LabelInvariant.agreeUpToOrder_iff_comapConstLabel
    {X Y : AlgebraicLabelledBranchedRoughPath T α R} {n : Nat}
    (hX : LabelInvariant X) (hY : LabelInvariant Y) (x : α) :
    AgreeUpToOrder X Y n ↔
      AlgebraicBranchedRoughPath.AgreeUpToOrder
        (comapConstLabel x X) (comapConstLabel x Y) n := by
  constructor
  · exact AgreeUpToOrder.comapConstLabel x
  · intro h s t φ hφ
    have hconst := h s t (LRootedForest.erase φ) (by simpa using hφ)
    calc
      X.coeff s t φ =
          X.coeff s t (LRootedForest.constLabel x (LRootedForest.erase φ)) := by
            exact (hX.coeff_eq (by simp)).symm
      _ = Y.coeff s t (LRootedForest.constLabel x (LRootedForest.erase φ)) := by
            rw [coeff_comapConstLabel, coeff_comapConstLabel] at hconst
            exact hconst
      _ = Y.coeff s t φ := by
            exact hY.coeff_eq (by simp)

theorem LabelInvariant.agreeUpToOrder_all_iff_comapConstLabel
    {X Y : AlgebraicLabelledBranchedRoughPath T α R}
    (hX : LabelInvariant X) (hY : LabelInvariant Y) (x : α) :
    (∀ n, AgreeUpToOrder X Y n) ↔
      ∀ n, AlgebraicBranchedRoughPath.AgreeUpToOrder
        (comapConstLabel x X) (comapConstLabel x Y) n := by
  constructor
  · intro h n
    exact AgreeUpToOrder.comapConstLabel x (h n)
  · intro h n
    exact (hX.agreeUpToOrder_iff_comapConstLabel hY x).2 (h n)

theorem labelInvariantEquiv_agreeUpToOrder [Nonempty α]
    {X Y : AlgebraicBranchedRoughPath T R} {n : Nat} :
    AgreeUpToOrder (labelInvariantEquiv (α := α) (T := T) (R := R) X).1
        (labelInvariantEquiv (α := α) (T := T) (R := R) Y).1 n ↔
      AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n := by
  simpa using (agreeUpToOrder_comapEraseLabels_iff (α := α) (X := X) (Y := Y) (n := n))

theorem labelInvariantEquiv_symm_agreeUpToOrder [Nonempty α]
    {X Y : {X : AlgebraicLabelledBranchedRoughPath T α R // LabelInvariant X}} {n : Nat} :
    AlgebraicBranchedRoughPath.AgreeUpToOrder
        ((labelInvariantEquiv (α := α) (T := T) (R := R)).symm X)
        ((labelInvariantEquiv (α := α) (T := T) (R := R)).symm Y) n ↔
      AgreeUpToOrder X.1 Y.1 n := by
  rw [labelInvariantEquiv_symm_apply, labelInvariantEquiv_symm_apply]
  exact (X.2.agreeUpToOrder_iff_comapConstLabel Y.2
    (Classical.choice (inferInstance : Nonempty α))).symm

theorem labelInvariantEquiv_agreeUpToOrder_all [Nonempty α]
    {X Y : AlgebraicBranchedRoughPath T R} :
    (∀ n, AgreeUpToOrder (labelInvariantEquiv (α := α) (T := T) (R := R) X).1
        (labelInvariantEquiv (α := α) (T := T) (R := R) Y).1 n) ↔
      ∀ n, AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n := by
  simpa using (agreeUpToOrder_all_comapEraseLabels_iff (α := α) (X := X) (Y := Y))

theorem labelInvariantEquiv_symm_agreeUpToOrder_all [Nonempty α]
    {X Y : {X : AlgebraicLabelledBranchedRoughPath T α R // LabelInvariant X}} :
    (∀ n, AlgebraicBranchedRoughPath.AgreeUpToOrder
        ((labelInvariantEquiv (α := α) (T := T) (R := R)).symm X)
        ((labelInvariantEquiv (α := α) (T := T) (R := R)).symm Y) n) ↔
      ∀ n, AgreeUpToOrder X.1 Y.1 n := by
  constructor
  · intro h n
    exact (labelInvariantEquiv_symm_agreeUpToOrder (α := α) (X := X) (Y := Y)
      (n := n)).1 (h n)
  · intro h n
    exact (labelInvariantEquiv_symm_agreeUpToOrder (α := α) (X := X) (Y := Y)
      (n := n)).2 (h n)

theorem coeff_self (X : AlgebraicLabelledBranchedRoughPath T α R)
    (t : T) (φ : LRootedForest α) :
    X.coeff t t φ = LForestAlgebra.counitCoeff (R := R) φ :=
  (X.coeff_diagonal t φ).trans (LBCK.counitCoeff_eq_boolIte φ).symm

theorem increment_convolution_reverse
    (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : T) :
    LForestAlgebra.Character.convolution (X.lcharacter s t) (X.lcharacter t s) =
      LForestAlgebra.Character.unit α R := by
  rw [← lchen_eq X s t s, lcharacter_self X s]

theorem reverse_convolution_increment
    (X : AlgebraicLabelledBranchedRoughPath T α R) (s t : T) :
    LForestAlgebra.Character.convolution (X.lcharacter t s) (X.lcharacter s t) =
      LForestAlgebra.Character.unit α R := by
  rw [← lchen_eq X t s t, lcharacter_self X t]

theorem chen_coeff (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t u : T) (φ : LRootedForest α) :
    X.coeff s u φ =
      LRootedForest.convolutionCoeff (X.lcharacter s t) (X.lcharacter t u) φ := by
  rw [← LForestAlgebra.Character.convolution_evalForest, ← lchen_eq X s t u,
    lcharacter_evalForest]

theorem chen_treeCoeff (X : AlgebraicLabelledBranchedRoughPath T α R)
    (s t u : T) (τ : LRootedTree α) :
    treeCoeff X s u τ =
      LRootedTree.convolutionCoeff (X.lcharacter s t) (X.lcharacter t u) τ := by
  rw [treeCoeff, chen_coeff]
  exact (LRootedTree.convolutionCoeff_eq_singleton
    (X.lcharacter s t) (X.lcharacter t u) τ).symm

theorem unit_coeff (s t : T) (φ : LRootedForest α) :
    (unit T α R).coeff s t φ = LForestAlgebra.counitCoeff (R := R) φ :=
  (LBCK.counitCoeff_eq_boolIte φ).symm

end

end AlgebraicLabelledBranchedRoughPath

end RoughPaths
