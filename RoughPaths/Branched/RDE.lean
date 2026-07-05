/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.RDE
import RoughPaths.Branched.Log

/-!
# Branched rough differential equations

Taylor increments and log-ODE vector fields driven by branched
(labelled) rough paths, indexed by rooted forests.
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z y x

open scoped BigOperators

noncomputable section


/-! ## Branched expansions -/

/-- Abstract elementary differentials indexed by unlabelled forests. -/
structure BranchedIteratedVectorFields (E : Type u) where
  eval : RootedForest → E → E
  eval_empty : ∀ y, eval RootedForest.empty y = y

namespace BranchedIteratedVectorFields

variable {R : Type u} {E : Type v} {T : Type w}

@[ext]
theorem ext {V W : BranchedIteratedVectorFields E}
    (h : ∀ φ y, V.eval φ y = W.eval φ y) : V = W := by
  cases V with
  | mk evalV hV =>
    cases W with
    | mk evalW hW =>
      have heval : evalV = evalW := by
        funext φ y
        exact h φ y
      subst evalW
      rfl

@[simp]
theorem eval_empty_apply (V : BranchedIteratedVectorFields E) (y : E) :
    V.eval RootedForest.empty y = y :=
  V.eval_empty y

/-- Apply a branched signature over a finite list of forests. -/
def applyCharacterOn [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) (χ : BranchedSignature R)
    (terms : List RootedForest) (y : E) : E :=
  (terms.map fun φ => χ.evalForest φ • V.eval φ y).sum

/-- Apply a branched infinitesimal character over a finite list of forests. -/
def applyFunctionalOn [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) (ℓ : ForestAlgebra.LinearFunctional R)
    (terms : List RootedForest) (y : E) : E :=
  (terms.map fun φ => ForestAlgebra.LinearFunctional.evalForest ℓ φ • V.eval φ y).sum

theorem applyCharacterOn_congr [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) {χ ψ : BranchedSignature R}
    {terms : List RootedForest}
    (h : ∀ φ, φ ∈ terms → χ.evalForest φ = ψ.evalForest φ) (y : E) :
    V.applyCharacterOn χ terms y = V.applyCharacterOn ψ terms y := by
  unfold applyCharacterOn
  apply congrArg List.sum
  apply List.map_congr_left
  intro φ hφ
  rw [h φ hφ]

theorem applyFunctionalOn_congr [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E)
    {ℓ m : ForestAlgebra.LinearFunctional R} {terms : List RootedForest}
    (h : ∀ φ, φ ∈ terms →
      ForestAlgebra.LinearFunctional.evalForest ℓ φ =
        ForestAlgebra.LinearFunctional.evalForest m φ) (y : E) :
    V.applyFunctionalOn ℓ terms y = V.applyFunctionalOn m terms y := by
  unfold applyFunctionalOn
  apply congrArg List.sum
  apply List.map_congr_left
  intro φ hφ
  rw [h φ hφ]

@[simp]
theorem applyFunctionalOn_zero [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) (terms : List RootedForest) (y : E) :
    V.applyFunctionalOn (0 : ForestAlgebra.LinearFunctional R) terms y = 0 := by
  induction terms with
  | nil =>
      rfl
  | cons φ terms ih =>
      have ih' :
          (terms.map fun φ =>
            ForestAlgebra.LinearFunctional.evalForest
              (0 : ForestAlgebra.LinearFunctional R) φ • V.eval φ y).sum = 0 := by
        simpa [applyFunctionalOn] using ih
      simp only [applyFunctionalOn, List.map_cons, List.sum_cons]
      rw [show
        ForestAlgebra.LinearFunctional.evalForest (0 : ForestAlgebra.LinearFunctional R) φ = 0 by
          rfl]
      rw [ih']
      simp

/-- The finite branched Taylor increment driven by a branched rough path. -/
def taylorIncrementOn [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) (X : AlgebraicBranchedRoughPath T R)
    (terms : List RootedForest) (s t : T) (y : E) : E :=
  V.applyCharacterOn (X.character s t) terms y

@[simp]
theorem taylorIncrementOn_comapTime [CommSemiring R] [AddCommMonoid E] [Module R E]
    {S : Type z} (f : S → T) (V : BranchedIteratedVectorFields E)
    (X : AlgebraicBranchedRoughPath T R) (terms : List RootedForest)
    (s t : S) (y : E) :
    V.taylorIncrementOn (AlgebraicBranchedRoughPath.comapTime f X) terms s t y =
      V.taylorIncrementOn X terms (f s) (f t) y :=
  rfl

theorem taylorIncrementOn_eq_of_agreeUpToOrder
    [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) {X Y : AlgebraicBranchedRoughPath T R}
    {terms : List RootedForest} {n : Nat}
    (h : AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n)
    (hterms : ∀ φ, φ ∈ terms → RootedForest.order φ ≤ n)
    (s t : T) (y : E) :
    V.taylorIncrementOn X terms s t y = V.taylorIncrementOn Y terms s t y := by
  apply V.applyCharacterOn_congr
  intro φ hφ
  rw [AlgebraicBranchedRoughPath.character_evalForest,
    AlgebraicBranchedRoughPath.character_evalForest]
  exact h s t φ (hterms φ hφ)

/-- The finite branched log-ODE vector field over a list of forests. -/
def logODEVectorFieldOn [Field R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) (X : AlgebraicBranchedRoughPath T R)
    (n : Nat) (terms : List RootedForest) (s t : T) : E → E :=
  fun y => V.applyFunctionalOn
    (AlgebraicBranchedRoughPath.logIncrementTruncated X s t n) terms y

@[simp]
theorem logODEVectorFieldOn_apply [Field R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) (X : AlgebraicBranchedRoughPath T R)
    (n : Nat) (terms : List RootedForest) (s t : T) (y : E) :
    V.logODEVectorFieldOn X n terms s t y =
      V.applyFunctionalOn
        (AlgebraicBranchedRoughPath.logIncrementTruncated X s t n) terms y :=
  rfl

@[simp]
theorem logODEVectorFieldOn_self [Field R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) (X : AlgebraicBranchedRoughPath T R)
    (n : Nat) (terms : List RootedForest) (t : T) (y : E) :
    V.logODEVectorFieldOn X n terms t t y = 0 := by
  simp [logODEVectorFieldOn]

@[simp]
theorem logODEVectorFieldOn_zero [Field R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) (X : AlgebraicBranchedRoughPath T R)
    (terms : List RootedForest) (s t : T) (y : E) :
    V.logODEVectorFieldOn X 0 terms s t y = 0 := by
  simp [logODEVectorFieldOn]

@[simp]
theorem logODEVectorFieldOn_comapTime [Field R] [AddCommMonoid E] [Module R E]
    {S : Type z} (f : S → T) (V : BranchedIteratedVectorFields E)
    (X : AlgebraicBranchedRoughPath T R) (n : Nat)
    (terms : List RootedForest) (s t : S) (y : E) :
    V.logODEVectorFieldOn
        (AlgebraicBranchedRoughPath.comapTime f X) n terms s t y =
      V.logODEVectorFieldOn X n terms (f s) (f t) y :=
  rfl

theorem logODEVectorFieldOn_eq_of_agreeUpToOrder
    [Field R] [AddCommMonoid E] [Module R E]
    (V : BranchedIteratedVectorFields E) {X Y : AlgebraicBranchedRoughPath T R}
    {terms : List RootedForest} {n : Nat}
    (h : AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n)
    (hterms : ∀ φ, φ ∈ terms → RootedForest.order φ ≤ n)
    (s t : T) (y : E) :
    V.logODEVectorFieldOn X n terms s t y =
      V.logODEVectorFieldOn Y n terms s t y := by
  apply V.applyFunctionalOn_congr
  intro φ hφ
  exact h.logIncrementTruncated_evalForest s t φ (hterms φ hφ)

end BranchedIteratedVectorFields

/-! ## Labelled branched expansions -/

/-- Abstract elementary differentials indexed by labelled forests. -/
structure LabelledBranchedIteratedVectorFields (α : Type u) (E : Type v) where
  eval : LRootedForest α → E → E
  eval_empty : ∀ y, eval LRootedForest.empty y = y

namespace LabelledBranchedIteratedVectorFields

variable {α : Type u} {β : Type v} {R : Type w} {E : Type z} {T : Type y}

@[ext]
theorem ext {V W : LabelledBranchedIteratedVectorFields α E}
    (h : ∀ φ y, V.eval φ y = W.eval φ y) : V = W := by
  cases V with
  | mk evalV hV =>
    cases W with
    | mk evalW hW =>
      have heval : evalV = evalW := by
        funext φ y
        exact h φ y
      subst evalW
      rfl

@[simp]
theorem eval_empty_apply (V : LabelledBranchedIteratedVectorFields α E) (y : E) :
    V.eval LRootedForest.empty y = y :=
  V.eval_empty y

/-- Pull labelled elementary differentials back along a relabelling map. -/
def comapMapLabels (f : α → β) (V : LabelledBranchedIteratedVectorFields β E) :
    LabelledBranchedIteratedVectorFields α E where
  eval φ y := V.eval (LRootedForest.mapLabels f φ) y
  eval_empty y := by
    simp

/-- Pull unlabelled elementary differentials back to labelled forests. -/
def comapEraseLabels (V : BranchedIteratedVectorFields E) :
    LabelledBranchedIteratedVectorFields α E where
  eval φ y := V.eval (LRootedForest.erase φ) y
  eval_empty y := by
    simp

@[simp]
theorem comapMapLabels_eval (f : α → β)
    (V : LabelledBranchedIteratedVectorFields β E)
    (φ : LRootedForest α) (y : E) :
    (comapMapLabels f V).eval φ y = V.eval (LRootedForest.mapLabels f φ) y :=
  rfl

@[simp]
theorem comapEraseLabels_eval
    (V : BranchedIteratedVectorFields E) (φ : LRootedForest α) (y : E) :
    (comapEraseLabels V).eval φ y = V.eval (LRootedForest.erase φ) y :=
  rfl

@[simp]
theorem comapMapLabels_id (V : LabelledBranchedIteratedVectorFields α E) :
    comapMapLabels id V = V := by
  ext φ y
  simp [comapMapLabels]

theorem comapMapLabels_comp {γ : Type u}
    (f : α → β) (g : β → γ)
    (V : LabelledBranchedIteratedVectorFields γ E) :
    comapMapLabels f (comapMapLabels g V) = comapMapLabels (g ∘ f) V := by
  ext φ y
  simp [comapMapLabels, LRootedForest.mapLabels_comp, Function.comp_def]

/-- Apply a labelled branched signature over a finite list of labelled forests. -/
def applyCharacterOn [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    (χ : LabelledBranchedSignature α R) (terms : List (LRootedForest α)) (y : E) :
    E :=
  (terms.map fun φ => χ.evalForest φ • V.eval φ y).sum

/-- Apply a labelled branched infinitesimal character over a finite list of forests. -/
def applyFunctionalOn [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    (ℓ : LForestAlgebra.LinearFunctional α R)
    (terms : List (LRootedForest α)) (y : E) : E :=
  (terms.map fun φ => LForestAlgebra.LinearFunctional.evalForest ℓ φ • V.eval φ y).sum

theorem applyCharacterOn_congr [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    {χ ψ : LabelledBranchedSignature α R} {terms : List (LRootedForest α)}
    (h : ∀ φ, φ ∈ terms → χ.evalForest φ = ψ.evalForest φ) (y : E) :
    V.applyCharacterOn χ terms y = V.applyCharacterOn ψ terms y := by
  unfold applyCharacterOn
  apply congrArg List.sum
  apply List.map_congr_left
  intro φ hφ
  rw [h φ hφ]

theorem applyFunctionalOn_congr [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    {ℓ m : LForestAlgebra.LinearFunctional α R} {terms : List (LRootedForest α)}
    (h : ∀ φ, φ ∈ terms →
      LForestAlgebra.LinearFunctional.evalForest ℓ φ =
        LForestAlgebra.LinearFunctional.evalForest m φ) (y : E) :
    V.applyFunctionalOn ℓ terms y = V.applyFunctionalOn m terms y := by
  unfold applyFunctionalOn
  apply congrArg List.sum
  apply List.map_congr_left
  intro φ hφ
  rw [h φ hφ]

@[simp]
theorem applyFunctionalOn_zero [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    (terms : List (LRootedForest α)) (y : E) :
    V.applyFunctionalOn (0 : LForestAlgebra.LinearFunctional α R) terms y = 0 := by
  induction terms with
  | nil =>
      rfl
  | cons φ terms ih =>
      have ih' :
          (terms.map fun φ =>
            LForestAlgebra.LinearFunctional.evalForest
              (0 : LForestAlgebra.LinearFunctional α R) φ • V.eval φ y).sum = 0 := by
        simpa [applyFunctionalOn] using ih
      simp only [applyFunctionalOn, List.map_cons, List.sum_cons]
      rw [show
        LForestAlgebra.LinearFunctional.evalForest
            (0 : LForestAlgebra.LinearFunctional α R) φ = 0 by
          rfl]
      rw [ih']
      simp

/-- The finite labelled branched Taylor increment driven by a branched rough path. -/
def taylorIncrementOn [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (terms : List (LRootedForest α)) (s t : T) (y : E) : E :=
  V.applyCharacterOn (X.lcharacter s t) terms y

@[simp]
theorem taylorIncrementOn_comapTime [CommSemiring R] [AddCommMonoid E] [Module R E]
    {S : Type x} (f : S → T) (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (terms : List (LRootedForest α)) (s t : S) (y : E) :
    V.taylorIncrementOn
        (AlgebraicLabelledBranchedRoughPath.comapTime f X) terms s t y =
      V.taylorIncrementOn X terms (f s) (f t) y :=
  rfl

theorem taylorIncrementOn_eq_of_agreeUpToOrder
    [CommSemiring R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    {X Y : AlgebraicLabelledBranchedRoughPath T α R}
    {terms : List (LRootedForest α)} {n : Nat}
    (h : AlgebraicLabelledBranchedRoughPath.AgreeUpToOrder X Y n)
    (hterms : ∀ φ, φ ∈ terms → LRootedForest.order φ ≤ n)
    (s t : T) (y : E) :
    V.taylorIncrementOn X terms s t y = V.taylorIncrementOn Y terms s t y := by
  apply V.applyCharacterOn_congr
  intro φ hφ
  rw [AlgebraicLabelledBranchedRoughPath.lcharacter_evalForest,
    AlgebraicLabelledBranchedRoughPath.lcharacter_evalForest]
  exact h s t φ (hterms φ hφ)

/-- The finite labelled branched log-ODE vector field over a list of forests. -/
def logODEVectorFieldOn [Field R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (n : Nat) (terms : List (LRootedForest α)) (s t : T) : E → E :=
  fun y => V.applyFunctionalOn
    (AlgebraicLabelledBranchedRoughPath.logIncrementTruncated X s t n) terms y

@[simp]
theorem logODEVectorFieldOn_apply [Field R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (n : Nat) (terms : List (LRootedForest α)) (s t : T) (y : E) :
    V.logODEVectorFieldOn X n terms s t y =
      V.applyFunctionalOn
        (AlgebraicLabelledBranchedRoughPath.logIncrementTruncated X s t n) terms y :=
  rfl

@[simp]
theorem logODEVectorFieldOn_self [Field R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (n : Nat) (terms : List (LRootedForest α)) (t : T) (y : E) :
    V.logODEVectorFieldOn X n terms t t y = 0 := by
  simp [logODEVectorFieldOn]

@[simp]
theorem logODEVectorFieldOn_zero [Field R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (terms : List (LRootedForest α)) (s t : T) (y : E) :
    V.logODEVectorFieldOn X 0 terms s t y = 0 := by
  simp [logODEVectorFieldOn]

@[simp]
theorem logODEVectorFieldOn_comapTime [Field R] [AddCommMonoid E] [Module R E]
    {S : Type x} (f : S → T) (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (n : Nat) (terms : List (LRootedForest α)) (s t : S) (y : E) :
    V.logODEVectorFieldOn
        (AlgebraicLabelledBranchedRoughPath.comapTime f X) n terms s t y =
      V.logODEVectorFieldOn X n terms (f s) (f t) y :=
  rfl

theorem logODEVectorFieldOn_eq_of_agreeUpToOrder
    [Field R] [AddCommMonoid E] [Module R E]
    (V : LabelledBranchedIteratedVectorFields α E)
    {X Y : AlgebraicLabelledBranchedRoughPath T α R}
    {terms : List (LRootedForest α)} {n : Nat}
    (h : AlgebraicLabelledBranchedRoughPath.AgreeUpToOrder X Y n)
    (hterms : ∀ φ, φ ∈ terms → LRootedForest.order φ ≤ n)
    (s t : T) (y : E) :
    V.logODEVectorFieldOn X n terms s t y =
      V.logODEVectorFieldOn Y n terms s t y := by
  apply V.applyFunctionalOn_congr
  intro φ hφ
  exact h.logIncrementTruncated_evalForest s t φ (hterms φ hφ)

end LabelledBranchedIteratedVectorFields

end

end RoughPaths
