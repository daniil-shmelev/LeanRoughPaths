/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.Analytic
import RoughPaths.Branched.Basic

/-!
# Analytic control of branched rough paths

Forest-coordinate controls (`HasForestControl`) for branched and
labelled branched rough paths, extending the geometric controls of
`RoughPaths.Analytic`.
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z y

noncomputable section


namespace AlgebraicBranchedRoughPath

variable {T : Type u} {R : Type v} [Preorder T] [CommSemiring R]

/-- All forest coordinates of a branched rough path are bounded by a control. -/
def HasForestControl (X : AlgebraicBranchedRoughPath T R)
    (ω : Control T) (size : R → ENNReal)
    (gauge : Nat → ENNReal → ENNReal) : Prop :=
  ∀ {s t : T}, s ≤ t → ∀ φ : RootedForest,
    size (X.coeff s t φ) ≤ gauge (RootedForest.order φ) (ω s t)

theorem HasForestControl.coeff_bound {X : AlgebraicBranchedRoughPath T R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    {s t : T} (hst : s ≤ t) (φ : RootedForest) :
    size (X.coeff s t φ) ≤ gauge (RootedForest.order φ) (ω s t) :=
  h hst φ

theorem HasForestControl.incrementControlledBy {X : AlgebraicBranchedRoughPath T R}
    {ω η : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge) (φ : RootedForest)
    (hη : ∀ {s t : T}, s ≤ t → gauge (RootedForest.order φ) (ω s t) ≤ η s t) :
    IncrementControlledBy (fun s t => X.coeff s t φ) size η := by
  intro s t hst
  exact le_trans (h hst φ) (hη hst)

theorem HasForestControl.treeCoeff_bound {X : AlgebraicBranchedRoughPath T R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    {s t : T} (hst : s ≤ t) (τ : RootedTree) :
    size (treeCoeff X s t τ) ≤ gauge (RootedTree.order τ) (ω s t) := by
  change
    size (X.coeff s t (RootedForest.singleton τ)) ≤
      gauge (RootedTree.order τ) (ω s t)
  simpa [RootedForest.order_singleton] using
    h hst (RootedForest.singleton τ)

theorem HasForestControl.treeIncrementControlledBy {X : AlgebraicBranchedRoughPath T R}
    {ω η : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge) (τ : RootedTree)
    (hη : ∀ {s t : T}, s ≤ t → gauge (RootedTree.order τ) (ω s t) ≤ η s t) :
    IncrementControlledBy (fun s t => treeCoeff X s t τ) size η := by
  intro s t hst
  exact le_trans (h.treeCoeff_bound hst τ) (hη hst)

theorem HasForestControl.comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f) {X : AlgebraicBranchedRoughPath T R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge) :
    (AlgebraicBranchedRoughPath.comapTime f X).HasForestControl
      (ω.comap f hf) size gauge := by
  intro s t hst φ
  rw [AlgebraicBranchedRoughPath.coeff_comapTime]
  exact h (hf hst) φ

theorem HasForestControl.mono_gauge {X : AlgebraicBranchedRoughPath T R}
    {ω : Control T} {size : R → ENNReal}
    {gauge gauge' : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    (hgauge : ∀ n r, gauge n r ≤ gauge' n r) :
    X.HasForestControl ω size gauge' := by
  intro s t hst φ
  exact le_trans (h hst φ) (hgauge (RootedForest.order φ) (ω s t))

theorem HasForestControl.mono_size {X : AlgebraicBranchedRoughPath T R}
    {ω : Control T} {size size' : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    (hsize : ∀ r : R, size' r ≤ size r) :
    X.HasForestControl ω size' gauge := by
  intro s t hst φ
  exact le_trans (hsize (X.coeff s t φ)) (h hst φ)

theorem HasForestControl.mono_control {X : AlgebraicBranchedRoughPath T R}
    {ω η : Control T} {size : R → ENNReal}
    {gauge gauge' : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    (hω : ∀ {s t : T}, s ≤ t → ω s t ≤ η s t)
    (hgauge : ∀ n {r r' : ENNReal}, r ≤ r' → gauge n r ≤ gauge' n r') :
    X.HasForestControl η size gauge' := by
  intro s t hst φ
  exact le_trans (h hst φ) (hgauge (RootedForest.order φ) (hω hst))

/-- A branched rough path together with a forest-coordinate control certificate. -/
structure Controlled (T : Type u) (R : Type v) [Preorder T] [CommSemiring R]
    (size : R → ENNReal) (gauge : Nat → ENNReal → ENNReal) where
  toAlgebraic : AlgebraicBranchedRoughPath T R
  control : Control T
  controlled : toAlgebraic.HasForestControl control size gauge

namespace Controlled

variable {size : R → ENNReal} {gauge : Nat → ENNReal → ENNReal}

@[ext]
theorem ext {X Y : Controlled T R size gauge}
    (halg : X.toAlgebraic = Y.toAlgebraic) (hcontrol : X.control = Y.control) :
    X = Y := by
  cases X with
  | mk Xalg Xcontrol Xcontrolled =>
    cases Y with
    | mk Yalg Ycontrol Ycontrolled =>
      cases halg
      cases hcontrol
      congr

/-- Pull a controlled branched rough path back along a monotone map of time domains. -/
def comapTime {S : Type z} [Preorder S] (f : S → T) (hf : Monotone f)
    (X : Controlled T R size gauge) : Controlled S R size gauge where
  toAlgebraic := AlgebraicBranchedRoughPath.comapTime f X.toAlgebraic
  control := X.control.comap f hf
  controlled := AlgebraicBranchedRoughPath.HasForestControl.comapTime f hf X.controlled

/-- Coordinate of a controlled branched rough path increment on a forest. -/
def coeff (X : Controlled T R size gauge) (s t : T) (φ : RootedForest) : R :=
  X.toAlgebraic.coeff s t φ

/-- Coordinate of a controlled branched rough path increment on a tree. -/
def treeCoeff (X : Controlled T R size gauge) (s t : T) (τ : RootedTree) : R :=
  AlgebraicBranchedRoughPath.treeCoeff X.toAlgebraic s t τ

@[simp]
theorem coeff_apply (X : Controlled T R size gauge) (s t : T) (φ : RootedForest) :
    X.coeff s t φ = X.toAlgebraic.coeff s t φ :=
  rfl

@[simp]
theorem treeCoeff_apply (X : Controlled T R size gauge) (s t : T) (τ : RootedTree) :
    X.treeCoeff s t τ = AlgebraicBranchedRoughPath.treeCoeff X.toAlgebraic s t τ :=
  rfl

@[simp]
theorem comapTime_toAlgebraic {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f) (X : Controlled T R size gauge) :
    (comapTime f hf X).toAlgebraic =
      AlgebraicBranchedRoughPath.comapTime f X.toAlgebraic :=
  rfl

@[simp]
theorem coeff_comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f)
    (X : Controlled T R size gauge) (s t : S) (φ : RootedForest) :
    (comapTime f hf X).coeff s t φ = X.coeff (f s) (f t) φ :=
  rfl

@[simp]
theorem treeCoeff_comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f)
    (X : Controlled T R size gauge) (s t : S) (τ : RootedTree) :
    (comapTime f hf X).treeCoeff s t τ = X.treeCoeff (f s) (f t) τ :=
  rfl

@[simp]
theorem comapTime_id (X : Controlled T R size gauge) :
    comapTime id (fun _ _ h => h) X = X := by
  apply ext
  · simp [comapTime]
  · exact Control.comap_id X.control

theorem comapTime_comp {S : Type z} {U : Type y} [Preorder S] [Preorder U]
    (f : S → T) (hf : Monotone f) (g : U → S) (hg : Monotone g)
    (X : Controlled T R size gauge) :
    comapTime g hg (comapTime f hf X) =
      comapTime (f ∘ g) (fun _ _ h => hf (hg h)) X := by
  apply ext
  · simp [comapTime, AlgebraicBranchedRoughPath.comapTime_comp]
  · exact Control.comap_comp X.control f hf g hg

theorem coordinate_bound (X : Controlled T R size gauge)
    {s t : T} (hst : s ≤ t) (φ : RootedForest) :
    size (X.coeff s t φ) ≤ gauge (RootedForest.order φ) (X.control s t) :=
  X.controlled hst φ

theorem tree_coordinate_bound (X : Controlled T R size gauge)
    {s t : T} (hst : s ≤ t) (τ : RootedTree) :
    size (X.treeCoeff s t τ) ≤ gauge (RootedTree.order τ) (X.control s t) :=
  HasForestControl.treeCoeff_bound X.controlled hst τ

end Controlled

end AlgebraicBranchedRoughPath

namespace AlgebraicLabelledBranchedRoughPath

variable {T : Type u} {α : Type v} {R : Type w} [Preorder T] [CommSemiring R]

/-- All labelled forest coordinates are bounded by a control and gauge. -/
def HasForestControl (X : AlgebraicLabelledBranchedRoughPath T α R)
    (ω : Control T) (size : R → ENNReal)
    (gauge : Nat → ENNReal → ENNReal) : Prop :=
  ∀ {s t : T}, s ≤ t → ∀ φ : LRootedForest α,
    size (X.coeff s t φ) ≤ gauge (LRootedForest.order φ) (ω s t)

theorem HasForestControl.coeff_bound {X : AlgebraicLabelledBranchedRoughPath T α R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    {s t : T} (hst : s ≤ t) (φ : LRootedForest α) :
    size (X.coeff s t φ) ≤ gauge (LRootedForest.order φ) (ω s t) :=
  h hst φ

theorem HasForestControl.incrementControlledBy
    {X : AlgebraicLabelledBranchedRoughPath T α R}
    {ω η : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge) (φ : LRootedForest α)
    (hη : ∀ {s t : T}, s ≤ t → gauge (LRootedForest.order φ) (ω s t) ≤ η s t) :
    IncrementControlledBy (fun s t => X.coeff s t φ) size η := by
  intro s t hst
  exact le_trans (h hst φ) (hη hst)

theorem HasForestControl.treeCoeff_bound
    {X : AlgebraicLabelledBranchedRoughPath T α R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    {s t : T} (hst : s ≤ t) (τ : LRootedTree α) :
    size (treeCoeff X s t τ) ≤ gauge (LRootedTree.order τ) (ω s t) := by
  change
    size (X.coeff s t (LRootedForest.singleton τ)) ≤
      gauge (LRootedTree.order τ) (ω s t)
  simpa [LRootedForest.order_singleton] using
    h hst (LRootedForest.singleton τ)

theorem HasForestControl.treeIncrementControlledBy
    {X : AlgebraicLabelledBranchedRoughPath T α R}
    {ω η : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge) (τ : LRootedTree α)
    (hη : ∀ {s t : T}, s ≤ t → gauge (LRootedTree.order τ) (ω s t) ≤ η s t) :
    IncrementControlledBy (fun s t => treeCoeff X s t τ) size η := by
  intro s t hst
  exact le_trans (h.treeCoeff_bound hst τ) (hη hst)

theorem HasForestControl.comapMapLabels {β : Type z} (f : α → β)
    {X : AlgebraicLabelledBranchedRoughPath T β R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge) :
    (AlgebraicLabelledBranchedRoughPath.comapMapLabels f X).HasForestControl
      ω size gauge := by
  intro s t hst φ
  rw [AlgebraicLabelledBranchedRoughPath.coeff_comapMapLabels]
  simpa using h hst (LRootedForest.mapLabels f φ)

theorem HasForestControl.comapEraseLabels
    {X : AlgebraicBranchedRoughPath T R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge) :
    (AlgebraicLabelledBranchedRoughPath.comapEraseLabels (α := α) X).HasForestControl
      ω size gauge := by
  intro s t hst φ
  rw [AlgebraicLabelledBranchedRoughPath.coeff_comapEraseLabels]
  simpa using h hst (LRootedForest.erase φ)

theorem HasForestControl.comapConstLabel (a : α)
    {X : AlgebraicLabelledBranchedRoughPath T α R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge) :
    AlgebraicBranchedRoughPath.HasForestControl
      (AlgebraicLabelledBranchedRoughPath.comapConstLabel a X) ω size gauge := by
  intro s t hst φ
  rw [AlgebraicLabelledBranchedRoughPath.coeff_comapConstLabel]
  simpa using h hst (LRootedForest.constLabel a φ)

theorem HasForestControl.comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f)
    {X : AlgebraicLabelledBranchedRoughPath T α R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge) :
    (AlgebraicLabelledBranchedRoughPath.comapTime f X).HasForestControl
      (ω.comap f hf) size gauge := by
  intro s t hst φ
  rw [AlgebraicLabelledBranchedRoughPath.coeff_comapTime]
  exact h (hf hst) φ

theorem HasForestControl.mono_gauge
    {X : AlgebraicLabelledBranchedRoughPath T α R}
    {ω : Control T} {size : R → ENNReal}
    {gauge gauge' : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    (hgauge : ∀ n r, gauge n r ≤ gauge' n r) :
    X.HasForestControl ω size gauge' := by
  intro s t hst φ
  exact le_trans (h hst φ) (hgauge (LRootedForest.order φ) (ω s t))

theorem HasForestControl.mono_size
    {X : AlgebraicLabelledBranchedRoughPath T α R}
    {ω : Control T} {size size' : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    (hsize : ∀ r : R, size' r ≤ size r) :
    X.HasForestControl ω size' gauge := by
  intro s t hst φ
  exact le_trans (hsize (X.coeff s t φ)) (h hst φ)

theorem HasForestControl.mono_control
    {X : AlgebraicLabelledBranchedRoughPath T α R}
    {ω η : Control T} {size : R → ENNReal}
    {gauge gauge' : Nat → ENNReal → ENNReal}
    (h : X.HasForestControl ω size gauge)
    (hω : ∀ {s t : T}, s ≤ t → ω s t ≤ η s t)
    (hgauge : ∀ n {r r' : ENNReal}, r ≤ r' → gauge n r ≤ gauge' n r') :
    X.HasForestControl η size gauge' := by
  intro s t hst φ
  exact le_trans (h hst φ) (hgauge (LRootedForest.order φ) (hω hst))

/-- A labelled branched rough path with a forest-coordinate control certificate. -/
structure Controlled (T : Type u) (α : Type v) (R : Type w)
    [Preorder T] [CommSemiring R]
    (size : R → ENNReal) (gauge : Nat → ENNReal → ENNReal) where
  toAlgebraic : AlgebraicLabelledBranchedRoughPath T α R
  control : Control T
  controlled : toAlgebraic.HasForestControl control size gauge

namespace Controlled

variable {size : R → ENNReal} {gauge : Nat → ENNReal → ENNReal}

@[ext]
theorem ext {X Y : Controlled T α R size gauge}
    (halg : X.toAlgebraic = Y.toAlgebraic) (hcontrol : X.control = Y.control) :
    X = Y := by
  cases X with
  | mk Xalg Xcontrol Xcontrolled =>
    cases Y with
    | mk Yalg Ycontrol Ycontrolled =>
      cases halg
      cases hcontrol
      congr

/-- Pull a controlled labelled branched rough path back along a relabelling map. -/
def comapMapLabels {β : Type z} (f : α → β)
    (X : Controlled T β R size gauge) : Controlled T α R size gauge where
  toAlgebraic := AlgebraicLabelledBranchedRoughPath.comapMapLabels f X.toAlgebraic
  control := X.control
  controlled := AlgebraicLabelledBranchedRoughPath.HasForestControl.comapMapLabels
    f X.controlled

/-- Pull an unlabelled controlled branched rough path back to labelled forests. -/
def comapEraseLabels
    (X : AlgebraicBranchedRoughPath.Controlled T R size gauge) :
    Controlled T α R size gauge where
  toAlgebraic := AlgebraicLabelledBranchedRoughPath.comapEraseLabels
    (α := α) X.toAlgebraic
  control := X.control
  controlled := AlgebraicLabelledBranchedRoughPath.HasForestControl.comapEraseLabels
    (α := α) X.controlled

/-- Restrict a labelled controlled branched rough path to one constant label. -/
def comapConstLabel (a : α) (X : Controlled T α R size gauge) :
    AlgebraicBranchedRoughPath.Controlled T R size gauge where
  toAlgebraic := AlgebraicLabelledBranchedRoughPath.comapConstLabel a X.toAlgebraic
  control := X.control
  controlled := AlgebraicLabelledBranchedRoughPath.HasForestControl.comapConstLabel
    a X.controlled

/-- Pull a controlled labelled branched rough path back along a monotone map of time domains. -/
def comapTime {S : Type z} [Preorder S] (f : S → T) (hf : Monotone f)
    (X : Controlled T α R size gauge) : Controlled S α R size gauge where
  toAlgebraic := AlgebraicLabelledBranchedRoughPath.comapTime f X.toAlgebraic
  control := X.control.comap f hf
  controlled := AlgebraicLabelledBranchedRoughPath.HasForestControl.comapTime
    f hf X.controlled

/-- Coordinate of a controlled labelled branched rough path on a forest. -/
def coeff (X : Controlled T α R size gauge) (s t : T) (φ : LRootedForest α) : R :=
  X.toAlgebraic.coeff s t φ

/-- Coordinate of a controlled labelled branched rough path on a tree. -/
def treeCoeff (X : Controlled T α R size gauge) (s t : T) (τ : LRootedTree α) : R :=
  AlgebraicLabelledBranchedRoughPath.treeCoeff X.toAlgebraic s t τ

@[simp]
theorem coeff_apply
    (X : Controlled T α R size gauge) (s t : T) (φ : LRootedForest α) :
    X.coeff s t φ =
      X.toAlgebraic.coeff s t φ :=
  rfl

@[simp]
theorem treeCoeff_apply
    (X : Controlled T α R size gauge) (s t : T) (τ : LRootedTree α) :
    X.treeCoeff s t τ =
      AlgebraicLabelledBranchedRoughPath.treeCoeff X.toAlgebraic s t τ :=
  rfl

theorem coeff_comapMapLabels {β : Type z} (f : α → β)
    (X : Controlled T β R size gauge) (s t : T) (φ : LRootedForest α) :
    (comapMapLabels f X).coeff s t φ =
      X.coeff s t (LRootedForest.mapLabels f φ) :=
  AlgebraicLabelledBranchedRoughPath.coeff_comapMapLabels f X.toAlgebraic s t φ

theorem treeCoeff_comapMapLabels {β : Type z} (f : α → β)
    (X : Controlled T β R size gauge) (s t : T) (τ : LRootedTree α) :
    (comapMapLabels f X).treeCoeff s t τ =
      X.treeCoeff s t (LRootedTree.map f τ) :=
  AlgebraicLabelledBranchedRoughPath.treeCoeff_comapMapLabels f X.toAlgebraic s t τ

@[simp]
theorem comapEraseLabels_toAlgebraic
    (X : AlgebraicBranchedRoughPath.Controlled T R size gauge) :
    (comapEraseLabels (α := α) X).toAlgebraic =
      AlgebraicLabelledBranchedRoughPath.comapEraseLabels
        (α := α) X.toAlgebraic :=
  rfl

@[simp]
theorem comapConstLabel_toAlgebraic
    (a : α) (X : Controlled T α R size gauge) :
    (comapConstLabel a X).toAlgebraic =
      AlgebraicLabelledBranchedRoughPath.comapConstLabel a X.toAlgebraic :=
  rfl

theorem coeff_comapEraseLabels
    (X : AlgebraicBranchedRoughPath.Controlled T R size gauge)
    (s t : T) (φ : LRootedForest α) :
    (comapEraseLabels (α := α) X).coeff s t φ =
      X.coeff s t (LRootedForest.erase φ) :=
  AlgebraicLabelledBranchedRoughPath.coeff_comapEraseLabels X.toAlgebraic s t φ

theorem treeCoeff_comapEraseLabels
    (X : AlgebraicBranchedRoughPath.Controlled T R size gauge)
    (s t : T) (τ : LRootedTree α) :
    (comapEraseLabels (α := α) X).treeCoeff s t τ =
      X.treeCoeff s t (LRootedTree.erase τ) :=
  AlgebraicLabelledBranchedRoughPath.treeCoeff_comapEraseLabels X.toAlgebraic s t τ

theorem coeff_comapConstLabel
    (a : α) (X : Controlled T α R size gauge) (s t : T) (φ : RootedForest) :
    (comapConstLabel a X).coeff s t φ =
      X.coeff s t (LRootedForest.constLabel a φ) :=
  AlgebraicLabelledBranchedRoughPath.coeff_comapConstLabel a X.toAlgebraic s t φ

theorem treeCoeff_comapConstLabel
    (a : α) (X : Controlled T α R size gauge) (s t : T) (τ : RootedTree) :
    (comapConstLabel a X).treeCoeff s t τ =
      X.treeCoeff s t (LRootedTree.constLabel a τ) :=
  AlgebraicLabelledBranchedRoughPath.treeCoeff_comapConstLabel a X.toAlgebraic s t τ

@[simp]
theorem comapTime_toAlgebraic {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f) (X : Controlled T α R size gauge) :
    (comapTime f hf X).toAlgebraic =
      AlgebraicLabelledBranchedRoughPath.comapTime f X.toAlgebraic :=
  rfl

@[simp]
theorem coeff_comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f)
    (X : Controlled T α R size gauge) (s t : S) (φ : LRootedForest α) :
    (comapTime f hf X).coeff s t φ = X.coeff (f s) (f t) φ :=
  rfl

@[simp]
theorem treeCoeff_comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f)
    (X : Controlled T α R size gauge) (s t : S) (τ : LRootedTree α) :
    (comapTime f hf X).treeCoeff s t τ = X.treeCoeff (f s) (f t) τ :=
  rfl

@[simp]
theorem comapMapLabels_id (X : Controlled T α R size gauge) :
    comapMapLabels id X = X := by
  apply ext
  · simp [comapMapLabels]
  · rfl

theorem comapMapLabels_comp {β : Type z} {γ : Type y}
    (f : α → β) (g : β → γ) (X : Controlled T γ R size gauge) :
    comapMapLabels f (comapMapLabels g X) = comapMapLabels (g ∘ f) X := by
  apply ext
  · simp [comapMapLabels, AlgebraicLabelledBranchedRoughPath.comapMapLabels_comp]
  · rfl

@[simp]
theorem comapConstLabel_comapEraseLabels
    (a : α) (X : AlgebraicBranchedRoughPath.Controlled T R size gauge) :
    comapConstLabel a (comapEraseLabels (α := α) X) = X := by
  apply AlgebraicBranchedRoughPath.Controlled.ext
  · exact AlgebraicLabelledBranchedRoughPath.comapConstLabel_comapEraseLabels
      a X.toAlgebraic
  · rfl

/-- A controlled labelled branched rough path whose algebraic part descends to
unlabelled forests. -/
def LabelInvariant (X : Controlled T α R size gauge) : Prop :=
  AlgebraicLabelledBranchedRoughPath.LabelInvariant X.toAlgebraic

theorem LabelInvariant.toAlgebraic {X : Controlled T α R size gauge}
    (h : LabelInvariant X) :
    AlgebraicLabelledBranchedRoughPath.LabelInvariant X.toAlgebraic :=
  h

theorem labelInvariant_comapEraseLabels
    (X : AlgebraicBranchedRoughPath.Controlled T R size gauge) :
    LabelInvariant (comapEraseLabels (α := α) X) :=
  AlgebraicLabelledBranchedRoughPath.labelInvariant_comapEraseLabels X.toAlgebraic

theorem LabelInvariant.comapMapLabels {β : Type z}
    {X : Controlled T β R size gauge} (h : LabelInvariant X)
    (f : α → β) : LabelInvariant (comapMapLabels f X) :=
  AlgebraicLabelledBranchedRoughPath.LabelInvariant.comapMapLabels h f

theorem LabelInvariant.comapEraseLabels_comapConstLabel
    {X : Controlled T α R size gauge} (h : LabelInvariant X) (a : α) :
    comapEraseLabels (α := α) (comapConstLabel a X) = X := by
  apply ext
  · exact h.toAlgebraic.comapEraseLabels_comapConstLabel a
  · rfl

/-- Unlabelled controlled branched rough paths are equivalent to label-invariant
labelled controlled branched rough paths. -/
noncomputable def labelInvariantEquiv [Nonempty α] :
    AlgebraicBranchedRoughPath.Controlled T R size gauge ≃
      {X : Controlled T α R size gauge // LabelInvariant X} where
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
theorem labelInvariantEquiv_apply [Nonempty α]
    (X : AlgebraicBranchedRoughPath.Controlled T R size gauge) :
    (labelInvariantEquiv (α := α) X).1 = comapEraseLabels (α := α) X :=
  rfl

@[simp]
theorem labelInvariantEquiv_symm_apply [Nonempty α]
    (X : {X : Controlled T α R size gauge // LabelInvariant X}) :
    (labelInvariantEquiv (α := α) (T := T) (R := R)).symm X =
      comapConstLabel (Classical.choice (inferInstance : Nonempty α)) X.1 :=
  rfl

theorem labelInvariant_iff_exists_comapEraseLabels [Nonempty α]
    (X : Controlled T α R size gauge) :
    LabelInvariant X ↔
      ∃ Y : AlgebraicBranchedRoughPath.Controlled T R size gauge,
        comapEraseLabels (α := α) Y = X := by
  constructor
  · intro hX
    let a := Classical.choice (inferInstance : Nonempty α)
    exact ⟨comapConstLabel a X, hX.comapEraseLabels_comapConstLabel a⟩
  · rintro ⟨Y, rfl⟩
    exact labelInvariant_comapEraseLabels (α := α) Y

@[simp]
theorem comapTime_id (X : Controlled T α R size gauge) :
    comapTime id (fun _ _ h => h) X = X := by
  apply ext
  · simp [comapTime]
  · exact Control.comap_id X.control

theorem comapTime_comp {S : Type z} {U : Type y} [Preorder S] [Preorder U]
    (f : S → T) (hf : Monotone f) (g : U → S) (hg : Monotone g)
    (X : Controlled T α R size gauge) :
    comapTime g hg (comapTime f hf X) =
      comapTime (f ∘ g) (fun _ _ h => hf (hg h)) X := by
  apply ext
  · simp [comapTime, AlgebraicLabelledBranchedRoughPath.comapTime_comp]
  · exact Control.comap_comp X.control f hf g hg

theorem coordinate_bound (X : Controlled T α R size gauge)
    {s t : T} (hst : s ≤ t) (φ : LRootedForest α) :
    size (X.coeff s t φ) ≤ gauge (LRootedForest.order φ) (X.control s t) :=
  X.controlled hst φ

theorem tree_coordinate_bound (X : Controlled T α R size gauge)
    {s t : T} (hst : s ≤ t) (τ : LRootedTree α) :
    size (X.treeCoeff s t τ) ≤ gauge (LRootedTree.order τ) (X.control s t) :=
  HasForestControl.treeCoeff_bound X.controlled hst τ

end Controlled

end AlgebraicLabelledBranchedRoughPath

end

end RoughPaths
