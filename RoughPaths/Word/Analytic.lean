/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.Algebraic
import Mathlib.Data.ENNReal.Basic

/-!
# Analytic Rough Path Bounds

This file adds a lightweight analytic layer for rough paths. The central
object is a control, a superadditive two-parameter function used in the
standard formulation of rough path variation estimates.

The bounds are deliberately stated with an abstract coordinate size and gauge.
This keeps the definitions independent of a particular normed coefficient
space or choice of exponent.

## Main definitions

* `Control` - superadditive two-parameter control function
* `IncrementControlledBy` - generic bound for an increment map
* `AlgebraicRoughPath.HasCoordinateControl` - word-coordinate bounds

Forest-coordinate controls for branched rough paths live downstream in
LeanBSeries (`BSeries.RoughPaths.Analytic`).
-/

namespace RoughPaths

universe u v w z y

noncomputable section

/-- A control is a superadditive two-parameter function with zero diagonal. -/
structure Control (T : Type u) [Preorder T] where
  toFun : T → T → ENNReal
  diagonal : ∀ t : T, toFun t t = 0
  superadditive :
    ∀ {s u t : T}, s ≤ u → u ≤ t → toFun s u + toFun u t ≤ toFun s t

namespace Control

variable {S : Type z} {T : Type u} [Preorder S] [Preorder T]

instance : CoeFun (Control T) (fun _ => T → T → ENNReal) where
  coe ω := ω.toFun

@[ext]
theorem ext {ω η : Control T} (h : ∀ s t : T, ω s t = η s t) : ω = η := by
  cases ω with
  | mk f hf hsuper =>
    cases η with
    | mk g hg gsuper =>
      have hfg : f = g := funext fun s => funext fun t => h s t
      subst g
      rfl

@[simp]
theorem diagonal_apply (ω : Control T) (t : T) : ω t t = 0 :=
  ω.diagonal t

theorem superadditive_apply (ω : Control T) {s u t : T}
    (hsu : s ≤ u) (hut : u ≤ t) : ω s u + ω u t ≤ ω s t :=
  ω.superadditive hsu hut

/-- The zero control. -/
def zero (T : Type u) [Preorder T] : Control T where
  toFun _ _ := 0
  diagonal _ := rfl
  superadditive _ _ := by simp

@[simp]
theorem zero_apply (s t : T) : zero T s t = 0 :=
  rfl

/-- Pull a control back along a monotone map of time domains. -/
def comap (ω : Control T) (f : S → T) (hf : Monotone f) : Control S where
  toFun s t := ω (f s) (f t)
  diagonal s := ω.diagonal (f s)
  superadditive hsu hut := ω.superadditive (hf hsu) (hf hut)

@[simp]
theorem comap_apply (ω : Control T) (f : S → T) (hf : Monotone f) (s t : S) :
    ω.comap f hf s t = ω (f s) (f t) :=
  rfl

@[simp]
theorem comap_id (ω : Control T) :
    ω.comap id (fun _ _ h => h) = ω := by
  ext s t
  rfl

theorem comap_comp {U : Type y} [Preorder U]
    (ω : Control T) (f : S → T) (hf : Monotone f)
    (g : U → S) (hg : Monotone g) :
    (ω.comap f hf).comap g hg =
      ω.comap (f ∘ g) (fun _ _ h => hf (hg h)) := by
  ext s t
  rfl

end Control

/-- A generic coordinate increment bound by a control. -/
def IncrementControlledBy {T : Type u} {E : Type v} [Preorder T]
    (x : T → T → E) (size : E → ENNReal) (ω : Control T) : Prop :=
  ∀ {s t : T}, s ≤ t → size (x s t) ≤ ω s t

namespace IncrementControlledBy

variable {T : Type u} {E : Type v} [Preorder T]
variable {S : Type z} [Preorder S]
variable {x : T → T → E} {size size' : E → ENNReal}
variable {ω η : Control T}

theorem mono_control (h : IncrementControlledBy x size ω)
    (hω : ∀ {s t : T}, s ≤ t → ω s t ≤ η s t) :
    IncrementControlledBy x size η := by
  intro s t hst
  exact le_trans (h hst) (hω hst)

theorem mono_size (h : IncrementControlledBy x size ω)
    (hsize : ∀ y : E, size' y ≤ size y) :
    IncrementControlledBy x size' ω := by
  intro s t hst
  exact le_trans (hsize (x s t)) (h hst)

theorem comapTime (h : IncrementControlledBy x size ω)
    (f : S → T) (hf : Monotone f) :
    IncrementControlledBy (fun s t => x (f s) (f t)) size (ω.comap f hf) := by
  intro s t hst
  exact h (hf hst)

end IncrementControlledBy

namespace AlgebraicRoughPath

variable {T : Type u} {α : Type v} {R : Type w} [Preorder T] [Semiring R]

/-- All word coordinates of a rough path are bounded by a control and gauge. -/
def HasCoordinateControl (X : AlgebraicRoughPath T α R)
    (ω : Control T) (size : R → ENNReal)
    (gauge : Nat → ENNReal → ENNReal) : Prop :=
  ∀ {s t : T}, s ≤ t → ∀ word : List α,
    size (coeff X s t word) ≤ gauge word.length (ω s t)

theorem HasCoordinateControl.coeff_bound {X : AlgebraicRoughPath T α R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasCoordinateControl ω size gauge)
    {s t : T} (hst : s ≤ t) (word : List α) :
    size (coeff X s t word) ≤ gauge word.length (ω s t) :=
  h hst word

theorem HasCoordinateControl.incrementControlledBy {X : AlgebraicRoughPath T α R}
    {ω η : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasCoordinateControl ω size gauge) (word : List α)
    (hη : ∀ {s t : T}, s ≤ t → gauge word.length (ω s t) ≤ η s t) :
    IncrementControlledBy (fun s t => coeff X s t word) size η := by
  intro s t hst
  exact le_trans (h hst word) (hη hst)

theorem HasCoordinateControl.comapMapLetters {β : Type z} (f : α → β)
    {X : AlgebraicRoughPath T β R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasCoordinateControl ω size gauge) :
    (AlgebraicRoughPath.comapMapLetters f X).HasCoordinateControl ω size gauge := by
  intro s t hst word
  rw [AlgebraicRoughPath.coeff_comapMapLetters]
  simpa using h hst (word.map f)

theorem HasCoordinateControl.comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f) {X : AlgebraicRoughPath T α R}
    {ω : Control T} {size : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasCoordinateControl ω size gauge) :
    (AlgebraicRoughPath.comapTime f X).HasCoordinateControl (ω.comap f hf) size gauge := by
  intro s t hst word
  rw [AlgebraicRoughPath.coeff_comapTime]
  exact h (hf hst) word

theorem HasCoordinateControl.mono_gauge {X : AlgebraicRoughPath T α R}
    {ω : Control T} {size : R → ENNReal}
    {gauge gauge' : Nat → ENNReal → ENNReal}
    (h : X.HasCoordinateControl ω size gauge)
    (hgauge : ∀ n r, gauge n r ≤ gauge' n r) :
    X.HasCoordinateControl ω size gauge' := by
  intro s t hst word
  exact le_trans (h hst word) (hgauge word.length (ω s t))

theorem HasCoordinateControl.mono_size {X : AlgebraicRoughPath T α R}
    {ω : Control T} {size size' : R → ENNReal}
    {gauge : Nat → ENNReal → ENNReal}
    (h : X.HasCoordinateControl ω size gauge)
    (hsize : ∀ r : R, size' r ≤ size r) :
    X.HasCoordinateControl ω size' gauge := by
  intro s t hst word
  exact le_trans (hsize (coeff X s t word)) (h hst word)

theorem HasCoordinateControl.mono_control {X : AlgebraicRoughPath T α R}
    {ω η : Control T} {size : R → ENNReal}
    {gauge gauge' : Nat → ENNReal → ENNReal}
    (h : X.HasCoordinateControl ω size gauge)
    (hω : ∀ {s t : T}, s ≤ t → ω s t ≤ η s t)
    (hgauge : ∀ n {r r' : ENNReal}, r ≤ r' → gauge n r ≤ gauge' n r') :
    X.HasCoordinateControl η size gauge' := by
  intro s t hst word
  exact le_trans (h hst word) (hgauge word.length (hω hst))

/-- A rough path together with a coordinate control certificate. -/
structure Controlled (T : Type u) (α : Type v) (R : Type w)
    [Preorder T] [Semiring R]
    (size : R → ENNReal) (gauge : Nat → ENNReal → ENNReal) where
  toAlgebraic : AlgebraicRoughPath T α R
  control : Control T
  controlled : toAlgebraic.HasCoordinateControl control size gauge

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

/-- Pull a controlled rough path back along a map of alphabets. -/
def comapMapLetters {β : Type z} (f : α → β)
    (X : Controlled T β R size gauge) : Controlled T α R size gauge where
  toAlgebraic := AlgebraicRoughPath.comapMapLetters f X.toAlgebraic
  control := X.control
  controlled := AlgebraicRoughPath.HasCoordinateControl.comapMapLetters f X.controlled

/-- Pull a controlled rough path back along a monotone map of time domains. -/
def comapTime {S : Type z} [Preorder S] (f : S → T) (hf : Monotone f)
    (X : Controlled T α R size gauge) : Controlled S α R size gauge where
  toAlgebraic := AlgebraicRoughPath.comapTime f X.toAlgebraic
  control := X.control.comap f hf
  controlled := AlgebraicRoughPath.HasCoordinateControl.comapTime f hf X.controlled

/-- Coordinate of a controlled rough path increment on a word. -/
def coeff (X : Controlled T α R size gauge) (s t : T) (word : List α) : R :=
  AlgebraicRoughPath.coeff X.toAlgebraic s t word

@[simp]
theorem comapMapLetters_toAlgebraic {β : Type z} (f : α → β)
    (X : Controlled T β R size gauge) :
    (comapMapLetters f X).toAlgebraic =
      AlgebraicRoughPath.comapMapLetters f X.toAlgebraic :=
  rfl

@[simp]
theorem coeff_apply (X : Controlled T α R size gauge) (s t : T) (word : List α) :
    X.coeff s t word = AlgebraicRoughPath.coeff X.toAlgebraic s t word :=
  rfl

@[simp]
theorem coeff_comapMapLetters {β : Type z} (f : α → β)
    (X : Controlled T β R size gauge) (s t : T) (word : List α) :
    (comapMapLetters f X).coeff s t word = X.coeff s t (word.map f) :=
  rfl

@[simp]
theorem comapTime_toAlgebraic {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f) (X : Controlled T α R size gauge) :
    (comapTime f hf X).toAlgebraic =
      AlgebraicRoughPath.comapTime f X.toAlgebraic :=
  rfl

@[simp]
theorem coeff_comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f)
    (X : Controlled T α R size gauge) (s t : S) (word : List α) :
    (comapTime f hf X).coeff s t word = X.coeff (f s) (f t) word :=
  rfl

@[simp]
theorem comapMapLetters_id (X : Controlled T α R size gauge) :
    comapMapLetters id X = X := by
  apply ext
  · simp [comapMapLetters]
  · rfl

theorem comapMapLetters_comp {β : Type z} {γ : Type y}
    (f : α → β) (g : β → γ) (X : Controlled T γ R size gauge) :
    comapMapLetters f (comapMapLetters g X) = comapMapLetters (g ∘ f) X := by
  apply ext
  · simp [comapMapLetters, AlgebraicRoughPath.comapMapLetters_comp]
  · rfl

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
  · simp [comapTime, AlgebraicRoughPath.comapTime_comp]
  · exact Control.comap_comp X.control f hf g hg

theorem coordinate_bound (X : Controlled T α R size gauge)
    {s t : T} (hst : s ≤ t) (word : List α) :
    size (X.coeff s t word) ≤ gauge word.length (X.control s t) :=
  X.controlled hst word

end Controlled

end AlgebraicRoughPath

end

end RoughPaths
