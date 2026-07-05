/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.Analytic
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Concrete controls

Constructions of superadditive controls: the linear control `c·(t − s)` on
the real line, sums, scalar multiples, powers `ω^p` for `p ≥ 1`, controls
from bounded variation, and the bridge from Hölder continuity. Also the
standard power gauge `(k, r) ↦ C^k · r^(a·k)` instantiating the abstract
gauge of `RoughPaths.Analytic`.
-/

namespace RoughPaths

open scoped ENNReal NNReal

universe u v

noncomputable section

namespace Control

variable {T : Type u} [Preorder T]

/-- The linear control `c·(t − s)` on the real line. -/
def ofReal (c : ℝ≥0∞) : Control ℝ where
  toFun s t := c * ENNReal.ofReal (t - s)
  diagonal t := by simp
  superadditive {s u t} hsu hut := le_of_eq (by
    have h : u - s + (t - u) = t - s := by ring
    rw [← mul_add,
      ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ u - s)
        (by linarith : (0:ℝ) ≤ t - u), h])

@[simp]
theorem ofReal_apply (c : ℝ≥0∞) (s t : ℝ) :
    ofReal c s t = c * ENNReal.ofReal (t - s) :=
  rfl

/-- The sum of two controls. -/
def add (ω η : Control T) : Control T where
  toFun s t := ω s t + η s t
  diagonal t := by simp
  superadditive {s u t} hsu hut := by
    calc ω s u + η s u + (ω u t + η u t)
        = (ω s u + ω u t) + (η s u + η u t) := by ring
      _ ≤ ω s t + η s t :=
        add_le_add (ω.superadditive hsu hut) (η.superadditive hsu hut)

@[simp]
theorem add_apply (ω η : Control T) (s t : T) :
    ω.add η s t = ω s t + η s t :=
  rfl

/-- A scalar multiple of a control. -/
def constMul (c : ℝ≥0∞) (ω : Control T) : Control T where
  toFun s t := c * ω s t
  diagonal t := by simp
  superadditive {s u t} hsu hut := by
    rw [← mul_add]
    exact mul_le_mul_right (ω.superadditive hsu hut) c

@[simp]
theorem constMul_apply (c : ℝ≥0∞) (ω : Control T) (s t : T) :
    ω.constMul c s t = c * ω s t :=
  rfl

/-- The `p`-th power of a control is a control for `p ≥ 1`. -/
def rpow (ω : Control T) (p : ℝ) (hp : 1 ≤ p) : Control T where
  toFun s t := ω s t ^ p
  diagonal t := by
    rw [ω.diagonal]
    exact ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hp)
  superadditive {s u t} hsu hut :=
    le_trans (ENNReal.add_rpow_le_rpow_add _ _ hp)
      (ENNReal.rpow_le_rpow (ω.superadditive hsu hut)
        (le_trans zero_le_one hp))

@[simp]
theorem rpow_apply (ω : Control T) (p : ℝ) (hp : 1 ≤ p) (s t : T) :
    ω.rpow p hp s t = ω s t ^ p :=
  rfl

/-- The control given by the extended variation of a path on `[s, t]`. -/
def ofEVariation {E : Type v} [PseudoEMetricSpace E] (f : ℝ → E) : Control ℝ where
  toFun s t := if s ≤ t then eVariationOn f (Set.Icc s t) else 0
  diagonal t := by
    simp [Set.Icc_self]
  superadditive {s u t} hsu hut := by
    rw [if_pos hsu, if_pos hut, if_pos (le_trans hsu hut)]
    refine le_of_eq ?_
    simpa [Set.univ_inter] using
      eVariationOn.Icc_add_Icc f (s := Set.univ) hsu hut (Set.mem_univ u)

@[simp]
theorem ofEVariation_apply_of_le {E : Type v} [PseudoEMetricSpace E]
    (f : ℝ → E) {s t : ℝ} (hst : s ≤ t) :
    ofEVariation f s t = eVariationOn f (Set.Icc s t) :=
  if_pos hst

/-- The linear control associated with a `(C, r)`-Hölder bound: the control
stays LINEAR (so fine partitions are free) and the Hölder exponent lives in
the sewing exponent `θ`. -/
def holder (C r : ℝ≥0) : Control ℝ :=
  ofReal ((C : ℝ≥0∞) ^ (1 / (r : ℝ)))

/-- A `(C, r)`-Hölder path has increments bounded by `(holder C r) ^ r`. -/
theorem holder_bound {E : Type v} [SeminormedAddCommGroup E]
    {C r : ℝ≥0} (hr : 0 < r) {f : ℝ → E} (hf : HolderWith C r f)
    {s t : ℝ} (hst : s ≤ t) :
    ‖f t - f s‖ₑ ≤ holder C r s t ^ (r : ℝ) := by
  have h1 : ‖f t - f s‖ₑ = edist (f t) (f s) := (edist_eq_enorm_sub _ _).symm
  have h2 : edist t s = ENNReal.ofReal (t - s) := by
    rw [edist_dist, Real.dist_eq, abs_of_nonneg (by linarith)]
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  rw [h1]
  refine le_trans (hf.edist_le t s) (le_of_eq ?_)
  rw [h2, holder, ofReal_apply,
    ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hr'),
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr'.ne', ENNReal.rpow_one]

end Control

/-- The standard power gauge `(k, r) ↦ C^k · r^(a·k)` bounding the word
coordinates of a rough path of regularity `a`. -/
def powGauge (C : ℝ≥0∞) (a : ℝ) : Nat → ℝ≥0∞ → ℝ≥0∞ :=
  fun k r => C ^ k * r ^ (a * k)

@[simp]
theorem powGauge_apply (C : ℝ≥0∞) (a : ℝ) (k : Nat) (r : ℝ≥0∞) :
    powGauge C a k r = C ^ k * r ^ (a * k) :=
  rfl

end

end RoughPaths
