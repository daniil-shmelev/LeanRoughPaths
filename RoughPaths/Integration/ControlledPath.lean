/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.Algebraic
import RoughPaths.Integration.FinePartitions

/-!
# Level-2 rough paths and controlled paths

Analytic regularity for a `d`-dimensional rough path with respect to a
control `ω`: the first-level coordinates are bounded by `ω^α` and the
second-level ones by `ω^{2α}`, with `1/3 < α ≤ 1/2`. A path `Y` is
*controlled* by such a rough path (Gubinelli) when it admits a derivative
`Y'` along the first level with remainder of order `ω^{2α}`. Certificates
(the constants) are carried as data so that all downstream estimates are
fully quantitative.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ}

/-- Level-2 Hölder-type bounds for a rough path over the alphabet `Fin d`
with respect to a control `ω`. Covers non-geometric (e.g. Itô-type) rough
paths: only Chen's identity and these bounds are used. -/
structure IsLevel2RoughPath (X : AlgebraicRoughPath ℝ (Fin d) ℝ)
    (ω : Control ℝ) (α : ℝ) : Prop where
  one_third_lt : 1 / 3 < α
  le_half : α ≤ 1 / 2
  bound_one : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ i : Fin d,
    ‖X.coeff s t [i]‖ₑ ≤ ω s t ^ α
  bound_two : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ i j : Fin d,
    ‖X.coeff s t [i, j]‖ₑ ≤ ω s t ^ (2 * α)

theorem IsLevel2RoughPath.alpha_pos {X : AlgebraicRoughPath ℝ (Fin d) ℝ}
    {ω : Control ℝ} {α : ℝ} (hX : IsLevel2RoughPath X ω α) : 0 < α :=
  lt_trans (by norm_num) hX.one_third_lt

theorem IsLevel2RoughPath.one_lt_three_alpha
    {X : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ} {α : ℝ}
    (hX : IsLevel2RoughPath X ω α) : 1 < 3 * α := by
  have := hX.one_third_lt
  linarith

/-- A path with values in `W` controlled by the rough path `X`: a
Gubinelli derivative `Yd` along the first level, a sup bound and an
`α`-Hölder bound on the derivative, and an `ω^{2α}` remainder. -/
structure ControlledPath (X : AlgebraicRoughPath ℝ (Fin d) ℝ)
    (ω : Control ℝ) (α : ℝ) (W : Type*)
    [NormedAddCommGroup W] [NormedSpace ℝ W] where
  /-- The underlying path. -/
  Y : ℝ → W
  /-- The Gubinelli derivative along the first level of `X`. -/
  Yd : ℝ → Fin d → W
  /-- Sup bound for the derivative. -/
  Cb : ℝ≥0
  /-- Hölder constant of the derivative. -/
  Cd : ℝ≥0
  /-- Remainder constant. -/
  Cy : ℝ≥0
  bound_Yd : ∀ (s : ℝ) (i : Fin d), ‖Yd s i‖ₑ ≤ Cb
  holder_Yd : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ i : Fin d,
    ‖Yd t i - Yd s i‖ₑ ≤ Cd * ω s t ^ α
  remainder : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖Y t - Y s - ∑ i, X.coeff s t [i] • Yd s i‖ₑ ≤ Cy * ω s t ^ (2 * α)

namespace ControlledPath

variable {X : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ} {α : ℝ}
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Extended-norm homogeneity of real scalar multiplication. -/
theorem enorm_real_smul (c : ℝ) (x : W) : ‖c • x‖ₑ = ‖c‖ₑ * ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _), norm_smul]

/-- A constant path is controlled with zero derivative. -/
def const (X : AlgebraicRoughPath ℝ (Fin d) ℝ) (ω : Control ℝ) (α : ℝ)
    (w : W) : ControlledPath X ω α W where
  Y _ := w
  Yd _ _ := 0
  Cb := 0
  Cd := 0
  Cy := 0
  bound_Yd s i := by simp
  holder_Yd s t _ i := by simp
  remainder s t _ := by simp

/-- A uniform bound on `Fin d`-indexed summands gives a `d`-scaled
bound. -/
theorem _root_.RoughPaths.enorm_fin_sum_le {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {g : Fin d → F} {C : ℝ≥0∞}
    (h : ∀ i, ‖g i‖ₑ ≤ C) :
    ‖∑ i, g i‖ₑ ≤ d * C :=
  le_trans (enorm_sum_le _ _) <|
    le_trans (Finset.sum_le_sum fun i _ => h i) <| le_of_eq <| by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-- The path increment of a controlled path is bounded by
`d·Cb·ω^α + Cy·ω^{2α}`. -/
theorem enorm_increment_le (hX : IsLevel2RoughPath X ω α)
    (Z : ControlledPath X ω α W) ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖Z.Y t - Z.Y s‖ₑ ≤
      (d : ℝ≥0∞) * Z.Cb * ω s t ^ α + Z.Cy * ω s t ^ (2 * α) := by
  have hsplit : Z.Y t - Z.Y s =
      (Z.Y t - Z.Y s - ∑ i, X.coeff s t [i] • Z.Yd s i) +
        ∑ i, X.coeff s t [i] • Z.Yd s i := by abel
  rw [hsplit]
  refine le_trans (enorm_add_le _ _) ?_
  rw [add_comm]
  refine add_le_add (le_trans (enorm_fin_sum_le fun i => ?_)
    (le_of_eq (mul_assoc _ _ _).symm)) (Z.remainder hst)
  rw [enorm_real_smul]
  exact le_trans (mul_le_mul' (hX.bound_one hst i) (Z.bound_Yd s i))
    (le_of_eq (mul_comm _ _))

end ControlledPath

end RoughPaths
