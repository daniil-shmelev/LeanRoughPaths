/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Integration.RoughIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Composition of controlled paths with vector fields

Friz–Hairer Lemma 7.3, the key step towards RDE well-posedness: if `Y` is
controlled by `X` with Gubinelli derivative `Y'`, and `V = (f, Df)` is a
vector field with bounded, Lipschitz derivative, then `t ↦ f(Y_t)` is
again controlled by `X`, with Gubinelli derivative `Df(Y_t)∘Y'_t` and
fully explicit certificates. The remainder analysis combines the
first-order Taylor bound `‖f(z) - f(y) - Df(y)(z-y)‖ ≤ C₂‖z-y‖²` (from
the mean value inequality applied to `w ↦ f(w) - Df(y)w`) with the
controlled remainder of `Y` pushed through `Df`.

All estimates are stated on a control window `ω ≤ 1`, the normalisation
under which the Picard iteration is run.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Window arithmetic for control powers -/

theorem rpow_two_mul_eq {α : ℝ} (hα : 0 ≤ α) (x : ℝ≥0∞) :
    x ^ (2 * α) = x ^ α * x ^ α := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ hα hα]
  ring_nf

theorem rpow_three_mul_eq {α : ℝ} (hα : 0 ≤ α) (x : ℝ≥0∞) :
    x ^ (3 * α) = x ^ α * x ^ (2 * α) := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ hα (by positivity)]
  ring_nf

theorem rpow_pow_two {α : ℝ} (x : ℝ≥0∞) :
    (x ^ α) ^ (2 : ℕ) = x ^ (2 * α) := by
  rw [← ENNReal.rpow_natCast (x ^ α) 2, ← ENNReal.rpow_mul,
    show α * ((2 : ℕ) : ℝ) = 2 * α by push_cast; ring]

theorem rpow_three_mul_le_mul {α : ℝ} {x : ℝ≥0∞} {δα : ℝ≥0}
    (hα : 0 ≤ α) (hδ : x ^ α ≤ (δα : ℝ≥0∞)) :
    x ^ (3 * α) ≤ (δα : ℝ≥0∞) * x ^ (2 * α) := by
  rw [rpow_three_mul_eq hα]
  exact mul_le_mul' hδ le_rfl

theorem rpow_two_mul_le_coe {α : ℝ} {x : ℝ≥0∞} {δα : ℝ≥0}
    (hα : 0 ≤ α) (hδ : x ^ α ≤ (δα : ℝ≥0∞)) (hδ1 : δα ≤ 1) :
    x ^ (2 * α) ≤ (δα : ℝ≥0∞) := by
  rw [rpow_two_mul_eq hα]
  calc x ^ α * x ^ α ≤ (δα : ℝ≥0∞) * δα := mul_le_mul' hδ hδ
    _ ≤ (δα : ℝ≥0∞) * 1 := mul_le_mul' le_rfl (by exact_mod_cast hδ1)
    _ = (δα : ℝ≥0∞) := mul_one _

theorem rpow_three_mul_le_coe {α : ℝ} {x : ℝ≥0∞} {δα : ℝ≥0}
    (hα : 0 ≤ α) (hδ : x ^ α ≤ (δα : ℝ≥0∞)) (hδ1 : δα ≤ 1) :
    x ^ (3 * α) ≤ (δα : ℝ≥0∞) := by
  refine le_trans (rpow_three_mul_le_mul hα hδ) ?_
  calc (δα : ℝ≥0∞) * x ^ (2 * α) ≤ (δα : ℝ≥0∞) * 1 :=
        mul_le_mul' le_rfl (le_trans (rpow_two_mul_le_coe hα hδ hδ1)
          (by exact_mod_cast hδ1))
    _ = (δα : ℝ≥0∞) := mul_one _

/-- A vector field driving an RDE: components `f i : E → E` with globally
bounded, globally Lipschitz derivatives, all constants explicit. Any
`C²_b` vector field yields such data. -/
structure RDEVectorField (d : ℕ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  /-- The components of the vector field. -/
  f : Fin d → E → E
  /-- The derivative of each component. -/
  deriv : Fin d → E → E →L[ℝ] E
  /-- Sup bound for the components. -/
  C0 : ℝ≥0
  /-- Sup bound for the derivatives. -/
  C1 : ℝ≥0
  /-- Lipschitz constant of the derivatives. -/
  C2 : ℝ≥0
  hasFDeriv : ∀ (i : Fin d) (y : E), HasFDerivAt (f i) (deriv i y) y
  bound_f : ∀ (i : Fin d) (y : E), ‖f i y‖ ≤ C0
  bound_deriv : ∀ (i : Fin d) (y : E), ‖deriv i y‖ ≤ C1
  lipschitz_deriv : ∀ (i : Fin d) (y z : E),
    ‖deriv i y - deriv i z‖ ≤ C2 * ‖y - z‖

namespace RDEVectorField

/-! ### Extended-norm utilities -/

theorem enorm_le_coe {F : Type*} [NormedAddCommGroup F] {x : F}
    {c : ℝ≥0} (h : ‖x‖ ≤ c) : ‖x‖ₑ ≤ (c : ℝ≥0∞) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal h

theorem enorm_clm_apply_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (x : E) :
    ‖L x‖ₑ ≤ ‖L‖ₑ * ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (L.le_opNorm x)

theorem enorm_lipschitz (V : RDEVectorField d E) (i : Fin d)
    (y z : E) :
    ‖V.deriv i y - V.deriv i z‖ₑ ≤ (V.C2 : ℝ≥0∞) * ‖y - z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  calc ENNReal.ofReal ‖V.deriv i y - V.deriv i z‖
      ≤ ENNReal.ofReal (V.C2 * ‖y - z‖) :=
        ENNReal.ofReal_le_ofReal (V.lipschitz_deriv i y z)
    _ = ENNReal.ofReal (V.C2 : ℝ) * ENNReal.ofReal ‖y - z‖ :=
        ENNReal.ofReal_mul (by positivity)
    _ = (V.C2 : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
        rw [ENNReal.ofReal_coe_nnreal]

omit [NormedSpace ℝ E] in
/-- Coordinatewise extended-norm bounds give a `Pi` sup-norm bound. -/
theorem pi_enorm_le {g : Fin d → E} {C : ℝ≥0∞}
    (h : ∀ i, ‖g i‖ₑ ≤ C) : ‖g‖ₑ ≤ C := by
  rcases eq_or_ne C ⊤ with rfl | hC
  · exact le_top
  · have hcoord : ∀ i, ‖g i‖ ≤ C.toReal := by
      intro i
      have := h i
      rw [← ofReal_norm] at this
      exact (ENNReal.ofReal_le_iff_le_toReal hC).1 this
    have hnorm : ‖g‖ ≤ C.toReal :=
      (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2 hcoord
    rw [← ofReal_norm]
    exact le_trans (ENNReal.ofReal_le_ofReal hnorm)
      ENNReal.ofReal_toReal_le

/-! ### The first-order Taylor bound -/

private theorem norm_sub_le_of_mem_segment {y z w : E}
    (hw : w ∈ segment ℝ y z) : ‖w - y‖ ≤ ‖z - y‖ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
  have hb1 : b ≤ 1 := by linarith
  have hwy : a • y + b • z - y = b • (z - y) := by
    have ha1 : a = 1 - b := by linarith
    rw [ha1]
    module
  rw [hwy, norm_smul, Real.norm_of_nonneg hb]
  exact mul_le_of_le_one_left (norm_nonneg _) hb1

/-- **First-order Taylor estimate** for a vector field with Lipschitz
derivative: `‖f(z) - f(y) - Df(y)(z-y)‖ ≤ C₂·‖z-y‖²`. -/
theorem taylor_norm (V : RDEVectorField d E) (i : Fin d) (y z : E) :
    ‖V.f i z - V.f i y - V.deriv i y (z - y)‖ ≤
      V.C2 * ‖z - y‖ ^ 2 := by
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun w => V.f i w - V.deriv i y w)
    (f' := fun w => V.deriv i w - V.deriv i y)
    (s := segment ℝ y z) (C := (V.C2 : ℝ) * ‖z - y‖)
    (fun w _ => ((V.hasFDeriv i w).sub
      ((V.deriv i y).hasFDerivAt)).hasFDerivWithinAt)
    (fun w hw => le_trans (V.lipschitz_deriv i w y)
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hw)
        (by positivity)))
    (convex_segment y z) (left_mem_segment ℝ y z)
    (right_mem_segment ℝ y z)
  have hre : V.f i z - V.deriv i y z - (V.f i y - V.deriv i y y) =
      V.f i z - V.f i y - V.deriv i y (z - y) := by
    rw [map_sub]
    abel
  rw [hre] at key
  calc ‖V.f i z - V.f i y - V.deriv i y (z - y)‖
      ≤ V.C2 * ‖z - y‖ * ‖z - y‖ := key
    _ = V.C2 * ‖z - y‖ ^ 2 := by ring

/-- The Taylor estimate in extended norms. -/
theorem taylor_enorm (V : RDEVectorField d E) (i : Fin d) (y z : E) :
    ‖V.f i z - V.f i y - V.deriv i y (z - y)‖ₑ ≤
      (V.C2 : ℝ≥0∞) * ‖z - y‖ₑ ^ (2 : ℕ) := by
  rw [← ofReal_norm, ← ofReal_norm]
  calc ENNReal.ofReal ‖V.f i z - V.f i y - V.deriv i y (z - y)‖
      ≤ ENNReal.ofReal (V.C2 * ‖z - y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (V.taylor_norm i y z)
    _ = ENNReal.ofReal (V.C2 : ℝ) * ENNReal.ofReal (‖z - y‖ ^ 2) :=
        ENNReal.ofReal_mul (by positivity)
    _ = (V.C2 : ℝ≥0∞) * ENNReal.ofReal ‖z - y‖ ^ (2 : ℕ) := by
        rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow (norm_nonneg _)]

/-! ### Composition (Friz–Hairer Lemma 7.3) -/

variable {X : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ} {α : ℝ}

/-- The increment of a controlled path on a unit control window is of
order `ω^α` with constant `d·Cb + Cy`. -/
theorem increment_le (hX : IsLevel2RoughPath X ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (Z : ControlledPath X ω α E) ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖Z.Y t - Z.Y s‖ₑ ≤
      ((d : ℝ≥0∞) * Z.Cb + Z.Cy) * ω s t ^ α := by
  refine le_trans (ControlledPath.enorm_increment_le hX Z hst) ?_
  rw [add_mul]
  refine add_le_add le_rfl (mul_le_mul' le_rfl ?_)
  exact ENNReal.rpow_le_rpow_of_exponent_ge (hω1 hst)
    (by linarith [hX.alpha_pos])

/-- **Composition of a controlled path with a vector field** (FH Lemma
7.3): `t ↦ (f i (Y t))_i` is controlled by `X` with Gubinelli derivative
`(Df i (Y t) (Y'_j t))_{ij}` and explicit certificates. -/
noncomputable def compControlled (V : RDEVectorField d E)
    (hX : IsLevel2RoughPath X ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (Z : ControlledPath X ω α E) :
    ControlledPath X ω α (Fin d → E) where
  Y t := fun i => V.f i (Z.Y t)
  Yd t j := fun i => V.deriv i (Z.Y t) (Z.Yd t j)
  Cb := V.C1 * Z.Cb
  Cd := V.C1 * Z.Cd + V.C2 * Z.Cb * (d * Z.Cb + Z.Cy)
  Cy := V.C1 * Z.Cy + V.C2 * (d * Z.Cb + Z.Cy) ^ 2
  bound_Yd := by
    intro s j
    refine pi_enorm_le fun i => ?_
    calc ‖V.deriv i (Z.Y s) (Z.Yd s j)‖ₑ
        ≤ ‖V.deriv i (Z.Y s)‖ₑ * ‖Z.Yd s j‖ₑ := enorm_clm_apply_le _ _
      _ ≤ (V.C1 : ℝ≥0∞) * Z.Cb :=
          mul_le_mul' (enorm_le_coe (V.bound_deriv i (Z.Y s)))
            (Z.bound_Yd s j)
      _ = ((V.C1 * Z.Cb : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
  holder_Yd := by
    intro s t hst j
    refine pi_enorm_le fun i => ?_
    have hsplit : V.deriv i (Z.Y t) (Z.Yd t j) -
        V.deriv i (Z.Y s) (Z.Yd s j) =
        V.deriv i (Z.Y t) (Z.Yd t j - Z.Yd s j) +
          (V.deriv i (Z.Y t) - V.deriv i (Z.Y s)) (Z.Yd s j) := by
      rw [map_sub, sub_apply]
      abel
    simp only [Pi.sub_apply]
    rw [hsplit]
    refine le_trans (enorm_add_le _ _) ?_
    have h1 : ‖V.deriv i (Z.Y t) (Z.Yd t j - Z.Yd s j)‖ₑ ≤
        (V.C1 : ℝ≥0∞) * (Z.Cd * ω s t ^ α) := by
      calc ‖V.deriv i (Z.Y t) (Z.Yd t j - Z.Yd s j)‖ₑ
          ≤ ‖V.deriv i (Z.Y t)‖ₑ * ‖Z.Yd t j - Z.Yd s j‖ₑ :=
            enorm_clm_apply_le _ _
        _ ≤ (V.C1 : ℝ≥0∞) * (Z.Cd * ω s t ^ α) :=
            mul_le_mul' (enorm_le_coe (V.bound_deriv i (Z.Y t)))
              (Z.holder_Yd hst j)
    have h2 : ‖(V.deriv i (Z.Y t) - V.deriv i (Z.Y s)) (Z.Yd s j)‖ₑ ≤
        (V.C2 : ℝ≥0∞) * (((d : ℝ≥0∞) * Z.Cb + Z.Cy) * ω s t ^ α) *
          Z.Cb := by
      calc ‖(V.deriv i (Z.Y t) - V.deriv i (Z.Y s)) (Z.Yd s j)‖ₑ
          ≤ ‖V.deriv i (Z.Y t) - V.deriv i (Z.Y s)‖ₑ * ‖Z.Yd s j‖ₑ :=
            enorm_clm_apply_le _ _
        _ ≤ ((V.C2 : ℝ≥0∞) * ‖Z.Y t - Z.Y s‖ₑ) * Z.Cb :=
            mul_le_mul' (V.enorm_lipschitz i _ _) (Z.bound_Yd s j)
        _ ≤ ((V.C2 : ℝ≥0∞) *
              (((d : ℝ≥0∞) * Z.Cb + Z.Cy) * ω s t ^ α)) * Z.Cb :=
            mul_le_mul' (mul_le_mul' le_rfl
              (increment_le hX hω1 Z hst)) le_rfl
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    push_cast
    ring
  remainder := by
    intro s t hst
    have hcoord : ∀ i : Fin d,
        ((fun i => V.f i (Z.Y t)) - (fun i => V.f i (Z.Y s)) -
          ∑ j, X.coeff s t [j] •
            fun i => V.deriv i (Z.Y s) (Z.Yd s j)) i =
        V.f i (Z.Y t) - V.f i (Z.Y s) -
          V.deriv i (Z.Y s) (Z.Y t - Z.Y s) +
          V.deriv i (Z.Y s)
            (Z.Y t - Z.Y s - ∑ j, X.coeff s t [j] • Z.Yd s j) := by
      intro i
      have happly : (∑ j, X.coeff s t [j] •
          fun i => V.deriv i (Z.Y s) (Z.Yd s j)) i =
          V.deriv i (Z.Y s) (∑ j, X.coeff s t [j] • Z.Yd s j) := by
        rw [Finset.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, map_smul]
      simp only [Pi.sub_apply]
      rw [happly, map_sub, map_sub, map_sub]
      abel
    refine pi_enorm_le fun i => ?_
    rw [hcoord i]
    refine le_trans (enorm_add_le _ _) ?_
    have h1 : ‖V.f i (Z.Y t) - V.f i (Z.Y s) -
        V.deriv i (Z.Y s) (Z.Y t - Z.Y s)‖ₑ ≤
        (V.C2 : ℝ≥0∞) * (((d : ℝ≥0∞) * Z.Cb + Z.Cy) ^ (2 : ℕ) *
          ω s t ^ (2 * α)) := by
      refine le_trans (V.taylor_enorm i (Z.Y s) (Z.Y t)) ?_
      have hsq : ‖Z.Y t - Z.Y s‖ₑ ^ (2 : ℕ) ≤
          ((d : ℝ≥0∞) * Z.Cb + Z.Cy) ^ (2 : ℕ) * ω s t ^ (2 * α) := by
        calc ‖Z.Y t - Z.Y s‖ₑ ^ (2 : ℕ)
            ≤ ((((d : ℝ≥0∞) * Z.Cb + Z.Cy)) * ω s t ^ α) ^ (2 : ℕ) :=
              pow_le_pow_left' (increment_le hX hω1 Z hst) 2
          _ = ((d : ℝ≥0∞) * Z.Cb + Z.Cy) ^ (2 : ℕ) *
                (ω s t ^ α) ^ (2 : ℕ) := mul_pow _ _ 2
          _ = ((d : ℝ≥0∞) * Z.Cb + Z.Cy) ^ (2 : ℕ) *
                ω s t ^ (2 * α) := by rw [rpow_pow_two]
      exact mul_le_mul' le_rfl hsq
    have h2 : ‖V.deriv i (Z.Y s)
        (Z.Y t - Z.Y s - ∑ j, X.coeff s t [j] • Z.Yd s j)‖ₑ ≤
        (V.C1 : ℝ≥0∞) * (Z.Cy * ω s t ^ (2 * α)) := by
      calc ‖V.deriv i (Z.Y s)
            (Z.Y t - Z.Y s - ∑ j, X.coeff s t [j] • Z.Yd s j)‖ₑ
          ≤ ‖V.deriv i (Z.Y s)‖ₑ *
              ‖Z.Y t - Z.Y s - ∑ j, X.coeff s t [j] • Z.Yd s j‖ₑ :=
            enorm_clm_apply_le _ _
        _ ≤ (V.C1 : ℝ≥0∞) * (Z.Cy * ω s t ^ (2 * α)) :=
            mul_le_mul' (enorm_le_coe (V.bound_deriv i (Z.Y s)))
              (Z.remainder hst)
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    push_cast
    ring

@[simp]
theorem compControlled_Y (V : RDEVectorField d E)
    (hX : IsLevel2RoughPath X ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (Z : ControlledPath X ω α E) (t : ℝ) (i : Fin d) :
    (V.compControlled hX hω1 Z).Y t i = V.f i (Z.Y t) :=
  rfl

@[simp]
theorem compControlled_Yd (V : RDEVectorField d E)
    (hX : IsLevel2RoughPath X ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (Z : ControlledPath X ω α E) (t : ℝ) (j i : Fin d) :
    (V.compControlled hX hω1 Z).Yd t j i =
      V.deriv i (Z.Y t) (Z.Yd t j) :=
  rfl

end RDEVectorField

end RoughPaths
