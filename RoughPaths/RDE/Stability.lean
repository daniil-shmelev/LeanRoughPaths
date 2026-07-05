/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.RDE.Composition

/-!
# Stability of the rough integral in the integrand

Certified distances between controlled paths: a `ControlledDist Z₁ Z₂`
carries sup, derivative-sup, derivative-Hölder and remainder bounds for
the difference `Z₁ - Z₂`, making the difference itself a controlled path.
The Gubinelli germ is linear in the controlled-path data, so by the
uniqueness half of the sewing lemma the difference of two rough integrals
is the rough integral of the difference — with the *small* germ constant
`roughConst` of the difference, the key input to the Picard contraction.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ} {E W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {X : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ} {α : ℝ}

/-- Certified distance data between two controlled paths: quantitative
bounds on the difference path, its Gubinelli derivative, and their
regularity. -/
structure ControlledDist (Z₁ Z₂ : ControlledPath X ω α W) where
  /-- Sup bound for the difference of paths. -/
  D0 : ℝ≥0
  /-- Sup bound for the difference of derivatives. -/
  Db : ℝ≥0
  /-- Hölder constant of the difference of derivatives. -/
  Dd : ℝ≥0
  /-- Remainder constant of the difference. -/
  Dy : ℝ≥0
  bound_Y : ∀ s : ℝ, ‖Z₁.Y s - Z₂.Y s‖ₑ ≤ D0
  bound_Yd : ∀ (s : ℝ) (i : Fin d), ‖Z₁.Yd s i - Z₂.Yd s i‖ₑ ≤ Db
  holder_Yd : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ i : Fin d,
    ‖Z₁.Yd t i - Z₂.Yd t i - (Z₁.Yd s i - Z₂.Yd s i)‖ₑ ≤ Dd * ω s t ^ α
  remainder : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖Z₁.Y t - Z₂.Y t - (Z₁.Y s - Z₂.Y s) -
        ∑ i, X.coeff s t [i] • (Z₁.Yd s i - Z₂.Yd s i)‖ₑ ≤
      Dy * ω s t ^ (2 * α)

namespace ControlledDist

variable {Z₁ Z₂ : ControlledPath X ω α W}

/-- The difference of two controlled paths, as a controlled path with the
distance certificates. -/
def toControlledPath (D : ControlledDist Z₁ Z₂) :
    ControlledPath X ω α W where
  Y t := Z₁.Y t - Z₂.Y t
  Yd t i := Z₁.Yd t i - Z₂.Yd t i
  Cb := D.Db
  Cd := D.Dd
  Cy := D.Dy
  bound_Yd := D.bound_Yd
  holder_Yd := D.holder_Yd
  remainder := D.remainder

@[simp]
theorem toControlledPath_Y (D : ControlledDist Z₁ Z₂) (t : ℝ) :
    D.toControlledPath.Y t = Z₁.Y t - Z₂.Y t :=
  rfl

@[simp]
theorem toControlledPath_Yd (D : ControlledDist Z₁ Z₂) (t : ℝ)
    (i : Fin d) :
    D.toControlledPath.Yd t i = Z₁.Yd t i - Z₂.Yd t i :=
  rfl

@[simp]
theorem toControlledPath_Cb (D : ControlledDist Z₁ Z₂) :
    D.toControlledPath.Cb = D.Db := rfl

@[simp]
theorem toControlledPath_Cd (D : ControlledDist Z₁ Z₂) :
    D.toControlledPath.Cd = D.Dd := rfl

@[simp]
theorem toControlledPath_Cy (D : ControlledDist Z₁ Z₂) :
    D.toControlledPath.Cy = D.Dy := rfl

end ControlledDist

/-- **Linearity of the Gubinelli germ** in the controlled-path data. -/
theorem gubinelliGerm_sub {Z₁ Z₂ : ControlledPath X ω α (Fin d → E)}
    (D : ControlledDist Z₁ Z₂) (s t : ℝ) :
    gubinelliGerm Z₁ s t - gubinelliGerm Z₂ s t =
      gubinelliGerm D.toControlledPath s t := by
  rw [gubinelliGerm_apply, gubinelliGerm_apply, gubinelliGerm_apply]
  have h1 : ∑ i, X.coeff s t [i] • D.toControlledPath.Y s i =
      (∑ i, X.coeff s t [i] • Z₁.Y s i) -
        ∑ i, X.coeff s t [i] • Z₂.Y s i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ControlledDist.toControlledPath_Y, Pi.sub_apply, smul_sub]
  have h2 : ∑ i, ∑ j, X.coeff s t [i, j] •
      D.toControlledPath.Yd s i j =
      (∑ i, ∑ j, X.coeff s t [i, j] • Z₁.Yd s i j) -
        ∑ i, ∑ j, X.coeff s t [i, j] • Z₂.Yd s i j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ControlledDist.toControlledPath_Yd, Pi.sub_apply, smul_sub]
  rw [h1, h2]
  abel

/-- The increment of the difference of two controlled paths. -/
theorem ControlledDist.increment_sub_le (hX : IsLevel2RoughPath X ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    {Z₁ Z₂ : ControlledPath X ω α W} (D : ControlledDist Z₁ Z₂)
    ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s)‖ₑ ≤
      ((d : ℝ≥0∞) * D.Db + D.Dy) * ω s t ^ α := by
  rw [show Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s) =
    Z₁.Y t - Z₂.Y t - (Z₁.Y s - Z₂.Y s) by abel]
  exact RDEVectorField.increment_le hX hω1 D.toControlledPath hst

/-- **Stability of the rough integral in the integrand**: the difference
of two rough integrals is controlled by the *distance* germ constant of
the integrands — not merely by the sum of their individual constants. -/
theorem roughIntegral_sub [CompleteSpace E]
    (hX : IsLevel2RoughPath X ω α)
    (hfine : Sewing.HasFinePartitions ω)
    (hω : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    {Z₁ Z₂ : ControlledPath X ω α (Fin d → E)}
    (D : ControlledDist Z₁ Z₂)
    {I₁ I₂ : ℝ → ℝ → E}
    (hadd₁ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₁ s u + I₁ u t = I₁ s t)
    (hadd₂ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₂ s u + I₂ u t = I₂ s t)
    (hgerm₁ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - gubinelliGerm Z₁ s t‖ₑ ≤
        Sewing.sewingConst (3 * α) * (roughConst Z₁ * ω s t ^ (3 * α)))
    (hgerm₂ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₂ s t - gubinelliGerm Z₂ s t‖ₑ ≤
        Sewing.sewingConst (3 * α) * (roughConst Z₂ * ω s t ^ (3 * α))) :
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - I₂ s t - gubinelliGerm D.toControlledPath s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst D.toControlledPath * ω s t ^ (3 * α)) := by
  have h3α := hX.one_lt_three_alpha
  have hKne : Sewing.sewingConst (3 * α) ≠ ⊤ :=
    (Sewing.sewingConst_lt_top h3α).ne
  -- the sewn integral of the difference path
  obtain ⟨J, hJadd, hJgerm, -⟩ :=
    exists_roughIntegral hX D.toControlledPath hfine hω
  -- `I₁ - I₂` and `J` are both additive primitives of the difference germ
  have heq : ∀ ⦃s t : ℝ⦄, s ≤ t → I₁ s t - I₂ s t = J s t := by
    intro s t hst
    refine Sewing.eq_of_additive_of_germ_bound ω
      (gubinelliGerm D.toControlledPath) h3α
      (C := Sewing.sewingConst (3 * α) * (roughConst Z₁ + roughConst Z₂))
      (C' := Sewing.sewingConst (3 * α) * roughConst D.toControlledPath)
      (ENNReal.mul_ne_top hKne (ENNReal.add_ne_top.2
        ⟨roughConst_ne_top Z₁, roughConst_ne_top Z₂⟩))
      (ENNReal.mul_ne_top hKne (roughConst_ne_top D.toControlledPath))
      hfine
      (fun a u b hau hub => by
        have h₁ := hadd₁ hau hub
        have h₂ := hadd₂ hau hub
        rw [show I₁ a u - I₂ a u + (I₁ u b - I₂ u b) =
          (I₁ a u + I₁ u b) - (I₂ a u + I₂ u b) by abel, h₁, h₂])
      hJadd
      (fun a b hab => by
        rw [← gubinelliGerm_sub D a b,
          show I₁ a b - I₂ a b -
            (gubinelliGerm Z₁ a b - gubinelliGerm Z₂ a b) =
            (I₁ a b - gubinelliGerm Z₁ a b) -
              (I₂ a b - gubinelliGerm Z₂ a b) by abel]
        refine le_trans enorm_sub_le ?_
        refine le_trans (add_le_add (hgerm₁ hab) (hgerm₂ hab)) (le_of_eq ?_)
        ring)
      (fun a b hab => by
        rw [mul_assoc]
        exact hJgerm hab)
      hst (hω hst)
  intro s t hst
  rw [heq hst]
  exact hJgerm hst

/-! ### Two-path estimates for a vector field with Lipschitz second
derivative -/

/-- A vector field with second-derivative data: the base `RDEVectorField`
together with a bounded, Lipschitz second derivative (a `C³_b`-type
assumption, needed for the Lipschitz dependence of the composition on the
controlled path, as in Friz–Hairer Thm 8.4). -/
structure RDEVectorField3 (d : ℕ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] extends RDEVectorField d E where
  /-- The second derivative of each component. -/
  deriv2 : Fin d → E → E →L[ℝ] E →L[ℝ] E
  /-- Lipschitz constant of the second derivatives. -/
  C3 : ℝ≥0
  hasFDeriv2 : ∀ (i : Fin d) (y : E), HasFDerivAt (deriv i) (deriv2 i y) y
  bound_deriv2 : ∀ (i : Fin d) (y : E), ‖deriv2 i y‖ ≤ C2
  lipschitz_deriv2 : ∀ (i : Fin d) (y z : E),
    ‖deriv2 i y - deriv2 i z‖ ≤ C3 * ‖y - z‖

namespace RDEVectorField3

variable (V : RDEVectorField3 d E)

/-- Components of the vector field are `C₁`-Lipschitz. -/
theorem f_lipschitz (i : Fin d) (y z : E) :
    ‖V.f i z - V.f i y‖ ≤ V.C1 * ‖z - y‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun w => V.deriv i w)
    (fun w _ => (V.hasFDeriv i w).hasFDerivWithinAt)
    (fun w _ => V.bound_deriv i w)
    (convex_segment y z) (left_mem_segment ℝ y z)
    (right_mem_segment ℝ y z)

private theorem hasDerivAt_line (y v : E) (r : ℝ) :
    HasDerivAt (fun r : ℝ => y + r • v) v r := by
  simpa using ((hasDerivAt_id r).smul_const v).const_add y

/-- **Second-order double difference**: derivative increments along two
segments differ by at most
`C₂‖v₁-v₂‖ + C₃(‖y₁-y₂‖+‖v₁-v₂‖)‖v₂‖`. -/
theorem deriv_double_diff (i : Fin d) (y₁ y₂ v₁ v₂ : E) :
    ‖V.deriv i (y₁ + v₁) - V.deriv i y₁ -
        (V.deriv i (y₂ + v₂) - V.deriv i y₂)‖ ≤
      V.C2 * ‖v₁ - v₂‖ + V.C3 * (‖y₁ - y₂‖ + ‖v₁ - v₂‖) * ‖v₂‖ := by
  set φ : ℝ → (E →L[ℝ] E) :=
    fun r => V.deriv i (y₁ + r • v₁) - V.deriv i (y₂ + r • v₂) with hφ
  have hderiv : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt φ
        (V.deriv2 i (y₁ + r • v₁) v₁ - V.deriv2 i (y₂ + r • v₂) v₂)
        (Set.Icc 0 1) r := by
    intro r _
    have h₁ : HasDerivAt (fun r : ℝ => V.deriv i (y₁ + r • v₁))
        (V.deriv2 i (y₁ + r • v₁) v₁) r :=
      (V.hasFDeriv2 i (y₁ + r • v₁)).comp_hasDerivAt r
        (hasDerivAt_line y₁ v₁ r)
    have h₂ : HasDerivAt (fun r : ℝ => V.deriv i (y₂ + r • v₂))
        (V.deriv2 i (y₂ + r • v₂) v₂) r :=
      (V.hasFDeriv2 i (y₂ + r • v₂)).comp_hasDerivAt r
        (hasDerivAt_line y₂ v₂ r)
    exact (h₁.sub h₂).hasDerivWithinAt
  have hbound : ∀ r ∈ Set.Ico (0 : ℝ) 1,
      ‖V.deriv2 i (y₁ + r • v₁) v₁ - V.deriv2 i (y₂ + r • v₂) v₂‖ ≤
        V.C2 * ‖v₁ - v₂‖ + V.C3 * (‖y₁ - y₂‖ + ‖v₁ - v₂‖) * ‖v₂‖ := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := hr.1
    have hr1 : r ≤ 1 := hr.2.le
    have hsplit : V.deriv2 i (y₁ + r • v₁) v₁ -
        V.deriv2 i (y₂ + r • v₂) v₂ =
        V.deriv2 i (y₁ + r • v₁) (v₁ - v₂) +
          (V.deriv2 i (y₁ + r • v₁) - V.deriv2 i (y₂ + r • v₂)) v₂ := by
      rw [map_sub, sub_apply]
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · calc ‖V.deriv2 i (y₁ + r • v₁) (v₁ - v₂)‖
          ≤ ‖V.deriv2 i (y₁ + r • v₁)‖ * ‖v₁ - v₂‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ V.C2 * ‖v₁ - v₂‖ :=
            mul_le_mul_of_nonneg_right (V.bound_deriv2 i _)
              (norm_nonneg _)
    · calc ‖(V.deriv2 i (y₁ + r • v₁) - V.deriv2 i (y₂ + r • v₂)) v₂‖
          ≤ ‖V.deriv2 i (y₁ + r • v₁) - V.deriv2 i (y₂ + r • v₂)‖ *
              ‖v₂‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (V.C3 * ‖y₁ + r • v₁ - (y₂ + r • v₂)‖) * ‖v₂‖ :=
            mul_le_mul_of_nonneg_right (V.lipschitz_deriv2 i _ _)
              (norm_nonneg _)
        _ ≤ V.C3 * (‖y₁ - y₂‖ + ‖v₁ - v₂‖) * ‖v₂‖ := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (norm_nonneg _)
            have hpt : y₁ + r • v₁ - (y₂ + r • v₂) =
                (y₁ - y₂) + r • (v₁ - v₂) := by
              rw [smul_sub]
              abel
            rw [hpt]
            refine le_trans (norm_add_le _ _) (add_le_add le_rfl ?_)
            rw [norm_smul, Real.norm_of_nonneg hr0]
            exact mul_le_of_le_one_left (norm_nonneg _) hr1
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  have h0 : φ 0 = V.deriv i y₁ - V.deriv i y₂ := by
    rw [hφ]
    norm_num
  have h1 : φ 1 = V.deriv i (y₁ + v₁) - V.deriv i (y₂ + v₂) := by
    rw [hφ]
    norm_num
  rw [h0, h1] at key
  calc ‖V.deriv i (y₁ + v₁) - V.deriv i y₁ -
        (V.deriv i (y₂ + v₂) - V.deriv i y₂)‖
      = ‖V.deriv i (y₁ + v₁) - V.deriv i (y₂ + v₂) -
          (V.deriv i y₁ - V.deriv i y₂)‖ := by
        congr 1
        abel
    _ ≤ V.C2 * ‖v₁ - v₂‖ + V.C3 * (‖y₁ - y₂‖ + ‖v₁ - v₂‖) * ‖v₂‖ := key

/-- **Two-path Taylor difference**: the Taylor remainders of `f` along two
base points and increments differ by at most
`C₂‖Δ₁-Δ₂‖(‖Δ₁‖+‖Δ₂‖) + C₃(‖y₁-y₂‖+‖Δ₁-Δ₂‖)‖Δ₂‖²`. -/
theorem taylor_diff (i : Fin d) (y₁ y₂ Δ₁ Δ₂ : E) :
    ‖V.f i (y₁ + Δ₁) - V.f i y₁ - V.deriv i y₁ Δ₁ -
        (V.f i (y₂ + Δ₂) - V.f i y₂ - V.deriv i y₂ Δ₂)‖ ≤
      V.C2 * ‖Δ₁ - Δ₂‖ * (‖Δ₁‖ + ‖Δ₂‖) +
        V.C3 * (‖y₁ - y₂‖ + ‖Δ₁ - Δ₂‖) * ‖Δ₂‖ ^ 2 := by
  set g : ℝ → E := fun r => V.f i (y₁ + r • Δ₁) - V.f i (y₂ + r • Δ₂) -
    r • (V.deriv i y₁ Δ₁ - V.deriv i y₂ Δ₂) with hg
  have hderiv : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g
        (V.deriv i (y₁ + r • Δ₁) Δ₁ - V.deriv i (y₂ + r • Δ₂) Δ₂ -
          (V.deriv i y₁ Δ₁ - V.deriv i y₂ Δ₂))
        (Set.Icc 0 1) r := by
    intro r _
    have h₁ : HasDerivAt (fun r : ℝ => V.f i (y₁ + r • Δ₁))
        (V.deriv i (y₁ + r • Δ₁) Δ₁) r :=
      (V.hasFDeriv i (y₁ + r • Δ₁)).comp_hasDerivAt r
        (hasDerivAt_line y₁ Δ₁ r)
    have h₂ : HasDerivAt (fun r : ℝ => V.f i (y₂ + r • Δ₂))
        (V.deriv i (y₂ + r • Δ₂) Δ₂) r :=
      (V.hasFDeriv i (y₂ + r • Δ₂)).comp_hasDerivAt r
        (hasDerivAt_line y₂ Δ₂ r)
    have h₃ : HasDerivAt
        (fun r : ℝ => r • (V.deriv i y₁ Δ₁ - V.deriv i y₂ Δ₂))
        (V.deriv i y₁ Δ₁ - V.deriv i y₂ Δ₂) r := by
      simpa using (hasDerivAt_id r).smul_const
        (V.deriv i y₁ Δ₁ - V.deriv i y₂ Δ₂)
    exact ((h₁.sub h₂).sub h₃).hasDerivWithinAt
  have hbound : ∀ r ∈ Set.Ico (0 : ℝ) 1,
      ‖V.deriv i (y₁ + r • Δ₁) Δ₁ - V.deriv i (y₂ + r • Δ₂) Δ₂ -
          (V.deriv i y₁ Δ₁ - V.deriv i y₂ Δ₂)‖ ≤
        V.C2 * ‖Δ₁ - Δ₂‖ * (‖Δ₁‖ + ‖Δ₂‖) +
          V.C3 * (‖y₁ - y₂‖ + ‖Δ₁ - Δ₂‖) * ‖Δ₂‖ ^ 2 := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := hr.1
    have hr1 : r ≤ 1 := hr.2.le
    have hsm : ‖r • Δ₁ - r • Δ₂‖ ≤ ‖Δ₁ - Δ₂‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hr0]
      exact mul_le_of_le_one_left (norm_nonneg _) hr1
    have hsm₁ : ‖r • Δ₁‖ ≤ ‖Δ₁‖ := by
      rw [norm_smul, Real.norm_of_nonneg hr0]
      exact mul_le_of_le_one_left (norm_nonneg _) hr1
    have hsm₂ : ‖r • Δ₂‖ ≤ ‖Δ₂‖ := by
      rw [norm_smul, Real.norm_of_nonneg hr0]
      exact mul_le_of_le_one_left (norm_nonneg _) hr1
    have hsplit : V.deriv i (y₁ + r • Δ₁) Δ₁ -
        V.deriv i (y₂ + r • Δ₂) Δ₂ -
        (V.deriv i y₁ Δ₁ - V.deriv i y₂ Δ₂) =
        (V.deriv i (y₁ + r • Δ₁) - V.deriv i y₁) (Δ₁ - Δ₂) +
          (V.deriv i (y₁ + r • Δ₁) - V.deriv i y₁ -
            (V.deriv i (y₂ + r • Δ₂) - V.deriv i y₂)) Δ₂ := by
      simp only [sub_apply, map_sub]
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hA : ‖(V.deriv i (y₁ + r • Δ₁) - V.deriv i y₁) (Δ₁ - Δ₂)‖ ≤
        V.C2 * ‖Δ₁‖ * ‖Δ₁ - Δ₂‖ := by
      calc ‖(V.deriv i (y₁ + r • Δ₁) - V.deriv i y₁) (Δ₁ - Δ₂)‖
          ≤ ‖V.deriv i (y₁ + r • Δ₁) - V.deriv i y₁‖ * ‖Δ₁ - Δ₂‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (V.C2 * ‖y₁ + r • Δ₁ - y₁‖) * ‖Δ₁ - Δ₂‖ :=
            mul_le_mul_of_nonneg_right (V.lipschitz_deriv i _ _)
              (norm_nonneg _)
        _ ≤ (V.C2 * ‖Δ₁‖) * ‖Δ₁ - Δ₂‖ := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (norm_nonneg _)
            have hred : y₁ + r • Δ₁ - y₁ = r • Δ₁ := by abel
            rw [hred]
            exact hsm₁
    have hdd : ‖V.deriv i (y₁ + r • Δ₁) - V.deriv i y₁ -
        (V.deriv i (y₂ + r • Δ₂) - V.deriv i y₂)‖ ≤
        V.C2 * ‖Δ₁ - Δ₂‖ + V.C3 * (‖y₁ - y₂‖ + ‖Δ₁ - Δ₂‖) * ‖Δ₂‖ := by
      refine le_trans (V.deriv_double_diff i y₁ y₂ (r • Δ₁) (r • Δ₂)) ?_
      have hC2 : (V.C2 : ℝ) * ‖r • Δ₁ - r • Δ₂‖ ≤ V.C2 * ‖Δ₁ - Δ₂‖ :=
        mul_le_mul_of_nonneg_left hsm (by positivity)
      have hC3 : (V.C3 : ℝ) * (‖y₁ - y₂‖ + ‖r • Δ₁ - r • Δ₂‖) *
          ‖r • Δ₂‖ ≤ V.C3 * (‖y₁ - y₂‖ + ‖Δ₁ - Δ₂‖) * ‖Δ₂‖ := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
          hsm₂ (norm_nonneg _) (by positivity)
        linarith
      linarith
    have hB : ‖(V.deriv i (y₁ + r • Δ₁) - V.deriv i y₁ -
        (V.deriv i (y₂ + r • Δ₂) - V.deriv i y₂)) Δ₂‖ ≤
        (V.C2 * ‖Δ₁ - Δ₂‖ +
          V.C3 * (‖y₁ - y₂‖ + ‖Δ₁ - Δ₂‖) * ‖Δ₂‖) * ‖Δ₂‖ := by
      calc ‖(V.deriv i (y₁ + r • Δ₁) - V.deriv i y₁ -
            (V.deriv i (y₂ + r • Δ₂) - V.deriv i y₂)) Δ₂‖
          ≤ ‖V.deriv i (y₁ + r • Δ₁) - V.deriv i y₁ -
              (V.deriv i (y₂ + r • Δ₂) - V.deriv i y₂)‖ * ‖Δ₂‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hdd (norm_nonneg _)
    have hnn₁ : (0 : ℝ) ≤ ‖Δ₁‖ := norm_nonneg _
    have hnn₂ : (0 : ℝ) ≤ ‖Δ₂‖ := norm_nonneg _
    have hnnd : (0 : ℝ) ≤ ‖Δ₁ - Δ₂‖ := norm_nonneg _
    have hnny : (0 : ℝ) ≤ ‖y₁ - y₂‖ := norm_nonneg _
    have hC2nn : (0 : ℝ) ≤ V.C2 := V.C2.coe_nonneg
    have hC3nn : (0 : ℝ) ≤ V.C3 := V.C3.coe_nonneg
    nlinarith [hA, hB, mul_nonneg (mul_nonneg hC2nn hnnd) hnn₂,
      mul_nonneg (mul_nonneg hC3nn (add_nonneg hnny hnnd)) hnn₂]
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  have h0 : g 0 = V.f i y₁ - V.f i y₂ := by
    rw [hg]
    norm_num
  have h1 : g 1 = V.f i (y₁ + Δ₁) - V.f i (y₂ + Δ₂) -
      (V.deriv i y₁ Δ₁ - V.deriv i y₂ Δ₂) := by
    rw [hg]
    norm_num
  rw [h0, h1] at key
  calc ‖V.f i (y₁ + Δ₁) - V.f i y₁ - V.deriv i y₁ Δ₁ -
        (V.f i (y₂ + Δ₂) - V.f i y₂ - V.deriv i y₂ Δ₂)‖
      = ‖V.f i (y₁ + Δ₁) - V.f i (y₂ + Δ₂) -
          (V.deriv i y₁ Δ₁ - V.deriv i y₂ Δ₂) -
          (V.f i y₁ - V.f i y₂)‖ := by
        congr 1
        abel
    _ ≤ _ := key

/-! ### Extended-norm endpoint forms -/

theorem enorm_f_lipschitz (i : Fin d) (a b : E) :
    ‖V.f i a - V.f i b‖ₑ ≤ (V.C1 : ℝ≥0∞) * ‖a - b‖ₑ := by
  calc ‖V.f i a - V.f i b‖ₑ
      = ENNReal.ofReal ‖V.f i a - V.f i b‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (V.C1 * ‖a - b‖) :=
        ENNReal.ofReal_le_ofReal (V.f_lipschitz i b a)
    _ = (V.C1 : ℝ≥0∞) * ‖a - b‖ₑ := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_coe_nnreal, ofReal_norm]

/-- The second-order double difference in extended norms, endpoint
form. -/
theorem enorm_deriv_double_diff (i : Fin d) (a b c e : E) :
    ‖V.deriv i a - V.deriv i b - (V.deriv i c - V.deriv i e)‖ₑ ≤
      (V.C2 : ℝ≥0∞) * ‖a - b - (c - e)‖ₑ +
        (V.C3 : ℝ≥0∞) * (‖b - e‖ₑ + ‖a - b - (c - e)‖ₑ) * ‖c - e‖ₑ := by
  have hnorm := V.deriv_double_diff i b e (a - b) (c - e)
  rw [add_sub_cancel, add_sub_cancel] at hnorm
  calc ‖V.deriv i a - V.deriv i b - (V.deriv i c - V.deriv i e)‖ₑ
      = ENNReal.ofReal
          ‖V.deriv i a - V.deriv i b - (V.deriv i c - V.deriv i e)‖ :=
        (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (V.C2 * ‖a - b - (c - e)‖ +
          V.C3 * (‖b - e‖ + ‖a - b - (c - e)‖) * ‖c - e‖) :=
        ENNReal.ofReal_le_ofReal hnorm
    _ ≤ ENNReal.ofReal (V.C2 * ‖a - b - (c - e)‖) +
          ENNReal.ofReal
            (V.C3 * (‖b - e‖ + ‖a - b - (c - e)‖) * ‖c - e‖) :=
        ENNReal.ofReal_add_le
    _ = (V.C2 : ℝ≥0∞) * ‖a - b - (c - e)‖ₑ +
          (V.C3 : ℝ≥0∞) * (‖b - e‖ₑ + ‖a - b - (c - e)‖ₑ) *
            ‖c - e‖ₑ := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_coe_nnreal, ofReal_norm,
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_coe_nnreal, ofReal_norm,
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
          ofReal_norm, ofReal_norm]

/-- The two-path Taylor difference in extended norms, endpoint form. -/
theorem enorm_taylor_diff (i : Fin d) (a b c e : E) :
    ‖V.f i a - V.f i b - V.deriv i b (a - b) -
        (V.f i c - V.f i e - V.deriv i e (c - e))‖ₑ ≤
      (V.C2 : ℝ≥0∞) * ‖a - b - (c - e)‖ₑ * (‖a - b‖ₑ + ‖c - e‖ₑ) +
        (V.C3 : ℝ≥0∞) * (‖b - e‖ₑ + ‖a - b - (c - e)‖ₑ) *
          ‖c - e‖ₑ ^ (2 : ℕ) := by
  have hnorm := V.taylor_diff i b e (a - b) (c - e)
  rw [add_sub_cancel, add_sub_cancel] at hnorm
  calc ‖V.f i a - V.f i b - V.deriv i b (a - b) -
        (V.f i c - V.f i e - V.deriv i e (c - e))‖ₑ
      = ENNReal.ofReal ‖V.f i a - V.f i b - V.deriv i b (a - b) -
          (V.f i c - V.f i e - V.deriv i e (c - e))‖ :=
        (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal
          (V.C2 * ‖a - b - (c - e)‖ * (‖a - b‖ + ‖c - e‖) +
            V.C3 * (‖b - e‖ + ‖a - b - (c - e)‖) * ‖c - e‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hnorm
    _ ≤ ENNReal.ofReal
          (V.C2 * ‖a - b - (c - e)‖ * (‖a - b‖ + ‖c - e‖)) +
          ENNReal.ofReal
            (V.C3 * (‖b - e‖ + ‖a - b - (c - e)‖) * ‖c - e‖ ^ 2) :=
        ENNReal.ofReal_add_le
    _ = (V.C2 : ℝ≥0∞) * ‖a - b - (c - e)‖ₑ * (‖a - b‖ₑ + ‖c - e‖ₑ) +
          (V.C3 : ℝ≥0∞) * (‖b - e‖ₑ + ‖a - b - (c - e)‖ₑ) *
            ‖c - e‖ₑ ^ (2 : ℕ) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_coe_nnreal, ofReal_norm,
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
          ofReal_norm, ofReal_norm,
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
          ofReal_norm, ofReal_norm,
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-! ### Two-path stability of composition (Friz–Hairer Lemma 7.4) -/

open RDEVectorField in
/-- **Two-path stability of composition**: distance certificates between
`f(Y¹)` and `f(Y²)` linear in the distance certificates of `Y¹, Y²`. -/
noncomputable def compControlledDist (hX : IsLevel2RoughPath X ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    {Z₁ Z₂ : ControlledPath X ω α E} (D : ControlledDist Z₁ Z₂) :
    ControlledDist (V.toRDEVectorField.compControlled hX hω1 Z₁)
      (V.toRDEVectorField.compControlled hX hω1 Z₂) where
  D0 := V.C1 * D.D0
  Db := V.C1 * D.Db + V.C2 * D.D0 * Z₂.Cb
  Dd := V.C1 * D.Dd + V.C2 * D.D0 * Z₂.Cd +
    V.C2 * (d * Z₁.Cb + Z₁.Cy) * D.Db +
    (V.C2 * (d * D.Db + D.Dy) +
      V.C3 * (D.D0 + (d * D.Db + D.Dy)) * (d * Z₂.Cb + Z₂.Cy)) * Z₂.Cb
  Dy := V.C2 * (d * D.Db + D.Dy) *
      ((d * Z₁.Cb + Z₁.Cy) + (d * Z₂.Cb + Z₂.Cy)) +
    V.C3 * (D.D0 + (d * D.Db + D.Dy)) * (d * Z₂.Cb + Z₂.Cy) ^ 2 +
    V.C1 * D.Dy + V.C2 * D.D0 * Z₂.Cy
  bound_Y := by
    intro s
    refine pi_enorm_le fun i => ?_
    simp only [Pi.sub_apply, compControlled_Y]
    calc ‖V.f i (Z₁.Y s) - V.f i (Z₂.Y s)‖ₑ
        ≤ (V.C1 : ℝ≥0∞) * ‖Z₁.Y s - Z₂.Y s‖ₑ := V.enorm_f_lipschitz i _ _
      _ ≤ (V.C1 : ℝ≥0∞) * D.D0 := mul_le_mul' le_rfl (D.bound_Y s)
      _ = ((V.C1 * D.D0 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
  bound_Yd := by
    intro s j
    refine pi_enorm_le fun i => ?_
    simp only [Pi.sub_apply, compControlled_Yd]
    have hsplit : V.deriv i (Z₁.Y s) (Z₁.Yd s j) -
        V.deriv i (Z₂.Y s) (Z₂.Yd s j) =
        V.deriv i (Z₁.Y s) (Z₁.Yd s j - Z₂.Yd s j) +
          (V.deriv i (Z₁.Y s) - V.deriv i (Z₂.Y s)) (Z₂.Yd s j) := by
      rw [map_sub, sub_apply]
      abel
    rw [hsplit]
    refine le_trans (enorm_add_le _ _) ?_
    have h1 : ‖V.deriv i (Z₁.Y s) (Z₁.Yd s j - Z₂.Yd s j)‖ₑ ≤
        (V.C1 : ℝ≥0∞) * D.Db :=
      le_trans (enorm_clm_apply_le _ _)
        (mul_le_mul' (enorm_le_coe (V.bound_deriv i _)) (D.bound_Yd s j))
    have h2 : ‖(V.deriv i (Z₁.Y s) - V.deriv i (Z₂.Y s)) (Z₂.Yd s j)‖ₑ ≤
        (V.C2 : ℝ≥0∞) * D.D0 * Z₂.Cb := by
      refine le_trans (enorm_clm_apply_le _ _) ?_
      refine mul_le_mul' (le_trans
        (RDEVectorField.enorm_lipschitz V.toRDEVectorField i _ _) ?_)
        (Z₂.bound_Yd s j)
      exact mul_le_mul' le_rfl (D.bound_Y s)
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    push_cast
    ring
  holder_Yd := by
    intro s t hst j
    have hα := hX.alpha_pos
    have hω_le_one : ω s t ^ α ≤ 1 :=
      le_trans (ENNReal.rpow_le_rpow (hω1 hst) hα.le)
        (le_of_eq (ENNReal.one_rpow α))
    have hincD := D.increment_sub_le hX hω1 hst
    have hinc₁ : ‖Z₁.Y t - Z₁.Y s‖ₑ ≤
        ((d : ℝ≥0∞) * Z₁.Cb + Z₁.Cy) * ω s t ^ α :=
      increment_le hX hω1 Z₁ hst
    have hinc₂ : ‖Z₂.Y t - Z₂.Y s‖ₑ ≤
        ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy) * ω s t ^ α :=
      increment_le hX hω1 Z₂ hst
    refine pi_enorm_le fun i => ?_
    simp only [Pi.sub_apply, compControlled_Yd]
    have hsplit : V.deriv i (Z₁.Y t) (Z₁.Yd t j) -
        V.deriv i (Z₂.Y t) (Z₂.Yd t j) -
        (V.deriv i (Z₁.Y s) (Z₁.Yd s j) -
          V.deriv i (Z₂.Y s) (Z₂.Yd s j)) =
        V.deriv i (Z₁.Y t)
          (Z₁.Yd t j - Z₂.Yd t j - (Z₁.Yd s j - Z₂.Yd s j)) +
        (V.deriv i (Z₁.Y t) - V.deriv i (Z₂.Y t))
          (Z₂.Yd t j - Z₂.Yd s j) +
        (V.deriv i (Z₁.Y t) - V.deriv i (Z₁.Y s))
          (Z₁.Yd s j - Z₂.Yd s j) +
        (V.deriv i (Z₁.Y t) - V.deriv i (Z₁.Y s) -
          (V.deriv i (Z₂.Y t) - V.deriv i (Z₂.Y s))) (Z₂.Yd s j) := by
      simp only [map_sub, sub_apply]
      abel
    rw [hsplit]
    have hT1a : ‖V.deriv i (Z₁.Y t)
        (Z₁.Yd t j - Z₂.Yd t j - (Z₁.Yd s j - Z₂.Yd s j))‖ₑ ≤
        (V.C1 : ℝ≥0∞) * D.Dd * ω s t ^ α := by
      refine le_trans (enorm_clm_apply_le _ _) ?_
      refine le_trans (mul_le_mul'
        (enorm_le_coe (V.bound_deriv i _)) (D.holder_Yd hst j))
        (le_of_eq ?_)
      ring
    have hT1b : ‖(V.deriv i (Z₁.Y t) - V.deriv i (Z₂.Y t))
        (Z₂.Yd t j - Z₂.Yd s j)‖ₑ ≤
        (V.C2 : ℝ≥0∞) * D.D0 * Z₂.Cd * ω s t ^ α := by
      refine le_trans (enorm_clm_apply_le _ _) ?_
      refine le_trans (mul_le_mul' (le_trans
        (RDEVectorField.enorm_lipschitz V.toRDEVectorField i _ _)
        (mul_le_mul' le_rfl (D.bound_Y t))) (Z₂.holder_Yd hst j))
        (le_of_eq ?_)
      ring
    have hT2a : ‖(V.deriv i (Z₁.Y t) - V.deriv i (Z₁.Y s))
        (Z₁.Yd s j - Z₂.Yd s j)‖ₑ ≤
        (V.C2 : ℝ≥0∞) * ((d : ℝ≥0∞) * Z₁.Cb + Z₁.Cy) * D.Db *
          ω s t ^ α := by
      refine le_trans (enorm_clm_apply_le _ _) ?_
      refine le_trans (mul_le_mul' (le_trans
        (RDEVectorField.enorm_lipschitz V.toRDEVectorField i _ _)
        (mul_le_mul' le_rfl hinc₁)) (D.bound_Yd s j)) (le_of_eq ?_)
      ring
    have hT2b : ‖(V.deriv i (Z₁.Y t) - V.deriv i (Z₁.Y s) -
        (V.deriv i (Z₂.Y t) - V.deriv i (Z₂.Y s))) (Z₂.Yd s j)‖ₑ ≤
        ((V.C2 : ℝ≥0∞) * ((d : ℝ≥0∞) * D.Db + D.Dy) +
          (V.C3 : ℝ≥0∞) * ((D.D0 : ℝ≥0∞) + ((d : ℝ≥0∞) * D.Db + D.Dy)) *
            ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy)) * Z₂.Cb * ω s t ^ α := by
      refine le_trans (enorm_clm_apply_le _ _) ?_
      have hdd := V.enorm_deriv_double_diff i (Z₁.Y t) (Z₁.Y s)
        (Z₂.Y t) (Z₂.Y s)
      have hbound : ‖V.deriv i (Z₁.Y t) - V.deriv i (Z₁.Y s) -
          (V.deriv i (Z₂.Y t) - V.deriv i (Z₂.Y s))‖ₑ ≤
          ((V.C2 : ℝ≥0∞) * ((d : ℝ≥0∞) * D.Db + D.Dy) +
            (V.C3 : ℝ≥0∞) *
              ((D.D0 : ℝ≥0∞) + ((d : ℝ≥0∞) * D.Db + D.Dy)) *
              ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy)) * ω s t ^ α := by
        refine le_trans hdd ?_
        have h1 : (V.C2 : ℝ≥0∞) *
            ‖Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s)‖ₑ ≤
            (V.C2 : ℝ≥0∞) * (((d : ℝ≥0∞) * D.Db + D.Dy) * ω s t ^ α) :=
          mul_le_mul' le_rfl hincD
        have h2 : (V.C3 : ℝ≥0∞) *
            (‖Z₁.Y s - Z₂.Y s‖ₑ +
              ‖Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s)‖ₑ) *
            ‖Z₂.Y t - Z₂.Y s‖ₑ ≤
            (V.C3 : ℝ≥0∞) *
              ((D.D0 : ℝ≥0∞) + ((d : ℝ≥0∞) * D.Db + D.Dy)) *
              (((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy) * ω s t ^ α) := by
          refine mul_le_mul' (mul_le_mul' le_rfl ?_) hinc₂
          refine add_le_add (D.bound_Y s) ?_
          refine le_trans hincD ?_
          exact le_trans (mul_le_mul' le_rfl hω_le_one) (le_of_eq
            (mul_one _))
        refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
        ring
      refine le_trans (mul_le_mul' hbound (Z₂.bound_Yd s j))
        (le_of_eq ?_)
      ring
    refine le_trans (enorm_add_le _ _) ?_
    refine le_trans (add_le_add (le_trans (enorm_add_le _ _)
      (add_le_add (le_trans (enorm_add_le _ _)
        (add_le_add hT1a hT1b)) hT2a)) hT2b) (le_of_eq ?_)
    push_cast
    ring
  remainder := by
    intro s t hst
    have hα := hX.alpha_pos
    have hω_le_one : ω s t ^ α ≤ 1 :=
      le_trans (ENNReal.rpow_le_rpow (hω1 hst) hα.le)
        (le_of_eq (ENNReal.one_rpow α))
    have hincD := D.increment_sub_le hX hω1 hst
    have hinc₁ : ‖Z₁.Y t - Z₁.Y s‖ₑ ≤
        ((d : ℝ≥0∞) * Z₁.Cb + Z₁.Cy) * ω s t ^ α :=
      increment_le hX hω1 Z₁ hst
    have hinc₂ : ‖Z₂.Y t - Z₂.Y s‖ₑ ≤
        ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy) * ω s t ^ α :=
      increment_le hX hω1 Z₂ hst
    refine pi_enorm_le fun i => ?_
    have happly₁ : (∑ j, X.coeff s t [j] •
        (V.toRDEVectorField.compControlled hX hω1 Z₁).Yd s j) i =
        V.deriv i (Z₁.Y s) (∑ j, X.coeff s t [j] • Z₁.Yd s j) := by
      rw [Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, map_smul, compControlled_Yd]
    have happly₂ : (∑ j, X.coeff s t [j] •
        (V.toRDEVectorField.compControlled hX hω1 Z₂).Yd s j) i =
        V.deriv i (Z₂.Y s) (∑ j, X.coeff s t [j] • Z₂.Yd s j) := by
      rw [Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, map_smul, compControlled_Yd]
    have hcoordsum : (∑ j, X.coeff s t [j] •
        ((V.toRDEVectorField.compControlled hX hω1 Z₁).Yd s j -
          (V.toRDEVectorField.compControlled hX hω1 Z₂).Yd s j)) i =
        V.deriv i (Z₁.Y s) (∑ j, X.coeff s t [j] • Z₁.Yd s j) -
          V.deriv i (Z₂.Y s) (∑ j, X.coeff s t [j] • Z₂.Yd s j) := by
      have hsum : (∑ j, X.coeff s t [j] •
          ((V.toRDEVectorField.compControlled hX hω1 Z₁).Yd s j -
            (V.toRDEVectorField.compControlled hX hω1 Z₂).Yd s j)) =
          (∑ j, X.coeff s t [j] •
            (V.toRDEVectorField.compControlled hX hω1 Z₁).Yd s j) -
          ∑ j, X.coeff s t [j] •
            (V.toRDEVectorField.compControlled hX hω1 Z₂).Yd s j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => smul_sub _ _ _
      rw [hsum, Pi.sub_apply, happly₁, happly₂]
    simp only [Pi.sub_apply, compControlled_Y]
    rw [hcoordsum]
    have hsplit : V.f i (Z₁.Y t) - V.f i (Z₂.Y t) -
        (V.f i (Z₁.Y s) - V.f i (Z₂.Y s)) -
        (V.deriv i (Z₁.Y s) (∑ j, X.coeff s t [j] • Z₁.Yd s j) -
          V.deriv i (Z₂.Y s) (∑ j, X.coeff s t [j] • Z₂.Yd s j)) =
        (V.f i (Z₁.Y t) - V.f i (Z₁.Y s) -
          V.deriv i (Z₁.Y s) (Z₁.Y t - Z₁.Y s) -
          (V.f i (Z₂.Y t) - V.f i (Z₂.Y s) -
            V.deriv i (Z₂.Y s) (Z₂.Y t - Z₂.Y s))) +
        (V.deriv i (Z₁.Y s)
            (Z₁.Y t - Z₁.Y s - ∑ j, X.coeff s t [j] • Z₁.Yd s j) -
          V.deriv i (Z₂.Y s)
            (Z₂.Y t - Z₂.Y s - ∑ j, X.coeff s t [j] • Z₂.Yd s j)) := by
      simp only [map_sub]
      abel
    rw [hsplit]
    refine le_trans (enorm_add_le _ _) ?_
    have hA : ‖V.f i (Z₁.Y t) - V.f i (Z₁.Y s) -
        V.deriv i (Z₁.Y s) (Z₁.Y t - Z₁.Y s) -
        (V.f i (Z₂.Y t) - V.f i (Z₂.Y s) -
          V.deriv i (Z₂.Y s) (Z₂.Y t - Z₂.Y s))‖ₑ ≤
        ((V.C2 : ℝ≥0∞) * ((d : ℝ≥0∞) * D.Db + D.Dy) *
            (((d : ℝ≥0∞) * Z₁.Cb + Z₁.Cy) +
              ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy)) +
          (V.C3 : ℝ≥0∞) *
            ((D.D0 : ℝ≥0∞) + ((d : ℝ≥0∞) * D.Db + D.Dy)) *
            ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy) ^ (2 : ℕ)) *
          ω s t ^ (2 * α) := by
      refine le_trans (V.enorm_taylor_diff i (Z₁.Y t) (Z₁.Y s)
        (Z₂.Y t) (Z₂.Y s)) ?_
      have h1 : (V.C2 : ℝ≥0∞) *
          ‖Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s)‖ₑ *
          (‖Z₁.Y t - Z₁.Y s‖ₑ + ‖Z₂.Y t - Z₂.Y s‖ₑ) ≤
          (V.C2 : ℝ≥0∞) * (((d : ℝ≥0∞) * D.Db + D.Dy) * ω s t ^ α) *
            ((((d : ℝ≥0∞) * Z₁.Cb + Z₁.Cy) +
              ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy)) * ω s t ^ α) := by
        refine mul_le_mul' (mul_le_mul' le_rfl hincD) ?_
        refine le_trans (add_le_add hinc₁ hinc₂) (le_of_eq ?_)
        ring
      have h2 : (V.C3 : ℝ≥0∞) *
          (‖Z₁.Y s - Z₂.Y s‖ₑ +
            ‖Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s)‖ₑ) *
          ‖Z₂.Y t - Z₂.Y s‖ₑ ^ (2 : ℕ) ≤
          (V.C3 : ℝ≥0∞) *
            ((D.D0 : ℝ≥0∞) + ((d : ℝ≥0∞) * D.Db + D.Dy)) *
            ((((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy)) * ω s t ^ α) ^ (2 : ℕ) := by
        refine mul_le_mul' (mul_le_mul' le_rfl ?_)
          (pow_le_pow_left' hinc₂ 2)
        refine add_le_add (D.bound_Y s) ?_
        refine le_trans hincD ?_
        exact le_trans (mul_le_mul' le_rfl hω_le_one)
          (le_of_eq (mul_one _))
      refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
      rw [rpow_two_mul_eq hα.le]
      ring
    have hR : ‖Z₁.Y t - Z₁.Y s - (∑ j, X.coeff s t [j] • Z₁.Yd s j) -
        (Z₂.Y t - Z₂.Y s - ∑ j, X.coeff s t [j] • Z₂.Yd s j)‖ₑ ≤
        (D.Dy : ℝ≥0∞) * ω s t ^ (2 * α) := by
      have hre : Z₁.Y t - Z₁.Y s - (∑ j, X.coeff s t [j] • Z₁.Yd s j) -
          (Z₂.Y t - Z₂.Y s - ∑ j, X.coeff s t [j] • Z₂.Yd s j) =
          Z₁.Y t - Z₂.Y t - (Z₁.Y s - Z₂.Y s) -
            ∑ j, X.coeff s t [j] • (Z₁.Yd s j - Z₂.Yd s j) := by
        have hsum : ∑ j, X.coeff s t [j] • (Z₁.Yd s j - Z₂.Yd s j) =
            (∑ j, X.coeff s t [j] • Z₁.Yd s j) -
              ∑ j, X.coeff s t [j] • Z₂.Yd s j := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => smul_sub _ _ _
        rw [hsum]
        abel
      rw [hre]
      exact D.remainder hst
    have hB : ‖V.deriv i (Z₁.Y s)
        (Z₁.Y t - Z₁.Y s - ∑ j, X.coeff s t [j] • Z₁.Yd s j) -
        V.deriv i (Z₂.Y s)
          (Z₂.Y t - Z₂.Y s - ∑ j, X.coeff s t [j] • Z₂.Yd s j)‖ₑ ≤
        ((V.C1 : ℝ≥0∞) * D.Dy + (V.C2 : ℝ≥0∞) * D.D0 * Z₂.Cy) *
          ω s t ^ (2 * α) := by
      have hbsplit : V.deriv i (Z₁.Y s)
          (Z₁.Y t - Z₁.Y s - ∑ j, X.coeff s t [j] • Z₁.Yd s j) -
          V.deriv i (Z₂.Y s)
            (Z₂.Y t - Z₂.Y s - ∑ j, X.coeff s t [j] • Z₂.Yd s j) =
          V.deriv i (Z₁.Y s)
            (Z₁.Y t - Z₁.Y s - (∑ j, X.coeff s t [j] • Z₁.Yd s j) -
              (Z₂.Y t - Z₂.Y s - ∑ j, X.coeff s t [j] • Z₂.Yd s j)) +
          (V.deriv i (Z₁.Y s) - V.deriv i (Z₂.Y s))
            (Z₂.Y t - Z₂.Y s - ∑ j, X.coeff s t [j] • Z₂.Yd s j) := by
        simp only [map_sub, sub_apply]
        abel
      rw [hbsplit]
      refine le_trans (enorm_add_le _ _) ?_
      have hb1 : ‖V.deriv i (Z₁.Y s)
          (Z₁.Y t - Z₁.Y s - (∑ j, X.coeff s t [j] • Z₁.Yd s j) -
            (Z₂.Y t - Z₂.Y s - ∑ j, X.coeff s t [j] • Z₂.Yd s j))‖ₑ ≤
          (V.C1 : ℝ≥0∞) * (D.Dy * ω s t ^ (2 * α)) :=
        le_trans (enorm_clm_apply_le _ _)
          (mul_le_mul' (enorm_le_coe (V.bound_deriv i _)) hR)
      have hb2 : ‖(V.deriv i (Z₁.Y s) - V.deriv i (Z₂.Y s))
          (Z₂.Y t - Z₂.Y s - ∑ j, X.coeff s t [j] • Z₂.Yd s j)‖ₑ ≤
          (V.C2 : ℝ≥0∞) * D.D0 * (Z₂.Cy * ω s t ^ (2 * α)) := by
        refine le_trans (enorm_clm_apply_le _ _) ?_
        refine le_trans (mul_le_mul' (le_trans
          (RDEVectorField.enorm_lipschitz V.toRDEVectorField i _ _)
          (mul_le_mul' le_rfl (D.bound_Y s))) (Z₂.remainder hst))
          (le_of_eq ?_)
        ring
      refine le_trans (add_le_add hb1 hb2) (le_of_eq ?_)
      ring
    refine le_trans (add_le_add hA hB) (le_of_eq ?_)
    push_cast
    ring

end RDEVectorField3

end RoughPaths
