/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.RDE.Stability
import RoughPaths.RDE.Solution

/-!
# The Picard map for rough differential equations

The Picard map of `dY = f(Y)·dX` with initial condition `y₀`: a
controlled path `Z` is sent to the path based at `y₀` with increments the
rough integral of the composed integrand `f(Z)`, and Gubinelli derivative
`f(Z.Y)`. On a control window normalised by `ω ≤ 1` and
`ω^α ≤ δα`, the map preserves an explicit certificate box (for suitable
box constants), the first step towards the fixed-point construction of
solutions.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ} {E W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {X : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ} {α : ℝ}

/-- The `ℝ≥0`-valued germ constant of a controlled path. -/
def ControlledPath.roughConstN (Z : ControlledPath X ω α W) : ℝ≥0 :=
  d * Z.Cy + d ^ 2 * Z.Cd

theorem roughConst_eq_coe (Z : ControlledPath X ω α (Fin d → E)) :
    roughConst Z = ((Z.roughConstN : ℝ≥0) : ℝ≥0∞) := by
  rw [roughConst, ControlledPath.roughConstN]
  push_cast
  ring

/-- Distance form of an extended-norm bound. -/
theorem dist_le_coe_of_enorm_le {F : Type*} [NormedAddCommGroup F]
    {x y : F} {c : ℝ≥0} (h : ‖y - x‖ₑ ≤ (c : ℝ≥0∞)) :
    dist x y ≤ (c : ℝ) := by
  rw [dist_comm, dist_eq_norm]
  have h2 := ENNReal.toReal_mono ENNReal.coe_ne_top h
  rwa [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.coe_toReal] at h2

/-- Geometric extraction: `2ⁿ·(w·a) ≤ ρ` gives `a ≤ (ρ/w)·(1/2)ⁿ`. -/
theorem coe_le_geom_of_pow_mul_le {a ρ w : ℝ≥0} {n : ℕ} (hw : 0 < w)
    (h : 2 ^ n * (w * a) ≤ ρ) :
    (a : ℝ) ≤ (ρ : ℝ) / (w : ℝ) * (1 / 2) ^ n := by
  have hcast : (2 : ℝ) ^ n * ((w : ℝ) * a) ≤ (ρ : ℝ) := by
    exact_mod_cast h
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw
  calc (a : ℝ) ≤ (ρ : ℝ) / ((w : ℝ) * 2 ^ n) :=
        (le_div_iff₀ (by positivity)).2 (le_trans (le_of_eq (by ring))
          hcast)
    _ = (ρ : ℝ) / (w : ℝ) * (1 / 2) ^ n := by
        rw [div_pow, one_pow]
        ring

/-! ### Basing an additive increment family at an initial point -/

/-- The path based at `y₀` with increments `I`. -/
noncomputable def basedPath (I : ℝ → ℝ → E) (y₀ : E) (t : ℝ) : E :=
  if 0 ≤ t then y₀ + I 0 t else y₀ - I t 0

omit [NormedSpace ℝ E] in
theorem basedPath_increment {I : ℝ → ℝ → E}
    (hadd : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I s u + I u t = I s t)
    (y₀ : E) ⦃s t : ℝ⦄ (hst : s ≤ t) :
    basedPath I y₀ t - basedPath I y₀ s = I s t := by
  rw [basedPath, basedPath]
  by_cases hs : 0 ≤ s
  · rw [if_pos (le_trans hs hst), if_pos hs, ← hadd hs hst]
    abel
  · by_cases ht : 0 ≤ t
    · rw [if_pos ht, if_neg hs, ← hadd (not_le.1 hs).le ht]
      abel
    · rw [if_neg ht, if_neg hs, ← hadd hst (not_le.1 ht).le]
      abel

omit [NormedSpace ℝ E] in
theorem basedPath_zero {I : ℝ → ℝ → E}
    (hadd : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I s u + I u t = I s t)
    (y₀ : E) :
    basedPath I y₀ 0 = y₀ := by
  have h0 : I 0 0 = 0 := by
    have h := hadd (le_refl (0 : ℝ)) (le_refl 0)
    exact add_left_cancel (h.trans (add_zero _).symm)
  rw [basedPath, if_pos le_rfl, h0, add_zero]

/-! ### The Picard map -/

section Picard

variable [CompleteSpace E]
variable (V : RDEVectorField3 d E) (hX : IsLevel2RoughPath X ω α)
variable (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
variable (hfine : Sewing.HasFinePartitions ω)
variable (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
variable {δα : ℝ≥0}
variable (y₀ : E)

/-- The chosen rough integral of the composed integrand. -/
noncomputable def picardIntegral (Z : ControlledPath X ω α E) :
    ℝ → ℝ → E :=
  Classical.choose (exists_roughIntegral hX
    (V.toRDEVectorField.compControlled hX hω1 Z) hfine hωne)

theorem picardIntegral_additive (Z : ControlledPath X ω α E) :
    ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t →
      picardIntegral V hX hω1 hfine hωne Z s u +
        picardIntegral V hX hω1 hfine hωne Z u t =
        picardIntegral V hX hω1 hfine hωne Z s t :=
  (Classical.choose_spec (exists_roughIntegral hX
    (V.toRDEVectorField.compControlled hX hω1 Z) hfine hωne)).1

theorem picardIntegral_germ (Z : ControlledPath X ω α E) :
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖picardIntegral V hX hω1 hfine hωne Z s t -
          gubinelliGerm (V.toRDEVectorField.compControlled hX hω1 Z)
            s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst (V.toRDEVectorField.compControlled hX hω1 Z) *
            ω s t ^ (3 * α)) :=
  (Classical.choose_spec (exists_roughIntegral hX
    (V.toRDEVectorField.compControlled hX hω1 Z) hfine hωne)).2.1

/-- **The Picard map**: base point `y₀`, increments the rough integral of
`f(Z)`, Gubinelli derivative `f(Z.Y)`, with explicit certificates. -/
noncomputable def picardMap (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω s t ^ α ≤ (δα : ℝ≥0∞))
    (Z : ControlledPath X ω α E) : ControlledPath X ω α E where
  Y := basedPath (picardIntegral V hX hω1 hfine hωne Z) y₀
  Yd t i := V.f i (Z.Y t)
  Cb := V.C0
  Cd := V.C1 * (d * Z.Cb + Z.Cy)
  Cy := (Sewing.sewingConst (3 * α)).toNNReal *
      (d * (V.C1 * Z.Cy + V.C2 * (d * Z.Cb + Z.Cy) ^ 2) +
        d ^ 2 * (V.C1 * Z.Cd + V.C2 * Z.Cb * (d * Z.Cb + Z.Cy))) * δα +
    d ^ 2 * (V.C1 * Z.Cb)
  bound_Yd s i := RDEVectorField.enorm_le_coe (V.bound_f i (Z.Y s))
  holder_Yd := by
    intro s t hst i
    refine le_trans (V.enorm_f_lipschitz i (Z.Y t) (Z.Y s)) ?_
    refine le_trans (mul_le_mul' le_rfl
      (RDEVectorField.increment_le hX hω1 Z hst)) (le_of_eq ?_)
    push_cast
    ring
  remainder := by
    intro s t hst
    have hα := hX.alpha_pos
    have h3α := hX.one_lt_three_alpha
    rw [show basedPath (picardIntegral V hX hω1 hfine hωne Z) y₀ t -
        basedPath (picardIntegral V hX hω1 hfine hωne Z) y₀ s =
        picardIntegral V hX hω1 hfine hωne Z s t from
      basedPath_increment (picardIntegral_additive V hX hω1 hfine hωne Z)
        y₀ hst]
    refine le_trans (roughIntegral_sub_linear hX
      (V.toRDEVectorField.compControlled hX hω1 Z)
      (picardIntegral_germ V hX hω1 hfine hωne Z) hst) ?_
    -- fold `ω^{3α} ≤ δα·ω^{2α}` and collect constants
    have hsplit3 : ω s t ^ (3 * α) ≤ (δα : ℝ≥0∞) * ω s t ^ (2 * α) :=
      rpow_three_mul_le_mul hα.le (hδα hst)
    have hK : Sewing.sewingConst (3 * α) =
        (((Sewing.sewingConst (3 * α)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
      (ENNReal.coe_toNNReal (Sewing.sewingConst_lt_top h3α).ne).symm
    have hrc : roughConst (V.toRDEVectorField.compControlled hX hω1 Z) =
        (((d * (V.C1 * Z.Cy + V.C2 * (d * Z.Cb + Z.Cy) ^ 2) +
          d ^ 2 * (V.C1 * Z.Cd + V.C2 * Z.Cb * (d * Z.Cb + Z.Cy)) :
            ℝ≥0)) : ℝ≥0∞) := by
      rw [roughConst_eq_coe]
      congr 1
    have h1 : Sewing.sewingConst (3 * α) *
        (roughConst (V.toRDEVectorField.compControlled hX hω1 Z) *
          ω s t ^ (3 * α)) ≤
        (((Sewing.sewingConst (3 * α)).toNNReal *
          (d * (V.C1 * Z.Cy + V.C2 * (d * Z.Cb + Z.Cy) ^ 2) +
            d ^ 2 * (V.C1 * Z.Cd + V.C2 * Z.Cb * (d * Z.Cb + Z.Cy))) *
          δα : ℝ≥0) : ℝ≥0∞) * ω s t ^ (2 * α) := by
      conv_lhs => rw [hK, hrc]
      refine le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hsplit3))
        (le_of_eq ?_)
      push_cast
      ring
    have h2 : ((d : ℝ≥0∞)) ^ 2 *
        (V.toRDEVectorField.compControlled hX hω1 Z).Cb *
        ω s t ^ (2 * α) =
        ((d ^ 2 * (V.C1 * Z.Cb) : ℝ≥0) : ℝ≥0∞) * ω s t ^ (2 * α) := by
      have hCb : (V.toRDEVectorField.compControlled hX hω1 Z).Cb =
          V.C1 * Z.Cb := rfl
      rw [hCb]
      push_cast
      ring
    refine le_trans (add_le_add h1 (le_of_eq h2)) (le_of_eq ?_)
    push_cast
    ring

@[simp]
theorem picardMap_Yd (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω s t ^ α ≤ (δα : ℝ≥0∞))
    (Z : ControlledPath X ω α E) (t : ℝ) (i : Fin d) :
    (picardMap V hX hω1 hfine hωne y₀ hδα Z).Yd t i = V.f i (Z.Y t) :=
  rfl

theorem picardMap_zero (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω s t ^ α ≤ (δα : ℝ≥0∞))
    (Z : ControlledPath X ω α E) :
    (picardMap V hX hω1 hfine hωne y₀ hδα Z).Y 0 = y₀ :=
  basedPath_zero (picardIntegral_additive V hX hω1 hfine hωne Z) y₀

/-! ### Box invariance -/

/-- Membership of the certificate box. -/
def InBox (Bb Bd By : ℝ≥0) (Z : ControlledPath X ω α E) : Prop :=
  Z.Cb ≤ Bb ∧ Z.Cd ≤ Bd ∧ Z.Cy ≤ By

/-- **Box invariance of the Picard map**: for box constants satisfying
the three closure inequalities, the Picard map preserves the box. -/
theorem picardMap_inBox (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω s t ^ α ≤ (δα : ℝ≥0∞))
    {Bb Bd By : ℝ≥0}
    (hBb : V.C0 ≤ Bb)
    (hBd : V.C1 * (d * Bb + By) ≤ Bd)
    (hBy : (Sewing.sewingConst (3 * α)).toNNReal *
        (d * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2) +
          d ^ 2 * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By))) * δα +
      d ^ 2 * (V.C1 * Bb) ≤ By)
    {Z : ControlledPath X ω α E} (hZ : InBox Bb Bd By Z) :
    InBox Bb Bd By (picardMap V hX hω1 hfine hωne y₀ hδα Z) := by
  obtain ⟨hb, hd, hy⟩ := hZ
  refine ⟨hBb, ?_, ?_⟩
  · refine le_trans ?_ hBd
    show V.C1 * (d * Z.Cb + Z.Cy) ≤ V.C1 * (d * Bb + By)
    gcongr
  · refine le_trans ?_ hBy
    show (Sewing.sewingConst (3 * α)).toNNReal *
        (d * (V.C1 * Z.Cy + V.C2 * (d * Z.Cb + Z.Cy) ^ 2) +
          d ^ 2 * (V.C1 * Z.Cd + V.C2 * Z.Cb * (d * Z.Cb + Z.Cy))) * δα +
      d ^ 2 * (V.C1 * Z.Cb) ≤ _
    gcongr

end Picard

/-! ### The distance step -/

/-- Pointwise bound for a Gubinelli germ from a sup bound on the path
data. -/
theorem enorm_gubinelliGerm_le (hX : IsLevel2RoughPath X ω α)
    (Z' : ControlledPath X ω α (Fin d → E)) {B0 : ℝ≥0∞}
    (hY : ∀ s : ℝ, ‖Z'.Y s‖ₑ ≤ B0) ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖gubinelliGerm Z' s t‖ₑ ≤
      (d : ℝ≥0∞) * B0 * ω s t ^ α +
        (d : ℝ≥0∞) ^ 2 * Z'.Cb * ω s t ^ (2 * α) := by
  rw [gubinelliGerm_apply]
  refine le_trans (enorm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (enorm_fin_sum_le (C := B0 * ω s t ^ α) fun i => ?_)
      (le_of_eq (mul_assoc _ _ _).symm)
    rw [ControlledPath.enorm_real_smul]
    exact le_trans (mul_le_mul' (hX.bound_one hst i)
      (le_trans (enorm_apply_le i) (hY s))) (le_of_eq (mul_comm _ _))
  · refine le_trans (enorm_fin_sum_le
      (C := (d : ℝ≥0∞) * (Z'.Cb * ω s t ^ (2 * α))) fun i =>
        enorm_fin_sum_le (C := Z'.Cb * ω s t ^ (2 * α)) fun j => ?_)
      (le_of_eq (by ring))
    rw [ControlledPath.enorm_real_smul]
    exact le_trans (mul_le_mul' (hX.bound_two hst i j)
      (le_trans (enorm_apply_le j) (Z'.bound_Yd s i)))
      (le_of_eq (mul_comm _ _))

section Picard2

variable [CompleteSpace E]
variable (V : RDEVectorField3 d E) (hX : IsLevel2RoughPath X ω α)
variable (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
variable (hfine : Sewing.HasFinePartitions ω)
variable (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
variable {δα : ℝ≥0}
variable (y₀ : E)

include hfine hωne in
/-- The difference of two additive families with sewing germ bounds for
the composed integrands is bounded by the distance constants with the
full window gain. -/
theorem integral_dist_bound
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hδα1 : δα ≤ 1)
    {Z₁ Z₂ : ControlledPath X ω α E} (D : ControlledDist Z₁ Z₂)
    {I₁ I₂ : ℝ → ℝ → E}
    (hadd₁ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₁ s u + I₁ u t = I₁ s t)
    (hadd₂ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₂ s u + I₂ u t = I₂ s t)
    (hgerm₁ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - gubinelliGerm
          (V.toRDEVectorField.compControlled hX hω1 Z₁) s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst (V.toRDEVectorField.compControlled hX hω1 Z₁) *
            ω s t ^ (3 * α)))
    (hgerm₂ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₂ s t - gubinelliGerm
          (V.toRDEVectorField.compControlled hX hω1 Z₂) s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst (V.toRDEVectorField.compControlled hX hω1 Z₂) *
            ω s t ^ (3 * α))) :
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - I₂ s t‖ₑ ≤
        (((d : ℝ≥0) * (V.compControlledDist hX hω1 D).D0 +
          (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Db +
          (Sewing.sewingConst (3 * α)).toNNReal *
            ((d : ℝ≥0) * (V.compControlledDist hX hω1 D).Dy +
              (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Dd)) *
          δα : ℝ≥0) := by
  intro s t hst
  have hα := hX.alpha_pos
  have h3α := hX.one_lt_three_alpha
  have hωα : ω s t ^ α ≤ (δα : ℝ≥0∞) := hδα hst
  have hω2α : ω s t ^ (2 * α) ≤ (δα : ℝ≥0∞) :=
    rpow_two_mul_le_coe hα.le hωα hδα1
  have hω3α : ω s t ^ (3 * α) ≤ (δα : ℝ≥0∞) :=
    rpow_three_mul_le_coe hα.le hωα hδα1
  have hsub := roughIntegral_sub hX hfine hωne
    (V.compControlledDist hX hω1 D) hadd₁ hadd₂ hgerm₁ hgerm₂ hst
  have hgerm := enorm_gubinelliGerm_le hX
    (V.compControlledDist hX hω1 D).toControlledPath
    (fun s => (V.compControlledDist hX hω1 D).bound_Y s) hst
  have htri : ‖I₁ s t - I₂ s t‖ₑ ≤
      ‖I₁ s t - I₂ s t -
          gubinelliGerm
            (V.compControlledDist hX hω1 D).toControlledPath s t‖ₑ +
        ‖gubinelliGerm
          (V.compControlledDist hX hω1 D).toControlledPath s t‖ₑ := by
    refine le_trans (le_of_eq ?_) (enorm_add_le _ _)
    congr 1
    abel
  refine le_trans htri ?_
  refine le_trans (add_le_add hsub hgerm) ?_
  have hK : Sewing.sewingConst (3 * α) =
      (((Sewing.sewingConst (3 * α)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal (Sewing.sewingConst_lt_top h3α).ne).symm
  have hrc : roughConst
      (V.compControlledDist hX hω1 D).toControlledPath =
      (((d : ℝ≥0) * (V.compControlledDist hX hω1 D).Dy +
        (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Dd :
          ℝ≥0) : ℝ≥0∞) := by
    rw [roughConst_eq_coe]
    congr 1
  have hCb : (V.compControlledDist hX hω1 D).toControlledPath.Cb =
      (V.compControlledDist hX hω1 D).Db := rfl
  have h1 : Sewing.sewingConst (3 * α) *
      (roughConst (V.compControlledDist hX hω1 D).toControlledPath *
        ω s t ^ (3 * α)) ≤
      (((Sewing.sewingConst (3 * α)).toNNReal *
        ((d : ℝ≥0) * (V.compControlledDist hX hω1 D).Dy +
          (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Dd) :
          ℝ≥0) : ℝ≥0∞) * δα := by
    conv_lhs => rw [hK, hrc]
    refine le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hω3α))
      (le_of_eq ?_)
    push_cast
    ring
  have h2 : (d : ℝ≥0∞) *
        (V.compControlledDist hX hω1 D).D0 * ω s t ^ α +
      (d : ℝ≥0∞) ^ 2 *
        (V.compControlledDist hX hω1 D).toControlledPath.Cb *
        ω s t ^ (2 * α) ≤
      (((d : ℝ≥0) * (V.compControlledDist hX hω1 D).D0 +
        (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Db :
          ℝ≥0) : ℝ≥0∞) * δα := by
    rw [hCb]
    refine le_trans (add_le_add
      (mul_le_mul' le_rfl hωα) (mul_le_mul' le_rfl hω2α))
      (le_of_eq ?_)
    push_cast
    ring
  refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
  push_cast
  ring

include hfine hωne in
include hfine hωne in
/-- The folded form of the integral-difference germ bound on the
window. -/
theorem integral_sub_germ_folded
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    {Z₁ Z₂ : ControlledPath X ω α E} (D : ControlledDist Z₁ Z₂)
    {I₁ I₂ : ℝ → ℝ → E}
    (hadd₁ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₁ s u + I₁ u t = I₁ s t)
    (hadd₂ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₂ s u + I₂ u t = I₂ s t)
    (hgerm₁ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - gubinelliGerm
          (V.toRDEVectorField.compControlled hX hω1 Z₁) s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst (V.toRDEVectorField.compControlled hX hω1 Z₁) *
            ω s t ^ (3 * α)))
    (hgerm₂ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₂ s t - gubinelliGerm
          (V.toRDEVectorField.compControlled hX hω1 Z₂) s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst (V.toRDEVectorField.compControlled hX hω1 Z₂) *
            ω s t ^ (3 * α))) ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖I₁ s t - I₂ s t - gubinelliGerm
        (V.compControlledDist hX hω1 D).toControlledPath s t‖ₑ ≤
      (((Sewing.sewingConst (3 * α)).toNNReal *
        ((d : ℝ≥0) * (V.compControlledDist hX hω1 D).Dy +
          (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Dd) *
        δα : ℝ≥0) : ℝ≥0∞) * ω s t ^ (2 * α) := by
  have hα := hX.alpha_pos
  have h3α := hX.one_lt_three_alpha
  have hω3α : ω s t ^ (3 * α) ≤ (δα : ℝ≥0∞) * ω s t ^ (2 * α) :=
    rpow_three_mul_le_mul hα.le (hδα hst)
  have hK : Sewing.sewingConst (3 * α) =
      (((Sewing.sewingConst (3 * α)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal (Sewing.sewingConst_lt_top h3α).ne).symm
  have hrc : roughConst
      (V.compControlledDist hX hω1 D).toControlledPath =
      (((d : ℝ≥0) * (V.compControlledDist hX hω1 D).Dy +
        (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Dd :
          ℝ≥0) : ℝ≥0∞) := by
    rw [roughConst_eq_coe]
    congr 1
  refine le_trans (roughIntegral_sub hX hfine hωne
    (V.compControlledDist hX hω1 D) hadd₁ hadd₂ hgerm₁ hgerm₂ hst) ?_
  conv_lhs => rw [hK, hrc]
  refine le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hω3α))
    (le_of_eq ?_)
  push_cast
  ring

/-- **The distance step**: certificates for the distance between two
Picard iterates, linear in the input distance with an explicit window
gain `δα` on the sup and remainder slots. -/
noncomputable def picardDist
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hδα1 : δα ≤ 1)
    {Z₁ Z₂ : ControlledPath X ω α E} (D : ControlledDist Z₁ Z₂) :
    ControlledDist (picardMap V hX hω1 hfine hωne y₀ hδα Z₁)
      (picardMap V hX hω1 hfine hωne y₀ hδα Z₂) where
  D0 := ((d : ℝ≥0) *
      (V.compControlledDist hX hω1 D).D0 +
    (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Db +
    (Sewing.sewingConst (3 * α)).toNNReal *
      ((d : ℝ≥0) * (V.compControlledDist hX hω1 D).Dy +
        (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Dd)) * δα
  Db := V.C1 * D.D0
  Dd := (d : ℝ≥0) * (V.compControlledDist hX hω1 D).Db +
    (V.compControlledDist hX hω1 D).Dy
  Dy := (Sewing.sewingConst (3 * α)).toNNReal *
      ((d : ℝ≥0) * (V.compControlledDist hX hω1 D).Dy +
        (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Dd) * δα +
    (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Db
  bound_Y := by
    intro u
    have hIdiff := integral_dist_bound V hX hω1 hfine hωne hδα hδα1 D
      (picardIntegral_additive V hX hω1 hfine hωne Z₁)
      (picardIntegral_additive V hX hω1 hfine hωne Z₂)
      (picardIntegral_germ V hX hω1 hfine hωne Z₁)
      (picardIntegral_germ V hX hω1 hfine hωne Z₂)
    -- basedPath differences reduce to integral differences
    show ‖basedPath (picardIntegral V hX hω1 hfine hωne Z₁) y₀ u -
        basedPath (picardIntegral V hX hω1 hfine hωne Z₂) y₀ u‖ₑ ≤ _
    rw [basedPath, basedPath]
    by_cases hu : 0 ≤ u
    · rw [if_pos hu, if_pos hu,
        show y₀ + picardIntegral V hX hω1 hfine hωne Z₁ 0 u -
          (y₀ + picardIntegral V hX hω1 hfine hωne Z₂ 0 u) =
          picardIntegral V hX hω1 hfine hωne Z₁ 0 u -
            picardIntegral V hX hω1 hfine hωne Z₂ 0 u by abel]
      exact hIdiff hu
    · rw [if_neg hu, if_neg hu,
        show y₀ - picardIntegral V hX hω1 hfine hωne Z₁ u 0 -
          (y₀ - picardIntegral V hX hω1 hfine hωne Z₂ u 0) =
          -(picardIntegral V hX hω1 hfine hωne Z₁ u 0 -
            picardIntegral V hX hω1 hfine hωne Z₂ u 0) by abel,
        enorm_neg]
      exact hIdiff (not_le.1 hu).le
  bound_Yd := by
    intro s i
    show ‖V.f i (Z₁.Y s) - V.f i (Z₂.Y s)‖ₑ ≤ _
    refine le_trans (V.enorm_f_lipschitz i _ _) ?_
    refine le_trans (mul_le_mul' le_rfl (D.bound_Y s)) (le_of_eq ?_)
    push_cast
    ring
  holder_Yd := by
    intro s t hst i
    show ‖V.f i (Z₁.Y t) - V.f i (Z₂.Y t) -
      (V.f i (Z₁.Y s) - V.f i (Z₂.Y s))‖ₑ ≤ _
    have hcoord : V.f i (Z₁.Y t) - V.f i (Z₂.Y t) -
        (V.f i (Z₁.Y s) - V.f i (Z₂.Y s)) =
        ((V.compControlledDist hX hω1 D).toControlledPath.Y t -
          (V.compControlledDist hX hω1 D).toControlledPath.Y s) i := by
      simp only [ControlledDist.toControlledPath_Y, Pi.sub_apply,
        RDEVectorField.compControlled_Y]
    rw [hcoord]
    refine le_trans (enorm_apply_le i) ?_
    refine le_trans (RDEVectorField.increment_le hX hω1
      (V.compControlledDist hX hω1 D).toControlledPath hst)
      (le_of_eq ?_)
    simp only [ControlledDist.toControlledPath_Cb,
      ControlledDist.toControlledPath_Cy]
    push_cast
    ring
  remainder := by
    intro s t hst
    -- increments of the based paths are the integral difference
    have hbp : (picardMap V hX hω1 hfine hωne y₀ hδα Z₁).Y t -
        (picardMap V hX hω1 hfine hωne y₀ hδα Z₂).Y t -
        ((picardMap V hX hω1 hfine hωne y₀ hδα Z₁).Y s -
          (picardMap V hX hω1 hfine hωne y₀ hδα Z₂).Y s) =
        picardIntegral V hX hω1 hfine hωne Z₁ s t -
          picardIntegral V hX hω1 hfine hωne Z₂ s t := by
      have h₁ := basedPath_increment
        (picardIntegral_additive V hX hω1 hfine hωne Z₁) y₀ hst
      have h₂ := basedPath_increment
        (picardIntegral_additive V hX hω1 hfine hωne Z₂) y₀ hst
      show basedPath (picardIntegral V hX hω1 hfine hωne Z₁) y₀ t -
        basedPath (picardIntegral V hX hω1 hfine hωne Z₂) y₀ t -
        (basedPath (picardIntegral V hX hω1 hfine hωne Z₁) y₀ s -
          basedPath (picardIntegral V hX hω1 hfine hωne Z₂) y₀ s) = _
      rw [← h₁, ← h₂]
      abel
    rw [hbp]
    -- the linear part is the level-one part of the difference germ
    have hlin : ∀ i : Fin d,
        (picardMap V hX hω1 hfine hωne y₀ hδα Z₁).Yd s i -
          (picardMap V hX hω1 hfine hωne y₀ hδα Z₂).Yd s i =
        (V.compControlledDist hX hω1 D).toControlledPath.Y s i := by
      intro i
      simp only [picardMap_Yd, ControlledDist.toControlledPath_Y,
        Pi.sub_apply, RDEVectorField.compControlled_Y]
    have hsplit : picardIntegral V hX hω1 hfine hωne Z₁ s t -
        picardIntegral V hX hω1 hfine hωne Z₂ s t -
        ∑ i, X.coeff s t [i] •
          ((picardMap V hX hω1 hfine hωne y₀ hδα Z₁).Yd s i -
            (picardMap V hX hω1 hfine hωne y₀ hδα Z₂).Yd s i) =
        (picardIntegral V hX hω1 hfine hωne Z₁ s t -
          picardIntegral V hX hω1 hfine hωne Z₂ s t -
          gubinelliGerm
            (V.compControlledDist hX hω1 D).toControlledPath s t) +
        ∑ i, ∑ j, X.coeff s t [i, j] •
          (V.compControlledDist hX hω1 D).toControlledPath.Yd s i j := by
      rw [Finset.sum_congr rfl fun i _ => by rw [hlin i],
        gubinelliGerm_apply]
      abel
    rw [hsplit]
    refine le_trans (enorm_add_le _ _) ?_
    have h1 := integral_sub_germ_folded V hX hω1 hfine hωne hδα D
      (picardIntegral_additive V hX hω1 hfine hωne Z₁)
      (picardIntegral_additive V hX hω1 hfine hωne Z₂)
      (picardIntegral_germ V hX hω1 hfine hωne Z₁)
      (picardIntegral_germ V hX hω1 hfine hωne Z₂) hst
    have h2 : ‖∑ i, ∑ j, X.coeff s t [i, j] •
        (V.compControlledDist hX hω1 D).toControlledPath.Yd s i j‖ₑ ≤
        (((d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Db : ℝ≥0) :
          ℝ≥0∞) * ω s t ^ (2 * α) := by
      refine le_trans (enorm_fin_sum_le
        (C := (d : ℝ≥0∞) *
          ((V.compControlledDist hX hω1 D).Db * ω s t ^ (2 * α)))
        fun i => enorm_fin_sum_le
          (C := (V.compControlledDist hX hω1 D).Db * ω s t ^ (2 * α))
          fun j => ?_)
        (le_of_eq (by push_cast; ring))
      rw [ControlledPath.enorm_real_smul]
      exact le_trans (mul_le_mul' (hX.bound_two hst i j)
        (le_trans (enorm_apply_le j)
          ((V.compControlledDist hX hω1 D).bound_Yd s i)))
        (le_of_eq (mul_comm _ _))
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    push_cast
    ring

/-! ### The distance step for a pair of solutions -/

open RDEVectorField in
/-- **The distance step for two solutions**: solutions of the same RDE
from the same initial condition satisfy the Picard distance-step
inequalities directly, with their own increment families. -/
noncomputable def solutionDistStep
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hδα1 : δα ≤ 1)
    {Z₁ Z₂ : ControlledPath X ω α E} {I₁ I₂ : ℝ → ℝ → E}
    (hsol₁ : V.IsRDESolution hX hω1 Z₁ I₁)
    (hsol₂ : V.IsRDESolution hX hω1 Z₂ I₂)
    (h0 : Z₁.Y 0 = Z₂.Y 0)
    (D : ControlledDist Z₁ Z₂) : ControlledDist Z₁ Z₂ where
  D0 := ((d : ℝ≥0) * (V.compControlledDist hX hω1 D).D0 +
    (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Db +
    (Sewing.sewingConst (3 * α)).toNNReal *
      ((d : ℝ≥0) * (V.compControlledDist hX hω1 D).Dy +
        (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Dd)) * δα
  Db := V.C1 * D.D0
  Dd := (d : ℝ≥0) * (V.compControlledDist hX hω1 D).Db +
    (V.compControlledDist hX hω1 D).Dy
  Dy := (Sewing.sewingConst (3 * α)).toNNReal *
      ((d : ℝ≥0) * (V.compControlledDist hX hω1 D).Dy +
        (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Dd) * δα +
    (d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Db
  bound_Y := by
    intro u
    have hIdiff := integral_dist_bound V hX hω1 hfine hωne hδα hδα1 D
      hsol₁.additive hsol₂.additive hsol₁.germ_bound hsol₂.germ_bound
    by_cases hu : 0 ≤ u
    · have hre : Z₁.Y u - Z₂.Y u = I₁ 0 u - I₂ 0 u := by
        rw [← hsol₁.increment_eq hu, ← hsol₂.increment_eq hu, h0]
        abel
      rw [hre]
      exact hIdiff hu
    · have hu' : u ≤ 0 := (not_le.1 hu).le
      have hre : Z₁.Y u - Z₂.Y u = -(I₁ u 0 - I₂ u 0) := by
        rw [← hsol₁.increment_eq hu', ← hsol₂.increment_eq hu', h0]
        abel
      rw [hre, enorm_neg]
      exact hIdiff hu'
  bound_Yd := by
    intro s i
    rw [hsol₁.deriv_eq s i, hsol₂.deriv_eq s i]
    refine le_trans (V.enorm_f_lipschitz i _ _) ?_
    refine le_trans (mul_le_mul' le_rfl (D.bound_Y s)) (le_of_eq ?_)
    push_cast
    ring
  holder_Yd := by
    intro s t hst i
    rw [hsol₁.deriv_eq t i, hsol₂.deriv_eq t i, hsol₁.deriv_eq s i,
      hsol₂.deriv_eq s i]
    have hcoord : V.f i (Z₁.Y t) - V.f i (Z₂.Y t) -
        (V.f i (Z₁.Y s) - V.f i (Z₂.Y s)) =
        ((V.compControlledDist hX hω1 D).toControlledPath.Y t -
          (V.compControlledDist hX hω1 D).toControlledPath.Y s) i := by
      simp only [ControlledDist.toControlledPath_Y, Pi.sub_apply,
        RDEVectorField.compControlled_Y]
    rw [hcoord]
    refine le_trans (enorm_apply_le i) ?_
    refine le_trans (RDEVectorField.increment_le hX hω1
      (V.compControlledDist hX hω1 D).toControlledPath hst)
      (le_of_eq ?_)
    simp only [ControlledDist.toControlledPath_Cb,
      ControlledDist.toControlledPath_Cy]
    push_cast
    ring
  remainder := by
    intro s t hst
    have hbp : Z₁.Y t - Z₂.Y t - (Z₁.Y s - Z₂.Y s) =
        I₁ s t - I₂ s t := by
      rw [← hsol₁.increment_eq hst, ← hsol₂.increment_eq hst]
      abel
    rw [hbp]
    have hlin : ∀ i : Fin d, Z₁.Yd s i - Z₂.Yd s i =
        (V.compControlledDist hX hω1 D).toControlledPath.Y s i := by
      intro i
      rw [hsol₁.deriv_eq s i, hsol₂.deriv_eq s i]
      simp only [ControlledDist.toControlledPath_Y, Pi.sub_apply,
        RDEVectorField.compControlled_Y]
    have hsplit : I₁ s t - I₂ s t -
        ∑ i, X.coeff s t [i] • (Z₁.Yd s i - Z₂.Yd s i) =
        (I₁ s t - I₂ s t -
          gubinelliGerm
            (V.compControlledDist hX hω1 D).toControlledPath s t) +
        ∑ i, ∑ j, X.coeff s t [i, j] •
          (V.compControlledDist hX hω1 D).toControlledPath.Yd s i j := by
      rw [Finset.sum_congr rfl fun i _ => by rw [hlin i],
        gubinelliGerm_apply]
      abel
    rw [hsplit]
    refine le_trans (enorm_add_le _ _) ?_
    have h1 := integral_sub_germ_folded V hX hω1 hfine hωne hδα D
      hsol₁.additive hsol₂.additive hsol₁.germ_bound hsol₂.germ_bound hst
    have h2 : ‖∑ i, ∑ j, X.coeff s t [i, j] •
        (V.compControlledDist hX hω1 D).toControlledPath.Yd s i j‖ₑ ≤
        (((d : ℝ≥0) ^ 2 * (V.compControlledDist hX hω1 D).Db : ℝ≥0) :
          ℝ≥0∞) * ω s t ^ (2 * α) := by
      refine le_trans (enorm_fin_sum_le
        (C := (d : ℝ≥0∞) *
          ((V.compControlledDist hX hω1 D).Db * ω s t ^ (2 * α)))
        fun i => enorm_fin_sum_le
          (C := (V.compControlledDist hX hω1 D).Db * ω s t ^ (2 * α))
          fun j => ?_)
        (le_of_eq (by push_cast; ring))
      rw [ControlledPath.enorm_real_smul]
      exact le_trans (mul_le_mul' (hX.bound_two hst i j)
        (le_trans (enorm_apply_le j)
          ((V.compControlledDist hX hω1 D).bound_Yd s i)))
        (le_of_eq (mul_comm _ _))
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    push_cast
    ring

/-! ### Uniqueness of solutions -/

/-- Any two box-certified controlled paths with the same initial value
admit a finite distance certificate on the window. -/
noncomputable def seedDist
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    {Bb Bd By : ℝ≥0} {Z₁ Z₂ : ControlledPath X ω α E}
    (h0 : Z₁.Y 0 = Z₂.Y 0)
    (hZ₁ : InBox Bb Bd By Z₁) (hZ₂ : InBox Bb Bd By Z₂) :
    ControlledDist Z₁ Z₂ where
  D0 := 2 * ((d * Bb + By) * δα)
  Db := 2 * Bb
  Dd := 2 * Bd
  Dy := 2 * By
  bound_Y := by
    intro u
    have hbox : ∀ (Z : ControlledPath X ω α E), InBox Bb Bd By Z →
        ∀ ⦃s t : ℝ⦄, s ≤ t → ‖Z.Y t - Z.Y s‖ₑ ≤
          (((d * Bb + By) * δα : ℝ≥0) : ℝ≥0∞) := by
      intro Z hZ s t hst
      refine le_trans (RDEVectorField.increment_le hX hω1 Z hst) ?_
      calc ((d : ℝ≥0∞) * Z.Cb + Z.Cy) * ω s t ^ α
          ≤ ((d : ℝ≥0∞) * Bb + By) * (δα : ℝ≥0∞) := by
            refine mul_le_mul' (add_le_add
              (mul_le_mul' le_rfl ?_) ?_) (hδα hst)
            · exact_mod_cast hZ.1
            · exact_mod_cast hZ.2.2
        _ = (((d * Bb + By) * δα : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    by_cases hu : 0 ≤ u
    · have hre : Z₁.Y u - Z₂.Y u =
          (Z₁.Y u - Z₁.Y 0) - (Z₂.Y u - Z₂.Y 0) := by
        rw [h0]
        abel
      rw [hre]
      refine le_trans enorm_sub_le ?_
      refine le_trans (add_le_add (hbox Z₁ hZ₁ hu) (hbox Z₂ hZ₂ hu))
        (le_of_eq ?_)
      push_cast
      ring
    · have hu' : u ≤ 0 := (not_le.1 hu).le
      have hre : Z₁.Y u - Z₂.Y u =
          -((Z₁.Y 0 - Z₁.Y u) - (Z₂.Y 0 - Z₂.Y u)) := by
        rw [h0]
        abel
      rw [hre, enorm_neg]
      refine le_trans enorm_sub_le ?_
      refine le_trans (add_le_add (hbox Z₁ hZ₁ hu') (hbox Z₂ hZ₂ hu'))
        (le_of_eq ?_)
      push_cast
      ring
  bound_Yd := by
    intro s i
    refine le_trans enorm_sub_le ?_
    refine le_trans (add_le_add (Z₁.bound_Yd s i) (Z₂.bound_Yd s i)) ?_
    have h1 : (Z₁.Cb : ℝ≥0∞) + Z₂.Cb ≤ (Bb : ℝ≥0∞) + Bb := by
      refine add_le_add ?_ ?_
      · exact_mod_cast hZ₁.1
      · exact_mod_cast hZ₂.1
    refine le_trans h1 (le_of_eq ?_)
    push_cast
    ring
  holder_Yd := by
    intro s t hst i
    have hre : Z₁.Yd t i - Z₂.Yd t i - (Z₁.Yd s i - Z₂.Yd s i) =
        (Z₁.Yd t i - Z₁.Yd s i) - (Z₂.Yd t i - Z₂.Yd s i) := by
      abel
    rw [hre]
    refine le_trans enorm_sub_le ?_
    refine le_trans (add_le_add (Z₁.holder_Yd hst i) (Z₂.holder_Yd hst i))
      ?_
    have h1 : (Z₁.Cd : ℝ≥0∞) * ω s t ^ α + Z₂.Cd * ω s t ^ α ≤
        ((2 * Bd : ℝ≥0) : ℝ≥0∞) * ω s t ^ α := by
      rw [← add_mul]
      refine mul_le_mul' ?_ le_rfl
      have : (Z₁.Cd : ℝ≥0∞) + Z₂.Cd ≤ (Bd : ℝ≥0∞) + Bd := by
        refine add_le_add ?_ ?_
        · exact_mod_cast hZ₁.2.1
        · exact_mod_cast hZ₂.2.1
      refine le_trans this (le_of_eq ?_)
      push_cast
      ring
    exact h1
  remainder := by
    intro s t hst
    have hsum : ∑ i, X.coeff s t [i] • (Z₁.Yd s i - Z₂.Yd s i) =
        (∑ i, X.coeff s t [i] • Z₁.Yd s i) -
          ∑ i, X.coeff s t [i] • Z₂.Yd s i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => smul_sub _ _ _
    have hre : Z₁.Y t - Z₂.Y t - (Z₁.Y s - Z₂.Y s) -
        ∑ i, X.coeff s t [i] • (Z₁.Yd s i - Z₂.Yd s i) =
        (Z₁.Y t - Z₁.Y s - ∑ i, X.coeff s t [i] • Z₁.Yd s i) -
          (Z₂.Y t - Z₂.Y s - ∑ i, X.coeff s t [i] • Z₂.Yd s i) := by
      rw [hsum]
      abel
    rw [hre]
    refine le_trans enorm_sub_le ?_
    refine le_trans (add_le_add (Z₁.remainder hst) (Z₂.remainder hst)) ?_
    have h1 : (Z₁.Cy : ℝ≥0∞) * ω s t ^ (2 * α) +
        Z₂.Cy * ω s t ^ (2 * α) ≤
        ((2 * By : ℝ≥0) : ℝ≥0∞) * ω s t ^ (2 * α) := by
      rw [← add_mul]
      refine mul_le_mul' ?_ le_rfl
      have : (Z₁.Cy : ℝ≥0∞) + Z₂.Cy ≤ (By : ℝ≥0∞) + By := by
        refine add_le_add ?_ ?_
        · exact_mod_cast hZ₁.2.2
        · exact_mod_cast hZ₂.2.2
      refine le_trans this (le_of_eq ?_)
      push_cast
      ring
    exact h1

include hfine hωne in
/-- **Uniqueness of RDE solutions** (Friz–Hairer Thm 8.4-type): two
box-certified solutions of `dY = f(Y)·dX` from the same initial value
coincide on the window, provided the distance step contracts a weighted
combination of the distance certificates. -/
theorem rde_unique
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hδα1 : δα ≤ 1)
    {Bb Bd By wa wb wc we : ℝ≥0} (hwa : 0 < wa)
    {Z₁ Z₂ : ControlledPath X ω α E} {I₁ I₂ : ℝ → ℝ → E}
    (hsol₁ : V.IsRDESolution hX hω1 Z₁ I₁)
    (hsol₂ : V.IsRDESolution hX hω1 Z₂ I₂)
    (h0 : Z₁.Y 0 = Z₂.Y 0)
    (hZ₁ : InBox Bb Bd By Z₁) (hZ₂ : InBox Bb Bd By Z₂)
    (hcontr : ∀ D : ControlledDist Z₁ Z₂,
      2 * (wa * (solutionDistStep V hX hω1 hfine hωne hδα hδα1
            hsol₁ hsol₂ h0 D).D0 +
          wb * (solutionDistStep V hX hω1 hfine hωne hδα hδα1
            hsol₁ hsol₂ h0 D).Db +
          wc * (solutionDistStep V hX hω1 hfine hωne hδα hδα1
            hsol₁ hsol₂ h0 D).Dd +
          we * (solutionDistStep V hX hω1 hfine hωne hδα hδα1
            hsol₁ hsol₂ h0 D).Dy) ≤
        wa * D.D0 + wb * D.Db + wc * D.Dd + we * D.Dy) :
    ∀ u : ℝ, Z₁.Y u = Z₂.Y u := by
  intro u
  -- the iterated distance certificates
  let Dseq : ℕ → ControlledDist Z₁ Z₂ := fun n =>
    Nat.rec (seedDist hX hω1 hδα h0 hZ₁ hZ₂)
      (fun _ D => solutionDistStep V hX hω1 hfine hωne hδα hδα1
        hsol₁ hsol₂ h0 D) n
  have hDsucc : ∀ n : ℕ, Dseq (n + 1) =
      solutionDistStep V hX hω1 hfine hωne hδα hδα1
        hsol₁ hsol₂ h0 (Dseq n) := fun n => rfl
  -- weighted geometric decay
  set ρ : ℕ → ℝ≥0 := fun n =>
    wa * (Dseq n).D0 + wb * (Dseq n).Db + wc * (Dseq n).Dd +
      we * (Dseq n).Dy with hρdef
  have hdecay : ∀ n : ℕ, 2 ^ n * ρ n ≤ ρ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep : 2 * ρ (n + 1) ≤ ρ n := by
          rw [hρdef]
          simp only [hDsucc n]
          exact hcontr (Dseq n)
        calc 2 ^ (n + 1) * ρ (n + 1) = 2 ^ n * (2 * ρ (n + 1)) := by ring
          _ ≤ 2 ^ n * ρ n := mul_le_mul' le_rfl hstep
          _ ≤ ρ 0 := ih
  -- extract the sup-distance and pass to the limit in ℝ
  have hbound : ∀ n : ℕ, ‖Z₁.Y u - Z₂.Y u‖ₑ ≤ ((Dseq n).D0 : ℝ≥0∞) :=
    fun n => (Dseq n).bound_Y u
  have hwa' : ∀ n : ℕ, (2 : ℝ≥0) ^ n * (wa * (Dseq n).D0) ≤ ρ 0 := by
    intro n
    refine le_trans ?_ (hdecay n)
    rw [hρdef]
    refine mul_le_mul' le_rfl ?_
    simp only []
    calc wa * (Dseq n).D0 ≤ wa * (Dseq n).D0 + wb * (Dseq n).Db +
        wc * (Dseq n).Dd + we * (Dseq n).Dy := by
          exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
            (le_add_of_le_of_nonneg le_rfl zero_le) zero_le) zero_le
      _ = _ := rfl
  -- the enorm is finite, so work with its real value
  have hfin : ‖Z₁.Y u - Z₂.Y u‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hbound 0)
    exact ENNReal.coe_ne_top
  have hreal : ∀ n : ℕ, (‖Z₁.Y u - Z₂.Y u‖ₑ).toReal ≤
      ((ρ 0 : ℝ≥0) : ℝ) / (wa : ℝ) / 2 ^ n := by
    intro n
    have h1 : (‖Z₁.Y u - Z₂.Y u‖ₑ).toReal ≤ (((Dseq n).D0 : ℝ≥0) : ℝ) := by
      have := ENNReal.toReal_mono ENNReal.coe_ne_top (hbound n)
      simpa using this
    refine le_trans h1 (le_trans
      (coe_le_geom_of_pow_mul_le hwa (hwa' n)) (le_of_eq ?_))
    rw [div_pow, one_pow]
    ring
  have hlim : Filter.Tendsto
      (fun n : ℕ => ((ρ 0 : ℝ≥0) : ℝ) / (wa : ℝ) / 2 ^ n)
      Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have h2 := h.const_mul (((ρ 0 : ℝ≥0) : ℝ) / (wa : ℝ))
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    rw [div_pow, one_pow]
    ring
  have hzero : (‖Z₁.Y u - Z₂.Y u‖ₑ).toReal ≤ 0 :=
    ge_of_tendsto' hlim hreal |>.trans_eq rfl
  have henorm : ‖Z₁.Y u - Z₂.Y u‖ₑ = 0 := by
    have h1 : (‖Z₁.Y u - Z₂.Y u‖ₑ).toReal = 0 :=
      le_antisymm hzero ENNReal.toReal_nonneg
    rcases (ENNReal.toReal_eq_zero_iff _).1 h1 with h | h
    · exact h
    · exact absurd h hfin
  have := enorm_eq_zero.1 henorm
  exact sub_eq_zero.1 this

end Picard2

/-! ### Weakening certificates -/

section Weaken

variable {Bb Bd By : ℝ≥0}

/-- Enlarge the certificates of a controlled path to given box
constants. -/
def ControlledPath.weaken (Z : ControlledPath X ω α W)
    (h1 : Z.Cb ≤ Bb) (h2 : Z.Cd ≤ Bd) (h3 : Z.Cy ≤ By) :
    ControlledPath X ω α W where
  Y := Z.Y
  Yd := Z.Yd
  Cb := Bb
  Cd := Bd
  Cy := By
  bound_Yd s i := le_trans (Z.bound_Yd s i) (by exact_mod_cast h1)
  holder_Yd s t hst i := le_trans (Z.holder_Yd hst i)
    (mul_le_mul' (by exact_mod_cast h2) le_rfl)
  remainder s t hst := le_trans (Z.remainder hst)
    (mul_le_mul' (by exact_mod_cast h3) le_rfl)

@[simp]
theorem ControlledPath.weaken_Y (Z : ControlledPath X ω α W)
    (h1 : Z.Cb ≤ Bb) (h2 : Z.Cd ≤ Bd) (h3 : Z.Cy ≤ By) :
    (Z.weaken h1 h2 h3).Y = Z.Y :=
  rfl

@[simp]
theorem ControlledPath.weaken_Yd (Z : ControlledPath X ω α W)
    (h1 : Z.Cb ≤ Bb) (h2 : Z.Cd ≤ Bd) (h3 : Z.Cy ≤ By) :
    (Z.weaken h1 h2 h3).Yd = Z.Yd :=
  rfl

/-- Distance certificates transport across weakening (the paths are
unchanged). -/
def ControlledDist.ofWeaken {Z₁ Z₂ : ControlledPath X ω α W}
    (D : ControlledDist Z₁ Z₂)
    (h1 : Z₁.Cb ≤ Bb) (h2 : Z₁.Cd ≤ Bd) (h3 : Z₁.Cy ≤ By)
    (h1' : Z₂.Cb ≤ Bb) (h2' : Z₂.Cd ≤ Bd) (h3' : Z₂.Cy ≤ By) :
    ControlledDist (Z₁.weaken h1 h2 h3) (Z₂.weaken h1' h2' h3') where
  D0 := D.D0
  Db := D.Db
  Dd := D.Dd
  Dy := D.Dy
  bound_Y := D.bound_Y
  bound_Yd := D.bound_Yd
  holder_Yd := D.holder_Yd
  remainder := D.remainder

end Weaken

/-! ### The Picard iteration -/

section Existence

variable [CompleteSpace E]
variable (V : RDEVectorField3 d E) (hX : IsLevel2RoughPath X ω α)
variable (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
variable (hfine : Sewing.HasFinePartitions ω)
variable (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
variable {δα : ℝ≥0}
variable (y₀ : E)

variable {Bb Bd By : ℝ≥0}

/-- The Picard iterates: starting from the constant path, apply the
Picard map and re-certify to the box at every step. All iterates carry
literal box constants and start at `y₀`. -/
noncomputable def picardSeq
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hBb : V.C0 ≤ Bb)
    (hBd : V.C1 * (d * Bb + By) ≤ Bd)
    (hBy : (Sewing.sewingConst (3 * α)).toNNReal *
        (d * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2) +
          d ^ 2 * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By))) * δα +
      d ^ 2 * (V.C1 * Bb) ≤ By) :
    ℕ → {Z : ControlledPath X ω α E //
      Z.Cb = Bb ∧ Z.Cd = Bd ∧ Z.Cy = By ∧ Z.Y 0 = y₀}
  | 0 =>
      ⟨(ControlledPath.const X ω α y₀).weaken
          (zero_le) (zero_le) (zero_le),
        rfl, rfl, rfl, rfl⟩
  | n + 1 =>
      let h := picardMap_inBox V hX hω1 hfine hωne y₀ hδα hBb hBd hBy
        ⟨le_of_eq (picardSeq hδα hBb hBd hBy n).2.1,
          le_of_eq (picardSeq hδα hBb hBd hBy n).2.2.1,
          le_of_eq (picardSeq hδα hBb hBd hBy n).2.2.2.1⟩
      ⟨(picardMap V hX hω1 hfine hωne y₀ hδα
          (picardSeq hδα hBb hBd hBy n).val).weaken h.1 h.2.1 h.2.2,
        rfl, rfl, rfl,
        picardMap_zero V hX hω1 hfine hωne y₀ hδα
          (picardSeq hδα hBb hBd hBy n).val⟩

/-- Distance certificates between consecutive Picard iterates. -/
noncomputable def picardSeqDist
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hδα1 : δα ≤ 1)
    (hBb : V.C0 ≤ Bb)
    (hBd : V.C1 * (d * Bb + By) ≤ Bd)
    (hBy : (Sewing.sewingConst (3 * α)).toNNReal *
        (d * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2) +
          d ^ 2 * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By))) * δα +
      d ^ 2 * (V.C1 * Bb) ≤ By) :
    ∀ n : ℕ,
      ControlledDist (picardSeq V hX hω1 hfine hωne y₀ hδα
          hBb hBd hBy (n + 1)).val
        (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val
  | 0 =>
      seedDist hX hω1 hδα
        (((picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy 1).2.2.2.2).trans
          ((picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy 0).2.2.2.2).symm)
        ⟨le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy 1).2.1,
          le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy 1).2.2.1,
          le_of_eq
            (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy 1).2.2.2.1⟩
        ⟨le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy 0).2.1,
          le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy 0).2.2.1,
          le_of_eq
            (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy 0).2.2.2.1⟩
  | n + 1 =>
      let h₁ := picardMap_inBox V hX hω1 hfine hωne y₀ hδα hBb hBd hBy
        ⟨le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα
            hBb hBd hBy (n + 1)).2.1,
          le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα
            hBb hBd hBy (n + 1)).2.2.1,
          le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα
            hBb hBd hBy (n + 1)).2.2.2.1⟩
      let h₂ := picardMap_inBox V hX hω1 hfine hωne y₀ hδα hBb hBd hBy
        ⟨le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα
            hBb hBd hBy n).2.1,
          le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα
            hBb hBd hBy n).2.2.1,
          le_of_eq (picardSeq V hX hω1 hfine hωne y₀ hδα
            hBb hBd hBy n).2.2.2.1⟩
      ControlledDist.ofWeaken
        (picardDist V hX hω1 hfine hωne y₀ hδα hδα1
          (picardSeqDist hδα hδα1 hBb hBd hBy n))
        h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2

/-- The weighted distance decays geometrically along the iteration. -/
theorem picardSeqDist_decay
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hδα1 : δα ≤ 1)
    (hBb : V.C0 ≤ Bb)
    (hBd : V.C1 * (d * Bb + By) ≤ Bd)
    (hBy : (Sewing.sewingConst (3 * α)).toNNReal *
        (d * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2) +
          d ^ 2 * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By))) * δα +
      d ^ 2 * (V.C1 * Bb) ≤ By)
    {wa wb wc we : ℝ≥0}
    (hcontr : ∀ (Z₁ Z₂ : ControlledPath X ω α E),
      Z₁.Cb = Bb → Z₁.Cd = Bd → Z₁.Cy = By →
      Z₂.Cb = Bb → Z₂.Cd = Bd → Z₂.Cy = By →
      ∀ D : ControlledDist Z₁ Z₂,
        2 * (wa * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).D0 +
          wb * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Db +
          wc * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dd +
          we * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dy) ≤
        wa * D.D0 + wb * D.Db + wc * D.Dd + we * D.Dy) :
    ∀ n : ℕ, 2 ^ n *
        (wa * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy n).D0 +
          wb * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy n).Db +
          wc * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy n).Dd +
          we * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy n).Dy) ≤
      wa * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
          hBb hBd hBy 0).D0 +
        wb * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
          hBb hBd hBy 0).Db +
        wc * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
          hBb hBd hBy 0).Dd +
        we * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
          hBb hBd hBy 0).Dy := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : 2 * (wa * (picardSeqDist V hX hω1 hfine hωne y₀ hδα
            hδα1 hBb hBd hBy (n + 1)).D0 +
          wb * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy (n + 1)).Db +
          wc * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy (n + 1)).Dd +
          we * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy (n + 1)).Dy) ≤
          wa * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy n).D0 +
          wb * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy n).Db +
          wc * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy n).Dd +
          we * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy n).Dy := by
        exact hcontr _ _
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy (n + 1)).2.1
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy (n + 1)).2.2.1
          (picardSeq V hX hω1 hfine hωne y₀ hδα
            hBb hBd hBy (n + 1)).2.2.2.1
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).2.1
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).2.2.1
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).2.2.2.1
          (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1 hBb hBd hBy n)
      calc 2 ^ (n + 1) * (wa * (picardSeqDist V hX hω1 hfine hωne y₀ hδα
            hδα1 hBb hBd hBy (n + 1)).D0 +
          wb * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy (n + 1)).Db +
          wc * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy (n + 1)).Dd +
          we * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
            hBb hBd hBy (n + 1)).Dy)
          = 2 ^ n * (2 * (wa * (picardSeqDist V hX hω1 hfine hωne y₀ hδα
              hδα1 hBb hBd hBy (n + 1)).D0 +
            wb * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
              hBb hBd hBy (n + 1)).Db +
            wc * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
              hBb hBd hBy (n + 1)).Dd +
            we * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
              hBb hBd hBy (n + 1)).Dy)) := by ring
        _ ≤ 2 ^ n * (wa * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
              hBb hBd hBy n).D0 +
            wb * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
              hBb hBd hBy n).Db +
            wc * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
              hBb hBd hBy n).Dd +
            we * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
              hBb hBd hBy n).Dy) := mul_le_mul' le_rfl hstep
        _ ≤ _ := ih

section Limit

variable (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
variable (hδα1 : δα ≤ 1)
variable (hBb : V.C0 ≤ Bb)
variable (hBd : V.C1 * (d * Bb + By) ≤ Bd)
variable (hBy : (Sewing.sewingConst (3 * α)).toNNReal *
    (d * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2) +
      d ^ 2 * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By))) * δα +
  d ^ 2 * (V.C1 * Bb) ≤ By)
variable {wa wb wc we : ℝ≥0}

/-- Shorthand for the weighted seed distance. -/
noncomputable def picardRho0 : ℝ≥0 :=
  wa * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
      hBb hBd hBy 0).D0 +
    wb * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
      hBb hBd hBy 0).Db +
    wc * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
      hBb hBd hBy 0).Dd +
    we * (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
      hBb hBd hBy 0).Dy

/-- Consecutive Picard iterates are geometrically close, pointwise. -/
theorem picardSeq_dist_le (hwa : 0 < wa)
    (hcontr : ∀ (Z₁ Z₂ : ControlledPath X ω α E),
      Z₁.Cb = Bb → Z₁.Cd = Bd → Z₁.Cy = By →
      Z₂.Cb = Bb → Z₂.Cd = Bd → Z₂.Cy = By →
      ∀ D : ControlledDist Z₁ Z₂,
        2 * (wa * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).D0 +
          wb * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Db +
          wc * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dd +
          we * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dy) ≤
        wa * D.D0 + wb * D.Db + wc * D.Dd + we * D.Dy)
    (n : ℕ) (u : ℝ) :
    dist ((picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val.Y u)
      ((picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy (n + 1)).val.Y u)
      ≤ ((picardRho0 V hX hω1 hfine hωne y₀ hδα hδα1 hBb hBd hBy
          (wa := wa) (wb := wb) (wc := wc) (we := we) : ℝ≥0) : ℝ) /
        (wa : ℝ) * (1 / 2) ^ n := by
  have hdecay := picardSeqDist_decay V hX hω1 hfine hωne y₀ hδα hδα1
    hBb hBd hBy hcontr n
  have hwa' : (2 : ℝ≥0) ^ n * (wa *
      (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
        hBb hBd hBy n).D0) ≤
      picardRho0 V hX hω1 hfine hωne y₀ hδα hδα1 hBb hBd hBy
        (wa := wa) (wb := wb) (wc := wc) (we := we) := by
    refine le_trans ?_ hdecay
    refine mul_le_mul' le_rfl ?_
    exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
      (le_add_of_le_of_nonneg le_rfl zero_le) zero_le) zero_le
  refine le_trans (dist_le_coe_of_enorm_le
    ((picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
      hBb hBd hBy n).bound_Y u)) ?_
  exact coe_le_geom_of_pow_mul_le hwa hwa'

/-- The Picard iterates converge pointwise: the limit path. -/
theorem picardSeq_cauchy (hwa : 0 < wa)
    (hcontr : ∀ (Z₁ Z₂ : ControlledPath X ω α E),
      Z₁.Cb = Bb → Z₁.Cd = Bd → Z₁.Cy = By →
      Z₂.Cb = Bb → Z₂.Cd = Bd → Z₂.Cy = By →
      ∀ D : ControlledDist Z₁ Z₂,
        2 * (wa * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).D0 +
          wb * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Db +
          wc * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dd +
          we * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dy) ≤
        wa * D.D0 + wb * D.Db + wc * D.Dd + we * D.Dy)
    (u : ℝ) :
    ∃ L : E, Filter.Tendsto (fun n =>
      (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val.Y u)
      Filter.atTop (nhds L) := by
  have hcauchy : CauchySeq (fun n =>
      (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val.Y u) := by
    refine cauchySeq_of_le_geometric (1 / 2)
      (((picardRho0 V hX hω1 hfine hωne y₀ hδα hδα1 hBb hBd hBy
        (wa := wa) (wb := wb) (wc := wc) (we := we) : ℝ≥0) : ℝ) /
        (wa : ℝ)) (by norm_num) ?_
    intro n
    exact picardSeq_dist_le V hX hω1 hfine hωne y₀ hδα hδα1
      hBb hBd hBy hwa hcontr n u
  exact cauchySeq_tendsto_of_complete hcauchy

/-- Consecutive Picard integrals are close, with the next distance
constant. -/
theorem picardIntegral_dist_le (n : ℕ) :
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖picardIntegral V hX hω1 hfine hωne
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy
            (n + 1)).val s t -
        picardIntegral V hX hω1 hfine hωne
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val
          s t‖ₑ ≤
      (((picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
        hBb hBd hBy (n + 1)).D0 : ℝ≥0) : ℝ≥0∞) :=
  integral_dist_bound V hX hω1 hfine hωne hδα hδα1
    (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1 hBb hBd hBy n)
    (picardIntegral_additive V hX hω1 hfine hωne _)
    (picardIntegral_additive V hX hω1 hfine hωne _)
    (picardIntegral_germ V hX hω1 hfine hωne _)
    (picardIntegral_germ V hX hω1 hfine hωne _)

/-- The Picard integrals converge pointwise on ordered pairs. -/
theorem picardIntegral_cauchy (hwa : 0 < wa)
    (hcontr : ∀ (Z₁ Z₂ : ControlledPath X ω α E),
      Z₁.Cb = Bb → Z₁.Cd = Bd → Z₁.Cy = By →
      Z₂.Cb = Bb → Z₂.Cd = Bd → Z₂.Cy = By →
      ∀ D : ControlledDist Z₁ Z₂,
        2 * (wa * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).D0 +
          wb * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Db +
          wc * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dd +
          we * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dy) ≤
        wa * D.D0 + wb * D.Db + wc * D.Dd + we * D.Dy)
    ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ∃ L : E, Filter.Tendsto (fun n =>
      picardIntegral V hX hω1 hfine hωne
        (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val s t)
      Filter.atTop (nhds L) := by
  have hstepd : ∀ n : ℕ, dist
      (picardIntegral V hX hω1 hfine hωne
        (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val s t)
      (picardIntegral V hX hω1 hfine hωne
        (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy
          (n + 1)).val s t) ≤
      ((picardRho0 V hX hω1 hfine hωne y₀ hδα hδα1 hBb hBd hBy
        (wa := wa) (wb := wb) (wc := wc) (we := we) : ℝ≥0) : ℝ) /
        (wa : ℝ) * (1 / 2) ^ n := by
    intro n
    have h1 := picardIntegral_dist_le V hX hω1 hfine hωne y₀ hδα hδα1
      hBb hBd hBy n hst
    have hdecay := picardSeqDist_decay V hX hω1 hfine hωne y₀ hδα hδα1
      hBb hBd hBy hcontr (n + 1)
    have hwa' : (2 : ℝ≥0) ^ (n + 1) * (wa *
        (picardSeqDist V hX hω1 hfine hωne y₀ hδα hδα1
          hBb hBd hBy (n + 1)).D0) ≤
        picardRho0 V hX hω1 hfine hωne y₀ hδα hδα1 hBb hBd hBy
          (wa := wa) (wb := wb) (wc := wc) (we := we) := by
      refine le_trans ?_ hdecay
      refine mul_le_mul' le_rfl ?_
      exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
        (le_add_of_le_of_nonneg le_rfl zero_le) zero_le) zero_le
    refine le_trans (dist_le_coe_of_enorm_le h1) ?_
    refine le_trans (coe_le_geom_of_pow_mul_le hwa hwa') ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
  have hcauchy : CauchySeq (fun n =>
      picardIntegral V hX hω1 hfine hωne
        (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val
        s t) :=
    cauchySeq_of_le_geometric (1 / 2)
      (((picardRho0 V hX hω1 hfine hωne y₀ hδα hδα1 hBb hBd hBy
        (wa := wa) (wb := wb) (wc := wc) (we := we) : ℝ≥0) : ℝ) /
        (wa : ℝ)) (by norm_num) hstepd
  exact cauchySeq_tendsto_of_complete hcauchy

include hBb hBd hBy in
/-- **Existence of RDE solutions** (Friz–Hairer Thm 8.3-type): under the
box-closure and weighted-contraction window conditions, the Picard
iterates converge to a box-certified solution of `dY = f(Y)·dX` started
at `y₀`. -/
theorem rde_exists (hwa : 0 < wa)
    (hcontr : ∀ (Z₁ Z₂ : ControlledPath X ω α E),
      Z₁.Cb = Bb → Z₁.Cd = Bd → Z₁.Cy = By →
      Z₂.Cb = Bb → Z₂.Cd = Bd → Z₂.Cy = By →
      ∀ D : ControlledDist Z₁ Z₂,
        2 * (wa * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).D0 +
          wb * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Db +
          wc * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dd +
          we * (picardDist V hX hω1 hfine hωne y₀ hδα hδα1 D).Dy) ≤
        wa * D.D0 + wb * D.Db + wc * D.Dd + we * D.Dy) :
    ∃ (Z : ControlledPath X ω α E) (I : ℝ → ℝ → E),
      V.IsRDESolution hX hω1 Z I ∧ Z.Y 0 = y₀ ∧ InBox Bb Bd By Z := by
  classical
  -- limits of the iterates and of their integrals
  have hY := fun u => picardSeq_cauchy V hX hω1 hfine hωne y₀ hδα hδα1
    hBb hBd hBy hwa hcontr u
  choose Ylim hYlim using hY
  have hIex : ∀ s t : ℝ, s ≤ t → ∃ L : E, Filter.Tendsto (fun n =>
      picardIntegral V hX hω1 hfine hωne
        (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val s t)
      Filter.atTop (nhds L) :=
    fun s t hst => picardIntegral_cauchy V hX hω1 hfine hωne y₀ hδα hδα1
      hBb hBd hBy hwa hcontr hst
  choose Ilim' hIlim' using hIex
  set Ilim : ℝ → ℝ → E := fun s t => if h : s ≤ t then Ilim' s t h else 0
    with hIlimdef
  have hIlim : ∀ ⦃s t : ℝ⦄ (hst : s ≤ t), Filter.Tendsto (fun n =>
      picardIntegral V hX hω1 hfine hωne
        (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val s t)
      Filter.atTop (nhds (Ilim s t)) := by
    intro s t hst
    rw [hIlimdef]
    simp only [dif_pos hst]
    exact hIlim' s t hst
  -- notation for the iterates
  set seqY : ℕ → ℝ → E := fun n =>
    (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val.Y
    with hseqYdef
  -- shifted limits
  have hYshift : ∀ u : ℝ, Filter.Tendsto (fun n => seqY (n + 1) u)
      Filter.atTop (nhds (Ylim u)) := by
    intro u
    exact (hYlim u).comp (Filter.tendsto_add_atTop_nat 1)
  -- continuity of the vector field along the limits
  have hf : ∀ (i : Fin d) (u : ℝ), Filter.Tendsto
      (fun n => V.f i (seqY n u)) Filter.atTop (nhds (V.f i (Ylim u))) :=
    fun i u => ((V.hasFDeriv i (Ylim u)).continuousAt.tendsto).comp
      (hYlim u)
  have hfshift : ∀ (i : Fin d) (u : ℝ), Filter.Tendsto
      (fun n => V.f i (seqY (n + 1) u)) Filter.atTop
      (nhds (V.f i (Ylim u))) :=
    fun i u => (hf i u).comp (Filter.tendsto_add_atTop_nat 1)
  -- increments of the iterates are the previous integrals
  have hinc : ∀ (n : ℕ) ⦃s t : ℝ⦄, s ≤ t →
      seqY (n + 1) t - seqY (n + 1) s =
        picardIntegral V hX hω1 hfine hωne
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val
          s t := by
    intro n s t hst
    exact basedPath_increment (picardIntegral_additive V hX hω1 hfine
      hωne _) y₀ hst
  -- the iterates' Gubinelli derivatives
  have hYd : ∀ (n : ℕ) (u : ℝ) (i : Fin d),
      (picardSeq V hX hω1 hfine hωne y₀ hδα
        hBb hBd hBy (n + 1)).val.Yd u i = V.f i (seqY n u) :=
    fun n u i => rfl
  -- the limit controlled path
  refine ⟨{ Y := Ylim
            Yd := fun u i => V.f i (Ylim u)
            Cb := Bb
            Cd := Bd
            Cy := By
            bound_Yd := ?_
            holder_Yd := ?_
            remainder := ?_ }, Ilim, ⟨?_, ?_, ?_, ?_⟩, ?_, le_rfl, le_rfl,
    le_rfl⟩
  · -- sup bound for the derivative
    intro u i
    refine le_trans (RDEVectorField.enorm_le_coe (V.bound_f i (Ylim u)))
      ?_
    exact_mod_cast hBb
  · -- Hölder bound for the derivative
    intro s t hst i
    refine le_trans (V.enorm_f_lipschitz i (Ylim t) (Ylim s)) ?_
    have hYinc : ‖Ylim t - Ylim s‖ₑ ≤
        (((d * Bb + By : ℝ≥0)) : ℝ≥0∞) * ω s t ^ α := by
      refine le_of_tendsto (((hYlim t).sub (hYlim s)).enorm)
        (Filter.Eventually.of_forall fun n => ?_)
      have h1 := RDEVectorField.increment_le hX hω1
        (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val hst
      refine le_trans h1 ?_
      refine mul_le_mul' (le_of_eq ?_) le_rfl
      rw [(picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).2.1,
        (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).2.2.2.1]
      push_cast
      ring
    calc (V.C1 : ℝ≥0∞) * ‖Ylim t - Ylim s‖ₑ
        ≤ (V.C1 : ℝ≥0∞) * ((((d * Bb + By : ℝ≥0)) : ℝ≥0∞) *
          ω s t ^ α) := mul_le_mul' le_rfl hYinc
      _ = (((V.C1 * (d * Bb + By) : ℝ≥0)) : ℝ≥0∞) * ω s t ^ α := by
          push_cast
          ring
      _ ≤ (Bd : ℝ≥0∞) * ω s t ^ α := by
          refine mul_le_mul' ?_ le_rfl
          exact_mod_cast hBd
  · -- remainder bound for the limit
    intro s t hst
    have hlim : Filter.Tendsto (fun n =>
        seqY (n + 1) t - seqY (n + 1) s -
          ∑ i, X.coeff s t [i] • V.f i (seqY n s))
        Filter.atTop (nhds (Ylim t - Ylim s -
          ∑ i, X.coeff s t [i] • V.f i (Ylim s))) := by
      refine ((hYshift t).sub (hYshift s)).sub ?_
      refine tendsto_finsetSum _ fun i _ => ?_
      exact (hf i s).const_smul _
    refine le_of_tendsto hlim.enorm
      (Filter.Eventually.of_forall fun n => ?_)
    have hrem := (picardSeq V hX hω1 hfine hωne y₀ hδα
      hBb hBd hBy (n + 1)).val.remainder hst
    have hCy : (picardSeq V hX hω1 hfine hωne y₀ hδα
        hBb hBd hBy (n + 1)).val.Cy = By :=
      (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy (n + 1)).2.2.2.1
    rw [hCy] at hrem
    exact hrem
  · -- the Gubinelli derivative is the vector field along the path
    intro u i
    rfl
  · -- additivity of the limit integral
    intro s u t hsu hut
    refine tendsto_nhds_unique (Filter.Tendsto.add (hIlim hsu)
      (hIlim hut)) ?_
    have heq : ∀ n : ℕ,
        picardIntegral V hX hω1 hfine hωne
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val s u +
        picardIntegral V hX hω1 hfine hωne
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val u t =
        picardIntegral V hX hω1 hfine hωne
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).val
          s t := fun n =>
      picardIntegral_additive V hX hω1 hfine hωne _ hsu hut
    exact (hIlim (le_trans hsu hut)).congr fun n => (heq n).symm
  · -- germ bound for the limit
    intro s t hst
    have hIshift : Filter.Tendsto (fun n =>
        picardIntegral V hX hω1 hfine hωne
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy
            (n + 1)).val s t)
        Filter.atTop (nhds (Ilim s t)) :=
      (hIlim hst).comp (Filter.tendsto_add_atTop_nat 1)
    have hYdentry : ∀ i j : Fin d, Filter.Tendsto (fun n =>
        V.deriv j (seqY (n + 1) s) (V.f i (seqY n s))) Filter.atTop
        (nhds (V.deriv j (Ylim s) (V.f i (Ylim s)))) := by
      intro i j
      rw [tendsto_iff_dist_tendsto_zero]
      have hle : ∀ n : ℕ,
          dist (V.deriv j (seqY (n + 1) s) (V.f i (seqY n s)))
            (V.deriv j (Ylim s) (V.f i (Ylim s))) ≤
          (V.C2 : ℝ) * V.C0 * dist (seqY (n + 1) s) (Ylim s) +
            (V.C1 : ℝ) * dist (V.f i (seqY n s)) (V.f i (Ylim s)) := by
        intro n
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
        have hsplit : V.deriv j (seqY (n + 1) s) (V.f i (seqY n s)) -
            V.deriv j (Ylim s) (V.f i (Ylim s)) =
            (V.deriv j (seqY (n + 1) s) - V.deriv j (Ylim s))
              (V.f i (seqY n s)) +
            V.deriv j (Ylim s) (V.f i (seqY n s) - V.f i (Ylim s)) := by
          simp only [sub_apply, map_sub]
          abel
        rw [hsplit]
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · calc ‖((V.deriv j (seqY (n + 1) s) - V.deriv j (Ylim s))
                (V.f i (seqY n s)))‖
              ≤ ‖V.deriv j (seqY (n + 1) s) - V.deriv j (Ylim s)‖ *
                ‖V.f i (seqY n s)‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ ((V.C2 : ℝ) * ‖seqY (n + 1) s - Ylim s‖) * V.C0 := by
                refine mul_le_mul (V.lipschitz_deriv j _ _)
                  (V.bound_f i _) (norm_nonneg _) (by positivity)
            _ = (V.C2 : ℝ) * V.C0 * ‖seqY (n + 1) s - Ylim s‖ := by ring
        · calc ‖(V.deriv j (Ylim s)
                (V.f i (seqY n s) - V.f i (Ylim s)))‖
              ≤ ‖V.deriv j (Ylim s)‖ *
                ‖V.f i (seqY n s) - V.f i (Ylim s)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ (V.C1 : ℝ) *
                ‖V.f i (seqY n s) - V.f i (Ylim s)‖ :=
                mul_le_mul_of_nonneg_right (V.bound_deriv j _)
                  (norm_nonneg _)
      refine squeeze_zero (fun n => dist_nonneg) hle ?_
      have h1 : Filter.Tendsto
          (fun n => dist (seqY (n + 1) s) (Ylim s))
          Filter.atTop (nhds 0) :=
        tendsto_iff_dist_tendsto_zero.1 (hYshift s)
      have h2 : Filter.Tendsto
          (fun n => dist (V.f i (seqY n s)) (V.f i (Ylim s)))
          Filter.atTop (nhds 0) :=
        tendsto_iff_dist_tendsto_zero.1 (hf i s)
      have hsum := (h1.const_mul ((V.C2 : ℝ) * V.C0)).add
        (h2.const_mul (V.C1 : ℝ))
      simpa using hsum
    have hgermlim : Filter.Tendsto (fun n =>
        gubinelliGerm (V.toRDEVectorField.compControlled hX hω1
          (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy
            (n + 1)).val) s t)
        Filter.atTop
        (nhds ((∑ i, X.coeff s t [i] • V.f i (Ylim s)) +
          ∑ i, ∑ j, X.coeff s t [i, j] •
            V.deriv j (Ylim s) (V.f i (Ylim s)))) := by
      simp only [gubinelliGerm_apply]
      refine Filter.Tendsto.add ?_ ?_
      · refine tendsto_finsetSum _ fun i _ => ?_
        exact (hfshift i s).const_smul _
      · refine tendsto_finsetSum _ fun i _ => ?_
        refine tendsto_finsetSum _ fun j _ => ?_
        exact (hYdentry i j).const_smul _
    refine le_of_tendsto (Filter.Tendsto.enorm (hIshift.sub hgermlim))
      (Filter.Eventually.of_forall fun n => ?_)
    exact picardIntegral_germ V hX hω1 hfine hωne
      (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy (n + 1)).val hst
  · -- increments of the limit are the limit integral
    intro s t hst
    refine tendsto_nhds_unique (((hYshift t).sub (hYshift s))) ?_
    exact (hIlim hst).congr fun n => (hinc n hst).symm
  · -- initial value
    refine tendsto_nhds_unique (hYlim 0) ?_
    have heq : ∀ n : ℕ, seqY n 0 = y₀ := fun n =>
      (picardSeq V hX hω1 hfine hωne y₀ hδα hBb hBd hBy n).2.2.2.2
    rw [show (fun n => seqY n 0) = fun _ => y₀ from funext heq]
    exact tendsto_const_nhds

end Limit

end Existence

end RoughPaths
