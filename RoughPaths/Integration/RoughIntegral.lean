/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Integration.ControlledPath
import RoughPaths.Sewing.Scaled
import RoughPaths.Sewing.Unique

/-!
# The rough integral (level 2)

The Gubinelli germ of a controlled path against a level-2 rough path is
`Ξ s t = Σᵢ X¹ᵢ(s,t)·Yᵢ(s) + Σᵢⱼ X²ᵢⱼ(s,t)·Y'ᵢⱼ(s)`. Chen's identity
makes its defect
`δΞ = -Σⱼ X¹ⱼ(u,t)·R_{su}(j) + Σᵢⱼ X²ᵢⱼ(u,t)·(Y'ᵢⱼ(s) - Y'ᵢⱼ(u))`,
of order `ω^{3α}` with `3α > 1`, so the additive sewing lemma produces the
**rough integral** `∫ Y dX` with the local estimate FH (4.21), unique
among additive maps with a germ bound of order greater than one, and
itself controlled by `X` with Gubinelli derivative `Y`. Only Chen's
identity is used — non-geometric (Itô-type) rough paths are covered.

## References

* P. Friz, M. Hairer, *A Course on Rough Paths*, Ch. 4
* M. Gubinelli, *Controlling rough paths*, J. Funct. Anal. 216 (2004)
-/

namespace RoughPaths

open HopfAlgebras

open scoped ENNReal NNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Chen's identity in level-1 and level-2 coordinates -/

theorem AlgebraicRoughPath.chen_coeff_one {T : Type*} {α₀ : Type*}
    {R : Type*} [Semiring R] (X : AlgebraicRoughPath T α₀ R) (s t u : T)
    (i : α₀) :
    X.coeff s u [i] = X.coeff s t [i] + X.coeff t u [i] := by
  simp only [AlgebraicRoughPath.coeff]
  rw [X.chen s t u, Word.tensorProduct_cons, Word.splits_nil]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    X.unitEmpty, one_mul, mul_one, add_zero]
  exact add_comm _ _

theorem AlgebraicRoughPath.chen_coeff_two {T : Type*} {α₀ : Type*}
    {R : Type*} [Semiring R] (X : AlgebraicRoughPath T α₀ R) (s t u : T)
    (i j : α₀) :
    X.coeff s u [i, j] =
      X.coeff s t [i, j] + X.coeff s t [i] * X.coeff t u [j] +
        X.coeff t u [i, j] := by
  simp only [AlgebraicRoughPath.coeff]
  rw [X.chen s t u, Word.tensorProduct_cons, Word.splits_cons,
    Word.splits_nil]
  simp only [List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, X.unitEmpty, one_mul, mul_one, add_zero]
  abel

/-! ### The Gubinelli germ and its defect -/

variable {X : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ} {α : ℝ}

/-- The Gubinelli germ of a controlled integrand: the two-term local
expansion of `∫_s^t Y dX`. -/
noncomputable def gubinelliGerm
    (Z : ControlledPath X ω α (Fin d → E)) : ℝ → ℝ → E :=
  fun s t => (∑ i, X.coeff s t [i] • Z.Y s i) +
    ∑ i, ∑ j, X.coeff s t [i, j] • Z.Yd s i j

theorem gubinelliGerm_apply (Z : ControlledPath X ω α (Fin d → E))
    (s t : ℝ) :
    gubinelliGerm Z s t = (∑ i, X.coeff s t [i] • Z.Y s i) +
      ∑ i, ∑ j, X.coeff s t [i, j] • Z.Yd s i j :=
  rfl

/-- **The algebraic defect identity**: by Chen's relations the germ's
defect is a remainder term paired with the first level plus a derivative
increment paired with the second level. -/
theorem gubinelliGerm_defect_eq (Z : ControlledPath X ω α (Fin d → E))
    (a b c : ℝ) :
    gubinelliGerm Z a c - gubinelliGerm Z a b - gubinelliGerm Z b c =
      (∑ j, X.coeff b c [j] •
        ((Z.Y a - Z.Y b + ∑ i, X.coeff a b [i] • Z.Yd a i) j)) +
      ∑ i, ∑ j, X.coeff b c [i, j] • (Z.Yd a i j - Z.Yd b i j) := by
  -- expand the level-1 block by Chen
  have hL : (∑ i, X.coeff a c [i] • Z.Y a i) =
      (∑ i, X.coeff a b [i] • Z.Y a i) +
        ∑ i, X.coeff b c [i] • Z.Y a i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [X.chen_coeff_one a b c i, add_smul]
  -- expand the level-2 block by Chen
  have hQ : (∑ i, ∑ j, X.coeff a c [i, j] • Z.Yd a i j) =
      (∑ i, ∑ j, X.coeff a b [i, j] • Z.Yd a i j) +
        ((∑ i, ∑ j, (X.coeff a b [i] * X.coeff b c [j]) • Z.Yd a i j) +
          ∑ i, ∑ j, X.coeff b c [i, j] • Z.Yd a i j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [X.chen_coeff_two a b c i j, add_smul, add_smul, add_assoc]
  -- the right side, expanded coordinatewise
  have hR : (∑ j, X.coeff b c [j] •
      ((Z.Y a - Z.Y b + ∑ i, X.coeff a b [i] • Z.Yd a i) j)) =
      ((∑ j, X.coeff b c [j] • Z.Y a j) -
        ∑ j, X.coeff b c [j] • Z.Y b j) +
        ∑ i, ∑ j, (X.coeff a b [i] * X.coeff b c [j]) • Z.Yd a i j := by
    have hcoord : ∀ j : Fin d,
        (Z.Y a - Z.Y b + ∑ i, X.coeff a b [i] • Z.Yd a i) j =
          Z.Y a j - Z.Y b j + ∑ i, X.coeff a b [i] • Z.Yd a i j := by
      intro j
      rw [Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
      refine congrArg (Z.Y a j - Z.Y b j + ·) ?_
      exact Finset.sum_congr rfl fun i _ => Pi.smul_apply _ _ _
    have hexp : ∀ j : Fin d, X.coeff b c [j] •
        ((Z.Y a - Z.Y b + ∑ i, X.coeff a b [i] • Z.Yd a i) j) =
        (X.coeff b c [j] • Z.Y a j - X.coeff b c [j] • Z.Y b j) +
          ∑ i, (X.coeff a b [i] * X.coeff b c [j]) • Z.Yd a i j := by
      intro j
      rw [hcoord j, smul_add, smul_sub, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm]
    rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_comm]
  have hS : (∑ i, ∑ j, X.coeff b c [i, j] •
      (Z.Yd a i j - Z.Yd b i j)) =
      (∑ i, ∑ j, X.coeff b c [i, j] • Z.Yd a i j) -
        ∑ i, ∑ j, X.coeff b c [i, j] • Z.Yd b i j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => smul_sub _ _ _
  rw [gubinelliGerm_apply, gubinelliGerm_apply, gubinelliGerm_apply,
    hL, hQ, hR, hS]
  abel

omit [NormedSpace ℝ E] in
/-- Coordinates of a `Pi`-valued vector are dominated by its sup norm. -/
theorem enorm_apply_le {f : Fin d → E} (j : Fin d) :
    ‖f j‖ₑ ≤ ‖f‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm f j)

/-- **The analytic defect bound**: the germ's defect has order
`ω^{3α}` with constant `d·Cy + d²·Cd`. -/
theorem gubinelliGerm_defect (hX : IsLevel2RoughPath X ω α)
    (Z : ControlledPath X ω α (Fin d → E)) :
    ∀ ⦃a b c : ℝ⦄, a ≤ b → b ≤ c →
      ‖gubinelliGerm Z a c - gubinelliGerm Z a b - gubinelliGerm Z b c‖ₑ ≤
        ((d : ℝ≥0∞) * Z.Cy + (d : ℝ≥0∞) ^ 2 * Z.Cd) * ω a c ^ (3 * α) := by
  intro a b c hab hbc
  have hα := hX.alpha_pos
  rw [gubinelliGerm_defect_eq Z a b c]
  refine le_trans (enorm_add_le _ _) ?_
  have hac_ab : ω a b ≤ ω a c := Sewing.control_mono ω le_rfl hab hbc
  have hac_bc : ω b c ≤ ω a c := Sewing.control_mono ω hab hbc le_rfl
  -- first block: `Σⱼ X¹ⱼ(b,c) • (-R_{ab})(j)`, of order `ω^α·ω^{2α}`
  have h1 : ‖∑ j, X.coeff b c [j] •
      ((Z.Y a - Z.Y b + ∑ i, X.coeff a b [i] • Z.Yd a i) j)‖ₑ ≤
      (d : ℝ≥0∞) * Z.Cy * ω a c ^ (3 * α) := by
    refine le_trans (enorm_fin_sum_le fun j => ?_)
      (le_of_eq (mul_assoc _ _ _).symm)
    rw [ControlledPath.enorm_real_smul]
    have hneg : (Z.Y a - Z.Y b + ∑ i, X.coeff a b [i] • Z.Yd a i) =
        -(Z.Y b - Z.Y a - ∑ i, X.coeff a b [i] • Z.Yd a i) := by abel
    have hcoord : ‖(Z.Y a - Z.Y b +
        ∑ i, X.coeff a b [i] • Z.Yd a i) j‖ₑ ≤
        Z.Cy * ω a b ^ (2 * α) := by
      refine le_trans (enorm_apply_le j) ?_
      rw [hneg, enorm_neg]
      exact Z.remainder hab
    calc ‖X.coeff b c [j]‖ₑ * ‖(Z.Y a - Z.Y b +
            ∑ i, X.coeff a b [i] • Z.Yd a i) j‖ₑ
        ≤ ω b c ^ α * (Z.Cy * ω a b ^ (2 * α)) :=
          mul_le_mul' (hX.bound_one hbc j) hcoord
      _ ≤ ω a c ^ α * (Z.Cy * ω a c ^ (2 * α)) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hac_bc hα.le)
            (mul_le_mul' le_rfl
              (ENNReal.rpow_le_rpow hac_ab (by positivity)))
      _ = Z.Cy * (ω a c ^ α * ω a c ^ (2 * α)) := by ring
      _ = Z.Cy * ω a c ^ (3 * α) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ hα.le (by positivity)]
          ring_nf
  -- second block: `Σᵢⱼ X²ᵢⱼ(b,c) • δYd`, of order `ω^{2α}·ω^α`
  have h2 : ‖∑ i, ∑ j, X.coeff b c [i, j] •
      (Z.Yd a i j - Z.Yd b i j)‖ₑ ≤
      (d : ℝ≥0∞) ^ 2 * Z.Cd * ω a c ^ (3 * α) := by
    refine le_trans (enorm_fin_sum_le
      (C := (d : ℝ≥0∞) * (Z.Cd * ω a c ^ (3 * α))) fun i =>
        enorm_fin_sum_le (C := Z.Cd * ω a c ^ (3 * α)) fun j => ?_)
      (le_of_eq (by ring))
    rw [ControlledPath.enorm_real_smul]
    have hYd : ‖Z.Yd a i j - Z.Yd b i j‖ₑ ≤ Z.Cd * ω a b ^ α := by
      have hpi : ‖Z.Yd b i - Z.Yd a i‖ₑ ≤ Z.Cd * ω a b ^ α :=
        Z.holder_Yd hab i
      have : ‖Z.Yd a i j - Z.Yd b i j‖ₑ =
          ‖(Z.Yd b i - Z.Yd a i) j‖ₑ := by
        rw [Pi.sub_apply, ← enorm_neg]
        congr 1
        abel
      rw [this]
      exact le_trans (enorm_apply_le j) hpi
    calc ‖X.coeff b c [i, j]‖ₑ * ‖Z.Yd a i j - Z.Yd b i j‖ₑ
        ≤ ω b c ^ (2 * α) * (Z.Cd * ω a b ^ α) :=
          mul_le_mul' (hX.bound_two hbc i j) hYd
      _ ≤ ω a c ^ (2 * α) * (Z.Cd * ω a c ^ α) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hac_bc (by positivity))
            (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hac_ab hα.le))
      _ = Z.Cd * (ω a c ^ (2 * α) * ω a c ^ α) := by ring
      _ = Z.Cd * ω a c ^ (3 * α) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) hα.le]
          ring_nf
  calc ‖∑ j, X.coeff b c [j] •
        ((Z.Y a - Z.Y b + ∑ i, X.coeff a b [i] • Z.Yd a i) j)‖ₑ +
      ‖∑ i, ∑ j, X.coeff b c [i, j] • (Z.Yd a i j - Z.Yd b i j)‖ₑ
      ≤ (d : ℝ≥0∞) * Z.Cy * ω a c ^ (3 * α) +
          (d : ℝ≥0∞) ^ 2 * Z.Cd * ω a c ^ (3 * α) := add_le_add h1 h2
    _ = ((d : ℝ≥0∞) * Z.Cy + (d : ℝ≥0∞) ^ 2 * Z.Cd) * ω a c ^ (3 * α) := by
        ring

/-! ### Existence, uniqueness, and controlledness of the rough integral -/

/-- The defect constant of a controlled path. -/
noncomputable def roughConst (Z : ControlledPath X ω α (Fin d → E)) :
    ℝ≥0∞ :=
  (d : ℝ≥0∞) * Z.Cy + (d : ℝ≥0∞) ^ 2 * Z.Cd

theorem roughConst_ne_top (Z : ControlledPath X ω α (Fin d → E)) :
    roughConst Z ≠ ⊤ :=
  ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) ENNReal.coe_ne_top,
      ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top d))
        ENNReal.coe_ne_top⟩

/-- **Existence of the rough integral** (Gubinelli; FH Thm 4.10): an
additive `∫ Y dX` with the local estimate
`‖∫_s^t Y dX - Σᵢ X¹ᵢ Yᵢ(s) - Σᵢⱼ X²ᵢⱼ Y'ᵢⱼ(s)‖ ≤ K·(d·Cy + d²·Cd)·ω^{3α}`,
approximating the compensated Riemann sums of every fine partition. -/
theorem exists_roughIntegral [CompleteSpace E]
    (hX : IsLevel2RoughPath X ω α)
    (Z : ControlledPath X ω α (Fin d → E))
    (hfine : Sewing.HasFinePartitions ω)
    (hω : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤) :
    ∃ I : ℝ → ℝ → E,
      (∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I s u + I u t = I s t) ∧
      (∀ ⦃s t : ℝ⦄, s ≤ t →
        ‖I s t - gubinelliGerm Z s t‖ₑ ≤
          Sewing.sewingConst (3 * α) *
            (roughConst Z * ω s t ^ (3 * α))) ∧
      (∀ ⦃s t : ℝ⦄, s ≤ t → ∀ (ε : ℝ≥0∞) (mid : List ℝ),
        List.IsChain (fun a b => a ≤ b ∧
          Control.constMul (roughConst Z ^ (3 * α)⁻¹) ω a b ≤ ε)
          (s :: (mid ++ [t])) →
        ‖I s t - Sewing.pairSum (gubinelliGerm Z) (s :: (mid ++ [t]))‖ₑ ≤
          Sewing.sewingConst (3 * α) *
            (ε ^ (3 * α - 1) *
              Control.constMul (roughConst Z ^ (3 * α)⁻¹) ω s t)) := by
  have hα := hX.alpha_pos
  exact Sewing.sewing_const_mul ω (gubinelliGerm Z) hX.one_lt_three_alpha
    (by positivity) (roughConst_ne_top Z) (gubinelliGerm_defect hX Z)
    hfine hω

/-- **Uniqueness of the rough integral** among additive maps with a
germ bound of order `3α > 1`. -/
theorem roughIntegral_unique (hX : IsLevel2RoughPath X ω α)
    (Z : ControlledPath X ω α (Fin d → E))
    {C C' : ℝ≥0∞} (hC : C ≠ ⊤) (hC' : C' ≠ ⊤)
    (hfine : Sewing.HasFinePartitions ω)
    {I I' : ℝ → ℝ → E}
    (hadd : ∀ ⦃a u b : ℝ⦄, a ≤ u → u ≤ b → I a u + I u b = I a b)
    (hadd' : ∀ ⦃a u b : ℝ⦄, a ≤ u → u ≤ b → I' a u + I' u b = I' a b)
    (hI : ∀ ⦃a b : ℝ⦄, a ≤ b → ‖I a b - gubinelliGerm Z a b‖ₑ ≤
      C * ω a b ^ (3 * α))
    (hI' : ∀ ⦃a b : ℝ⦄, a ≤ b → ‖I' a b - gubinelliGerm Z a b‖ₑ ≤
      C' * ω a b ^ (3 * α))
    {s t : ℝ} (hst : s ≤ t) (hω : ω s t ≠ ⊤) :
    I s t = I' s t :=
  Sewing.eq_of_additive_of_germ_bound ω (gubinelliGerm Z)
    hX.one_lt_three_alpha hC hC' hfine hadd hadd' hI hI' hst hω

/-- **The rough integral is controlled by `X` with Gubinelli derivative
`Y`**: subtracting only the first-level part leaves a remainder of order
`ω^{2α}` plus the higher-order sewing error. -/
theorem roughIntegral_sub_linear (hX : IsLevel2RoughPath X ω α)
    (Z : ControlledPath X ω α (Fin d → E)) {I : ℝ → ℝ → E}
    (hgerm : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I s t - gubinelliGerm Z s t‖ₑ ≤
        Sewing.sewingConst (3 * α) * (roughConst Z * ω s t ^ (3 * α)))
    ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖I s t - ∑ i, X.coeff s t [i] • Z.Y s i‖ₑ ≤
      Sewing.sewingConst (3 * α) * (roughConst Z * ω s t ^ (3 * α)) +
        (d : ℝ≥0∞) ^ 2 * Z.Cb * ω s t ^ (2 * α) := by
  have hsplit : I s t - ∑ i, X.coeff s t [i] • Z.Y s i =
      (I s t - gubinelliGerm Z s t) +
        ∑ i, ∑ j, X.coeff s t [i, j] • Z.Yd s i j := by
    rw [gubinelliGerm_apply]
    abel
  rw [hsplit]
  refine le_trans (enorm_add_le _ _) (add_le_add (hgerm hst) ?_)
  refine le_trans (enorm_fin_sum_le
    (C := (d : ℝ≥0∞) * (Z.Cb * ω s t ^ (2 * α))) fun i =>
      enorm_fin_sum_le (C := Z.Cb * ω s t ^ (2 * α)) fun j => ?_)
    (le_of_eq (by ring))
  rw [ControlledPath.enorm_real_smul]
  exact le_trans (mul_le_mul' (hX.bound_two hst i j)
    (le_trans (enorm_apply_le j) (Z.bound_Yd s i)))
    (le_of_eq (mul_comm _ _))

end RoughPaths
