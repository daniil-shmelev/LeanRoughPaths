/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.RDE.Picard
import RoughPaths.Integration.Metric

/-!
# Stability of the rough integral and RDE solutions in the driver

The two-driver stability calculus behind the continuity of the
Itô–Lyons map (Friz–Hairer §8.3): controlled paths over *different*
level-2 rough paths `X₁, X₂` at certified distance `(ρ₁, ρ₂)`
(`RoughPathDist`) are compared through `MixedDist` certificates, whose
remainder slot measures the difference of the two *own-driver*
remainders. Every one-driver estimate of `RDE/Stability` and
`RDE/Picard` has a two-driver analogue here, with the same certificate
formulas plus explicit `ρ`-offsets:

* `MixedDist.increment_sub_le` — increment of the difference path;
* `mixed_germ_defect` — the defect of the *difference of germs* is of
  order `ω^{3α}` with constant `d(Dy + ρ₁Cy) + d²(Dd + ρ₂Cd)`;
* `mixedIntegral_sub` — sewing: the difference of the two rough
  integrals is within `K·(mixed constant)·ω^{3α}` of the germ
  difference;
* `mixed_integral_dist_bound` / `mixed_integral_sub_germ_folded` — the
  window-gain forms feeding the distance-step slots.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ} {E W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {X₁ X₂ : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ}
variable {α : ℝ} {ρ₁ ρ₂ : ℝ≥0}

/-- Certified distance data between controlled paths over *different*
drivers. The remainder slot bounds the difference of the two own-driver
remainders (Friz–Hairer's "distance with different rough paths"). -/
structure MixedDist (Z₁ : ControlledPath X₁ ω α W)
    (Z₂ : ControlledPath X₂ ω α W) where
  /-- Sup bound for the difference of paths. -/
  D0 : ℝ≥0
  /-- Sup bound for the difference of derivatives. -/
  Db : ℝ≥0
  /-- Hölder constant of the difference of derivatives. -/
  Dd : ℝ≥0
  /-- Bound for the difference of the own-driver remainders. -/
  Dy : ℝ≥0
  bound_Y : ∀ s : ℝ, ‖Z₁.Y s - Z₂.Y s‖ₑ ≤ D0
  bound_Yd : ∀ (s : ℝ) (i : Fin d), ‖Z₁.Yd s i - Z₂.Yd s i‖ₑ ≤ Db
  holder_Yd : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ i : Fin d,
    ‖Z₁.Yd t i - Z₂.Yd t i - (Z₁.Yd s i - Z₂.Yd s i)‖ₑ ≤ Dd * ω s t ^ α
  remainder : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖Z₁.Y t - Z₁.Y s - (∑ i, X₁.coeff s t [i] • Z₁.Yd s i) -
        (Z₂.Y t - Z₂.Y s - ∑ i, X₂.coeff s t [i] • Z₂.Yd s i)‖ₑ ≤
      Dy * ω s t ^ (2 * α)

/-- Splitting a difference of scaled sums into a coefficient-difference
part and a data-difference part. -/
private theorem sum_smul_pair_split {n : ℕ} (a b : Fin n → ℝ)
    (u v : Fin n → W) :
    (∑ i, a i • u i) - ∑ i, b i • v i =
      (∑ i, (a i - b i) • u i) + ∑ i, b i • (u i - v i) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_smul, smul_sub]
  abel

namespace MixedDist

variable {Z₁ : ControlledPath X₁ ω α W} {Z₂ : ControlledPath X₂ ω α W}

/-- The increment of the difference of two controlled paths over
different drivers: the one-driver bound plus the offset `d·ρ₁·Cb₁`. -/
theorem increment_sub_le (hX₂ : IsLevel2RoughPath X₂ ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (hXd : RoughPathDist X₁ X₂ ω α ρ₁ ρ₂)
    (D : MixedDist Z₁ Z₂) ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s)‖ₑ ≤
      ((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) + D.Dy) *
        ω s t ^ α := by
  have hα := hX₂.alpha_pos
  have hω_le_one : ω s t ^ α ≤ 1 :=
    le_trans (ENNReal.rpow_le_rpow (hω1 hst) hα.le)
      (le_of_eq (ENNReal.one_rpow α))
  have hsplit : Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s) =
      (Z₁.Y t - Z₁.Y s - (∑ i, X₁.coeff s t [i] • Z₁.Yd s i) -
        (Z₂.Y t - Z₂.Y s - ∑ i, X₂.coeff s t [i] • Z₂.Yd s i)) +
      ((∑ i, (X₁.coeff s t [i] - X₂.coeff s t [i]) • Z₁.Yd s i) +
        ∑ i, X₂.coeff s t [i] • (Z₁.Yd s i - Z₂.Yd s i)) := by
    rw [← sum_smul_pair_split]
    abel
  rw [hsplit]
  have h1 : ‖∑ i, (X₁.coeff s t [i] - X₂.coeff s t [i]) • Z₁.Yd s i‖ₑ ≤
      (d : ℝ≥0∞) * ((ρ₁ : ℝ≥0∞) * ω s t ^ α * Z₁.Cb) := by
    refine enorm_fin_sum_le fun i => ?_
    rw [ControlledPath.enorm_real_smul]
    exact mul_le_mul' (hXd.bound_one hst i) (Z₁.bound_Yd s i)
  have h2 : ‖∑ i, X₂.coeff s t [i] • (Z₁.Yd s i - Z₂.Yd s i)‖ₑ ≤
      (d : ℝ≥0∞) * (ω s t ^ α * D.Db) := by
    refine enorm_fin_sum_le fun i => ?_
    rw [ControlledPath.enorm_real_smul]
    exact mul_le_mul' (hX₂.bound_one hst i) (D.bound_Yd s i)
  have hrem : (D.Dy : ℝ≥0∞) * ω s t ^ (2 * α) ≤
      (D.Dy : ℝ≥0∞) * ω s t ^ α := by
    refine mul_le_mul' le_rfl ?_
    rw [rpow_two_mul_eq hα.le]
    exact le_trans (mul_le_mul' le_rfl hω_le_one) (le_of_eq (mul_one _))
  refine le_trans (enorm_add_le _ _) ?_
  refine le_trans (add_le_add (le_trans (D.remainder hst) hrem)
    (le_trans (enorm_add_le _ _) (add_le_add h1 h2))) (le_of_eq ?_)
  ring

end MixedDist

/-! ### The difference of two Gubinelli germs -/

section Germ

variable {Z₁' : ControlledPath X₁ ω α (Fin d → E)}
variable {Z₂' : ControlledPath X₂ ω α (Fin d → E)}

/-- Sup bound for the difference of two Gubinelli germs over different
drivers, from a sup bound `B₁` on the first integrand. -/
theorem enorm_gubinelliGerm_sub_le (hX₂ : IsLevel2RoughPath X₂ ω α)
    (hXd : RoughPathDist X₁ X₂ ω α ρ₁ ρ₂)
    (DW : MixedDist Z₁' Z₂') {B₁ : ℝ≥0}
    (hB₁ : ∀ s : ℝ, ‖Z₁'.Y s‖ₑ ≤ B₁) ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖gubinelliGerm Z₁' s t - gubinelliGerm Z₂' s t‖ₑ ≤
      (d : ℝ≥0∞) * ((DW.D0 : ℝ≥0∞) + ρ₁ * B₁) * ω s t ^ α +
        (d : ℝ≥0∞) ^ 2 * ((DW.Db : ℝ≥0∞) + ρ₂ * Z₁'.Cb) *
          ω s t ^ (2 * α) := by
  rw [gubinelliGerm_apply, gubinelliGerm_apply]
  have hsplit : (∑ i, X₁.coeff s t [i] • Z₁'.Y s i) +
      (∑ i, ∑ j, X₁.coeff s t [i, j] • Z₁'.Yd s i j) -
      ((∑ i, X₂.coeff s t [i] • Z₂'.Y s i) +
        ∑ i, ∑ j, X₂.coeff s t [i, j] • Z₂'.Yd s i j) =
      ((∑ i, (X₁.coeff s t [i] - X₂.coeff s t [i]) • Z₁'.Y s i) +
        ∑ i, X₂.coeff s t [i] • (Z₁'.Y s i - Z₂'.Y s i)) +
      ((∑ i, ∑ j,
          (X₁.coeff s t [i, j] - X₂.coeff s t [i, j]) • Z₁'.Yd s i j) +
        ∑ i, ∑ j, X₂.coeff s t [i, j] • (Z₁'.Yd s i j - Z₂'.Yd s i j)) := by
    rw [← sum_smul_pair_split]
    have h2 : (∑ i, ∑ j, X₁.coeff s t [i, j] • Z₁'.Yd s i j) -
        ∑ i, ∑ j, X₂.coeff s t [i, j] • Z₂'.Yd s i j =
        (∑ i, ∑ j,
          (X₁.coeff s t [i, j] - X₂.coeff s t [i, j]) • Z₁'.Yd s i j) +
        ∑ i, ∑ j, X₂.coeff s t [i, j] • (Z₁'.Yd s i j - Z₂'.Yd s i j) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sum_smul_pair_split]
    rw [← h2]
    abel
  rw [hsplit]
  have hL1 : ‖∑ i, (X₁.coeff s t [i] - X₂.coeff s t [i]) •
      Z₁'.Y s i‖ₑ ≤
      (d : ℝ≥0∞) * ((ρ₁ : ℝ≥0∞) * ω s t ^ α * B₁) := by
    refine enorm_fin_sum_le fun i => ?_
    rw [ControlledPath.enorm_real_smul]
    exact mul_le_mul' (hXd.bound_one hst i)
      (le_trans (enorm_apply_le i) (hB₁ s))
  have hL2 : ‖∑ i, X₂.coeff s t [i] • (Z₁'.Y s i - Z₂'.Y s i)‖ₑ ≤
      (d : ℝ≥0∞) * (ω s t ^ α * DW.D0) := by
    refine enorm_fin_sum_le fun i => ?_
    rw [ControlledPath.enorm_real_smul]
    refine mul_le_mul' (hX₂.bound_one hst i) ?_
    have hco : Z₁'.Y s i - Z₂'.Y s i = (Z₁'.Y s - Z₂'.Y s) i := rfl
    rw [hco]
    exact le_trans (enorm_apply_le i) (DW.bound_Y s)
  have hQ1 : ‖∑ i, ∑ j,
      (X₁.coeff s t [i, j] - X₂.coeff s t [i, j]) • Z₁'.Yd s i j‖ₑ ≤
      (d : ℝ≥0∞) * ((d : ℝ≥0∞) *
        ((ρ₂ : ℝ≥0∞) * ω s t ^ (2 * α) * Z₁'.Cb)) := by
    refine enorm_fin_sum_le fun i => enorm_fin_sum_le fun j => ?_
    rw [ControlledPath.enorm_real_smul]
    exact mul_le_mul' (hXd.bound_two hst i j)
      (le_trans (enorm_apply_le j) (Z₁'.bound_Yd s i))
  have hQ2 : ‖∑ i, ∑ j, X₂.coeff s t [i, j] •
      (Z₁'.Yd s i j - Z₂'.Yd s i j)‖ₑ ≤
      (d : ℝ≥0∞) * ((d : ℝ≥0∞) * (ω s t ^ (2 * α) * DW.Db)) := by
    refine enorm_fin_sum_le fun i => enorm_fin_sum_le fun j => ?_
    rw [ControlledPath.enorm_real_smul]
    refine mul_le_mul' (hX₂.bound_two hst i j) ?_
    have hco : Z₁'.Yd s i j - Z₂'.Yd s i j =
        (Z₁'.Yd s i - Z₂'.Yd s i) j := rfl
    rw [hco]
    exact le_trans (enorm_apply_le j) (DW.bound_Yd s i)
  refine le_trans (enorm_add_le _ _) ?_
  refine le_trans (add_le_add
    (le_trans (enorm_add_le _ _) (add_le_add hL1 hL2))
    (le_trans (enorm_add_le _ _) (add_le_add hQ1 hQ2))) (le_of_eq ?_)
  ring


/-- The mixed defect constant: the one-driver `d·Dy + d²·Dd` with the
driver-distance offsets `d·ρ₁·Cy₁ + d²·ρ₂·Cd₁`. -/
noncomputable def mixedRoughConstN
    (Z₁' : ControlledPath X₁ ω α (Fin d → E))
    (DW : MixedDist Z₁' Z₂') (ρ₁ ρ₂ : ℝ≥0) : ℝ≥0 :=
  d * (DW.Dy + ρ₁ * Z₁'.Cy) + d ^ 2 * (DW.Dd + ρ₂ * Z₁'.Cd)

/-- **The mixed defect bound**: the defect of the difference of the two
Gubinelli germs is of order `ω^{3α}` with the mixed constant. This is
the two-driver core of the Itô–Lyons continuity. -/
theorem mixed_germ_defect (hX₁ : IsLevel2RoughPath X₁ ω α)
    (hX₂ : IsLevel2RoughPath X₂ ω α)
    (hXd : RoughPathDist X₁ X₂ ω α ρ₁ ρ₂)
    (DW : MixedDist Z₁' Z₂') :
    ∀ ⦃a b c : ℝ⦄, a ≤ b → b ≤ c →
      ‖(gubinelliGerm Z₁' a c - gubinelliGerm Z₂' a c) -
          (gubinelliGerm Z₁' a b - gubinelliGerm Z₂' a b) -
          (gubinelliGerm Z₁' b c - gubinelliGerm Z₂' b c)‖ₑ ≤
        ((mixedRoughConstN Z₁' DW ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞) *
          ω a c ^ (3 * α) := by
  intro a b c hab hbc
  have hα := hX₁.alpha_pos
  have hac_ab : ω a b ≤ ω a c := Sewing.control_mono ω le_rfl hab hbc
  have hac_bc : ω b c ≤ ω a c := Sewing.control_mono ω hab hbc le_rfl
  have hre : (gubinelliGerm Z₁' a c - gubinelliGerm Z₂' a c) -
      (gubinelliGerm Z₁' a b - gubinelliGerm Z₂' a b) -
      (gubinelliGerm Z₁' b c - gubinelliGerm Z₂' b c) =
      (gubinelliGerm Z₁' a c - gubinelliGerm Z₁' a b -
        gubinelliGerm Z₁' b c) -
      (gubinelliGerm Z₂' a c - gubinelliGerm Z₂' a b -
        gubinelliGerm Z₂' b c) := by abel
  rw [hre, gubinelliGerm_defect_eq Z₁' a b c,
    gubinelliGerm_defect_eq Z₂' a b c]
  -- notation for the two blocks of each defect
  set N₁ : Fin d → E := fun j =>
    (Z₁'.Y a - Z₁'.Y b + ∑ i, X₁.coeff a b [i] • Z₁'.Yd a i) j with hN₁
  set N₂ : Fin d → E := fun j =>
    (Z₂'.Y a - Z₂'.Y b + ∑ i, X₂.coeff a b [i] • Z₂'.Yd a i) j with hN₂
  have hsplit : (∑ j, X₁.coeff b c [j] • N₁ j) +
      (∑ i, ∑ j, X₁.coeff b c [i, j] • (Z₁'.Yd a i j - Z₁'.Yd b i j)) -
      ((∑ j, X₂.coeff b c [j] • N₂ j) +
        ∑ i, ∑ j, X₂.coeff b c [i, j] • (Z₂'.Yd a i j - Z₂'.Yd b i j)) =
      ((∑ j, (X₁.coeff b c [j] - X₂.coeff b c [j]) • N₁ j) +
        ∑ j, X₂.coeff b c [j] • (N₁ j - N₂ j)) +
      ((∑ i, ∑ j, (X₁.coeff b c [i, j] - X₂.coeff b c [i, j]) •
          (Z₁'.Yd a i j - Z₁'.Yd b i j)) +
        ∑ i, ∑ j, X₂.coeff b c [i, j] •
          (Z₁'.Yd a i j - Z₁'.Yd b i j - (Z₂'.Yd a i j - Z₂'.Yd b i j))) := by
    rw [← sum_smul_pair_split]
    have h2 : (∑ i, ∑ j, X₁.coeff b c [i, j] •
        (Z₁'.Yd a i j - Z₁'.Yd b i j)) -
        ∑ i, ∑ j, X₂.coeff b c [i, j] •
          (Z₂'.Yd a i j - Z₂'.Yd b i j) =
        (∑ i, ∑ j, (X₁.coeff b c [i, j] - X₂.coeff b c [i, j]) •
          (Z₁'.Yd a i j - Z₁'.Yd b i j)) +
        ∑ i, ∑ j, X₂.coeff b c [i, j] •
          (Z₁'.Yd a i j - Z₁'.Yd b i j -
            (Z₂'.Yd a i j - Z₂'.Yd b i j)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sum_smul_pair_split]
    rw [← h2]
    abel
  rw [hsplit]
  -- bounds on the four blocks
  have hN₁bound : ∀ j : Fin d, ‖N₁ j‖ₑ ≤
      (Z₁'.Cy : ℝ≥0∞) * ω a b ^ (2 * α) := by
    intro j
    rw [hN₁]
    have hneg : (Z₁'.Y a - Z₁'.Y b + ∑ i, X₁.coeff a b [i] • Z₁'.Yd a i) =
        -(Z₁'.Y b - Z₁'.Y a - ∑ i, X₁.coeff a b [i] • Z₁'.Yd a i) := by
      abel
    refine le_trans (enorm_apply_le j) ?_
    rw [hneg, enorm_neg]
    exact Z₁'.remainder hab
  have hNdiff : ∀ j : Fin d, ‖N₁ j - N₂ j‖ₑ ≤
      (DW.Dy : ℝ≥0∞) * ω a b ^ (2 * α) := by
    intro j
    rw [hN₁, hN₂]
    have hcoord : (Z₁'.Y a - Z₁'.Y b +
        ∑ i, X₁.coeff a b [i] • Z₁'.Yd a i) j -
        (Z₂'.Y a - Z₂'.Y b + ∑ i, X₂.coeff a b [i] • Z₂'.Yd a i) j =
        (-(Z₁'.Y b - Z₁'.Y a - (∑ i, X₁.coeff a b [i] • Z₁'.Yd a i) -
          (Z₂'.Y b - Z₂'.Y a - ∑ i, X₂.coeff a b [i] • Z₂'.Yd a i))) j := by
      simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply]
      abel
    rw [hcoord]
    refine le_trans (enorm_apply_le j) ?_
    rw [enorm_neg]
    exact DW.remainder hab
  have hM₁bound : ∀ i j : Fin d, ‖Z₁'.Yd a i j - Z₁'.Yd b i j‖ₑ ≤
      (Z₁'.Cd : ℝ≥0∞) * ω a b ^ α := by
    intro i j
    have hpi : ‖Z₁'.Yd b i - Z₁'.Yd a i‖ₑ ≤ Z₁'.Cd * ω a b ^ α :=
      Z₁'.holder_Yd hab i
    have hco : ‖Z₁'.Yd a i j - Z₁'.Yd b i j‖ₑ =
        ‖(Z₁'.Yd b i - Z₁'.Yd a i) j‖ₑ := by
      rw [Pi.sub_apply, ← enorm_neg]
      congr 1
      abel
    rw [hco]
    exact le_trans (enorm_apply_le j) hpi
  have hMdiff : ∀ i j : Fin d,
      ‖Z₁'.Yd a i j - Z₁'.Yd b i j - (Z₂'.Yd a i j - Z₂'.Yd b i j)‖ₑ ≤
        (DW.Dd : ℝ≥0∞) * ω a b ^ α := by
    intro i j
    have hpi := DW.holder_Yd hab i
    have hco : ‖Z₁'.Yd a i j - Z₁'.Yd b i j -
        (Z₂'.Yd a i j - Z₂'.Yd b i j)‖ₑ =
        ‖(Z₁'.Yd b i - Z₂'.Yd b i - (Z₁'.Yd a i - Z₂'.Yd a i)) j‖ₑ := by
      rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, ← enorm_neg]
      congr 1
      abel
    rw [hco]
    exact le_trans (enorm_apply_le j) hpi
  -- assemble, all against `ω a c`
  have hbc_one : ∀ j, ‖X₂.coeff b c [j]‖ₑ ≤ ω a c ^ α := fun j =>
    le_trans (hX₂.bound_one hbc j) (ENNReal.rpow_le_rpow hac_bc hα.le)
  have hbc_oned : ∀ j,
      ‖X₁.coeff b c [j] - X₂.coeff b c [j]‖ₑ ≤
        (ρ₁ : ℝ≥0∞) * ω a c ^ α := fun j =>
    le_trans (hXd.bound_one hbc j)
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hac_bc hα.le))
  have hbc_two : ∀ i j, ‖X₂.coeff b c [i, j]‖ₑ ≤ ω a c ^ (2 * α) :=
    fun i j => le_trans (hX₂.bound_two hbc i j)
      (ENNReal.rpow_le_rpow hac_bc (by positivity))
  have hbc_twod : ∀ i j,
      ‖X₁.coeff b c [i, j] - X₂.coeff b c [i, j]‖ₑ ≤
        (ρ₂ : ℝ≥0∞) * ω a c ^ (2 * α) := fun i j =>
    le_trans (hXd.bound_two hbc i j)
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hac_bc (by positivity)))
  have hab2 : ω a b ^ (2 * α) ≤ ω a c ^ (2 * α) :=
    ENNReal.rpow_le_rpow hac_ab (by positivity)
  have hab1 : ω a b ^ α ≤ ω a c ^ α :=
    ENNReal.rpow_le_rpow hac_ab hα.le
  have h3 : ω a c ^ α * ω a c ^ (2 * α) = ω a c ^ (3 * α) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ hα.le (by positivity)]
    ring_nf
  have hB1 : ‖∑ j, (X₁.coeff b c [j] - X₂.coeff b c [j]) • N₁ j‖ₑ ≤
      (d : ℝ≥0∞) * ((ρ₁ : ℝ≥0∞) * ω a c ^ α *
        (Z₁'.Cy * ω a c ^ (2 * α))) := by
    refine enorm_fin_sum_le fun j => ?_
    rw [ControlledPath.enorm_real_smul]
    exact mul_le_mul' (hbc_oned j)
      (le_trans (hN₁bound j) (mul_le_mul' le_rfl hab2))
  have hB2 : ‖∑ j, X₂.coeff b c [j] • (N₁ j - N₂ j)‖ₑ ≤
      (d : ℝ≥0∞) * (ω a c ^ α * (DW.Dy * ω a c ^ (2 * α))) := by
    refine enorm_fin_sum_le fun j => ?_
    rw [ControlledPath.enorm_real_smul]
    exact mul_le_mul' (hbc_one j)
      (le_trans (hNdiff j) (mul_le_mul' le_rfl hab2))
  have hB3 : ‖∑ i, ∑ j, (X₁.coeff b c [i, j] - X₂.coeff b c [i, j]) •
      (Z₁'.Yd a i j - Z₁'.Yd b i j)‖ₑ ≤
      (d : ℝ≥0∞) * ((d : ℝ≥0∞) * ((ρ₂ : ℝ≥0∞) * ω a c ^ (2 * α) *
        (Z₁'.Cd * ω a c ^ α))) := by
    refine enorm_fin_sum_le fun i => enorm_fin_sum_le fun j => ?_
    rw [ControlledPath.enorm_real_smul]
    exact mul_le_mul' (hbc_twod i j)
      (le_trans (hM₁bound i j) (mul_le_mul' le_rfl hab1))
  have hB4 : ‖∑ i, ∑ j, X₂.coeff b c [i, j] •
      (Z₁'.Yd a i j - Z₁'.Yd b i j - (Z₂'.Yd a i j - Z₂'.Yd b i j))‖ₑ ≤
      (d : ℝ≥0∞) * ((d : ℝ≥0∞) *
        (ω a c ^ (2 * α) * (DW.Dd * ω a c ^ α))) := by
    refine enorm_fin_sum_le fun i => enorm_fin_sum_le fun j => ?_
    rw [ControlledPath.enorm_real_smul]
    exact mul_le_mul' (hbc_two i j)
      (le_trans (hMdiff i j) (mul_le_mul' le_rfl hab1))
  refine le_trans (enorm_add_le _ _) ?_
  refine le_trans (add_le_add
    (le_trans (enorm_add_le _ _) (add_le_add hB1 hB2))
    (le_trans (enorm_add_le _ _) (add_le_add hB3 hB4))) (le_of_eq ?_)
  rw [mixedRoughConstN, ← h3]
  push_cast
  ring

/-- **Two-driver stability of the rough integral**: the difference of
two rough integrals over different drivers is within the *mixed* germ
constant of the difference of the germs. -/
theorem mixedIntegral_sub [CompleteSpace E]
    (hX₁ : IsLevel2RoughPath X₁ ω α) (hX₂ : IsLevel2RoughPath X₂ ω α)
    (hXd : RoughPathDist X₁ X₂ ω α ρ₁ ρ₂)
    (hfine : Sewing.HasFinePartitions ω)
    (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    (DW : MixedDist Z₁' Z₂')
    {I₁ I₂ : ℝ → ℝ → E}
    (hadd₁ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₁ s u + I₁ u t = I₁ s t)
    (hadd₂ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₂ s u + I₂ u t = I₂ s t)
    (hgerm₁ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - gubinelliGerm Z₁' s t‖ₑ ≤
        Sewing.sewingConst (3 * α) * (roughConst Z₁' * ω s t ^ (3 * α)))
    (hgerm₂ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₂ s t - gubinelliGerm Z₂' s t‖ₑ ≤
        Sewing.sewingConst (3 * α) * (roughConst Z₂' * ω s t ^ (3 * α))) :
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - I₂ s t -
          (gubinelliGerm Z₁' s t - gubinelliGerm Z₂' s t)‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (((mixedRoughConstN Z₁' DW ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞) *
            ω s t ^ (3 * α)) := by
  have h3α := hX₁.one_lt_three_alpha
  have hKne : Sewing.sewingConst (3 * α) ≠ ⊤ :=
    (Sewing.sewingConst_lt_top h3α).ne
  -- sew the difference of the germs
  obtain ⟨J, hJadd, hJgerm, -⟩ := Sewing.sewing_const_mul ω
    (fun s t => gubinelliGerm Z₁' s t - gubinelliGerm Z₂' s t)
    h3α (by positivity) ENNReal.coe_ne_top
    (fun a b c hab hbc => mixed_germ_defect hX₁ hX₂ hXd DW hab hbc)
    hfine hωne
  have heq : ∀ ⦃s t : ℝ⦄, s ≤ t → I₁ s t - I₂ s t = J s t := by
    intro s t hst
    refine Sewing.eq_of_additive_of_germ_bound ω
      (fun s t => gubinelliGerm Z₁' s t - gubinelliGerm Z₂' s t) h3α
      (C := Sewing.sewingConst (3 * α) * (roughConst Z₁' + roughConst Z₂'))
      (C' := Sewing.sewingConst (3 * α) *
        ((mixedRoughConstN Z₁' DW ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞))
      (ENNReal.mul_ne_top hKne (ENNReal.add_ne_top.2
        ⟨roughConst_ne_top Z₁', roughConst_ne_top Z₂'⟩))
      (ENNReal.mul_ne_top hKne ENNReal.coe_ne_top)
      hfine
      (fun a u b hau hub => by
        have h₁ := hadd₁ hau hub
        have h₂ := hadd₂ hau hub
        rw [show I₁ a u - I₂ a u + (I₁ u b - I₂ u b) =
          (I₁ a u + I₁ u b) - (I₂ a u + I₂ u b) by abel, h₁, h₂])
      hJadd
      (fun a b hab => by
        rw [show I₁ a b - I₂ a b -
          (gubinelliGerm Z₁' a b - gubinelliGerm Z₂' a b) =
          (I₁ a b - gubinelliGerm Z₁' a b) -
            (I₂ a b - gubinelliGerm Z₂' a b) by abel]
        refine le_trans enorm_sub_le ?_
        refine le_trans (add_le_add (hgerm₁ hab) (hgerm₂ hab))
          (le_of_eq ?_)
        ring)
      (fun a b hab => by
        rw [mul_assoc]
        exact hJgerm hab)
      hst (hωne hst)
  intro s t hst
  rw [heq hst]
  exact hJgerm hst

end Germ

/-! ### Two-driver stability of composition -/

namespace RDEVectorField3

variable [CompleteSpace E]
variable (V : RDEVectorField3 d E)
variable (hX₁ : IsLevel2RoughPath X₁ ω α) (hX₂ : IsLevel2RoughPath X₂ ω α)
variable (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
variable (hXd : RoughPathDist X₁ X₂ ω α ρ₁ ρ₂)
variable {Z₁ : ControlledPath X₁ ω α E} {Z₂ : ControlledPath X₂ ω α E}

open RDEVectorField in
/-- **Two-driver stability of composition** (Friz–Hairer Lemma 7.5-type):
mixed distance certificates between `f(Y¹)` (over `X₁`) and `f(Y²)`
(over `X₂`), linear in the mixed certificates of `Y¹, Y²` with the
driver-distance offset entering only through the increment constant
`d·(Db + ρ₁·Cb₁) + Dy`. -/
noncomputable def compMixedDist (D : MixedDist Z₁ Z₂) :
    MixedDist (V.toRDEVectorField.compControlled hX₁ hω1 Z₁)
      (V.toRDEVectorField.compControlled hX₂ hω1 Z₂) where
  D0 := V.C1 * D.D0
  Db := V.C1 * D.Db + V.C2 * D.D0 * Z₂.Cb
  Dd := V.C1 * D.Dd + V.C2 * D.D0 * Z₂.Cd +
    V.C2 * (d * Z₁.Cb + Z₁.Cy) * D.Db +
    (V.C2 * (d * (D.Db + ρ₁ * Z₁.Cb) + D.Dy) +
      V.C3 * (D.D0 + (d * (D.Db + ρ₁ * Z₁.Cb) + D.Dy)) *
        (d * Z₂.Cb + Z₂.Cy)) * Z₂.Cb
  Dy := V.C2 * (d * (D.Db + ρ₁ * Z₁.Cb) + D.Dy) *
      ((d * Z₁.Cb + Z₁.Cy) + (d * Z₂.Cb + Z₂.Cy)) +
    V.C3 * (D.D0 + (d * (D.Db + ρ₁ * Z₁.Cb) + D.Dy)) *
      (d * Z₂.Cb + Z₂.Cy) ^ 2 +
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
    have hα := hX₁.alpha_pos
    have hω_le_one : ω s t ^ α ≤ 1 :=
      le_trans (ENNReal.rpow_le_rpow (hω1 hst) hα.le)
        (le_of_eq (ENNReal.one_rpow α))
    have hincD := D.increment_sub_le hX₂ hω1 hXd hst
    have hinc₁ : ‖Z₁.Y t - Z₁.Y s‖ₑ ≤
        ((d : ℝ≥0∞) * Z₁.Cb + Z₁.Cy) * ω s t ^ α :=
      increment_le hX₁ hω1 Z₁ hst
    have hinc₂ : ‖Z₂.Y t - Z₂.Y s‖ₑ ≤
        ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy) * ω s t ^ α :=
      increment_le hX₂ hω1 Z₂ hst
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
        ((V.C2 : ℝ≥0∞) * ((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) +
            D.Dy) +
          (V.C3 : ℝ≥0∞) * ((D.D0 : ℝ≥0∞) +
              ((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) + D.Dy)) *
            ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy)) * Z₂.Cb * ω s t ^ α := by
      refine le_trans (enorm_clm_apply_le _ _) ?_
      have hdd := V.enorm_deriv_double_diff i (Z₁.Y t) (Z₁.Y s)
        (Z₂.Y t) (Z₂.Y s)
      have hbound : ‖V.deriv i (Z₁.Y t) - V.deriv i (Z₁.Y s) -
          (V.deriv i (Z₂.Y t) - V.deriv i (Z₂.Y s))‖ₑ ≤
          ((V.C2 : ℝ≥0∞) * ((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) +
              D.Dy) +
            (V.C3 : ℝ≥0∞) * ((D.D0 : ℝ≥0∞) +
                ((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) + D.Dy)) *
              ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy)) * ω s t ^ α := by
        refine le_trans hdd ?_
        have h1 : (V.C2 : ℝ≥0∞) *
            ‖Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s)‖ₑ ≤
            (V.C2 : ℝ≥0∞) *
              (((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) + D.Dy) *
                ω s t ^ α) :=
          mul_le_mul' le_rfl hincD
        have h2 : (V.C3 : ℝ≥0∞) *
            (‖Z₁.Y s - Z₂.Y s‖ₑ +
              ‖Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s)‖ₑ) *
            ‖Z₂.Y t - Z₂.Y s‖ₑ ≤
            (V.C3 : ℝ≥0∞) *
              ((D.D0 : ℝ≥0∞) +
                ((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) + D.Dy)) *
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
    have hα := hX₁.alpha_pos
    have hω_le_one : ω s t ^ α ≤ 1 :=
      le_trans (ENNReal.rpow_le_rpow (hω1 hst) hα.le)
        (le_of_eq (ENNReal.one_rpow α))
    have hincD := D.increment_sub_le hX₂ hω1 hXd hst
    have hinc₁ : ‖Z₁.Y t - Z₁.Y s‖ₑ ≤
        ((d : ℝ≥0∞) * Z₁.Cb + Z₁.Cy) * ω s t ^ α :=
      increment_le hX₁ hω1 Z₁ hst
    have hinc₂ : ‖Z₂.Y t - Z₂.Y s‖ₑ ≤
        ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy) * ω s t ^ α :=
      increment_le hX₂ hω1 Z₂ hst
    refine pi_enorm_le fun i => ?_
    have happly₁ : (∑ j, X₁.coeff s t [j] •
        (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s j) i =
        V.deriv i (Z₁.Y s) (∑ j, X₁.coeff s t [j] • Z₁.Yd s j) := by
      rw [Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, map_smul, compControlled_Yd]
    have happly₂ : (∑ j, X₂.coeff s t [j] •
        (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Yd s j) i =
        V.deriv i (Z₂.Y s) (∑ j, X₂.coeff s t [j] • Z₂.Yd s j) := by
      rw [Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, map_smul, compControlled_Yd]
    have hpi : ((V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Y t -
        (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Y s -
        (∑ j, X₁.coeff s t [j] •
          (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s j) -
        ((V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Y t -
          (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Y s -
          ∑ j, X₂.coeff s t [j] •
            (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Yd s j)) i =
        V.f i (Z₁.Y t) - V.f i (Z₁.Y s) -
          V.deriv i (Z₁.Y s) (∑ j, X₁.coeff s t [j] • Z₁.Yd s j) -
          (V.f i (Z₂.Y t) - V.f i (Z₂.Y s) -
            V.deriv i (Z₂.Y s) (∑ j, X₂.coeff s t [j] • Z₂.Yd s j)) := by
      simp only [Pi.sub_apply]
      rw [happly₁, happly₂]
      simp only [compControlled_Y]
    rw [hpi]
    have hsplit : V.f i (Z₁.Y t) - V.f i (Z₁.Y s) -
        V.deriv i (Z₁.Y s) (∑ j, X₁.coeff s t [j] • Z₁.Yd s j) -
        (V.f i (Z₂.Y t) - V.f i (Z₂.Y s) -
          V.deriv i (Z₂.Y s) (∑ j, X₂.coeff s t [j] • Z₂.Yd s j)) =
        (V.f i (Z₁.Y t) - V.f i (Z₁.Y s) -
          V.deriv i (Z₁.Y s) (Z₁.Y t - Z₁.Y s) -
          (V.f i (Z₂.Y t) - V.f i (Z₂.Y s) -
            V.deriv i (Z₂.Y s) (Z₂.Y t - Z₂.Y s))) +
        (V.deriv i (Z₁.Y s)
            (Z₁.Y t - Z₁.Y s - ∑ j, X₁.coeff s t [j] • Z₁.Yd s j) -
          V.deriv i (Z₂.Y s)
            (Z₂.Y t - Z₂.Y s - ∑ j, X₂.coeff s t [j] • Z₂.Yd s j)) := by
      simp only [map_sub]
      abel
    rw [hsplit]
    refine le_trans (enorm_add_le _ _) ?_
    have hA : ‖V.f i (Z₁.Y t) - V.f i (Z₁.Y s) -
        V.deriv i (Z₁.Y s) (Z₁.Y t - Z₁.Y s) -
        (V.f i (Z₂.Y t) - V.f i (Z₂.Y s) -
          V.deriv i (Z₂.Y s) (Z₂.Y t - Z₂.Y s))‖ₑ ≤
        ((V.C2 : ℝ≥0∞) *
            ((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) + D.Dy) *
            (((d : ℝ≥0∞) * Z₁.Cb + Z₁.Cy) +
              ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy)) +
          (V.C3 : ℝ≥0∞) * ((D.D0 : ℝ≥0∞) +
              ((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) + D.Dy)) *
            ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy) ^ (2 : ℕ)) *
          ω s t ^ (2 * α) := by
      refine le_trans (V.enorm_taylor_diff i (Z₁.Y t) (Z₁.Y s)
        (Z₂.Y t) (Z₂.Y s)) ?_
      have h1 : (V.C2 : ℝ≥0∞) *
          ‖Z₁.Y t - Z₁.Y s - (Z₂.Y t - Z₂.Y s)‖ₑ *
          (‖Z₁.Y t - Z₁.Y s‖ₑ + ‖Z₂.Y t - Z₂.Y s‖ₑ) ≤
          (V.C2 : ℝ≥0∞) *
            (((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) + D.Dy) *
              ω s t ^ α) *
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
            ((D.D0 : ℝ≥0∞) +
              ((d : ℝ≥0∞) * ((D.Db : ℝ≥0∞) + ρ₁ * Z₁.Cb) + D.Dy)) *
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
    have hR : ‖Z₁.Y t - Z₁.Y s - (∑ j, X₁.coeff s t [j] • Z₁.Yd s j) -
        (Z₂.Y t - Z₂.Y s - ∑ j, X₂.coeff s t [j] • Z₂.Yd s j)‖ₑ ≤
        (D.Dy : ℝ≥0∞) * ω s t ^ (2 * α) := D.remainder hst
    have hB : ‖V.deriv i (Z₁.Y s)
        (Z₁.Y t - Z₁.Y s - ∑ j, X₁.coeff s t [j] • Z₁.Yd s j) -
        V.deriv i (Z₂.Y s)
          (Z₂.Y t - Z₂.Y s - ∑ j, X₂.coeff s t [j] • Z₂.Yd s j)‖ₑ ≤
        ((V.C1 : ℝ≥0∞) * D.Dy + (V.C2 : ℝ≥0∞) * D.D0 * Z₂.Cy) *
          ω s t ^ (2 * α) := by
      have hbsplit : V.deriv i (Z₁.Y s)
          (Z₁.Y t - Z₁.Y s - ∑ j, X₁.coeff s t [j] • Z₁.Yd s j) -
          V.deriv i (Z₂.Y s)
            (Z₂.Y t - Z₂.Y s - ∑ j, X₂.coeff s t [j] • Z₂.Yd s j) =
          V.deriv i (Z₁.Y s)
            (Z₁.Y t - Z₁.Y s - (∑ j, X₁.coeff s t [j] • Z₁.Yd s j) -
              (Z₂.Y t - Z₂.Y s - ∑ j, X₂.coeff s t [j] • Z₂.Yd s j)) +
          (V.deriv i (Z₁.Y s) - V.deriv i (Z₂.Y s))
            (Z₂.Y t - Z₂.Y s - ∑ j, X₂.coeff s t [j] • Z₂.Yd s j) := by
        simp only [map_sub, sub_apply]
        abel
      rw [hbsplit]
      refine le_trans (enorm_add_le _ _) ?_
      have hb1 : ‖V.deriv i (Z₁.Y s)
          (Z₁.Y t - Z₁.Y s - (∑ j, X₁.coeff s t [j] • Z₁.Yd s j) -
            (Z₂.Y t - Z₂.Y s - ∑ j, X₂.coeff s t [j] • Z₂.Yd s j))‖ₑ ≤
          (V.C1 : ℝ≥0∞) * ((D.Dy : ℝ≥0∞) * ω s t ^ (2 * α)) :=
        le_trans (enorm_clm_apply_le _ _)
          (mul_le_mul' (enorm_le_coe (V.bound_deriv i _)) hR)
      have hb2 : ‖(V.deriv i (Z₁.Y s) - V.deriv i (Z₂.Y s))
          (Z₂.Y t - Z₂.Y s - ∑ j, X₂.coeff s t [j] • Z₂.Yd s j)‖ₑ ≤
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

/-! ### Window-gain bounds for the mixed integral difference -/

variable (hfine : Sewing.HasFinePartitions ω)
variable (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
variable {δα : ℝ≥0}

omit [CompleteSpace E] in
/-- The composed integrand is uniformly bounded by `C₀`. -/
theorem comp_bound_Y (Z : ControlledPath X₁ ω α E) (s : ℝ) :
    ‖(V.toRDEVectorField.compControlled hX₁ hω1 Z).Y s‖ₑ ≤
      (V.C0 : ℝ≥0∞) := by
  refine RDEVectorField.pi_enorm_le fun i => ?_
  simp only [RDEVectorField.compControlled_Y]
  exact RDEVectorField.enorm_le_coe (V.bound_f i _)

include hfine hωne in
/-- Mixed analogue of `integral_dist_bound`: the difference of the two
rough integrals over different drivers gains the full window factor. -/
theorem mixed_integral_dist_bound
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hδα1 : δα ≤ 1)
    (D : MixedDist Z₁ Z₂) {I₁ I₂ : ℝ → ℝ → E}
    (hadd₁ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₁ s u + I₁ u t = I₁ s t)
    (hadd₂ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₂ s u + I₂ u t = I₂ s t)
    (hgerm₁ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - gubinelliGerm
          (V.toRDEVectorField.compControlled hX₁ hω1 Z₁) s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst (V.toRDEVectorField.compControlled hX₁ hω1 Z₁) *
            ω s t ^ (3 * α)))
    (hgerm₂ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₂ s t - gubinelliGerm
          (V.toRDEVectorField.compControlled hX₂ hω1 Z₂) s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst (V.toRDEVectorField.compControlled hX₂ hω1 Z₂) *
            ω s t ^ (3 * α)))  :
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - I₂ s t‖ₑ ≤
        (((d : ℝ≥0) *
            ((V.compMixedDist hX₁ hX₂ hω1 hXd D).D0 + ρ₁ * V.C0) +
          (d : ℝ≥0) ^ 2 *
            ((V.compMixedDist hX₁ hX₂ hω1 hXd D).Db +
              ρ₂ * (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cb) +
          (Sewing.sewingConst (3 * α)).toNNReal *
            mixedRoughConstN
              (V.toRDEVectorField.compControlled hX₁ hω1 Z₁)
              (V.compMixedDist hX₁ hX₂ hω1 hXd D) ρ₁ ρ₂) *
          δα : ℝ≥0) := by
  intro s t hst
  have hα := hX₁.alpha_pos
  have h3α := hX₁.one_lt_three_alpha
  have hωα : ω s t ^ α ≤ (δα : ℝ≥0∞) := hδα hst
  have hω2α : ω s t ^ (2 * α) ≤ (δα : ℝ≥0∞) :=
    rpow_two_mul_le_coe hα.le hωα hδα1
  have hω3α : ω s t ^ (3 * α) ≤ (δα : ℝ≥0∞) :=
    rpow_three_mul_le_coe hα.le hωα hδα1
  have hsub := mixedIntegral_sub hX₁ hX₂ hXd hfine hωne
    (V.compMixedDist hX₁ hX₂ hω1 hXd D) hadd₁ hadd₂ hgerm₁ hgerm₂ hst
  have hgerm := enorm_gubinelliGerm_sub_le hX₂ hXd
    (V.compMixedDist hX₁ hX₂ hω1 hXd D) (B₁ := V.C0)
    (comp_bound_Y V hX₁ hω1 Z₁) hst
  have htri : ‖I₁ s t - I₂ s t‖ₑ ≤
      ‖I₁ s t - I₂ s t -
          (gubinelliGerm
              (V.toRDEVectorField.compControlled hX₁ hω1 Z₁) s t -
            gubinelliGerm
              (V.toRDEVectorField.compControlled hX₂ hω1 Z₂) s t)‖ₑ +
        ‖gubinelliGerm
            (V.toRDEVectorField.compControlled hX₁ hω1 Z₁) s t -
          gubinelliGerm
            (V.toRDEVectorField.compControlled hX₂ hω1 Z₂) s t‖ₑ := by
    refine le_trans (le_of_eq ?_) (enorm_add_le _ _)
    congr 1
    abel
  refine le_trans htri ?_
  refine le_trans (add_le_add hsub hgerm) ?_
  have hK : Sewing.sewingConst (3 * α) =
      (((Sewing.sewingConst (3 * α)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal (Sewing.sewingConst_lt_top h3α).ne).symm
  have h1 : Sewing.sewingConst (3 * α) *
      (((mixedRoughConstN
          (V.toRDEVectorField.compControlled hX₁ hω1 Z₁)
          (V.compMixedDist hX₁ hX₂ hω1 hXd D) ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞) *
        ω s t ^ (3 * α)) ≤
      ((((Sewing.sewingConst (3 * α)).toNNReal *
        mixedRoughConstN
          (V.toRDEVectorField.compControlled hX₁ hω1 Z₁)
          (V.compMixedDist hX₁ hX₂ hω1 hXd D) ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞)) *
        δα := by
    conv_lhs => rw [hK]
    refine le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hω3α))
      (le_of_eq ?_)
    push_cast
    ring
  have h2 : (d : ℝ≥0∞) *
        (((V.compMixedDist hX₁ hX₂ hω1 hXd D).D0 : ℝ≥0∞) +
          ρ₁ * V.C0) * ω s t ^ α +
      (d : ℝ≥0∞) ^ 2 *
        (((V.compMixedDist hX₁ hX₂ hω1 hXd D).Db : ℝ≥0∞) +
          ρ₂ * (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cb) *
        ω s t ^ (2 * α) ≤
      ((((d : ℝ≥0) *
          ((V.compMixedDist hX₁ hX₂ hω1 hXd D).D0 + ρ₁ * V.C0) +
        (d : ℝ≥0) ^ 2 *
          ((V.compMixedDist hX₁ hX₂ hω1 hXd D).Db +
            ρ₂ * (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cb) :
          ℝ≥0) : ℝ≥0∞)) * δα := by
    refine le_trans (add_le_add
      (mul_le_mul' le_rfl hωα) (mul_le_mul' le_rfl hω2α))
      (le_of_eq ?_)
    push_cast
    ring
  refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
  push_cast
  ring

include hfine hωne in
/-- Mixed analogue of `integral_sub_germ_folded`. -/
theorem mixed_integral_sub_germ_folded
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (D : MixedDist Z₁ Z₂) {I₁ I₂ : ℝ → ℝ → E}
    (hadd₁ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₁ s u + I₁ u t = I₁ s t)
    (hadd₂ : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I₂ s u + I₂ u t = I₂ s t)
    (hgerm₁ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₁ s t - gubinelliGerm
          (V.toRDEVectorField.compControlled hX₁ hω1 Z₁) s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst (V.toRDEVectorField.compControlled hX₁ hω1 Z₁) *
            ω s t ^ (3 * α)))
    (hgerm₂ : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I₂ s t - gubinelliGerm
          (V.toRDEVectorField.compControlled hX₂ hω1 Z₂) s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (roughConst (V.toRDEVectorField.compControlled hX₂ hω1 Z₂) *
            ω s t ^ (3 * α)))
    ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖I₁ s t - I₂ s t -
        (gubinelliGerm
            (V.toRDEVectorField.compControlled hX₁ hω1 Z₁) s t -
          gubinelliGerm
            (V.toRDEVectorField.compControlled hX₂ hω1 Z₂) s t)‖ₑ ≤
      (((Sewing.sewingConst (3 * α)).toNNReal *
        mixedRoughConstN
          (V.toRDEVectorField.compControlled hX₁ hω1 Z₁)
          (V.compMixedDist hX₁ hX₂ hω1 hXd D) ρ₁ ρ₂ *
        δα : ℝ≥0) : ℝ≥0∞) * ω s t ^ (2 * α) := by
  have hα := hX₁.alpha_pos
  have h3α := hX₁.one_lt_three_alpha
  have hω3α : ω s t ^ (3 * α) ≤ (δα : ℝ≥0∞) * ω s t ^ (2 * α) :=
    rpow_three_mul_le_mul hα.le (hδα hst)
  have hK : Sewing.sewingConst (3 * α) =
      (((Sewing.sewingConst (3 * α)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal (Sewing.sewingConst_lt_top h3α).ne).symm
  refine le_trans (mixedIntegral_sub hX₁ hX₂ hXd hfine hωne
    (V.compMixedDist hX₁ hX₂ hω1 hXd D) hadd₁ hadd₂ hgerm₁ hgerm₂ hst) ?_
  conv_lhs => rw [hK]
  refine le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hω3α))
    (le_of_eq ?_)
  push_cast
  ring

/-! ### The distance step for solutions along two drivers -/

open RDEVectorField in
/-- **The two-driver distance step**: solutions of `dY = f(Y)·dX₁` and
`dY = f(Y)·dX₂` from the same initial condition satisfy the mixed
distance-step inequalities — the one-driver step formulas plus explicit
`(ρ₁, ρ₂)`-offsets. -/
noncomputable def solutionDriverStep
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hδα1 : δα ≤ 1)
    {I₁ I₂ : ℝ → ℝ → E}
    (hsol₁ : V.IsRDESolution hX₁ hω1 Z₁ I₁)
    (hsol₂ : V.IsRDESolution hX₂ hω1 Z₂ I₂)
    (h0 : Z₁.Y 0 = Z₂.Y 0)
    (D : MixedDist Z₁ Z₂) : MixedDist Z₁ Z₂ where
  D0 := ((d : ℝ≥0) *
      ((V.compMixedDist hX₁ hX₂ hω1 hXd D).D0 + ρ₁ * V.C0) +
    (d : ℝ≥0) ^ 2 *
      ((V.compMixedDist hX₁ hX₂ hω1 hXd D).Db +
        ρ₂ * (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cb) +
    (Sewing.sewingConst (3 * α)).toNNReal *
      mixedRoughConstN (V.toRDEVectorField.compControlled hX₁ hω1 Z₁)
        (V.compMixedDist hX₁ hX₂ hω1 hXd D) ρ₁ ρ₂) * δα
  Db := V.C1 * D.D0
  Dd := (d : ℝ≥0) * ((V.compMixedDist hX₁ hX₂ hω1 hXd D).Db +
      ρ₁ * (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cb) +
    (V.compMixedDist hX₁ hX₂ hω1 hXd D).Dy
  Dy := (Sewing.sewingConst (3 * α)).toNNReal *
      mixedRoughConstN (V.toRDEVectorField.compControlled hX₁ hω1 Z₁)
        (V.compMixedDist hX₁ hX₂ hω1 hXd D) ρ₁ ρ₂ * δα +
    (d : ℝ≥0) ^ 2 *
      ((V.compMixedDist hX₁ hX₂ hω1 hXd D).Db +
        ρ₂ * (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cb)
  bound_Y := by
    intro u
    have hIdiff := mixed_integral_dist_bound V hX₁ hX₂ hω1 hXd hfine
      hωne hδα hδα1 D hsol₁.additive hsol₂.additive hsol₁.germ_bound
      hsol₂.germ_bound
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
        ((V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Y t -
          (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Y s -
          ((V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Y t -
            (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Y s)) i := by
      simp only [Pi.sub_apply, compControlled_Y]
      abel
    rw [hcoord]
    refine le_trans (enorm_apply_le i) ?_
    refine le_trans ((V.compMixedDist hX₁ hX₂ hω1 hXd D).increment_sub_le
      hX₂ hω1 hXd hst) (le_of_eq ?_)
    push_cast
    ring
  remainder := by
    intro s t hst
    rw [hsol₁.increment_eq hst, hsol₂.increment_eq hst]
    have hlin₁ : ∀ i : Fin d, Z₁.Yd s i =
        (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Y s i := by
      intro i
      rw [hsol₁.deriv_eq s i]
      simp only [compControlled_Y]
    have hlin₂ : ∀ i : Fin d, Z₂.Yd s i =
        (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Y s i := by
      intro i
      rw [hsol₂.deriv_eq s i]
      simp only [compControlled_Y]
    have hsplit : I₁ s t - (∑ i, X₁.coeff s t [i] • Z₁.Yd s i) -
        (I₂ s t - ∑ i, X₂.coeff s t [i] • Z₂.Yd s i) =
        (I₁ s t - I₂ s t -
          (gubinelliGerm
              (V.toRDEVectorField.compControlled hX₁ hω1 Z₁) s t -
            gubinelliGerm
              (V.toRDEVectorField.compControlled hX₂ hω1 Z₂) s t)) +
        ((∑ i, ∑ j, X₁.coeff s t [i, j] •
            (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s i j) -
          ∑ i, ∑ j, X₂.coeff s t [i, j] •
            (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Yd s i j) := by
      have hsum₁ : (∑ i, X₁.coeff s t [i] • Z₁.Yd s i) =
          ∑ i, X₁.coeff s t [i] •
            (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Y s i :=
        Finset.sum_congr rfl fun i _ => by rw [hlin₁ i]
      have hsum₂ : (∑ i, X₂.coeff s t [i] • Z₂.Yd s i) =
          ∑ i, X₂.coeff s t [i] •
            (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Y s i :=
        Finset.sum_congr rfl fun i _ => by rw [hlin₂ i]
      rw [hsum₁, hsum₂, gubinelliGerm_apply, gubinelliGerm_apply]
      abel
    rw [hsplit]
    refine le_trans (enorm_add_le _ _) ?_
    have h1 := mixed_integral_sub_germ_folded V hX₁ hX₂ hω1 hXd hfine
      hωne hδα D hsol₁.additive hsol₂.additive hsol₁.germ_bound
      hsol₂.germ_bound hst
    have h2 : ‖(∑ i, ∑ j, X₁.coeff s t [i, j] •
        (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s i j) -
        ∑ i, ∑ j, X₂.coeff s t [i, j] •
          (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Yd s i j‖ₑ ≤
        (((d : ℝ≥0) ^ 2 *
          ((V.compMixedDist hX₁ hX₂ hω1 hXd D).Db +
            ρ₂ * (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cb) :
          ℝ≥0) : ℝ≥0∞) * ω s t ^ (2 * α) := by
      have hpair : (∑ i, ∑ j, X₁.coeff s t [i, j] •
          (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s i j) -
          ∑ i, ∑ j, X₂.coeff s t [i, j] •
            (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Yd s i j =
          (∑ i, ∑ j, (X₁.coeff s t [i, j] - X₂.coeff s t [i, j]) •
            (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s i j) +
          ∑ i, ∑ j, X₂.coeff s t [i, j] •
            ((V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s i j -
              (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Yd s i j) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sum_smul_pair_split]
      rw [hpair]
      have ha : ‖∑ i, ∑ j, (X₁.coeff s t [i, j] - X₂.coeff s t [i, j]) •
          (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s i j‖ₑ ≤
          (d : ℝ≥0∞) * ((d : ℝ≥0∞) * ((ρ₂ : ℝ≥0∞) * ω s t ^ (2 * α) *
            (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cb)) := by
        refine enorm_fin_sum_le fun i => enorm_fin_sum_le fun j => ?_
        rw [ControlledPath.enorm_real_smul]
        exact mul_le_mul' (hXd.bound_two hst i j)
          (le_trans (enorm_apply_le j)
            ((V.toRDEVectorField.compControlled hX₁ hω1 Z₁).bound_Yd s i))
      have hb : ‖∑ i, ∑ j, X₂.coeff s t [i, j] •
          ((V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s i j -
            (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Yd s i j)‖ₑ ≤
          (d : ℝ≥0∞) * ((d : ℝ≥0∞) * (ω s t ^ (2 * α) *
            (V.compMixedDist hX₁ hX₂ hω1 hXd D).Db)) := by
        refine enorm_fin_sum_le fun i => enorm_fin_sum_le fun j => ?_
        rw [ControlledPath.enorm_real_smul]
        refine mul_le_mul' (hX₂.bound_two hst i j) ?_
        have hco :
            (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s i j -
            (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Yd s i j =
            ((V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Yd s i -
              (V.toRDEVectorField.compControlled hX₂ hω1 Z₂).Yd s i) j :=
          rfl
        rw [hco]
        exact le_trans (enorm_apply_le j)
          ((V.compMixedDist hX₁ hX₂ hω1 hXd D).bound_Yd s i)
      refine le_trans (enorm_add_le _ _)
        (le_trans (add_le_add ha hb) (le_of_eq ?_))
      push_cast
      ring
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    push_cast
    ring

/-- Any two box-certified controlled paths over different drivers with
the same initial value admit a finite mixed distance certificate. -/
noncomputable def mixedSeedDist
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    {Bb Bd By : ℝ≥0}
    (h0 : Z₁.Y 0 = Z₂.Y 0)
    (hZ₁ : InBox Bb Bd By Z₁) (hZ₂ : InBox Bb Bd By Z₂) :
    MixedDist Z₁ Z₂ where
  D0 := 2 * ((d * Bb + By) * δα)
  Db := 2 * Bb
  Dd := 2 * Bd
  Dy := 2 * By
  bound_Y := by
    intro u
    have hbox₁ : ∀ ⦃s t : ℝ⦄, s ≤ t → ‖Z₁.Y t - Z₁.Y s‖ₑ ≤
        (((d * Bb + By) * δα : ℝ≥0) : ℝ≥0∞) := by
      intro s t hst
      refine le_trans (RDEVectorField.increment_le hX₁ hω1 Z₁ hst) ?_
      calc ((d : ℝ≥0∞) * Z₁.Cb + Z₁.Cy) * ω s t ^ α
          ≤ ((d : ℝ≥0∞) * Bb + By) * (δα : ℝ≥0∞) := by
            refine mul_le_mul' (add_le_add
              (mul_le_mul' le_rfl ?_) ?_) (hδα hst)
            · exact_mod_cast hZ₁.1
            · exact_mod_cast hZ₁.2.2
        _ = (((d * Bb + By) * δα : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    have hbox₂ : ∀ ⦃s t : ℝ⦄, s ≤ t → ‖Z₂.Y t - Z₂.Y s‖ₑ ≤
        (((d * Bb + By) * δα : ℝ≥0) : ℝ≥0∞) := by
      intro s t hst
      refine le_trans (RDEVectorField.increment_le hX₂ hω1 Z₂ hst) ?_
      calc ((d : ℝ≥0∞) * Z₂.Cb + Z₂.Cy) * ω s t ^ α
          ≤ ((d : ℝ≥0∞) * Bb + By) * (δα : ℝ≥0∞) := by
            refine mul_le_mul' (add_le_add
              (mul_le_mul' le_rfl ?_) ?_) (hδα hst)
            · exact_mod_cast hZ₂.1
            · exact_mod_cast hZ₂.2.2
        _ = (((d * Bb + By) * δα : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    by_cases hu : 0 ≤ u
    · have hre : Z₁.Y u - Z₂.Y u =
          (Z₁.Y u - Z₁.Y 0) - (Z₂.Y u - Z₂.Y 0) := by
        rw [h0]
        abel
      rw [hre]
      refine le_trans enorm_sub_le ?_
      refine le_trans (add_le_add (hbox₁ hu) (hbox₂ hu)) (le_of_eq ?_)
      push_cast
      ring
    · have hu' : u ≤ 0 := (not_le.1 hu).le
      have hre : Z₁.Y u - Z₂.Y u =
          -((Z₁.Y 0 - Z₁.Y u) - (Z₂.Y 0 - Z₂.Y u)) := by
        rw [h0]
        abel
      rw [hre, enorm_neg]
      refine le_trans enorm_sub_le ?_
      refine le_trans (add_le_add (hbox₁ hu') (hbox₂ hu')) (le_of_eq ?_)
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
    refine le_trans (add_le_add (Z₁.holder_Yd hst i)
      (Z₂.holder_Yd hst i)) ?_
    calc (Z₁.Cd : ℝ≥0∞) * ω s t ^ α + Z₂.Cd * ω s t ^ α
        ≤ (Bd : ℝ≥0∞) * ω s t ^ α + Bd * ω s t ^ α := by
          refine add_le_add (mul_le_mul' ?_ le_rfl)
            (mul_le_mul' ?_ le_rfl)
          · exact_mod_cast hZ₁.2.1
          · exact_mod_cast hZ₂.2.1
      _ = ((2 * Bd : ℝ≥0) : ℝ≥0∞) * ω s t ^ α := by push_cast; ring
  remainder := by
    intro s t hst
    refine le_trans enorm_sub_le ?_
    refine le_trans (add_le_add (Z₁.remainder hst) (Z₂.remainder hst)) ?_
    calc (Z₁.Cy : ℝ≥0∞) * ω s t ^ (2 * α) + Z₂.Cy * ω s t ^ (2 * α)
        ≤ (By : ℝ≥0∞) * ω s t ^ (2 * α) + By * ω s t ^ (2 * α) := by
          refine add_le_add (mul_le_mul' ?_ le_rfl)
            (mul_le_mul' ?_ le_rfl)
          · exact_mod_cast hZ₁.2.2
          · exact_mod_cast hZ₂.2.2
      _ = ((2 * By : ℝ≥0) : ℝ≥0∞) * ω s t ^ (2 * α) := by push_cast; ring

end RDEVectorField3

end RoughPaths
