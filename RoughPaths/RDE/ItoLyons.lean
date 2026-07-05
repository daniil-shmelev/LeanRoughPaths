/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.RDE.DriverStability

/-!
# Continuity of the Itô–Lyons map

The quantitative core of the universal limit theorem (Friz–Hairer
Thm 8.5): two box-certified solutions of `dY = f(Y)·dX₁` and
`dY = f(Y)·dX₂` from the same initial condition, driven by rough paths
at certified distance `(ρ₁, ρ₂)`, stay uniformly within `Coff/wa` of
each other — where `Coff` is the affine offset of the two-driver
distance step (`solutionDriverStep`), which vanishes with
`(ρ₁, ρ₂) → 0`.

The mechanism is an affine fixed-point iteration: the mixed distance
step contracts the weighted certificate up to the `ρ`-offset, so
iterating from the seed certificate gives
`ρ_w(n) ≤ (1/2)ⁿ·ρ_w(0) + Coff` and the pointwise distance of the two
solutions is dominated by every `ρ_w(n)/wa`.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ} {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {X₁ X₂ : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ}
variable {α : ℝ} {ρ₁ ρ₂ : ℝ≥0}

namespace RDEVectorField3

variable (V : RDEVectorField3 d E)
variable (hX₁ : IsLevel2RoughPath X₁ ω α) (hX₂ : IsLevel2RoughPath X₂ ω α)
variable (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
variable (hXd : RoughPathDist X₁ X₂ ω α ρ₁ ρ₂)
variable (hfine : Sewing.HasFinePartitions ω)
variable (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
variable {δα : ℝ≥0}

/-- **Continuity of the Itô–Lyons map** (Friz–Hairer Thm 8.5-type,
quantitative form): two box-certified solutions along drivers at
certified distance `(ρ₁, ρ₂)` from the same initial condition satisfy
`dist (Y¹_u, Y²_u) ≤ Coff / wa` for every time `u`, where `Coff` is any
affine offset for the weighted two-driver distance step. Since the step
slots are polynomial in `(ρ₁, ρ₂)` with no constant term beyond the
one-driver formulas, `Coff` can be taken linear in `(ρ₁, ρ₂)`; the
solution therefore depends continuously — indeed Lipschitz-continuously
— on the driving rough path. -/
theorem itoLyons_dist_le
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (δα : ℝ≥0∞))
    (hδα1 : δα ≤ 1)
    {Bb Bd By wa wb wc we Coff : ℝ≥0} (hwa : 0 < wa)
    {Z₁ : ControlledPath X₁ ω α E} {Z₂ : ControlledPath X₂ ω α E}
    {I₁ I₂ : ℝ → ℝ → E}
    (hsol₁ : V.IsRDESolution hX₁ hω1 Z₁ I₁)
    (hsol₂ : V.IsRDESolution hX₂ hω1 Z₂ I₂)
    (h0 : Z₁.Y 0 = Z₂.Y 0)
    (hZ₁ : InBox Bb Bd By Z₁) (hZ₂ : InBox Bb Bd By Z₂)
    (hcontr : ∀ D : MixedDist Z₁ Z₂,
      2 * (wa * (solutionDriverStep V hX₁ hX₂ hω1 hXd hfine hωne hδα
            hδα1 hsol₁ hsol₂ h0 D).D0 +
          wb * (solutionDriverStep V hX₁ hX₂ hω1 hXd hfine hωne hδα
            hδα1 hsol₁ hsol₂ h0 D).Db +
          wc * (solutionDriverStep V hX₁ hX₂ hω1 hXd hfine hωne hδα
            hδα1 hsol₁ hsol₂ h0 D).Dd +
          we * (solutionDriverStep V hX₁ hX₂ hω1 hXd hfine hωne hδα
            hδα1 hsol₁ hsol₂ h0 D).Dy) ≤
        (wa * D.D0 + wb * D.Db + wc * D.Dd + we * D.Dy) + Coff) :
    ∀ u : ℝ, dist (Z₁.Y u) (Z₂.Y u) ≤ (Coff : ℝ) / (wa : ℝ) := by
  intro u
  -- the iterated mixed distance certificates
  let Dseq : ℕ → MixedDist Z₁ Z₂ := fun n =>
    Nat.rec (mixedSeedDist hX₁ hX₂ hω1 hδα h0 hZ₁ hZ₂)
      (fun _ D => solutionDriverStep V hX₁ hX₂ hω1 hXd hfine hωne hδα
        hδα1 hsol₁ hsol₂ h0 D) n
  have hDsucc : ∀ n : ℕ, Dseq (n + 1) =
      solutionDriverStep V hX₁ hX₂ hω1 hXd hfine hωne hδα hδα1
        hsol₁ hsol₂ h0 (Dseq n) := fun n => rfl
  set ρw : ℕ → ℝ≥0 := fun n =>
    wa * (Dseq n).D0 + wb * (Dseq n).Db + wc * (Dseq n).Dd +
      we * (Dseq n).Dy with hρdef
  have hstep : ∀ n : ℕ, 2 * ρw (n + 1) ≤ ρw n + Coff := by
    intro n
    rw [hρdef]
    simp only [hDsucc n]
    exact hcontr (Dseq n)
  -- affine geometric decay, in ℝ
  have hreal : ∀ n : ℕ, ((ρw n : ℝ≥0) : ℝ) ≤
      (1 / 2 : ℝ) ^ n * ((ρw 0 : ℝ≥0) : ℝ) + (Coff : ℝ) := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, one_mul]
        exact le_add_of_le_of_nonneg le_rfl Coff.coe_nonneg
    | succ n ih =>
        have h2 : (2 : ℝ) * ((ρw (n + 1) : ℝ≥0) : ℝ) ≤
            ((ρw n : ℝ≥0) : ℝ) + (Coff : ℝ) := by
          exact_mod_cast hstep n
        have hpowP : ((1 : ℝ) / 2) ^ (n + 1) * ((ρw 0 : ℝ≥0) : ℝ) =
            (1 / 2 : ℝ) ^ n * ((ρw 0 : ℝ≥0) : ℝ) * (1 / 2) := by
          rw [pow_succ]
          ring
        linarith [ih, h2, hpowP]
  -- pointwise distance dominated by every iterate
  have hdist : ∀ n : ℕ, dist (Z₁.Y u) (Z₂.Y u) ≤
      ((1 / 2 : ℝ) ^ n * ((ρw 0 : ℝ≥0) : ℝ) + (Coff : ℝ)) / (wa : ℝ) := by
    intro n
    have h1 : dist (Z₂.Y u) (Z₁.Y u) ≤ (((Dseq n).D0 : ℝ≥0) : ℝ) :=
      dist_le_coe_of_enorm_le ((Dseq n).bound_Y u)
    have hwa0 : ((Dseq n).D0 : ℝ) * (wa : ℝ) ≤ ((ρw n : ℝ≥0) : ℝ) := by
      have hle : wa * (Dseq n).D0 ≤ ρw n := by
        rw [hρdef]
        exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
          (le_add_of_le_of_nonneg le_rfl zero_le) zero_le) zero_le
      calc ((Dseq n).D0 : ℝ) * (wa : ℝ)
          = ((wa * (Dseq n).D0 : ℝ≥0) : ℝ) := by push_cast; ring
        _ ≤ ((ρw n : ℝ≥0) : ℝ) := by exact_mod_cast hle
    have hwapos : (0 : ℝ) < (wa : ℝ) := by exact_mod_cast hwa
    rw [dist_comm]
    calc dist (Z₂.Y u) (Z₁.Y u) ≤ (((Dseq n).D0 : ℝ≥0) : ℝ) := h1
      _ ≤ ((ρw n : ℝ≥0) : ℝ) / (wa : ℝ) :=
          (le_div_iff₀ hwapos).2 hwa0
      _ ≤ ((1 / 2 : ℝ) ^ n * ((ρw 0 : ℝ≥0) : ℝ) + (Coff : ℝ)) /
            (wa : ℝ) := by
          gcongr
          exact hreal n
  -- pass to the limit
  have hlim : Filter.Tendsto
      (fun n : ℕ =>
        ((1 / 2 : ℝ) ^ n * ((ρw 0 : ℝ≥0) : ℝ) + (Coff : ℝ)) / (wa : ℝ))
      Filter.atTop
      (nhds (((0 : ℝ) * ((ρw 0 : ℝ≥0) : ℝ) + (Coff : ℝ)) / (wa : ℝ))) := by
    refine Filter.Tendsto.div_const ?_ _
    refine Filter.Tendsto.add_const _ ?_
    refine Filter.Tendsto.mul_const _ ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num)
  rw [zero_mul, zero_add] at hlim
  exact ge_of_tendsto' hlim hdist

end RDEVectorField3

end RoughPaths
