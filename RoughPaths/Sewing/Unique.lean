/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Sewing.AdditiveLimit

/-!
# Uniqueness of the additive sewing

Any two additive two-parameter maps with a germ bound `C·ω^θ`, `θ > 1`,
agree (telescoping over fine partitions). Consequently the additive sewing
of `RoughPaths.Sewing.sewing` is unique.
-/

namespace RoughPaths

namespace Sewing

open scoped ENNReal

universe u v

variable {T : Type u} {E : Type v}

section PairSumHelpers

/-- Pair sums of an additive two-parameter map telescope. -/
theorem pairSum_eq_of_additive [LinearOrder T] [AddCommMonoid E] {I : T → T → E}
    (hadd : ∀ ⦃a u b : T⦄, a ≤ u → u ≤ b → I a u + I u b = I a b) :
    ∀ {mid : List T} {s t : T},
      List.IsChain (· ≤ ·) (s :: (mid ++ [t])) →
      pairSum (fun a b => I a b) (s :: (mid ++ [t])) = I s t
  | [], s, t, _ => by
      simp [pairSum_cons_cons]
  | y :: mid, s, t, h => by
      rw [List.cons_append, List.isChain_cons_cons] at h
      have hyt : y ≤ t := by
        have h1 := chain_mem_bounds h.2 y (by simp)
        exact h1.2
      rw [List.cons_append, pairSum_cons_cons,
        pairSum_eq_of_additive hadd h.2, hadd h.1 hyt]

/-- The extended norm of a pair sum is at most the pair sum of the
extended norms. -/
theorem enorm_pairSum_le [Preorder T] [NormedAddCommGroup E]
    (h : T → T → E) :
    ∀ l : List T, ‖pairSum h l‖ₑ ≤ pairSum (fun a b => ‖h a b‖ₑ) l
  | [] => by simp
  | [_] => by simp
  | x :: y :: rest => by
      rw [pairSum_cons_cons, pairSum_cons_cons]
      exact le_trans (enorm_add_le _ _)
        (add_le_add le_rfl (enorm_pairSum_le h (y :: rest)))

/-- Pair sums are monotone in the summand along a chain. -/
theorem pairSum_le_pairSum_of_chain [Preorder T]
    {h₁ h₂ : T → T → ℝ≥0∞}
    (hle : ∀ ⦃a b : T⦄, a ≤ b → h₁ a b ≤ h₂ a b) :
    ∀ {l : List T}, List.IsChain (· ≤ ·) l →
      pairSum h₁ l ≤ pairSum h₂ l
  | [], _ => le_refl _
  | [_], _ => le_refl _
  | x :: y :: rest, hchain => by
      rw [List.isChain_cons_cons] at hchain
      rw [pairSum_cons_cons, pairSum_cons_cons]
      exact add_le_add (hle hchain.1)
        (pairSum_le_pairSum_of_chain hle hchain.2)

/-- Constants pull out of pair sums. -/
theorem pairSum_const_mul [Preorder T] (C : ℝ≥0∞) (h : T → T → ℝ≥0∞) :
    ∀ l : List T, pairSum (fun a b => C * h a b) l = C * pairSum h l
  | [] => by simp
  | [_] => by simp
  | x :: y :: rest => by
      rw [pairSum_cons_cons, pairSum_cons_cons,
        pairSum_const_mul C h (y :: rest), mul_add]

end PairSumHelpers

section Uniqueness

variable [LinearOrder T] [NormedAddCommGroup E]

/-- **Uniqueness of the additive sewing**: two additive maps with germ
bounds `C·ω^θ`, `C'·ω^θ`, `θ > 1`, agree on comparable pairs. -/
theorem eq_of_additive_of_germ_bound
    (ω : Control T) (Ξ : T → T → E) {θ : ℝ} (hθ : 1 < θ)
    {C C' : ℝ≥0∞} (hC : C ≠ ⊤) (hC' : C' ≠ ⊤)
    (hfine : HasFinePartitions ω)
    {I I' : T → T → E}
    (hadd : ∀ ⦃a u b : T⦄, a ≤ u → u ≤ b → I a u + I u b = I a b)
    (hadd' : ∀ ⦃a u b : T⦄, a ≤ u → u ≤ b → I' a u + I' u b = I' a b)
    (hI : ∀ ⦃a b : T⦄, a ≤ b → ‖I a b - Ξ a b‖ₑ ≤ C * ω a b ^ θ)
    (hI' : ∀ ⦃a b : T⦄, a ≤ b → ‖I' a b - Ξ a b‖ₑ ≤ C' * ω a b ^ θ)
    {s t : T} (hst : s ≤ t) (hω : ω s t ≠ ⊤) :
    I s t = I' s t := by
  have hθ1 : (0 : ℝ) ≤ θ - 1 := by linarith
  set J : T → T → E := fun a b => I a b - I' a b with hJ
  have hJadd : ∀ ⦃a u b : T⦄, a ≤ u → u ≤ b → J a u + J u b = J a b := by
    intro a u b hau hub
    simp only [hJ]
    rw [show I a u - I' a u + (I u b - I' u b) =
      (I a u + I u b) - (I' a u + I' u b) by abel,
      hadd hau hub, hadd' hau hub]
  have hJbound : ∀ ⦃a b : T⦄, a ≤ b → ‖J a b‖ₑ ≤ (C + C') * ω a b ^ θ := by
    intro a b hab
    simp only [hJ]
    calc ‖I a b - I' a b‖ₑ
        = ‖(I a b - Ξ a b) - (I' a b - Ξ a b)‖ₑ := by
          congr 1
          abel
      _ ≤ ‖I a b - Ξ a b‖ₑ + ‖I' a b - Ξ a b‖ₑ := by
          rw [sub_eq_add_neg]
          refine le_trans (enorm_add_le _ _) (le_of_eq ?_)
          rw [enorm_neg]
      _ ≤ C * ω a b ^ θ + C' * ω a b ^ θ := add_le_add (hI hab) (hI' hab)
      _ = (C + C') * ω a b ^ θ := (add_mul _ _ _).symm
  -- telescope over fine chains
  have key : ∀ ε : ℝ≥0∞, 0 < ε →
      ‖J s t‖ₑ ≤ (C + C') * (ε ^ (θ - 1) * ω s t) := by
    intro ε hε
    obtain ⟨mid, hchain⟩ := hfine hst ε hε
    have hchain' : List.IsChain (· ≤ ·) (s :: (mid ++ [t])) :=
      hchain.imp fun a b hab => hab.1
    calc ‖J s t‖ₑ
        = ‖pairSum (fun a b => J a b) (s :: (mid ++ [t]))‖ₑ := by
          rw [pairSum_eq_of_additive hJadd hchain']
      _ ≤ pairSum (fun a b => ‖J a b‖ₑ) (s :: (mid ++ [t])) :=
          enorm_pairSum_le _ _
      _ ≤ pairSum (fun a b => (C + C') * ω a b ^ θ) (s :: (mid ++ [t])) :=
          pairSum_le_pairSum_of_chain (fun a b hab => hJbound hab) hchain'
      _ = (C + C') * pairSum (fun a b => ω a b ^ θ) (s :: (mid ++ [t])) :=
          pairSum_const_mul _ _ _
      _ ≤ (C + C') * (ε ^ (θ - 1) * ω s t) :=
          mul_le_mul_right (pairSum_rpow_le_of_fine ω hθ1 s mid t hchain) _
  -- let ε → 0 along the geometric sequence
  have hzero : Filter.Tendsto
      (fun k : ℕ => (C + C') *
        ((((2 : ℝ≥0∞)⁻¹ ^ (θ - 1)) ^ k) * ω s t))
      Filter.atTop (nhds 0) := by
    have hr₀lt : ((2 : ℝ≥0∞)⁻¹ ^ (θ - 1)) < 1 :=
      ENNReal.rpow_lt_one (ENNReal.inv_lt_one.2 (by norm_num)) (by linarith)
    have hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr₀lt
    have h1 := ENNReal.Tendsto.const_mul
      (a := (C + C') * ω s t) hpow
      (Or.inr (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hC, hC'⟩) hω))
    simpa [mul_zero, mul_comm, mul_assoc, mul_left_comm] using h1
  have hbound : ∀ k : ℕ, ‖J s t‖ₑ ≤ (C + C') *
      ((((2 : ℝ≥0∞)⁻¹ ^ (θ - 1)) ^ k) * ω s t) := by
    intro k
    have hεk : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ k :=
      ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) k
    have h1 := key ((2 : ℝ≥0∞)⁻¹ ^ k) hεk
    rw [pow_rpow_exchange (θ := θ) k] at h1
    exact h1
  have hnorm : ‖J s t‖ₑ = 0 :=
    le_antisymm (ge_of_tendsto' hzero hbound) zero_le
  have h0 : J s t = 0 := enorm_eq_zero.1 hnorm
  simpa [hJ, sub_eq_zero] using h0

end Uniqueness

end Sewing

end RoughPaths
