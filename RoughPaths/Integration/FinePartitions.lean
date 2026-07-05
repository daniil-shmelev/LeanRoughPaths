/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Sewing.Basic
import RoughPaths.Integration.Controls

/-!
# Discharging `HasFinePartitions`

Concrete controls admit arbitrarily fine partitions: the linear control on
`ℝ` via uniform subdivision (the workhorse), controls dominated by a fine
one, and powers of fine controls.
-/

namespace RoughPaths

open scoped ENNReal

universe u

namespace Sewing

variable {T : Type u} [Preorder T]

/-- A control dominated by one with fine partitions has fine partitions. -/
theorem HasFinePartitions.of_le {ω η : Control T}
    (h : HasFinePartitions η)
    (hle : ∀ ⦃s t : T⦄, s ≤ t → ω s t ≤ η s t) :
    HasFinePartitions ω := by
  intro s t hst ε hε
  obtain ⟨q, hq⟩ := h hst ε hε
  exact ⟨q, hq.imp fun a b hab => ⟨hab.1, le_trans (hle hab.1) hab.2⟩⟩

/-- Scalar multiples of controls with fine partitions have fine
partitions. -/
theorem HasFinePartitions.constMul {ω : Control T}
    (h : HasFinePartitions ω) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    HasFinePartitions (Control.constMul c ω) := by
  intro s t hst ε hε
  rcases eq_or_ne c 0 with rfl | hc0
  · obtain ⟨q, hq⟩ := h hst 1 zero_lt_one
    refine ⟨q, hq.imp fun a b hab => ⟨hab.1, ?_⟩⟩
    rw [Control.constMul_apply, zero_mul]
    exact zero_le
  · have hε' : 0 < ε / c := ENNReal.div_pos hε.ne' hc
    obtain ⟨q, hq⟩ := h hst (ε / c) hε'
    refine ⟨q, hq.imp fun a b hab => ⟨hab.1, ?_⟩⟩
    rw [Control.constMul_apply]
    calc c * ω a b ≤ c * (ε / c) := mul_le_mul' le_rfl hab.2
      _ ≤ ε := ENNReal.mul_div_le

/-- Between any two reals there is a uniform chain whose steps have length
at most `(t − s)/n`. -/
private theorem exists_uniform_chain :
    ∀ n : ℕ, 0 < n → ∀ s t : ℝ, s ≤ t →
      ∃ q : List ℝ,
        List.IsChain (fun a b => a ≤ b ∧ b - a ≤ (t - s) / n)
          (s :: (q ++ [t]))
  | 1, _, s, t, hst => ⟨[], by
      simp only [List.nil_append, List.isChain_cons_cons]
      exact ⟨⟨hst, by simp⟩, List.isChain_singleton t⟩⟩
  | (n + 2), _, s, t, hst => by
      push_cast
      have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hδ0 : 0 ≤ (t - s) / ((n : ℝ) + 2) := by positivity
      set δ : ℝ := (t - s) / ((n : ℝ) + 2) with hδ
      set s' : ℝ := s + δ with hs'
      have hss' : s ≤ s' := by rw [hs']; linarith
      have hs't : s' ≤ t := by
        rw [hs', hδ]
        have h1 : (t - s) / ((n : ℝ) + 2) ≤ t - s :=
          div_le_self (sub_nonneg.2 hst) (by linarith)
        linarith
      obtain ⟨q', hq'⟩ := exists_uniform_chain (n + 1) (Nat.succ_pos n) s' t hs't
      have hstep : (t - s') / ((n : ℝ) + 1) = δ := by
        rw [hs', hδ]
        field_simp
        ring
      refine ⟨s' :: q', ?_⟩
      have hchain : List.IsChain
          (fun a b => a ≤ b ∧ b - a ≤ (t - s) / ((n : ℝ) + 2))
          (s' :: (q' ++ [t])) := by
        refine hq'.imp fun a b hab => ⟨hab.1, ?_⟩
        have h2 := hab.2
        push_cast at h2
        calc b - a ≤ (t - s') / ((n : ℝ) + 1) := h2
          _ = δ := hstep
          _ = (t - s) / ((n : ℝ) + 2) := hδ
      simp only [List.cons_append, List.isChain_cons_cons]
      refine ⟨⟨hss', ?_⟩, hchain⟩
      rw [hs']
      simp only [add_sub_cancel_left]
      exact le_of_eq hδ

/-- The linear control on `ℝ` admits fine partitions (uniform subdivision). -/
theorem _root_.RoughPaths.Control.ofReal_hasFinePartitions
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    HasFinePartitions (Control.ofReal c) := by
  intro s t hst ε hε
  by_cases hεtop : ε = ⊤
  · refine ⟨[], ?_⟩
    simp only [List.nil_append, List.isChain_cons_cons]
    exact ⟨⟨hst, hεtop ▸ le_top⟩, List.isChain_singleton t⟩
  · have hx : c * ENNReal.ofReal (t - s) / ε ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top) hε.ne'
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact absurd hn (by simp)
      · exact h
    have hstep : c * ENNReal.ofReal ((t - s) / n) ≤ ε := by
      have h1 : c * ENNReal.ofReal (t - s) < n * ε :=
        (ENNReal.div_lt_iff (Or.inl hε.ne') (Or.inl hεtop)).1 hn
      have h2 : ENNReal.ofReal ((t - s) / n) =
          ENNReal.ofReal (t - s) / ENNReal.ofReal n := by
        rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn0)]
      rw [h2, ENNReal.ofReal_natCast, ← mul_div_assoc,
        ENNReal.div_le_iff (by exact_mod_cast hn0.ne') (ENNReal.natCast_ne_top n)]
      calc c * ENNReal.ofReal (t - s) ≤ n * ε := le_of_lt h1
        _ = ε * n := mul_comm _ _
    obtain ⟨q, hq⟩ := exists_uniform_chain n hn0 s t hst
    refine ⟨q, hq.imp fun a b hab => ⟨hab.1, ?_⟩⟩
    calc Control.ofReal c a b = c * ENNReal.ofReal (b - a) := rfl
      _ ≤ c * ENNReal.ofReal ((t - s) / n) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hab.2) c
      _ ≤ ε := hstep

/-- Powers of fine controls are fine. -/
theorem HasFinePartitions.rpow {ω : Control T}
    (h : HasFinePartitions ω) {p : ℝ} (hp : 1 ≤ p) :
    HasFinePartitions (ω.rpow p hp) := by
  intro s t hst ε hε
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hδ : (0 : ℝ≥0∞) < ε ^ (1 / p) := by
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · rw [ENNReal.top_rpow_of_pos (by positivity)]
      exact ENNReal.zero_lt_top
    · exact ENNReal.rpow_pos hε hεtop
  obtain ⟨q, hq⟩ := h hst _ hδ
  refine ⟨q, hq.imp fun a b hab => ⟨hab.1, ?_⟩⟩
  calc ω.rpow p hp a b = ω a b ^ p := rfl
    _ ≤ (ε ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow hab.2 (le_of_lt hp0)
    _ = ε := by
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]

end Sewing

end RoughPaths
