/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Sewing.ChainRefine
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The additive sewing lemma: partition comparison

Over a `LinearOrder` time set, two fine partitions of the same interval
have Riemann sums within `K·(ε^{θ−1} + ε'^{θ−1})·ω(s,t)` of each other:
each is compared with their common refinement through `ChainRefine`.
This is the quantitative core of the additive sewing lemma; the limit
construction lives in `RoughPaths.Sewing.AdditiveLimit`.
-/

namespace RoughPaths

namespace Sewing

open scoped ENNReal

universe u v

variable {T : Type u} [LinearOrder T] {E : Type v}

/-- The sewing constant `K(θ) = Σ_j (2/(j+1))^θ`. -/
noncomputable def sewingConst (θ : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, (2 / ((j : ℝ≥0∞) + 1)) ^ θ

theorem sewingConst_ne_top {θ : ℝ} (hθ : 1 < θ) : sewingConst θ ≠ ⊤ :=
  (sewingConst_lt_top hθ).ne

section Germ

variable [NormedAddCommGroup E]

/-- The germ of a sewing problem vanishes on the diagonal. -/
theorem germ_diag_eq_zero {ω : Control T} {Ξ : T → T → E} {θ : ℝ}
    (hθ : 0 < θ)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ) (t : T) :
    Ξ t t = 0 := by
  have h := hδ (le_refl t) (le_refl t)
  rw [ω.diagonal, ENNReal.zero_rpow_of_pos hθ] at h
  have h2 : Ξ t t - Ξ t t - Ξ t t = -Ξ t t := by abel
  rw [h2, enorm_neg] at h
  exact enorm_eq_zero.1 (le_antisymm h zero_le)

/-- Every element of a monotone chain lies between the endpoints. -/
theorem chain_mem_bounds :
    ∀ {mid : List T} {x t : T},
      List.IsChain (· ≤ ·) (x :: (mid ++ [t])) →
      ∀ z ∈ x :: (mid ++ [t]), x ≤ z ∧ z ≤ t
  | [], x, t, h, z, hz => by
      have hxt : x ≤ t := List.isChain_pair.1 (by simpa using h)
      rcases List.mem_cons.1 hz with rfl | hz'
      · exact ⟨le_refl z, hxt⟩
      · simp only [List.nil_append, List.mem_singleton] at hz'
        exact ⟨hz' ▸ hxt, le_of_eq hz'⟩
  | y :: mid, x, t, h, z, hz => by
      rw [List.cons_append, List.isChain_cons_cons] at h
      rcases List.mem_cons.1 hz with rfl | hz'
      · refine ⟨le_refl z, ?_⟩
        have h1 := chain_mem_bounds h.2 y (by simp)
        exact le_trans h.1 h1.2
      · have h1 := chain_mem_bounds h.2 z hz'
        exact ⟨le_trans h.1 h1.1, h1.2⟩

omit [LinearOrder T] in
/-- Riemann sums over chains from `t` to `t` vanish. -/
theorem pairSum_eq_zero_of_const {Ξ : T → T → E}
    (hdiag : ∀ t : T, Ξ t t = 0) :
    ∀ {l : List T} {t : T}, (∀ z ∈ l, z = t) → pairSum Ξ l = 0
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: rest, t, hconst => by
      have h1 : Ξ x y = 0 := by
        rw [hconst x (by simp), hconst y (by simp)]
        exact hdiag t
      rw [pairSum_cons_cons, h1, zero_add]
      exact pairSum_eq_zero_of_const hdiag fun z hz =>
        hconst z (List.mem_cons_of_mem _ hz)

end Germ

section Compare

variable [NormedAddCommGroup E]

variable (ω : Control T) (Ξ : T → T → E) {θ : ℝ}

/-- **Refinement comparison**: the Riemann sum of a fine chain is close to
that of any strict chain refining it. -/
theorem pairSum_sub_pairSum_le_of_refines
    (hθ0 : (0 : ℝ) ≤ θ) (hθ1 : (0 : ℝ) ≤ θ - 1)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ)
    {s t : T} {midp midr : List T} {ε : ℝ≥0∞}
    (hp : List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (s :: (midp ++ [t])))
    (hpstrict : List.IsChain (· < ·) (s :: (midp ++ [t])))
    (hr : List.IsChain (· < ·) (s :: (midr ++ [t])))
    (hsub : ∀ z ∈ s :: (midp ++ [t]), z ∈ s :: (midr ++ [t])) :
    ‖pairSum Ξ (s :: (midr ++ [t])) - pairSum Ξ (s :: (midp ++ [t]))‖ₑ ≤
      sewingConst θ * (ε ^ (θ - 1) * ω s t) := by
  set ps := refineAlong (s :: (midr ++ [t])) (s :: (midp ++ [t])) with hps
  have hbase : basePoints ps t = s :: (midp ++ [t]) :=
    basePoints_refineAlong _ midp s t
  have hglue : glue ps t = s :: (midr ++ [t]) := by
    rw [hps]
    refine glue_refineAlong midp s t (midr ++ [t]) hr hpstrict ?_ hsub
    rw [List.getLast_cons (by simp)]
    exact List.getLast_concat
  have hchain_glue : List.IsChain (· ≤ ·) (glue ps t) := by
    rw [hglue]
    exact hr.imp fun a b hab => le_of_lt hab
  have h1 := refine_bound ω Ξ θ hθ0 hδ ps t hchain_glue
  rw [hglue, hbase] at h1
  refine le_trans h1 ?_
  rw [show sewingConst θ * (ε ^ (θ - 1) * ω s t) =
    (∑' j : ℕ, (2 / ((j : ℝ≥0∞) + 1)) ^ θ) * (ε ^ (θ - 1) * ω s t) from rfl]
  exact mul_le_mul_right
    (pairSum_rpow_le_of_fine ω hθ1 s midp t hp) _

/-- **Mesh comparison of two fine chains** via their common refinement. -/
theorem pairSum_sub_pairSum_le_of_fine
    (hθ0 : (0 : ℝ) ≤ θ) (hθ1 : (0 : ℝ) ≤ θ - 1)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ)
    {s t : T} (hst : s < t) {midp midq : List T} {ε ε' : ℝ≥0∞}
    (hp : List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (s :: (midp ++ [t])))
    (hpstrict : List.IsChain (· < ·) (s :: (midp ++ [t])))
    (hq : List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε') (s :: (midq ++ [t])))
    (hqstrict : List.IsChain (· < ·) (s :: (midq ++ [t]))) :
    ‖pairSum Ξ (s :: (midp ++ [t])) - pairSum Ξ (s :: (midq ++ [t]))‖ₑ ≤
      sewingConst θ * (ε ^ (θ - 1) * ω s t) +
        sewingConst θ * (ε' ^ (θ - 1) * ω s t) := by
  -- the common refinement: sort and deduplicate the union of points
  set raw : List T :=
    ((s :: (midp ++ [t])) ++ (s :: (midq ++ [t]))).mergeSort
      (fun a b => decide (a ≤ b)) with hraw
  set r : List T := dedupChain raw with hrdef
  have hraw_sorted : List.IsChain (· ≤ ·) raw := by
    rw [List.isChain_iff_pairwise, hraw]
    exact List.pairwise_mergeSort' (· ≤ · : T → T → Prop) _
  have hr_strict : List.IsChain (· < ·) r := isChain_lt_dedupChain hraw_sorted
  have hmem_r : ∀ z, z ∈ r ↔ z ∈ (s :: (midp ++ [t])) ∨
      z ∈ (s :: (midq ++ [t])) := by
    intro z
    rw [hrdef, mem_dedupChain, hraw, List.mem_mergeSort, List.mem_append]
  have hmem_bounds : ∀ z ∈ r, s ≤ z ∧ z ≤ t := by
    intro z hz
    rcases (hmem_r z).1 hz with h0 | h0
    · exact chain_mem_bounds (hpstrict.imp fun a b h => le_of_lt h) z h0
    · exact chain_mem_bounds (hqstrict.imp fun a b h => le_of_lt h) z h0
  have hs_r : s ∈ r := (hmem_r s).2 (Or.inl (by simp))
  have ht_r : t ∈ r := (hmem_r t).2 (Or.inl (by simp))
  have hr_ne : r ≠ [] := List.ne_nil_of_mem hs_r
  -- put r into the canonical shape s :: (midr ++ [t])
  obtain ⟨w, ws, hr0⟩ : ∃ w ws, r = w :: ws := by
    rcases hr0 : r with _ | ⟨w, ws⟩
    · exact absurd hr0 hr_ne
    · exact ⟨w, ws, rfl⟩
  have hw : w = s := by
    have hws : s ≤ w := (hmem_bounds w (by rw [hr0]; simp)).1
    rcases List.mem_cons.1 (hr0 ▸ hs_r) with h0 | h0
    · exact h0.symm
    · exact absurd (lt_of_le_of_lt hws
        (head_lt_of_mem_tail (hr0 ▸ hr_strict) h0)) (lt_irrefl s)
  subst hw
  have hlast : (w :: ws).getLast (by simp) = t := by
    have hle : (w :: ws).getLast (by simp) ≤ t :=
      (hmem_bounds _ (by rw [hr0]; exact List.getLast_mem (by simp))).2
    rcases eq_or_lt_of_le hle with h0 | h0
    · exact h0
    · exfalso
      have ht_r' : t ∈ w :: ws := hr0 ▸ ht_r
      rw [← List.dropLast_append_getLast (l := w :: ws) (by simp),
        List.mem_append] at ht_r'
      rcases ht_r' with h1 | h1
      · exact absurd (lt_trans (lt_getLast_of_mem_dropLast
          (hr0 ▸ hr_strict) (by simp) t h1) h0) (lt_irrefl t)
      · simp only [List.mem_singleton] at h1
        exact absurd (h1 ▸ h0) (lt_irrefl t)
  have hws_ne : ws ≠ [] := by
    intro h0
    subst h0
    simp only [List.getLast_singleton] at hlast
    exact absurd (hlast ▸ hst) (lt_irrefl w)
  obtain ⟨midr, hws_eq⟩ : ∃ midr, ws = midr ++ [t] := by
    refine ⟨ws.dropLast, ?_⟩
    conv_lhs => rw [← List.dropLast_append_getLast hws_ne]
    rw [show ws.getLast hws_ne = t from by
      rw [List.getLast_cons hws_ne] at hlast
      exact hlast]
  subst hws_eq
  have hr_strict2 : List.IsChain (· < ·) (w :: (midr ++ [t])) :=
    hr0 ▸ hr_strict
  have hsubp : ∀ z ∈ w :: (midp ++ [t]), z ∈ w :: (midr ++ [t]) :=
    fun z hz => hr0 ▸ ((hmem_r z).2 (Or.inl hz))
  have hsubq : ∀ z ∈ w :: (midq ++ [t]), z ∈ w :: (midr ++ [t]) :=
    fun z hz => hr0 ▸ ((hmem_r z).2 (Or.inr hz))
  have h1 := pairSum_sub_pairSum_le_of_refines ω Ξ hθ0 hθ1 hδ
    hp hpstrict hr_strict2 hsubp
  have h2 := pairSum_sub_pairSum_le_of_refines ω Ξ hθ0 hθ1 hδ
    hq hqstrict hr_strict2 hsubq
  calc ‖pairSum Ξ (w :: (midp ++ [t])) - pairSum Ξ (w :: (midq ++ [t]))‖ₑ
      = ‖(pairSum Ξ (w :: (midr ++ [t])) - pairSum Ξ (w :: (midq ++ [t]))) -
          (pairSum Ξ (w :: (midr ++ [t])) - pairSum Ξ (w :: (midp ++ [t])))‖ₑ := by
        congr 1
        abel
    _ ≤ ‖pairSum Ξ (w :: (midr ++ [t])) - pairSum Ξ (w :: (midq ++ [t]))‖ₑ +
          ‖pairSum Ξ (w :: (midr ++ [t])) - pairSum Ξ (w :: (midp ++ [t]))‖ₑ := by
        rw [sub_eq_add_neg]
        refine le_trans (enorm_add_le _ _) (le_of_eq ?_)
        rw [enorm_neg]
    _ = ‖pairSum Ξ (w :: (midr ++ [t])) - pairSum Ξ (w :: (midp ++ [t]))‖ₑ +
          ‖pairSum Ξ (w :: (midr ++ [t])) - pairSum Ξ (w :: (midq ++ [t]))‖ₑ :=
        add_comm _ _
    _ ≤ _ := add_le_add h1 h2

end Compare

end Sewing

end RoughPaths
