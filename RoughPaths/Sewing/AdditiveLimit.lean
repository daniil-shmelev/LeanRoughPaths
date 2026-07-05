/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Sewing.Additive

/-!
# The additive sewing lemma: limit construction

Along a geometric sequence of finenesses the Riemann sums of fine
partitions form a Cauchy sequence; its limit is the sewing `I s t`. The
resulting two-parameter map is additive (`I s u + I u t = I s t`), close
to the germ (`‖I s t − Ξ s t‖ₑ ≤ K·ω^θ`), and approximates every fine
partition's Riemann sum — hence is the mesh limit and is unique among
additive maps with a germ bound.
-/

namespace RoughPaths

namespace Sewing

open scoped ENNReal
open Filter

universe u v

variable {T : Type u} [LinearOrder T] {E : Type v} [NormedAddCommGroup E]

omit [LinearOrder T] in
/-- Canonical shape of a list with prescribed distinct endpoints. -/
private theorem shape_of_head?_getLast? {l : List T} {s t : T}
    (hh : l.head? = some s) (hl : l.getLast? = some t) (hne : s ≠ t) :
    ∃ mid, l = s :: (mid ++ [t]) := by
  rcases l with _ | ⟨w, ws⟩
  · simp at hh
  obtain rfl : w = s := by simpa using hh
  have hws_ne : ws ≠ [] := by
    rintro rfl
    simp only [List.getLast?_singleton, Option.some_inj] at hl
    exact hne hl
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hws_ne
  rw [List.getLast?_cons_cons] at hl
  have hgl : (a :: as).getLast (by simp) = t := by
    rw [List.getLast?_eq_some_getLast (l := a :: as) (by simp)] at hl
    exact Option.some_injective _ hl
  refine ⟨(a :: as).dropLast, ?_⟩
  rw [List.cons_inj_right]
  conv_lhs => rw [← List.dropLast_append_getLast (l := a :: as) (by simp)]
  rw [hgl]

/-- The rpow/pow exchange for the geometric fineness sequence. -/
theorem pow_rpow_exchange {θ : ℝ} (k : ℕ) :
    (((2 : ℝ≥0∞)⁻¹ ^ k) : ℝ≥0∞) ^ (θ - 1) =
      ((2 : ℝ≥0∞)⁻¹ ^ (θ - 1)) ^ k := by
  rw [← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) k, ← ENNReal.rpow_mul,
    mul_comm, ENNReal.rpow_mul, ENNReal.rpow_natCast]

section Limit

variable [CompleteSpace E]

variable (ω : Control T) (Ξ : T → T → E) {θ : ℝ}

/-- **Existence of the sewing limit on one interval**: there is `L` within
`K·ε^{θ−1}·ω(s,t)` of the Riemann sum of every `ε`-fine partition. -/
theorem exists_sewing_limit (hθ : 1 < θ)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ)
    (hfine : HasFinePartitions ω) {s t : T} (hst : s ≤ t) (hω : ω s t ≠ ⊤) :
    ∃ L : E, ∀ (ε : ℝ≥0∞) (mid : List T),
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (s :: (mid ++ [t])) →
      ‖L - pairSum Ξ (s :: (mid ++ [t]))‖ₑ ≤
        sewingConst θ * (ε ^ (θ - 1) * ω s t) := by
  have hθ0 : (0 : ℝ) ≤ θ := le_trans zero_le_one (le_of_lt hθ)
  have hθ1 : (0 : ℝ) ≤ θ - 1 := by linarith
  have hdiag : ∀ u : T, Ξ u u = 0 :=
    germ_diag_eq_zero (lt_of_lt_of_le zero_lt_one (le_of_lt hθ)) hδ
  rcases eq_or_lt_of_le hst with rfl | hst'
  · -- degenerate interval: all fine chains are constant, sums vanish
    refine ⟨0, fun ε mid hchain => ?_⟩
    have hconst : ∀ z ∈ s :: (mid ++ [s]), z = s := by
      intro z hz
      have h1 := chain_mem_bounds (hchain.imp fun a b hab => hab.1) z hz
      exact le_antisymm h1.2 h1.1
    rw [pairSum_eq_zero_of_const hdiag hconst, zero_sub, enorm_neg,
      enorm_zero]
    exact zero_le

  -- geometric fineness sequence
  set ε' : ℕ → ℝ≥0∞ := fun k => (2 : ℝ≥0∞)⁻¹ ^ k with hε'
  have hε'pos : ∀ k, 0 < ε' k := fun k =>
    ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) k
  choose q hq using fun k => hfine hst (ε' k) (hε'pos k)
  -- deduplicate to strict chains in canonical shape
  have hshape : ∀ k, ∃ mid,
      dedupChain (s :: (q k ++ [t])) = s :: (mid ++ [t]) := by
    intro k
    refine shape_of_head?_getLast? ?_ ?_ (ne_of_lt hst')
    · rw [head?_dedupChain]
      rfl
    · rw [getLast?_dedupChain,
        show s :: (q k ++ [t]) = (s :: q k) ++ [t] from rfl]
      exact List.getLast?_concat
  choose mid hmid using hshape
  set S : ℕ → E := fun k => pairSum Ξ (s :: (mid k ++ [t])) with hS
  -- transported chain facts
  have hfineC : ∀ k, List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε' k)
      (s :: (mid k ++ [t])) := by
    intro k
    rw [← hmid k]
    exact isChain_fine_dedupChain (hq k)
  have hstrictC : ∀ k, List.IsChain (· < ·) (s :: (mid k ++ [t])) := by
    intro k
    rw [← hmid k]
    exact isChain_lt_dedupChain ((hq k).imp fun a b hab => hab.1)
  -- consecutive Cauchy estimate
  set r₀ : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ (θ - 1) with hr₀
  have hr₀lt : r₀ < 1 :=
    ENNReal.rpow_lt_one (ENNReal.inv_lt_one.2 (by norm_num)) (by linarith)
  have hr₀le : r₀ ≤ 1 := le_of_lt hr₀lt
  have hεpow : ∀ k, ε' k ^ (θ - 1) = r₀ ^ k := fun k => pow_rpow_exchange k
  set C₀ : ℝ≥0∞ := 2 * (sewingConst θ * ω s t) with hC₀
  have hC₀top : C₀ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (sewingConst_ne_top hθ) hω)
  have hcons : ∀ k, edist (S k) (S (k + 1)) ≤ C₀ * r₀ ^ k := by
    intro k
    rw [edist_eq_enorm_sub]
    refine le_trans (pairSum_sub_pairSum_le_of_fine ω Ξ hθ0 hθ1 hδ hst'
      (hfineC k) (hstrictC k) (hfineC (k + 1)) (hstrictC (k + 1))) ?_
    rw [hεpow k, hεpow (k + 1)]
    have h1 : r₀ ^ (k + 1) ≤ r₀ ^ k := by
      rw [pow_succ]
      exact le_trans (mul_le_mul_right hr₀le _) (by rw [mul_one])
    calc sewingConst θ * (r₀ ^ k * ω s t) +
          sewingConst θ * (r₀ ^ (k + 1) * ω s t)
        ≤ sewingConst θ * (r₀ ^ k * ω s t) +
          sewingConst θ * (r₀ ^ k * ω s t) := by
          gcongr
      _ = C₀ * r₀ ^ k := by
          rw [hC₀]
          ring
  -- the limit
  have hcauchy : CauchySeq S :=
    cauchySeq_of_edist_le_geometric r₀ C₀ hr₀lt hC₀top hcons
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have htail : ∀ k, edist (S k) L ≤ C₀ * r₀ ^ k / (1 - r₀) :=
    edist_le_of_edist_le_geometric_of_tendsto r₀ C₀ hcons hL
  refine ⟨L, fun ε midp hchain => ?_⟩
  -- deduplicate the given chain
  obtain ⟨midp', hmidp'⟩ : ∃ midp',
      dedupChain (s :: (midp ++ [t])) = s :: (midp' ++ [t]) := by
    refine shape_of_head?_getLast? ?_ ?_ (ne_of_lt hst')
    · rw [head?_dedupChain]
      rfl
    · rw [getLast?_dedupChain,
        show s :: (midp ++ [t]) = (s :: midp) ++ [t] from rfl]
      exact List.getLast?_concat
  have hsum_eq : pairSum Ξ (s :: (midp' ++ [t])) =
      pairSum Ξ (s :: (midp ++ [t])) := by
    rw [← hmidp']
    exact pairSum_dedupChain hdiag _
  have hfineP : List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε)
      (s :: (midp' ++ [t])) := by
    rw [← hmidp']
    exact isChain_fine_dedupChain hchain
  have hstrictP : List.IsChain (· < ·) (s :: (midp' ++ [t])) := by
    rw [← hmidp']
    exact isChain_lt_dedupChain (hchain.imp fun a b hab => hab.1)
  -- the k-indexed bound
  have hbound : ∀ k : ℕ, ‖L - pairSum Ξ (s :: (midp ++ [t]))‖ₑ ≤
      C₀ * r₀ ^ k / (1 - r₀) +
        (sewingConst θ * (r₀ ^ k * ω s t) +
          sewingConst θ * (ε ^ (θ - 1) * ω s t)) := by
    intro k
    have h1 : ‖S k - pairSum Ξ (s :: (midp' ++ [t]))‖ₑ ≤
        sewingConst θ * (ε' k ^ (θ - 1) * ω s t) +
          sewingConst θ * (ε ^ (θ - 1) * ω s t) :=
      pairSum_sub_pairSum_le_of_fine ω Ξ hθ0 hθ1 hδ hst'
        (hfineC k) (hstrictC k) hfineP hstrictP
    rw [hεpow k] at h1
    calc ‖L - pairSum Ξ (s :: (midp ++ [t]))‖ₑ
        = ‖(L - S k) + (S k - pairSum Ξ (s :: (midp' ++ [t])))‖ₑ := by
          rw [hsum_eq]
          congr 1
          abel
      _ ≤ ‖L - S k‖ₑ + ‖S k - pairSum Ξ (s :: (midp' ++ [t]))‖ₑ :=
          enorm_add_le _ _
      _ ≤ C₀ * r₀ ^ k / (1 - r₀) +
            (sewingConst θ * (r₀ ^ k * ω s t) +
              sewingConst θ * (ε ^ (θ - 1) * ω s t)) := by
          refine add_le_add ?_ h1
          rw [show ‖L - S k‖ₑ = edist (S k) L from by
            rw [edist_eq_enorm_sub, ← enorm_neg]
            congr 1
            abel]
          exact htail k
  -- pass to the limit in k
  have hzero : Tendsto (fun k : ℕ => C₀ * r₀ ^ k / (1 - r₀) +
      sewingConst θ * (r₀ ^ k * ω s t)) atTop (nhds 0) := by
    have hpow : Tendsto (fun k : ℕ => r₀ ^ k) atTop (nhds 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr₀lt
    have h1 : Tendsto (fun k : ℕ => C₀ * r₀ ^ k / (1 - r₀)) atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := C₀ / (1 - r₀)) hpow
        (Or.inr (ENNReal.div_ne_top hC₀top
          (tsub_pos_of_lt hr₀lt).ne'))
      simpa [mul_zero, div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
        using this
    have h2 : Tendsto (fun k : ℕ => sewingConst θ * (r₀ ^ k * ω s t))
        atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := sewingConst θ * ω s t) hpow
        (Or.inr (ENNReal.mul_ne_top (sewingConst_ne_top hθ) hω))
      simpa [mul_zero, mul_comm, mul_assoc, mul_left_comm] using this
    simpa using h1.add h2
  have hfinal : Tendsto (fun k : ℕ => C₀ * r₀ ^ k / (1 - r₀) +
      (sewingConst θ * (r₀ ^ k * ω s t) +
        sewingConst θ * (ε ^ (θ - 1) * ω s t))) atTop
      (nhds (sewingConst θ * (ε ^ (θ - 1) * ω s t))) := by
    have := hzero.add (tendsto_const_nhds
      (x := sewingConst θ * (ε ^ (θ - 1) * ω s t)) (f := atTop))
    simpa [add_assoc, zero_add] using this
  exact ge_of_tendsto' hfinal fun k => by
    simpa [add_assoc] using hbound k

/-- **The additive sewing lemma** (Friz–Hairer Lemma 4.2, additive form):
there is an additive two-parameter primitive `I` with the germ bound
`‖I s t − Ξ s t‖ₑ ≤ K·ω(s,t)^θ`, and `I s t` approximates the Riemann sum
of every `ε`-fine partition to within `K·ε^{θ−1}·ω(s,t)`. -/
theorem sewing (hθ : 1 < θ)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ)
    (hfine : HasFinePartitions ω)
    (hω : ∀ ⦃s t : T⦄, s ≤ t → ω s t ≠ ⊤) :
    ∃ I : T → T → E,
      (∀ ⦃s u t : T⦄, s ≤ u → u ≤ t → I s u + I u t = I s t) ∧
      (∀ ⦃s t : T⦄, s ≤ t → ‖I s t - Ξ s t‖ₑ ≤ sewingConst θ * ω s t ^ θ) ∧
      (∀ ⦃s t : T⦄, s ≤ t → ∀ (ε : ℝ≥0∞) (mid : List T),
        List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (s :: (mid ++ [t])) →
        ‖I s t - pairSum Ξ (s :: (mid ++ [t]))‖ₑ ≤
          sewingConst θ * (ε ^ (θ - 1) * ω s t)) := by
  have hθ1 : (0 : ℝ) ≤ θ - 1 := by linarith
  have H : ∀ s t : T, s ≤ t → ∃ L : E, ∀ (ε : ℝ≥0∞) (mid : List T),
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (s :: (mid ++ [t])) →
      ‖L - pairSum Ξ (s :: (mid ++ [t]))‖ₑ ≤
        sewingConst θ * (ε ^ (θ - 1) * ω s t) :=
    fun s t hst => exists_sewing_limit ω Ξ hθ hδ hfine hst (hω hst)
  choose L hL using H
  refine ⟨fun s t => if h : s ≤ t then L s t h else 0, ?_, ?_, ?_⟩
  · -- additivity
    intro s u t hsu hut
    have hst : s ≤ t := le_trans hsu hut
    show (if h : s ≤ u then L s u h else 0) +
        (if h : u ≤ t then L u t h else 0) =
      (if h : s ≤ t then L s t h else 0)
    rw [dif_pos hsu, dif_pos hut, dif_pos hst]
    set r₀ : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ (θ - 1) with hr₀
    have hr₀lt : r₀ < 1 :=
      ENNReal.rpow_lt_one (ENNReal.inv_lt_one.2 (by norm_num)) (by linarith)
    have key : ∀ k : ℕ, ‖L s t hst - (L s u hsu + L u t hut)‖ₑ ≤
        3 * (sewingConst θ * (r₀ ^ k * ω s t)) := by
      intro k
      set εk : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ k with hεk_def
      have hεk : 0 < εk := ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) k
      obtain ⟨q₁, hq₁⟩ := hfine hsu εk hεk
      obtain ⟨q₂, hq₂⟩ := hfine hut εk hεk
      have hshape : s :: ((q₁ ++ u :: q₂) ++ [t]) =
          (s :: q₁) ++ u :: (q₂ ++ [t]) := by simp
      have hcat : List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ εk)
          (s :: ((q₁ ++ u :: q₂) ++ [t])) := by
        rw [hshape, List.isChain_split]
        exact ⟨by simpa using hq₁, hq₂⟩
      have hsum : pairSum Ξ (s :: ((q₁ ++ u :: q₂) ++ [t])) =
          pairSum Ξ (s :: (q₁ ++ [u])) + pairSum Ξ (u :: (q₂ ++ [t])) := by
        rw [hshape, pairSum_append Ξ (s :: q₁) u (q₂ ++ [t])]
        rfl
      have b1 := hL s t hst εk (q₁ ++ u :: q₂) hcat
      have b2 := hL s u hsu εk q₁ hq₁
      have b3 := hL u t hut εk q₂ hq₂
      have hω1 : ω s u ≤ ω s t :=
        le_trans (self_le_add_right _ _) (ω.superadditive hsu hut)
      have hω2 : ω u t ≤ ω s t :=
        le_trans (self_le_add_left _ _) (ω.superadditive hsu hut)
      have hεpow : εk ^ (θ - 1) = r₀ ^ k := pow_rpow_exchange k
      rw [hεpow] at b1 b2 b3
      have hexp : L s t hst - (L s u hsu + L u t hut) =
          (L s t hst - pairSum Ξ (s :: ((q₁ ++ u :: q₂) ++ [t]))) -
            ((L s u hsu - pairSum Ξ (s :: (q₁ ++ [u]))) +
             (L u t hut - pairSum Ξ (u :: (q₂ ++ [t])))) := by
        rw [hsum]
        abel
      calc ‖L s t hst - (L s u hsu + L u t hut)‖ₑ
          = ‖(L s t hst - pairSum Ξ (s :: ((q₁ ++ u :: q₂) ++ [t]))) -
              ((L s u hsu - pairSum Ξ (s :: (q₁ ++ [u]))) +
               (L u t hut - pairSum Ξ (u :: (q₂ ++ [t]))))‖ₑ := by
            rw [hexp]
        _ ≤ ‖L s t hst - pairSum Ξ (s :: ((q₁ ++ u :: q₂) ++ [t]))‖ₑ +
              (‖L s u hsu - pairSum Ξ (s :: (q₁ ++ [u]))‖ₑ +
               ‖L u t hut - pairSum Ξ (u :: (q₂ ++ [t]))‖ₑ) := by
            have t1 : ∀ a b : E, ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := fun a b => by
              rw [sub_eq_add_neg]
              refine le_trans (enorm_add_le _ _) ?_
              rw [enorm_neg]
            exact le_trans (t1 _ _) (by
              gcongr
              exact enorm_add_le _ _)
        _ ≤ sewingConst θ * (r₀ ^ k * ω s t) +
              (sewingConst θ * (r₀ ^ k * ω s t) +
               sewingConst θ * (r₀ ^ k * ω s t)) := by
            refine add_le_add b1 (add_le_add (le_trans b2 ?_) (le_trans b3 ?_))
            · gcongr
            · gcongr
        _ = 3 * (sewingConst θ * (r₀ ^ k * ω s t)) := by ring
    have hzero : Filter.Tendsto
        (fun k : ℕ => 3 * (sewingConst θ * (r₀ ^ k * ω s t)))
        Filter.atTop (nhds 0) := by
      have hpow : Filter.Tendsto (fun k : ℕ => r₀ ^ k)
          Filter.atTop (nhds 0) :=
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr₀lt
      have h1 := ENNReal.Tendsto.const_mul
        (a := 3 * (sewingConst θ * ω s t)) hpow
        (Or.inr (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.mul_ne_top (sewingConst_ne_top hθ) (hω hst))))
      simpa [mul_zero, mul_comm, mul_assoc, mul_left_comm] using h1
    have hnorm : ‖L s t hst - (L s u hsu + L u t hut)‖ₑ = 0 :=
      le_antisymm (ge_of_tendsto' hzero key) zero_le
    have h0 := enorm_eq_zero.1 hnorm
    exact (sub_eq_zero.1 h0).symm
  · -- germ bound
    intro s t hst
    show ‖(if h : s ≤ t then L s t h else 0) - Ξ s t‖ₑ ≤
      sewingConst θ * ω s t ^ θ
    rw [dif_pos hst]
    have hchain : List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ω s t)
        (s :: (([] : List T) ++ [t])) := by
      simp only [List.nil_append]
      exact List.isChain_pair.2 ⟨hst, le_refl _⟩
    have h1 := hL s t hst (ω s t) [] hchain
    have hsum : pairSum Ξ (s :: (([] : List T) ++ [t])) = Ξ s t := by
      simp [pairSum_cons_cons]
    have hpow : ω s t ^ (θ - 1) * ω s t = ω s t ^ θ := by
      have h2 := ENNReal.rpow_add_of_nonneg (x := ω s t) (θ - 1) 1 hθ1 zero_le_one
      rw [ENNReal.rpow_one] at h2
      rw [← h2, show θ - 1 + 1 = θ by ring]
    rw [hsum, hpow] at h1
    exact h1
  · -- fine-partition approximation
    intro s t hst ε mid hchain
    show ‖(if h : s ≤ t then L s t h else 0) -
        pairSum Ξ (s :: (mid ++ [t]))‖ₑ ≤
      sewingConst θ * (ε ^ (θ - 1) * ω s t)
    rw [dif_pos hst]
    exact hL s t hst ε mid hchain

end Limit

end Sewing

end RoughPaths
