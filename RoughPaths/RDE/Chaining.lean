/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.RDE.Parameters

/-!
# Chaining RDE solutions across windows

Globalisation of the small-window well-posedness: given any partition
`0 ≤ t₀ ≤ t₁ ≤ … ≤ t_N` whose pieces satisfy the window conditions
`ω(tᵢ,tᵢ₊₁) ≤ 1` and `ω(tᵢ,tᵢ₊₁)^α ≤ δα` — no smallness of `ω` as a
whole — there is a single path `Y` starting at `y₀` that solves
`dY = f(Y)·dX` on every window (`rde_exists_chain`).

The mechanism: on each window `[a,b]` the driver and control are pulled
back along the clamp `r ↦ min (max r a) b`. The clamped control is
dominated both by `ω` (so finiteness and fine partitions transport) and
by the constant `ω a b` (so the window conditions hold **globally** for
the clamped data), hence `rde_wellposed` applies. Clamped solutions are
frozen outside `[a,b]` — their increments vanish where the clamp is
constant — so the window solutions can be glued at the knots.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ} {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ} {α : ℝ}

/-! ### Clamping to a window -/

/-- Clamp a real time to the window `[a, b]`. -/
noncomputable def clampIcc (a b r : ℝ) : ℝ :=
  min (max r a) b

theorem clampIcc_mono (a b : ℝ) : Monotone (clampIcc a b) :=
  fun _ _ h => min_le_min (max_le_max h le_rfl) le_rfl

theorem le_clampIcc {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    a ≤ clampIcc a b r :=
  le_min (le_max_right r a) hab

theorem clampIcc_le (a b r : ℝ) : clampIcc a b r ≤ b :=
  min_le_right _ _

theorem clampIcc_of_le {a b r : ℝ} (hab : a ≤ b) (h : r ≤ a) :
    clampIcc a b r = a := by
  rw [clampIcc, max_eq_right h, min_eq_left hab]

theorem clampIcc_of_ge {a b r : ℝ} (hab : a ≤ b) (h : b ≤ r) :
    clampIcc a b r = b := by
  rw [clampIcc, max_eq_left (le_trans hab h), min_eq_right h]

theorem clampIcc_of_mem {a b r : ℝ} (h1 : a ≤ r) (h2 : r ≤ b) :
    clampIcc a b r = r := by
  rw [clampIcc, max_eq_left h1, min_eq_left h2]

/-- The clamped control is dominated by the original control. -/
theorem comap_clampIcc_le (ω : Control ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω.comap (clampIcc a b) (clampIcc_mono a b) s t ≤ ω s t := by
  intro s t hst
  rw [Control.comap_apply]
  by_cases hs : b ≤ s
  · rw [clampIcc_of_ge hab hs, clampIcc_of_ge hab (le_trans hs hst),
      Control.diagonal_apply]
    exact zero_le
  · by_cases ht : t ≤ a
    · rw [clampIcc_of_le hab (le_trans hst ht), clampIcc_of_le hab ht,
        Control.diagonal_apply]
      exact zero_le
    · have hs' : s ≤ b := (not_le.1 hs).le
      have ht' : a ≤ t := (not_le.1 ht).le
      refine Sewing.control_mono ω (le_min (le_max_left s a) hs')
        (clampIcc_mono a b hst) ?_
      rw [clampIcc, max_eq_left ht']
      exact min_le_left _ _

/-- The clamped control is globally dominated by the window value. -/
theorem comap_clampIcc_le_window (ω : Control ℝ) {a b : ℝ} (hab : a ≤ b)
    ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ω.comap (clampIcc a b) (clampIcc_mono a b) s t ≤ ω a b := by
  rw [Control.comap_apply]
  exact Sewing.control_mono ω (le_clampIcc hab s)
    (clampIcc_mono a b hst) (clampIcc_le a b t)

/-- Level-2 bounds transport along monotone time changes. -/
theorem IsLevel2RoughPath.comap (hX : IsLevel2RoughPath X ω α)
    (f : ℝ → ℝ) (hf : Monotone f) :
    IsLevel2RoughPath (X.comapTime f) (ω.comap f hf) α where
  one_third_lt := hX.one_third_lt
  le_half := hX.le_half
  bound_one := fun _ _ hst i => hX.bound_one (hf hst) i
  bound_two := fun _ _ hst i j => hX.bound_two (hf hst) i j

/-! ### Solutions are frozen where the clamped data is constant -/

/-- A solution has constant path across any interval where the control
vanishes and the driver increment is the unit: the germ and hence the
increment are zero there. -/
theorem RDEVectorField.IsRDESolution.const_of_zero
    {V' : RDEVectorField d E} {hX : IsLevel2RoughPath X ω α}
    {hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1}
    {Z : ControlledPath X ω α E} {I : ℝ → ℝ → E}
    (hsol : V'.IsRDESolution hX hω1 Z I) ⦃s t : ℝ⦄ (hst : s ≤ t)
    (hω0 : ω s t = 0)
    (hXu : X.increment s t = Word.unit (Fin d) ℝ) :
    Z.Y t = Z.Y s := by
  have h3α := hX.one_lt_three_alpha
  have hI : I s t = gubinelliGerm (V'.compControlled hX hω1 Z) s t := by
    have h := hsol.germ_bound hst
    rw [hω0, ENNReal.zero_rpow_of_pos (by linarith), mul_zero,
      mul_zero] at h
    have h0 := enorm_eq_zero.1 (le_antisymm h zero_le)
    exact sub_eq_zero.1 h0
  have hc1 : ∀ i : Fin d, X.coeff s t [i] = 0 := by
    intro i
    show Word.coeff (X.increment s t) [i] = 0
    rw [hXu]
    rfl
  have hc2 : ∀ i j : Fin d, X.coeff s t [i, j] = 0 := by
    intro i j
    show Word.coeff (X.increment s t) [i, j] = 0
    rw [hXu]
    rfl
  have hgerm0 : gubinelliGerm (V'.compControlled hX hω1 Z) s t = 0 := by
    rw [gubinelliGerm_apply]
    have hs1 : (∑ i, X.coeff s t [i] •
        (V'.compControlled hX hω1 Z).Y s i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hc1 i, zero_smul]
    have hs2 : (∑ i, ∑ j, X.coeff s t [i, j] •
        (V'.compControlled hX hω1 Z).Yd s i j) = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        rw [hc2 i j, zero_smul]
    rw [hs1, hs2, add_zero]
  have hinc := hsol.increment_eq hst
  rw [hI, hgerm0] at hinc
  exact sub_eq_zero.1 hinc

/-- A solution of the clamped problem is frozen wherever the clamp is
constant. -/
theorem RDEVectorField.IsRDESolution.frozen_of_clamp_eq
    {V' : RDEVectorField d E} {a b : ℝ}
    {hXc : IsLevel2RoughPath (X.comapTime (clampIcc a b))
      (ω.comap (clampIcc a b) (clampIcc_mono a b)) α}
    {hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω.comap (clampIcc a b) (clampIcc_mono a b) s t ≤ 1}
    {Z : ControlledPath (X.comapTime (clampIcc a b))
      (ω.comap (clampIcc a b) (clampIcc_mono a b)) α E}
    {I : ℝ → ℝ → E}
    (hsol : V'.IsRDESolution hXc hω1 Z I) ⦃s t : ℝ⦄ (hst : s ≤ t)
    (hcl : clampIcc a b s = clampIcc a b t) :
    Z.Y t = Z.Y s := by
  refine hsol.const_of_zero hst ?_ ?_
  · rw [Control.comap_apply, hcl, Control.diagonal_apply]
  · show X.increment (clampIcc a b s) (clampIcc a b t) =
      Word.unit (Fin d) ℝ
    rw [hcl]
    exact X.identity _

/-! ### Solving on a single window -/

section Window

variable [CompleteSpace E]

/-- `Y` solves `dY = f(Y)·dX` **on the window** `[a,b]`: the problem with
driver and control clamped to `[a,b]` has a solution whose path agrees
with `Y` throughout the window. -/
def RDEVectorField3.SolvesOn (V : RDEVectorField3 d E)
    (hX : IsLevel2RoughPath X ω α) (Y : ℝ → E) (a b : ℝ) : Prop :=
  ∃ (_ : a ≤ b)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω.comap (clampIcc a b) (clampIcc_mono a b) s t ≤ 1)
    (Z : ControlledPath (X.comapTime (clampIcc a b))
      (ω.comap (clampIcc a b) (clampIcc_mono a b)) α E)
    (I : ℝ → ℝ → E),
    V.IsRDESolution (hX.comap (clampIcc a b) (clampIcc_mono a b)) hω1
      Z I ∧
    ∀ u : ℝ, a ≤ u → u ≤ b → Z.Y u = Y u

/-- **Solve on one window**: if the single window `[a,b] ⊆ [0,∞)`
satisfies the window conditions, the clamped problem has a box-certified
solution whose value at `a` is the prescribed `y`. -/
theorem rde_solve_window (V : RDEVectorField3 d E)
    (hX : IsLevel2RoughPath X ω α)
    (hfine : Sewing.HasFinePartitions ω)
    (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    (P : RDEVectorField3.PicardParams V α) {a b : ℝ} (hab : a ≤ b) (h0a : 0 ≤ a)
    (hwin1 : ω a b ≤ 1) (hwinα : ω a b ^ α ≤ (P.δα : ℝ≥0∞)) (y : E) :
    ∃ (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t →
        ω.comap (clampIcc a b) (clampIcc_mono a b) s t ≤ 1)
      (Z : ControlledPath (X.comapTime (clampIcc a b))
        (ω.comap (clampIcc a b) (clampIcc_mono a b)) α E)
      (I : ℝ → ℝ → E),
      V.IsRDESolution (hX.comap (clampIcc a b) (clampIcc_mono a b)) hω1
        Z I ∧
      Z.Y a = y := by
  have hα := hX.alpha_pos
  have hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω.comap (clampIcc a b) (clampIcc_mono a b) s t ≤ 1 :=
    fun s t hst => le_trans (comap_clampIcc_le_window ω hab hst) hwin1
  have hδαc : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω.comap (clampIcc a b) (clampIcc_mono a b) s t ^ α ≤
        (P.δα : ℝ≥0∞) :=
    fun s t hst => le_trans
      (ENNReal.rpow_le_rpow (comap_clampIcc_le_window ω hab hst) hα.le)
      hwinα
  have hfinec : Sewing.HasFinePartitions
      (ω.comap (clampIcc a b) (clampIcc_mono a b)) :=
    hfine.of_le (comap_clampIcc_le ω hab)
  have hωnec : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ω.comap (clampIcc a b) (clampIcc_mono a b) s t ≠ ⊤ :=
    fun s t hst =>
      ne_top_of_le_ne_top (hωne hst) (comap_clampIcc_le ω hab hst)
  obtain ⟨Z, I, hsol, hY0, -, -⟩ := V.rde_wellposed
    (hX.comap (clampIcc a b) (clampIcc_mono a b)) hω1 hfinec hωnec y P
    hδαc
  refine ⟨hω1, Z, I, hsol, ?_⟩
  have hfr : Z.Y a = Z.Y 0 :=
    hsol.frozen_of_clamp_eq h0a
      ((clampIcc_of_le hab le_rfl).trans
        (clampIcc_of_le hab h0a).symm).symm
  rw [hfr, hY0]

end Window

/-! ### The chain theorem -/

section Chain

variable [CompleteSpace E]

/-- **Globalisation by window chaining**: for any partition
`0 ≤ t₀ ≤ … ≤ t_N` whose pieces satisfy the window conditions — no
global smallness of `ω` — there is a single path `Y` with `Y (t 0) = y₀`
solving `dY = f(Y)·dX` on every window. Combined with
`exists_picardParams`, every `C³_b` RDE is solvable along any
sufficiently fine partition of an arbitrary horizon. -/
theorem rde_exists_chain (V : RDEVectorField3 d E)
    (hX : IsLevel2RoughPath X ω α)
    (hfine : Sewing.HasFinePartitions ω)
    (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    (P : RDEVectorField3.PicardParams V α) :
    ∀ (N : ℕ) (t : Fin (N + 1) → ℝ) (y₀ : E), 0 ≤ t 0 →
    (∀ i : Fin N, t i.castSucc ≤ t i.succ) →
    (∀ i : Fin N, ω (t i.castSucc) (t i.succ) ≤ 1) →
    (∀ i : Fin N, ω (t i.castSucc) (t i.succ) ^ α ≤ (P.δα : ℝ≥0∞)) →
    ∃ Y : ℝ → E, Y (t 0) = y₀ ∧
      ∀ i : Fin N, V.SolvesOn hX Y (t i.castSucc) (t i.succ) := by
  intro N
  induction N with
  | zero =>
      intro t y₀ _ _ _ _
      exact ⟨fun _ => y₀, rfl, fun i => i.elim0⟩
  | succ N IH =>
      intro t y₀ ht0 hmono hs1 hsα
      have hz : ((0 : Fin (N + 1)).castSucc : Fin (N + 2)) = 0 :=
        Fin.castSucc_zero
      have hab0 : t (0 : Fin (N + 1)).castSucc ≤
          t (0 : Fin (N + 1)).succ := hmono 0
      have h0a : (0 : ℝ) ≤ t (0 : Fin (N + 1)).castSucc := by
        rw [hz]; exact ht0
      obtain ⟨hω1₀, Z₀, I₀, hsol₀, hZa⟩ := rde_solve_window V hX hfine
        hωne P hab0 h0a (hs1 0) (hsα 0) y₀
      have hix : ∀ j : Fin N,
          t (j.succ : Fin (N + 1)).castSucc = t j.castSucc.succ :=
        fun j => congrArg t (Fin.succ_castSucc j).symm
      obtain ⟨Y', hY'0, hY'win⟩ := IH (fun k => t k.succ)
        (Z₀.Y (t (0 : Fin (N + 1)).succ)) (le_trans h0a hab0)
        (fun j => by rw [← hix j]; exact hmono j.succ)
        (fun j => by rw [← hix j]; exact hs1 j.succ)
        (fun j => by rw [← hix j]; exact hsα j.succ)
      have hmono' : Monotone (fun k : Fin (N + 1) => t k.succ) := by
        rw [Fin.monotone_iff_le_succ]
        intro j
        show t (j.castSucc).succ ≤ t j.succ.succ
        rw [← hix j]
        exact hmono j.succ
      have hstart : ∀ j : Fin N,
          t (0 : Fin (N + 1)).succ ≤ t j.castSucc.succ :=
        fun j => hmono' (Fin.zero_le j.castSucc)
      refine ⟨fun u => if u ≤ t (0 : Fin (N + 1)).succ then Z₀.Y u
        else Y' u, ?_, ?_⟩
      · show (if t (0 : Fin (N + 2)) ≤ t (0 : Fin (N + 1)).succ then
            Z₀.Y (t (0 : Fin (N + 2))) else Y' (t (0 : Fin (N + 2)))) =
          y₀
        rw [if_pos (by rw [← hz]; exact hab0), ← hz]
        exact hZa
      · intro i
        refine Fin.cases ?_ ?_ i
        · refine ⟨hab0, hω1₀, Z₀, I₀, hsol₀, fun u _ hu2 => ?_⟩
          show Z₀.Y u = if u ≤ t (0 : Fin (N + 1)).succ then Z₀.Y u
            else Y' u
          rw [if_pos hu2]
        · intro j
          obtain ⟨hab, hω1, Z, I, hsol, hagree⟩ := hY'win j
          rw [show t (j.succ : Fin (N + 1)).castSucc =
            t j.castSucc.succ from hix j]
          refine ⟨hab, hω1, Z, I, hsol, ?_⟩
          intro u hu1 hu2
          show Z.Y u = if u ≤ t (0 : Fin (N + 1)).succ then Z₀.Y u
            else Y' u
          by_cases hub : u ≤ t (0 : Fin (N + 1)).succ
          · have hub' : u = t (0 : Fin (N + 1)).succ := le_antisymm hub
              (le_trans (hstart j) hu1)
            rw [if_pos hub, hagree u hu1 hu2, hub']
            exact hY'0
          · rw [if_neg hub, hagree u hu1 hu2]

/-- **Existence of window chains**: fine partitions provide partitions
satisfying the window conditions between any two times. -/
theorem exists_window_chain (hfine : Sewing.HasFinePartitions ω)
    (hα : 0 < α) {δα : ℝ≥0} (hδα : 0 < δα) {s T : ℝ} (hsT : s ≤ T) :
    ∃ (N : ℕ) (t : Fin (N + 1) → ℝ), t 0 = s ∧ t (Fin.last N) = T ∧
      (∀ i : Fin N, t i.castSucc ≤ t i.succ) ∧
      (∀ i : Fin N, ω (t i.castSucc) (t i.succ) ≤ 1) ∧
      (∀ i : Fin N, ω (t i.castSucc) (t i.succ) ^ α ≤ (δα : ℝ≥0∞)) := by
  have hε0 : 0 < min 1 ((δα : ℝ≥0∞) ^ α⁻¹) := by
    refine lt_min zero_lt_one ?_
    exact ENNReal.rpow_pos (by exact_mod_cast hδα) ENNReal.coe_ne_top
  obtain ⟨q, hq⟩ := hfine hsT _ hε0
  have hget := List.isChain_iff_getElem.mp hq
  have hlen : (s :: (q ++ [T])).length = q.length + 2 := by simp
  refine ⟨q.length + 1,
    fun i => (s :: (q ++ [T]))[(i : ℕ)]'(by omega), rfl, ?_, ?_, ?_, ?_⟩
  · show (s :: (q ++ [T]))[(Fin.last (q.length + 1) : ℕ)]'_ = T
    have hv : ((Fin.last (q.length + 1) : Fin (q.length + 2)) : ℕ) =
        q.length + 1 := rfl
    simp only [hv, List.getElem_cons_succ, List.getElem_concat_length]
  all_goals
    intro i
    have hi := hget (i : ℕ) (by
      have := i.isLt
      omega)
  · exact hi.1
  · exact le_trans hi.2 (min_le_left _ _)
  · refine le_trans (ENNReal.rpow_le_rpow
      (le_trans hi.2 (min_le_right _ _)) hα.le) ?_
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hα.ne', ENNReal.rpow_one]

/-- **Global solvability along a fine partition**: for every `C³_b`
vector field, finite control with fine partitions, horizon `T₀ ≥ 0` and
initial value, there are Picard parameters, a partition of `[0, T₀]`
satisfying the window conditions, and a path started at `y₀` solving the
RDE on every window. -/
theorem rde_exists_global (V : RDEVectorField3 d E)
    (hX : IsLevel2RoughPath X ω α)
    (hfine : Sewing.HasFinePartitions ω)
    (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    {T₀ : ℝ} (h0T : 0 ≤ T₀) (y₀ : E) :
    ∃ (_ : RDEVectorField3.PicardParams V α) (N : ℕ)
      (t : Fin (N + 1) → ℝ),
      t 0 = 0 ∧ t (Fin.last N) = T₀ ∧
      (∀ i : Fin N, t i.castSucc ≤ t i.succ) ∧
      ∃ Y : ℝ → E, Y 0 = y₀ ∧
        ∀ i : Fin N, V.SolvesOn hX Y (t i.castSucc) (t i.succ) := by
  obtain ⟨P⟩ := RDEVectorField3.exists_picardParams V α
  obtain ⟨N, t, ht0, htL, hmono, hs1, hsα⟩ :=
    exists_window_chain hfine hX.alpha_pos P.δα_pos h0T
  obtain ⟨Y, hY0, hwin⟩ := rde_exists_chain V hX hfine hωne P N t y₀
    ht0.ge hmono hs1 hsα
  rw [ht0] at hY0
  exact ⟨P, N, t, ht0, htL, hmono, Y, hY0, hwin⟩

end Chain

end RoughPaths
