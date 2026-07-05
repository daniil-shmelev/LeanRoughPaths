/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Integration.FinePartitions
import Mathlib.Data.List.TakeWhile

/-!
# Chain refinement combinatorics

List-level machinery for the additive sewing lemma over a linear order:
deduplication of monotone chains (`dedupChain`), and the decomposition of a
strict chain as a glued refinement of a coarser strict chain through the
same points (`refineAlong`), giving common refinements of two chains.
-/

namespace RoughPaths

namespace Sewing

universe u

variable {T : Type u} [LinearOrder T]

/-! ### Deduplication of monotone chains -/

/-- Remove adjacent duplicates from a list (of a `≤`-chain, producing a
`<`-chain). -/
def dedupChain : List T → List T
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      if x = y then dedupChain (y :: rest) else x :: dedupChain (y :: rest)

@[simp]
theorem dedupChain_nil : dedupChain ([] : List T) = [] := rfl

@[simp]
theorem dedupChain_singleton (x : T) : dedupChain [x] = [x] := rfl

theorem dedupChain_cons_cons (x y : T) (rest : List T) :
    dedupChain (x :: y :: rest) =
      if x = y then dedupChain (y :: rest) else x :: dedupChain (y :: rest) :=
  rfl

theorem dedupChain_ne_nil : ∀ {l : List T}, l ≠ [] → dedupChain l ≠ [] := by
  intro l
  induction l with
  | nil => exact fun h => absurd rfl h
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y rest =>
          intro _
          rw [dedupChain_cons_cons]
          split
          · exact ih (by simp)
          · simp

@[simp]
theorem mem_dedupChain {a : T} : ∀ {l : List T}, a ∈ dedupChain l ↔ a ∈ l := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y rest =>
          rw [dedupChain_cons_cons]
          split
          · next hxy =>
              subst hxy
              rw [ih]
              simp
          · simp [ih]

@[simp]
theorem head?_dedupChain : ∀ l : List T, (dedupChain l).head? = l.head? := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y rest =>
          rw [dedupChain_cons_cons]
          split
          · next hxy =>
              subst hxy
              rw [ih]
              rfl
          · rfl

@[simp]
theorem getLast?_dedupChain : ∀ l : List T,
    (dedupChain l).getLast? = l.getLast? := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y rest =>
          rw [dedupChain_cons_cons, List.getLast?_cons_cons]
          split
          · rw [ih]
          · rcases hd : dedupChain (y :: rest) with _ | ⟨w, ws⟩
            · exact absurd hd (dedupChain_ne_nil (by simp))
            · rw [List.getLast?_cons_cons, ← hd, ih]

/-- Deduplicating a `≤`-chain yields a `<`-chain. -/
theorem isChain_lt_dedupChain :
    ∀ {l : List T}, List.IsChain (· ≤ ·) l →
      List.IsChain (· < ·) (dedupChain l) := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y rest =>
          intro h
          rw [List.isChain_cons_cons] at h
          rw [dedupChain_cons_cons]
          split
          · exact ih h.2
          · next hxy =>
              refine (ih h.2).cons fun z hz => ?_
              rw [head?_dedupChain] at hz
              simp only [List.head?_cons, Option.mem_some_iff] at hz
              subst hz
              exact lt_of_le_of_ne h.1 hxy

/-- Deduplication preserves the fine-chain property. -/
theorem isChain_fine_dedupChain {ω : Control T} {ε : ENNReal} :
    ∀ {l : List T},
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) l →
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (dedupChain l) := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y rest =>
          intro h
          rw [List.isChain_cons_cons] at h
          rw [dedupChain_cons_cons]
          split
          · exact ih h.2
          · refine (ih h.2).cons fun z hz => ?_
            rw [head?_dedupChain] at hz
            simp only [List.head?_cons, Option.mem_some_iff] at hz
            subst hz
            exact h.1

/-- Deduplication preserves pair sums when the summand vanishes on the
diagonal. -/
theorem pairSum_dedupChain {E : Type*} [AddCommMonoid E]
    {Ξ : T → T → E} (hdiag : ∀ t : T, Ξ t t = 0) :
    ∀ l : List T, pairSum Ξ (dedupChain l) = pairSum Ξ l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y rest =>
          rw [dedupChain_cons_cons]
          split
          · next hxy =>
              subst hxy
              rw [ih, pairSum_cons_cons, hdiag, zero_add]
          · rcases hd : dedupChain (y :: rest) with _ | ⟨w, ws⟩
            · exact absurd hd (dedupChain_ne_nil (by simp))
            · have hw : w = y := by
                have h1 := head?_dedupChain (y :: rest)
                rw [hd] at h1
                simpa using h1
              subst hw
              rw [pairSum_cons_cons, pairSum_cons_cons, ← hd, ih]

/-! ### Strict chains and their extremes -/

/-- On a strict chain, the head is strictly below every later element. -/
theorem head_lt_of_mem_tail {x : T} {l : List T}
    (h : List.IsChain (· < ·) (x :: l)) {z : T} (hz : z ∈ l) : x < z :=
  h.rel_cons hz

/-- On a strict chain, the head is at most the last element. -/
theorem head_le_getLast_of_lt :
    ∀ {l : List T}, List.IsChain (· < ·) l → (hl : l ≠ []) →
      l.head hl ≤ l.getLast hl
  | [], _, hl => absurd rfl hl
  | [x], _, _ => le_refl x
  | x :: y :: rest, h, _ => by
      have h' := List.isChain_cons_cons.1 h
      rw [List.getLast_cons (by simp : (y :: rest) ≠ [])]
      exact le_of_lt (lt_of_lt_of_le h'.1
        (head_le_getLast_of_lt h'.2 (by simp)))

/-- On a strict chain, every element other than the last is below the last. -/
theorem lt_getLast_of_mem_dropLast :
    ∀ {l : List T}, List.IsChain (· < ·) l → (hl : l ≠ []) →
      ∀ z ∈ l.dropLast, z < l.getLast hl
  | [], _, hl => absurd rfl hl
  | [x], _, _ => by simp
  | x :: y :: rest, h, _ => by
      intro z hz
      rw [List.dropLast_cons_cons, List.mem_cons] at hz
      rw [List.getLast_cons (by simp : (y :: rest) ≠ [])]
      have h' := List.isChain_cons_cons.1 h
      rcases hz with rfl | hz'
      · exact lt_of_lt_of_le h'.1 (head_le_getLast_of_lt h'.2 (by simp))
      · exact lt_getLast_of_mem_dropLast h'.2 (by simp) z hz'

/-- `dropWhile (· < y)` on a strict chain containing `y` starts at `y`. -/
private theorem dropWhile_eq_cons_of_mem :
    ∀ {l : List T}, List.IsChain (· < ·) l → ∀ {y : T}, y ∈ l →
      l.dropWhile (fun z => decide (z < y)) = y ::
        (l.dropWhile (fun z => decide (z < y))).tail
  | [], _, y, hy => absurd hy (by simp)
  | x :: ls, h, y, hy => by
      by_cases hx : x < y
      · have hy' : y ∈ ls := by
          rcases List.mem_cons.1 hy with h0 | h0
          · exact absurd (h0 ▸ hx) (lt_irrefl y)
          · exact h0
        rw [List.dropWhile_cons_of_pos (by simpa using hx)]
        exact dropWhile_eq_cons_of_mem h.tail hy'
      · rw [List.dropWhile_cons_of_neg (by simpa using hx)]
        have hxy : x = y := by
          rcases List.mem_cons.1 hy with h0 | h0
          · exact h0.symm
          · exact absurd (head_lt_of_mem_tail h h0) hx
        simp [hxy]

/-- On a `<`-chain, filtering by `(· < y)` is a prefix. -/
private theorem filter_eq_takeWhile_of_chain (y : T) :
    ∀ l : List T, List.IsChain (· < ·) l →
      l.filter (fun z => decide (z < y)) =
        l.takeWhile (fun z => decide (z < y))
  | [], _ => rfl
  | [x], _ => by
      by_cases hx : x < y
      · rw [List.filter_cons_of_pos (by simpa using hx),
          List.takeWhile_cons_of_pos (by simpa using hx)]
        rfl
      · rw [List.filter_cons_of_neg (by simpa using hx),
          List.takeWhile_cons_of_neg (by simpa using hx)]
        rfl
  | x :: w :: rest, h => by
      have h' := List.isChain_cons_cons.1 h
      by_cases hx : x < y
      · rw [List.filter_cons_of_pos (by simpa using hx),
          List.takeWhile_cons_of_pos (by simpa using hx),
          filter_eq_takeWhile_of_chain y (w :: rest) h'.2]
      · rw [List.filter_cons_of_neg (by simpa using hx),
          List.takeWhile_cons_of_neg (by simpa using hx)]
        rw [List.filter_eq_nil_iff.2]
        intro z hz
        simp only [decide_eq_true_eq]
        intro hzy
        rcases List.mem_cons.1 hz with h0 | hz'
        · exact hx (lt_trans (h0 ▸ h'.1) hzy)
        · exact hx (lt_trans (lt_trans h'.1
            (head_lt_of_mem_tail h'.2 hz')) hzy)

/-! ### Refinement decomposition along a finer chain -/

/-- Decompose a refinement `r` along a base chain: for consecutive base
points `x, y` the inserted points are the elements of `r` strictly between
them. -/
def refineAlong (r : List T) : List T → List (T × List T)
  | x :: y :: rest =>
      (x, r.filter fun z => decide (x < z) && decide (z < y)) ::
        refineAlong r (y :: rest)
  | _ => []

@[simp]
theorem refineAlong_nil (r : List T) : refineAlong r [] = [] := rfl

@[simp]
theorem refineAlong_singleton (r : List T) (x : T) :
    refineAlong r [x] = [] := rfl

@[simp]
theorem refineAlong_cons_cons (r : List T) (x y : T) (rest : List T) :
    refineAlong r (x :: y :: rest) =
      (x, r.filter fun z => decide (x < z) && decide (z < y)) ::
        refineAlong r (y :: rest) :=
  rfl

/-- `refineAlong` recovers the base partition. -/
theorem basePoints_refineAlong (r : List T) :
    ∀ (mid : List T) (x t : T),
      basePoints (refineAlong r (x :: (mid ++ [t]))) t = x :: (mid ++ [t])
  | [], x, t => by simp [refineAlong]
  | y :: mid, x, t => by
      rw [List.cons_append, refineAlong_cons_cons, basePoints_cons,
        basePoints_refineAlong r mid y t]

/-- The filters of `refineAlong` ignore a prefix lying strictly below the
base chain. -/
private theorem refineAlong_append_low (pre : List T) :
    ∀ (base : List T), List.IsChain (· < ·) base →
      (∀ z ∈ pre, ∀ w ∈ base.head?, z < w) →
      ∀ r' : List T, refineAlong (pre ++ r') base = refineAlong r' base
  | [], _, _, r' => by simp
  | [x], _, _, r' => by simp
  | x :: y :: rest, hbase, hlow, r' => by
      have hbase' := List.isChain_cons_cons.1 hbase
      rw [refineAlong_cons_cons, refineAlong_cons_cons]
      congr 1
      · congr 1
        rw [List.filter_append,
          List.filter_eq_nil_iff.2 (fun z hz => by
            have hzx : z < x := hlow z hz x (by simp)
            simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
            intro hxz
            exact absurd (lt_trans hzx hxz) (lt_irrefl z)),
          List.nil_append]
      · refine refineAlong_append_low pre (y :: rest) hbase'.2 ?_ r'
        intro z hz w hw
        simp only [List.head?_cons, Option.mem_some_iff] at hw
        subst hw
        exact lt_trans (hlow z hz x (by simp)) hbase'.1

/-- **`refineAlong` recovers the refinement**: if `r = x :: rtail` is a
strict chain ending at `t` containing all the base points, gluing the
decomposition along the base returns `r`. -/
theorem glue_refineAlong :
    ∀ (mid : List T) (x t : T) (rtail : List T),
      List.IsChain (· < ·) (x :: rtail) →
      List.IsChain (· < ·) (x :: (mid ++ [t])) →
      ((x :: rtail).getLast (by simp)) = t →
      (∀ z ∈ x :: (mid ++ [t]), z ∈ x :: rtail) →
      glue (refineAlong (x :: rtail) (x :: (mid ++ [t]))) t = x :: rtail
  | [], x, t, rtail, hr, hbase, hlast, _ => by
      rw [List.nil_append] at hbase ⊢
      rw [refineAlong_cons_cons, refineAlong_singleton, glue_cons, glue_nil]
      have hxt : x < t := List.isChain_pair.1 hbase
      have hrtail_ne : rtail ≠ [] := by
        intro h0
        subst h0
        simp only [List.getLast_singleton] at hlast
        exact absurd (hlast ▸ hxt) (lt_irrefl t)
      have hlast' : rtail.getLast hrtail_ne = t := by
        rw [List.getLast_cons hrtail_ne] at hlast
        exact hlast
      have hfilter : (x :: rtail).filter
          (fun z => decide (x < z) && decide (z < t)) =
          rtail.filter (fun z => decide (z < t)) := by
        rw [List.filter_cons_of_neg (by simp)]
        apply List.filter_congr
        intro z hz
        simp [head_lt_of_mem_tail hr hz]
      have hsplit : rtail = rtail.dropLast ++ [t] := by
        conv_lhs => rw [← List.dropLast_append_getLast hrtail_ne]
        rw [hlast']
      have hfilter2 : rtail.filter (fun z => decide (z < t)) =
          rtail.dropLast := by
        conv_lhs => rw [hsplit]
        rw [List.filter_append,
          List.filter_eq_self.2 (fun z hz => by
            simp only [decide_eq_true_eq]
            have hrt : List.IsChain (· < ·) rtail := hr.tail
            have h1 := lt_getLast_of_mem_dropLast hrt hrtail_ne z hz
            rw [hlast'] at h1
            exact h1),
          List.filter_cons_of_neg (by simp), List.filter_nil,
          List.append_nil]
      rw [hfilter, hfilter2, List.cons_inj_right]
      exact hsplit.symm
  | y :: mid, x, t, rtail, hr, hbase, hlast, hsub => by
      rw [List.cons_append] at hbase ⊢
      rw [refineAlong_cons_cons, glue_cons]
      have hbase' := List.isChain_cons_cons.1 hbase
      have hxy : x < y := hbase'.1
      have hy_r : y ∈ rtail := by
        have hy : y ∈ x :: rtail := hsub y (by simp)
        rcases List.mem_cons.1 hy with h0 | h0
        · exact absurd h0.symm (ne_of_lt hxy)
        · exact h0
      set pre : List T := rtail.takeWhile (fun z => decide (z < y)) with hpre
      set r' : List T := rtail.dropWhile (fun z => decide (z < y)) with hrr
      have hsplit : pre ++ r' = rtail := List.takeWhile_append_dropWhile
      have hr'_head : r' = y :: r'.tail :=
        dropWhile_eq_cons_of_mem hr.tail hy_r
      have hseg : (x :: rtail).filter
          (fun z => decide (x < z) && decide (z < y)) = pre := by
        rw [List.filter_cons_of_neg (by simp)]
        have h1 : rtail.filter (fun z => decide (x < z) && decide (z < y)) =
            rtail.filter (fun z => decide (z < y)) := by
          apply List.filter_congr
          intro z hz
          simp [head_lt_of_mem_tail hr hz]
        rw [h1, hpre]
        exact filter_eq_takeWhile_of_chain y rtail hr.tail
      have hchain_r' : List.IsChain (· < ·) r' :=
        hr.tail.sublist (List.dropWhile_suffix _).sublist
      have hchain_yr : List.IsChain (· < ·) (y :: r'.tail) := by
        rw [← hr'_head]
        exact hchain_r'
      have hr'_ne : r' ≠ [] := by
        rw [hr'_head]
        simp
      have hlast_r' : ((y :: r'.tail).getLast (by simp)) = t := by
        have hrtail_ne : rtail ≠ [] := by
          intro h0
          rw [h0] at hy_r
          exact absurd hy_r (by simp)
        have hlast'' : rtail.getLast hrtail_ne = t := by
          rw [List.getLast_cons hrtail_ne] at hlast
          exact hlast
        obtain ⟨pre2, hpre2⟩ : r' <:+ rtail := List.dropWhile_suffix _
        have h1 : rtail.getLast? = some t := by
          rw [List.getLast?_eq_some_getLast hrtail_ne, hlast'']
        have h2 : r'.getLast? = some t := by
          rw [← h1, ← hpre2, List.getLast?_append_of_ne_nil pre2 hr'_ne]
        rw [hr'_head, List.getLast?_eq_some_getLast (by simp)] at h2
        exact Option.some_injective _ h2
      have hsub' : ∀ z ∈ y :: (mid ++ [t]), z ∈ y :: r'.tail := by
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz'
        · simp
        · have hyz : y < z := head_lt_of_mem_tail hbase'.2 hz'
          have hz_r : z ∈ rtail := by
            have h1 := hsub z (by simp [hz'])
            rcases List.mem_cons.1 h1 with h0 | h0
            · exact absurd (h0 ▸ lt_trans hxy hyz) (lt_irrefl _)
            · exact h0
          rw [← hsplit, List.mem_append] at hz_r
          rcases hz_r with h0 | h0
          · have h1 := List.mem_takeWhile_imp h0
            simp only [decide_eq_true_eq] at h1
            exact absurd (lt_trans hyz h1) (lt_irrefl _)
          · rw [hr'_head] at h0
            exact h0
      have hlow : refineAlong (x :: rtail) (y :: (mid ++ [t])) =
          refineAlong r' (y :: (mid ++ [t])) := by
        have h1 : x :: rtail = (x :: pre) ++ r' := by
          rw [List.cons_append, hsplit]
        rw [h1]
        refine refineAlong_append_low (x :: pre) _ hbase'.2 ?_ r'
        intro z hz w hw
        simp only [List.head?_cons, Option.mem_some_iff] at hw
        subst hw
        rcases List.mem_cons.1 hz with rfl | hz'
        · exact hxy
        · have h1 := List.mem_takeWhile_imp (hpre ▸ hz')
          simpa using h1
      rw [hlow, hr'_head,
        glue_refineAlong mid y t r'.tail hchain_yr hbase'.2 hlast_r' hsub']
      rw [List.cons_inj_right, hseg, ← hsplit, ← hr'_head]

end Sewing

end RoughPaths
