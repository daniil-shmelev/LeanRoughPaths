/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.Analytic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.PSeries

/-!
# The maximal inequality behind the sewing lemma

The core estimate of rough integration theory (Friz–Hairer, Lemma 4.2;
Cass–Salvi lecture notes, arXiv:2404.06583): if a two-parameter map `Ξ` has
its Chen defect `δΞ(s,u,t) = Ξ s t - Ξ s u - Ξ u t` controlled by `ω^θ` for
a control `ω`, then Riemann sums of `Ξ` along any partition of `[s,t]` stay
within a uniform multiple of `ω(s,t)^θ` of `Ξ s t`.

The proof is the classical point-removal argument: any partition with
`k ≥ 2` intervals contains an interior point whose neighbouring control
mass is at most `2 ω(s,t) / (k-1)` (by superadditivity of `ω` applied to
alternating subchains), and removing it changes the Riemann sum by at most
`(2 ω(s,t) / (k-1))^θ`; iterating yields the bound `Σ_{j≥1} (2 ω(s,t)/j)^θ`.

All estimates are stated in `ENNReal` via the extended norm `‖·‖ₑ`, so no
summability side conditions are needed for the maximal inequality itself.
-/

namespace RoughPaths

namespace Sewing

open scoped ENNReal

universe u v

variable {T : Type u} [Preorder T]

/-- The sum of a two-parameter function along the consecutive pairs of a
partition, `Σᵢ f pᵢ pᵢ₊₁`. -/
def pairSum {E : Type v} [AddCommMonoid E] (f : T → T → E) : List T → E
  | x :: y :: rest => f x y + pairSum f (y :: rest)
  | _ => 0

omit [Preorder T] in
@[simp]
theorem pairSum_nil {E : Type v} [AddCommMonoid E] (f : T → T → E) :
    pairSum f [] = 0 := rfl

omit [Preorder T] in
@[simp]
theorem pairSum_single {E : Type v} [AddCommMonoid E] (f : T → T → E)
    (x : T) : pairSum f [x] = 0 := rfl

omit [Preorder T] in
@[simp]
theorem pairSum_cons_cons {E : Type v} [AddCommMonoid E] (f : T → T → E)
    (x y : T) (rest : List T) :
    pairSum f (x :: y :: rest) = f x y + pairSum f (y :: rest) := rfl

/-- The list of consecutive triples of a partition. -/
def triples : List T → List (T × T × T)
  | x :: y :: z :: rest => (x, y, z) :: triples (y :: z :: rest)
  | _ => []

omit [Preorder T] in
@[simp]
theorem triples_nil : triples ([] : List T) = [] := rfl

omit [Preorder T] in
@[simp]
theorem triples_single (x : T) : triples [x] = [] := rfl

omit [Preorder T] in
@[simp]
theorem triples_pair (x y : T) : triples [x, y] = [] := rfl

omit [Preorder T] in
@[simp]
theorem triples_cons_cons_cons (x y z : T) (rest : List T) :
    triples (x :: y :: z :: rest) = (x, y, z) :: triples (y :: z :: rest) :=
  rfl

omit [Preorder T] in
theorem length_triples : ∀ p : List T, (triples p).length = p.length - 2
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: y :: z :: rest => by
      rw [triples_cons_cons_cons, List.length_cons,
        length_triples (y :: z :: rest)]
      simp

omit [Preorder T] in
/-- A membership in the triple list decomposes the partition. -/
theorem eq_append_of_mem_triples :
    ∀ {p : List T} {x y z : T}, (x, y, z) ∈ triples p →
      ∃ u v : List T, p = u ++ x :: y :: z :: v
  | [], _, _, _, h => absurd h (by simp)
  | [_], _, _, _, h => absurd h (by simp)
  | [_, _], _, _, _, h => absurd h (by simp)
  | a :: b :: c :: rest, x, y, z, h => by
      rw [triples_cons_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · have h' : x = a ∧ y = b ∧ z = c := by simpa using h
        obtain ⟨rfl, rfl, rfl⟩ := h'
        exact ⟨[], rest, rfl⟩
      · obtain ⟨u, v, huv⟩ := eq_append_of_mem_triples h
        exact ⟨a :: u, v, by rw [List.cons_append, huv]⟩

/-- The head of a chained list is below its last element. -/
theorem isChain_head_le_getLast :
    ∀ (a : T) (l : List T), List.IsChain (· ≤ ·) (a :: l) →
      a ≤ (a :: l).getLast (by simp)
  | _, [], _ => le_refl _
  | a, b :: l, h => by
      rw [List.isChain_cons_cons] at h
      exact le_trans h.1 (by
        simpa [List.getLast_cons] using isChain_head_le_getLast b l h.2)

/-- The pair sum of a control along any chained list is bounded by the
control between the head and the last point. -/
theorem pairSum_le_head_getLast (ω : Control T) :
    ∀ (x : T) (q : List T), List.IsChain (· ≤ ·) (x :: q) →
      pairSum (fun a b => ω a b) (x :: q) ≤
        ω x ((x :: q).getLast (by simp))
  | _, [], _ => by simp
  | x, y :: q, h => by
      rw [List.isChain_cons_cons] at h
      have hxy := h.1
      have hyl : y ≤ (y :: q).getLast (by simp) :=
        isChain_head_le_getLast y q h.2
      have ih := pairSum_le_head_getLast ω y q h.2
      calc pairSum (fun a b => ω a b) (x :: y :: q)
          = ω x y + pairSum (fun a b => ω a b) (y :: q) := rfl
        _ ≤ ω x y + ω y ((y :: q).getLast (by simp)) := add_le_add le_rfl ih
        _ ≤ ω x ((y :: q).getLast (by simp)) := ω.superadditive hxy hyl
        _ = ω x ((x :: y :: q).getLast (by simp)) :=
            congrArg (ω x) (List.getLast_cons (by simp)).symm

/-- Monotonicity of controls in nested intervals. -/
theorem control_mono (ω : Control T) {s a b t : T} (hsa : s ≤ a)
    (hab : a ≤ b) (hbt : b ≤ t) : ω a b ≤ ω s t :=
  calc ω a b ≤ ω s a + ω a b := le_add_self
    _ ≤ ω s b := ω.superadditive hsa hab
    _ ≤ ω s b + ω b t := le_self_add
    _ ≤ ω s t := ω.superadditive (le_trans hsa hab) hbt

/-- The sum of the control over the consecutive triples of a partition. -/
def tripleSum (ω : Control T) (p : List T) : ENNReal :=
  ((triples p).map fun t => ω t.1 t.2.2).sum

@[simp]
theorem tripleSum_cons_cons_cons (ω : Control T) (x y z : T)
    (rest : List T) :
    tripleSum ω (x :: y :: z :: rest) =
      ω x z + tripleSum ω (y :: z :: rest) := rfl

/-- **The alternating superadditivity bound**: the triple sum of a control
along a chained partition is at most twice the control between the extreme
points (the even- and odd-indexed subchains each contribute one copy). -/
theorem tripleSum_le (ω : Control T) :
    ∀ (x y : T) (q : List T), List.IsChain (· ≤ ·) (x :: y :: q) →
      tripleSum ω (x :: y :: q) ≤
        ω x ((x :: y :: q).getLast (by simp)) +
          ω y ((x :: y :: q).getLast (by simp))
  | x, y, [], _ => by
      simp [tripleSum]
  | x, y, z :: q, h => by
      have h1 := h
      rw [List.isChain_cons_cons] at h1
      have hxy := h1.1
      have h2 := h1.2
      rw [List.isChain_cons_cons] at h2
      have hyz := h2.1
      have hzL : z ≤ (z :: q).getLast (by simp) :=
        isChain_head_le_getLast z q h2.2
      have ih := tripleSum_le ω y z q h1.2
      have hL : (y :: z :: q).getLast (by simp) =
          (x :: y :: z :: q).getLast (by simp) :=
        (List.getLast_cons (by simp)).symm
      have hL2 : (z :: q).getLast (by simp) =
          (y :: z :: q).getLast (by simp) :=
        (List.getLast_cons (by simp)).symm
      rw [tripleSum_cons_cons_cons, ← hL]
      calc ω x z + tripleSum ω (y :: z :: q)
          ≤ ω x z + (ω y ((y :: z :: q).getLast (by simp)) +
              ω z ((y :: z :: q).getLast (by simp))) :=
            add_le_add le_rfl ih
        _ = (ω x z + ω z ((y :: z :: q).getLast (by simp))) +
              ω y ((y :: z :: q).getLast (by simp)) := by
            ring
        _ ≤ ω x ((y :: z :: q).getLast (by simp)) +
              ω y ((y :: z :: q).getLast (by simp)) := by
            refine add_le_add ?_ le_rfl
            exact ω.superadditive (le_trans hxy hyz) (hL2 ▸ hzL)

/-- A nonempty list contains an element whose value is at most the average:
`length * f a ≤ Σ f`. -/
theorem exists_length_mul_le_sum {α : Type v} (f : α → ENNReal) :
    ∀ (l : List α), l ≠ [] →
      ∃ a ∈ l, (l.length : ENNReal) * f a ≤ (l.map f).sum
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp⟩
  | a :: b :: l, _ => by
      obtain ⟨c, hc, hle⟩ := exists_length_mul_le_sum f (b :: l) (by simp)
      rcases le_total (f a) (f c) with hac | hca
      · refine ⟨a, by simp, ?_⟩
        rw [List.length_cons, List.map_cons, List.sum_cons]
        push_cast
        calc ((b :: l).length + 1 : ENNReal) * f a
            = f a + ((b :: l).length : ENNReal) * f a := by ring
          _ ≤ f a + ((b :: l).length : ENNReal) * f c :=
              add_le_add le_rfl (mul_le_mul_right hac _)
          _ ≤ f a + ((b :: l).map f).sum := add_le_add le_rfl hle
      · refine ⟨c, List.mem_cons_of_mem a hc, ?_⟩
        rw [List.length_cons, List.map_cons, List.sum_cons]
        push_cast
        calc ((b :: l).length + 1 : ENNReal) * f c
            = f c + ((b :: l).length : ENNReal) * f c := by ring
          _ ≤ f a + ((b :: l).map f).sum := add_le_add hca hle

omit [Preorder T] in
/-- Splitting a pair sum at an interior point. -/
theorem pairSum_append {E : Type v} [AddCommMonoid E] (f : T → T → E) :
    ∀ (u : List T) (x : T) (w : List T),
      pairSum f (u ++ x :: w) = pairSum f (u ++ [x]) + pairSum f (x :: w)
  | [], x, w => by simp
  | [a], x, w => by simp
  | a :: b :: u, x, w => by
      have ih := pairSum_append f (b :: u) x w
      simp only [List.cons_append] at ih ⊢
      rw [pairSum_cons_cons, pairSum_cons_cons, ih, ← add_assoc]

section Maximal

variable {E : Type v} [SeminormedAddCommGroup E]

/-- **The maximal inequality of the sewing lemma** (Friz–Hairer, Lemma 4.2;
Cass–Salvi, arXiv:2404.06583, the key estimate behind rough integration):
if the Chen defect `δΞ(a,b,c) = Ξ a c - Ξ a b - Ξ b c` is bounded by
`ω(a,c)^θ` for a control `ω`, then the Riemann sum of `Ξ` along any chained
partition with `n + 1` intervals differs from `Ξ` of the endpoints by at
most `Σ_{j=1}^{n} (2 ω(s,t)/j)^θ`.

Proved by the point-removal argument: the pigeonhole applied to the
alternating superadditivity bound produces an interior point whose removal
costs at most `(2 ω(s,t)/n)^θ`. -/
theorem maximal_inequality (ω : Control T) (Ξ : T → T → E) (θ : ℝ)
    (hθ : 0 ≤ θ)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ) :
    ∀ (n : ℕ) (p : List T) (hne : p ≠ []), p.length = n + 2 →
      List.IsChain (· ≤ ·) p →
      ‖pairSum Ξ p - Ξ (p.head hne) (p.getLast hne)‖ₑ ≤
        ∑ j ∈ Finset.range n,
          (2 * ω (p.head hne) (p.getLast hne) / (j + 1)) ^ θ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hne hlen hchain
  revert hne hchain
  match n, p, hlen with
  | 0, [x, y], _ =>
      intro hne hchain
      show ‖pairSum Ξ [x, y] - Ξ x y‖ₑ ≤
        ∑ j ∈ Finset.range 0, (2 * ω x y / (j + 1)) ^ θ
      simp [enorm]
  | (m + 1), x :: y :: z :: rest, hlen =>
  intro hne hchain
  have hhx : (x :: y :: z :: rest).head hne = x := rfl
  rw [hhx]
  -- pigeonhole: some interior point has small neighbouring control mass
  have htne : triples (x :: y :: z :: rest) ≠ [] := by
    rw [triples_cons_cons_cons]
    simp
  obtain ⟨tr, htr, havg⟩ := exists_length_mul_le_sum
    (fun tr => ω tr.1 tr.2.2) (triples (x :: y :: z :: rest)) htne
  obtain ⟨a, b, c⟩ := tr
  have hlentr : ((triples (x :: y :: z :: rest)).length : ENNReal) =
      ((m + 1 : ℕ) : ENNReal) := by
    rw [length_triples]
    simp only [List.length_cons] at hlen ⊢
    norm_cast
    omega
  -- the triple sum is bounded by twice the endpoint control
  have hchain1 := hchain
  rw [List.isChain_cons_cons] at hchain1
  have hyL : y ≤ (y :: z :: rest).getLast (by simp) :=
    isChain_head_le_getLast y (z :: rest) hchain1.2
  have htsum : tripleSum ω (x :: y :: z :: rest) ≤
      2 * ω x ((x :: y :: z :: rest).getLast hne) := by
    have h1 := tripleSum_le ω x y (z :: rest) hchain
    have h2 : ω y ((x :: y :: z :: rest).getLast hne) ≤
        ω x ((x :: y :: z :: rest).getLast hne) :=
      control_mono ω hchain1.1 hyL (le_refl _)
    rw [two_mul]
    exact le_trans h1 (add_le_add le_rfl h2)
  -- the chosen interior point is cheap to remove
  have hsmall : ω a c ≤
      2 * ω x ((x :: y :: z :: rest).getLast hne) /
        ((m + 1 : ℕ) : ENNReal) := by
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (by exact_mod_cast Nat.succ_ne_zero m))
      (Or.inl (ENNReal.natCast_ne_top _)), mul_comm]
    calc ((m + 1 : ℕ) : ENNReal) * ω a c
        ≤ ((triples (x :: y :: z :: rest)).map
            fun tr => ω tr.1 tr.2.2).sum := by
          rw [← hlentr]
          exact havg
      _ = tripleSum ω (x :: y :: z :: rest) := rfl
      _ ≤ 2 * ω x ((x :: y :: z :: rest).getLast hne) := htsum
  -- decompose the partition at the chosen triple and remove the point
  obtain ⟨u, v, hp⟩ := eq_append_of_mem_triples htr
  have hchain2 : List.IsChain (· ≤ ·) (u ++ a :: b :: c :: v) :=
    hp ▸ hchain
  rw [List.isChain_split] at hchain2
  have hab : a ≤ b := (List.isChain_cons_cons.1 hchain2.2).1
  have hmid := (List.isChain_cons_cons.1 hchain2.2).2
  have hbc : b ≤ c := (List.isChain_cons_cons.1 hmid).1
  have hcv : List.IsChain (· ≤ ·) (c :: v) :=
    (List.isChain_cons_cons.1 hmid).2
  have hchain' : List.IsChain (· ≤ ·) (u ++ a :: c :: v) := by
    rw [List.isChain_split]
    exact ⟨hchain2.1, List.isChain_cons_cons.2 ⟨le_trans hab hbc, hcv⟩⟩
  have hne'' : u ++ a :: c :: v ≠ [] := by simp
  have hlen' : (u ++ a :: c :: v).length = m + 2 := by
    have h4 := congrArg List.length hp
    simp only [List.length_append, List.length_cons] at hlen h4 ⊢
    omega
  -- endpoints are unchanged by the removal
  have hhead : (u ++ a :: c :: v).head hne'' = x := by
    cases u with
    | nil =>
        have hxa : x = a := by
          have := congrArg List.head? hp
          simpa using this
        simp [hxa]
    | cons w u' =>
        have hxw : x = w := by
          have := congrArg List.head? hp
          simpa using this
        simp [hxw]
  have hlast : (u ++ a :: c :: v).getLast hne'' =
      (x :: y :: z :: rest).getLast hne := by
    have e1 : (u ++ a :: c :: v).getLast? = (c :: v).getLast? := by
      rw [show u ++ a :: c :: v = (u ++ [a]) ++ c :: v by simp,
        List.getLast?_append_cons]
    have e2 : (x :: y :: z :: rest).getLast? = (c :: v).getLast? := by
      rw [hp, show u ++ a :: b :: c :: v = (u ++ [a, b]) ++ c :: v by simp,
        List.getLast?_append_cons]
    have e3 := (List.getLast?_eq_getLast_of_ne_nil hne'').symm.trans
      (e1.trans e2.symm)
    rw [List.getLast?_eq_getLast_of_ne_nil hne] at e3
    exact Option.some.inj e3
  -- the Riemann sums differ by the Chen defect at the removed point
  have hdiff : pairSum Ξ (x :: y :: z :: rest) -
      pairSum Ξ (u ++ a :: c :: v) = -(Ξ a c - Ξ a b - Ξ b c) := by
    rw [hp, pairSum_append Ξ u a (b :: c :: v),
      pairSum_append Ξ u a (c :: v), pairSum_cons_cons,
      pairSum_cons_cons, pairSum_cons_cons]
    abel
  -- assemble via the triangle inequality and the inductive hypothesis
  have hIH := ih m (Nat.lt_succ_self m) (u ++ a :: c :: v) hne'' hlen'
    hchain'
  rw [hhead, hlast] at hIH
  calc ‖pairSum Ξ (x :: y :: z :: rest) -
        Ξ x ((x :: y :: z :: rest).getLast hne)‖ₑ
      = edist (pairSum Ξ (x :: y :: z :: rest))
          (Ξ x ((x :: y :: z :: rest).getLast hne)) :=
        (edist_eq_enorm_sub _ _).symm
    _ ≤ edist (pairSum Ξ (x :: y :: z :: rest))
          (pairSum Ξ (u ++ a :: c :: v)) +
        edist (pairSum Ξ (u ++ a :: c :: v))
          (Ξ x ((x :: y :: z :: rest).getLast hne)) :=
        edist_triangle _ _ _
    _ = ‖pairSum Ξ (x :: y :: z :: rest) -
            pairSum Ξ (u ++ a :: c :: v)‖ₑ +
          ‖pairSum Ξ (u ++ a :: c :: v) -
            Ξ x ((x :: y :: z :: rest).getLast hne)‖ₑ := by
        rw [edist_eq_enorm_sub, edist_eq_enorm_sub]
    _ ≤ (2 * ω x ((x :: y :: z :: rest).getLast hne) /
            ((m + 1 : ℕ) : ENNReal)) ^ θ +
          ∑ j ∈ Finset.range m,
            (2 * ω x ((x :: y :: z :: rest).getLast hne) / (j + 1)) ^ θ := by
        refine add_le_add ?_ hIH
        rw [hdiff, enorm_neg]
        exact le_trans (hδ hab hbc) (ENNReal.rpow_le_rpow hsmall hθ)
    _ = ∑ j ∈ Finset.range (m + 1),
          (2 * ω x ((x :: y :: z :: rest).getLast hne) / (j + 1)) ^ θ := by
        rw [Finset.sum_range_succ, add_comm]
        norm_cast

/-- The maximal inequality with a partition-independent constant:
Riemann sums along **any** chained partition stay within
`(Σ_j (2/(j+1))^θ) · ω(s,t)^θ` of the endpoint increment. -/
theorem maximal_inequality_tsum (ω : Control T) (Ξ : T → T → E) (θ : ℝ)
    (hθ : 0 ≤ θ)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ)
    (n : ℕ) (p : List T) (hne : p ≠ []) (hlen : p.length = n + 2)
    (hchain : List.IsChain (· ≤ ·) p) :
    ‖pairSum Ξ p - Ξ (p.head hne) (p.getLast hne)‖ₑ ≤
      (∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ) *
        ω (p.head hne) (p.getLast hne) ^ θ := by
  refine le_trans (maximal_inequality ω Ξ θ hθ hδ n p hne hlen hchain) ?_
  rw [← ENNReal.tsum_mul_right]
  refine le_trans (ENNReal.sum_le_tsum (Finset.range n)) ?_
  refine le_of_eq (tsum_congr fun j => ?_)
  have hbase : 2 * ω (p.head hne) (p.getLast hne) / ((j : ENNReal) + 1) =
      2 / ((j : ENNReal) + 1) * ω (p.head hne) (p.getLast hne) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [hbase, ENNReal.mul_rpow_of_nonneg _ _ hθ]

end Maximal

section Uniqueness

variable {E : Type v} [NormedAddCommGroup E]

private theorem enorm_add_le' (a b : E) : ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  simp only [enorm]
  exact_mod_cast nnnorm_add_le a b

private theorem enorm_sub_le' (a b : E) : ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  rw [sub_eq_add_neg]
  refine le_trans (enorm_add_le' a (-b)) ?_
  rw [enorm_neg]

/-- A control admits fine partitions if between any two comparable times
there is an interpolating chain all of whose consecutive control
increments are at most `ε`. This holds e.g. for controls continuous on a
compact time interval. -/
def HasFinePartitions (ω : Control T) : Prop :=
  ∀ ⦃s t : T⦄, s ≤ t → ∀ ε : ENNReal, 0 < ε →
    ∃ q : List T,
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (s :: (q ++ [t]))

/-- **Uniqueness in the sewing lemma** (Friz–Hairer, Lemma 4.2; Cass–Salvi,
arXiv:2404.06583): two primitives of `Ξ` with remainder `O(ω^θ)`, `θ > 1`,
have equal increments, provided the control admits fine partitions. -/
theorem sewing_unique (ω : Control T) (Ξ : T → T → E) {θ : ℝ}
    (hθ : 1 < θ) {C : ENNReal} (hC : C ≠ ⊤)
    (hfine : HasFinePartitions ω) {I I' : T → E}
    (hI : ∀ ⦃a b : T⦄, a ≤ b → ‖I b - I a - Ξ a b‖ₑ ≤ C * ω a b ^ θ)
    (hI' : ∀ ⦃a b : T⦄, a ≤ b → ‖I' b - I' a - Ξ a b‖ₑ ≤ C * ω a b ^ θ)
    {s t : T} (hst : s ≤ t) (hω : ω s t ≠ ⊤) :
    I t - I s = I' t - I' s := by
  have hθ1 : (0 : ℝ) ≤ θ - 1 := by linarith
  -- a single fine step contributes at most `2C ε^{θ-1} ω`
  have hstep : ∀ (ε : ENNReal) ⦃a b : T⦄, a ≤ b → ω a b ≤ ε →
      ‖(I b - I a) - (I' b - I' a)‖ₑ ≤
        2 * C * ε ^ (θ - 1) * ω a b := by
    intro ε a b hab hε
    have hsplit : (I b - I a) - (I' b - I' a) =
        (I b - I a - Ξ a b) - (I' b - I' a - Ξ a b) := by
      abel
    rw [hsplit]
    refine le_trans (enorm_sub_le' _ _) ?_
    refine le_trans (add_le_add (hI hab) (hI' hab)) ?_
    have hpow : ω a b ^ θ ≤ ε ^ (θ - 1) * ω a b := by
      have h1 : ω a b ^ (θ - 1) * ω a b ^ (1 : ℝ) = ω a b ^ θ := by
        rw [← ENNReal.rpow_add_of_nonneg (θ - 1) 1 hθ1 (by norm_num)]
        norm_num
      calc ω a b ^ θ = ω a b ^ (θ - 1) * ω a b ^ (1 : ℝ) := h1.symm
        _ = ω a b ^ (θ - 1) * ω a b := by rw [ENNReal.rpow_one]
        _ ≤ ε ^ (θ - 1) * ω a b :=
            mul_le_mul_left (ENNReal.rpow_le_rpow hε hθ1) _
    calc C * ω a b ^ θ + C * ω a b ^ θ
        = 2 * C * (ω a b ^ θ) := by ring
      _ ≤ 2 * C * (ε ^ (θ - 1) * ω a b) := mul_le_mul_right hpow _
      _ = 2 * C * ε ^ (θ - 1) * ω a b := by ring
  -- telescoping over a fine partition
  have htele : ∀ (ε : ENNReal) (x : T) (q : List T) (u : T),
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (x :: (q ++ [u])) →
      ‖(I u - I x) - (I' u - I' x)‖ₑ ≤
        2 * C * ε ^ (θ - 1) *
          pairSum (fun a b => ω a b) (x :: (q ++ [u])) := by
    intro ε x q
    induction q generalizing x with
    | nil =>
        intro u h
        have h1 := List.isChain_pair.1 (by simpa using h)
        rw [show pairSum (fun a b => ω a b) (x :: ([] ++ [u])) =
          ω x u + 0 from rfl, add_zero]
        exact hstep ε h1.1 h1.2
    | cons y q ih =>
        intro u h
        rw [List.cons_append, List.isChain_cons_cons] at h
        have hxy := h.1
        have hrest := ih y u h.2
        have hsplit : (I u - I x) - (I' u - I' x) =
            ((I y - I x) - (I' y - I' x)) +
              ((I u - I y) - (I' u - I' y)) := by
          abel
        rw [hsplit, show pairSum (fun a b => ω a b)
          (x :: ((y :: q) ++ [u])) =
          ω x y + pairSum (fun a b => ω a b) (y :: (q ++ [u])) from rfl,
          mul_add]
        exact le_trans (enorm_add_le' _ _)
          (add_le_add (hstep ε hxy.1 hxy.2) hrest)
  -- the total control mass along the partition is at most `ω s t`
  have hmass : ∀ (q : List T),
      List.IsChain (· ≤ ·) (s :: (q ++ [t])) →
      pairSum (fun a b => ω a b) (s :: (q ++ [t])) ≤ ω s t := by
    intro q hchain
    have h := pairSum_le_head_getLast ω s (q ++ [t]) hchain
    have hlast : ((s :: (q ++ [t]))).getLast (by simp) = t := by
      have h1 : (s :: (q ++ [t])).getLast? = some t := by
        rw [show s :: (q ++ [t]) = (s :: q) ++ [t] from rfl]
        exact List.getLast?_concat
      have h2 := List.getLast?_eq_getLast_of_ne_nil
        (l := s :: (q ++ [t])) (by simp)
      rw [h1] at h2
      exact (Option.some.inj h2).symm
    rw [hlast] at h
    exact h
  -- combine: the defect is at most `2C ε^{θ-1} ω(s,t)` for every `ε > 0`
  have hbound : ∀ ε : ENNReal, 0 < ε →
      ‖(I t - I s) - (I' t - I' s)‖ₑ ≤ 2 * C * ε ^ (θ - 1) * ω s t := by
    intro ε hε
    obtain ⟨q, hq⟩ := hfine hst ε hε
    have hchain : List.IsChain (· ≤ ·) (s :: (q ++ [t])) :=
      hq.imp fun _ _ h => h.1
    exact le_trans (htele ε s q t hq)
      (mul_le_mul_right (hmass q hchain) _)
  -- let `ε → 0`
  have hzero : ‖(I t - I s) - (I' t - I' s)‖ₑ = 0 := by
    have hle : ∀ δ : NNReal, 0 < δ → (0 : ENNReal) < ⊤ →
        ‖(I t - I s) - (I' t - I' s)‖ₑ ≤ (0 : ENNReal) + δ := by
      intro δ hδ _
      by_cases hCK : 2 * C * ω s t = 0
      · have := hbound 1 (by norm_num)
        rw [show 2 * C * (1 : ENNReal) ^ (θ - 1) * ω s t =
          2 * C * ω s t * 1 ^ (θ - 1) from by ring, hCK, zero_mul] at this
        exact le_trans this (by simp)
      · have hCK' : 2 * C * ω s t ≠ ⊤ := by
          refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ hC) hω
          norm_num
        set ε : ENNReal := ((δ : ENNReal) / (2 * C * ω s t)) ^ (θ - 1)⁻¹
          with hεdef
        have hεpos : 0 < ε := by
          rw [hεdef]
          refine ENNReal.rpow_pos ?_ ?_
          · exact ENNReal.div_pos (by exact_mod_cast hδ.ne') hCK'
          · exact ENNReal.div_ne_top (by simp) hCK
        have hεpow : ε ^ (θ - 1) = (δ : ENNReal) / (2 * C * ω s t) := by
          rw [hεdef, ← ENNReal.rpow_mul, inv_mul_cancel₀ (by linarith),
            ENNReal.rpow_one]
        have := hbound ε hεpos
        rw [show 2 * C * ε ^ (θ - 1) * ω s t =
          2 * C * ω s t * ε ^ (θ - 1) from by ring, hεpow,
          ENNReal.mul_div_cancel' (fun h => absurd h hCK)
            (fun h => absurd h hCK')] at this
        simpa using this
    have h0 := ENNReal.le_of_forall_pos_le_add hle
    simpa using h0
  have : (I t - I s) - (I' t - I' s) = 0 := by
    have := hzero
    simp only [enorm] at this
    exact_mod_cast nnnorm_eq_zero.1 (by exact_mod_cast this)
  exact sub_eq_zero.1 this

end Uniqueness

section Refinement

variable {E : Type v} [SeminormedAddCommGroup E]

private theorem enorm_add_le'' (a b : E) : ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  simp only [enorm]
  exact_mod_cast nnnorm_add_le a b

/-- Glue a partition (given as segment starting points with interpolating
interior chains) into a single refined partition ending at `t`. -/
def glue : List (T × List T) → T → List T
  | [], t => [t]
  | (x, q) :: rest, t => x :: (q ++ glue rest t)

omit [Preorder T] in
@[simp]
theorem glue_nil (t : T) : glue ([] : List (T × List T)) t = [t] := rfl

omit [Preorder T] in
@[simp]
theorem glue_cons (x : T) (q : List T) (rest : List (T × List T)) (t : T) :
    glue ((x, q) :: rest) t = x :: (q ++ glue rest t) := rfl

/-- The coarse partition underlying a glued refinement. -/
def basePoints : List (T × List T) → T → List T
  | [], t => [t]
  | (x, _) :: rest, t => x :: basePoints rest t

omit [Preorder T] in
@[simp]
theorem basePoints_nil (t : T) :
    basePoints ([] : List (T × List T)) t = [t] := rfl

omit [Preorder T] in
@[simp]
theorem basePoints_cons (x : T) (q : List T) (rest : List (T × List T))
    (t : T) : basePoints ((x, q) :: rest) t = x :: basePoints rest t := rfl

omit [Preorder T] in
theorem glue_ne_nil : ∀ (ps : List (T × List T)) (t : T), glue ps t ≠ []
  | [], _ => by simp
  | (_, _) :: _, _ => by simp

omit [Preorder T] in
theorem head_glue : ∀ (x : T) (q : List T) (rest : List (T × List T))
    (t : T), (glue ((x, q) :: rest) t).head (glue_ne_nil _ t) = x :=
  fun _ _ _ _ => rfl

omit [Preorder T] in
/-- The head of a glued partition is the head of its base. -/
theorem head_basePoints (x : T) (q : List T) (rest : List (T × List T))
    (t : T) : (basePoints ((x, q) :: rest) t).head (by simp) = x := rfl

omit [Preorder T] in
/-- The pair sum along a glued partition splits into the segment sums. -/
theorem pairSum_glue (f : T → T → E) :
    ∀ (ps : List (T × List T)) (t : T),
      pairSum f (glue ps t) =
        (List.zip ps ((ps.map Prod.fst).tail ++ [t])).foldr
          (fun seg acc => pairSum f (seg.1.1 :: (seg.1.2 ++ [seg.2])) + acc)
          0
  | [], t => rfl
  | [(x, q)], t => by
      simp only [glue_cons, glue_nil, List.map_cons, List.map_nil,
        List.tail_cons, List.nil_append, List.zip_cons_cons, List.zip_nil_right,
        List.foldr_cons, List.foldr_nil, add_zero]
  | (x, q) :: (y, r) :: rest, t => by
      have ih := pairSum_glue f ((y, r) :: rest) t
      simp only [glue_cons, List.map_cons, List.tail_cons, List.cons_append,
        List.zip_cons_cons, List.foldr_cons] at ih ⊢
      rw [← ih]
      rw [show (x :: (q ++ (y :: (r ++ glue rest t)))) =
        x :: (q ++ y :: (r ++ glue rest t)) from rfl]
      rw [show x :: (q ++ y :: (r ++ glue rest t)) =
        (x :: q) ++ y :: (r ++ glue rest t) from rfl]
      rw [pairSum_append f (x :: q) y (r ++ glue rest t)]
      rfl

set_option maxHeartbeats 1000000 in
/-- **The refinement bound**: refining each interval of a partition changes
the Riemann sum by at most the sewing constant times the `θ`-mass of the
coarse partition (Friz–Hairer, Lemma 4.2, the refinement step). -/
theorem refine_bound (ω : Control T) (Ξ : T → T → E) (θ : ℝ) (hθ : 0 ≤ θ)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ) :
    ∀ (ps : List (T × List T)) (t : T),
      List.IsChain (· ≤ ·) (glue ps t) →
      ‖pairSum Ξ (glue ps t) - pairSum Ξ (basePoints ps t)‖ₑ ≤
        (∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ) *
          pairSum (fun a b => ω a b ^ θ) (basePoints ps t)
  | [], t, _ => by
      simp [enorm]
  | [(x, q)], t, hchain => by
      have hseg : ‖pairSum Ξ (x :: (q ++ [t])) - Ξ x t‖ₑ ≤
          (∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ) * ω x t ^ θ := by
        have hne : (x :: (q ++ [t])) ≠ [] := by simp
        have hlen : (x :: (q ++ [t])).length = q.length + 2 := by simp
        have hb := maximal_inequality_tsum ω Ξ θ hθ hδ q.length
          (x :: (q ++ [t])) hne hlen (by simpa using hchain)
        have hhead : (x :: (q ++ [t])).head hne = x := rfl
        have hlast : (x :: (q ++ [t])).getLast hne = t := by
          have h1 : (x :: (q ++ [t])).getLast? = some t := by
            rw [show x :: (q ++ [t]) = (x :: q) ++ [t] from rfl]
            exact List.getLast?_concat
          have h2 := List.getLast?_eq_getLast_of_ne_nil
            (l := x :: (q ++ [t])) hne
          rw [h1] at h2
          exact (Option.some.inj h2).symm
        rw [hhead, hlast] at hb
        exact hb
      calc ‖pairSum Ξ (glue [(x, q)] t) -
            pairSum Ξ (basePoints [(x, q)] t)‖ₑ
          = ‖pairSum Ξ (x :: (q ++ [t])) - Ξ x t‖ₑ := by
            simp only [glue_cons, glue_nil, basePoints_cons, basePoints_nil,
              pairSum_cons_cons, pairSum_single, add_zero]
        _ ≤ (∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ) * ω x t ^ θ := hseg
        _ = (∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ) *
            pairSum (fun a b => ω a b ^ θ) (basePoints [(x, q)] t) := by
            simp only [basePoints_cons, basePoints_nil, pairSum_cons_cons,
              pairSum_single, add_zero]
  | (x, q) :: (y, r) :: rest, t, hchain => by
      -- split the glued chain at the second base point `y`
      have hsplit_list : glue ((x, q) :: (y, r) :: rest) t =
          (x :: q) ++ y :: (r ++ glue rest t) := rfl
      have hchain' := hchain
      rw [hsplit_list, List.isChain_split] at hchain'
      have hseg_chain : List.IsChain (· ≤ ·) ((x :: q) ++ [y]) := hchain'.1
      have htail_chain : List.IsChain (· ≤ ·)
          (glue ((y, r) :: rest) t) := hchain'.2
      have ih := refine_bound ω Ξ θ hθ hδ ((y, r) :: rest) t htail_chain
      -- the segment estimate
      have hseg : ‖pairSum Ξ (x :: (q ++ [y])) - Ξ x y‖ₑ ≤
          (∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ) * ω x y ^ θ := by
        have hne : (x :: (q ++ [y])) ≠ [] := by simp
        have hlen : (x :: (q ++ [y])).length = q.length + 2 := by simp
        have hb := maximal_inequality_tsum ω Ξ θ hθ hδ q.length
          (x :: (q ++ [y])) hne hlen (by simpa using hseg_chain)
        have hhead : (x :: (q ++ [y])).head hne = x := rfl
        have hlast : (x :: (q ++ [y])).getLast hne = y := by
          have h1 : (x :: (q ++ [y])).getLast? = some y := by
            rw [show x :: (q ++ [y]) = (x :: q) ++ [y] from rfl]
            exact List.getLast?_concat
          have h2 := List.getLast?_eq_getLast_of_ne_nil
            (l := x :: (q ++ [y])) hne
          rw [h1] at h2
          exact (Option.some.inj h2).symm
        rw [hhead, hlast] at hb
        exact hb
      -- assemble
      have hS : pairSum Ξ (glue ((x, q) :: (y, r) :: rest) t) =
          pairSum Ξ (x :: (q ++ [y])) +
            pairSum Ξ (glue ((y, r) :: rest) t) := by
        rw [hsplit_list, pairSum_append Ξ (x :: q) y (r ++ glue rest t)]
        rfl
      have hB : pairSum Ξ (basePoints ((x, q) :: (y, r) :: rest) t) =
          Ξ x y + pairSum Ξ (basePoints ((y, r) :: rest) t) := rfl
      have hsplit_diff : pairSum Ξ (glue ((x, q) :: (y, r) :: rest) t) -
          pairSum Ξ (basePoints ((x, q) :: (y, r) :: rest) t) =
          (pairSum Ξ (x :: (q ++ [y])) - Ξ x y) +
            (pairSum Ξ (glue ((y, r) :: rest) t) -
              pairSum Ξ (basePoints ((y, r) :: rest) t)) := by
        rw [hS, hB]
        abel
      rw [hsplit_diff]
      have hBθ : pairSum (fun a b => ω a b ^ θ)
          (basePoints ((x, q) :: (y, r) :: rest) t) =
          ω x y ^ θ + pairSum (fun a b => ω a b ^ θ)
            (basePoints ((y, r) :: rest) t) := rfl
      rw [hBθ, mul_add]
      exact le_trans (enorm_add_le'' _ _) (add_le_add hseg ih)

/-- **The θ-mass of a fine partition is small**: if every interval of a
chained partition has control at most `ε`, its `θ`-mass is bounded by
`ε^{θ-1} ω(s,t)`. -/
theorem pairSum_rpow_le_of_fine (ω : Control T) {θ : ℝ}
    (hθ1 : (0 : ℝ) ≤ θ - 1) {ε : ENNReal} :
    ∀ (x : T) (q : List T) (t : T),
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (x :: (q ++ [t])) →
      pairSum (fun a b => ω a b ^ θ) (x :: (q ++ [t])) ≤
        ε ^ (θ - 1) * ω x t := by
  have hpow : ∀ {a b : T}, ω a b ≤ ε →
      ω a b ^ θ ≤ ε ^ (θ - 1) * ω a b := by
    intro a b hab
    have h1 : ω a b ^ (θ - 1) * ω a b ^ (1 : ℝ) = ω a b ^ θ := by
      rw [← ENNReal.rpow_add_of_nonneg (θ - 1) 1 hθ1 (by norm_num)]
      norm_num
    calc ω a b ^ θ = ω a b ^ (θ - 1) * ω a b ^ (1 : ℝ) := h1.symm
      _ = ω a b ^ (θ - 1) * ω a b := by rw [ENNReal.rpow_one]
      _ ≤ ε ^ (θ - 1) * ω a b :=
          mul_le_mul_left (ENNReal.rpow_le_rpow hab hθ1) _
  intro x q
  induction q generalizing x with
  | nil =>
      intro t h
      have h1 := List.isChain_pair.1 (by simpa using h)
      rw [show pairSum (fun a b => ω a b ^ θ) (x :: ([] ++ [t])) =
        ω x t ^ θ + 0 from rfl, add_zero]
      exact hpow h1.2
  | cons y q ih =>
      intro t h
      rw [List.cons_append, List.isChain_cons_cons] at h
      have hxy := h.1
      have hrest := ih y t h.2
      have hplain : List.IsChain (· ≤ ·) (y :: (q ++ [t])) :=
        h.2.imp fun _ _ hab => hab.1
      have hyt : y ≤ t := by
        have hL := isChain_head_le_getLast y (q ++ [t]) hplain
        have hlast : ((y :: (q ++ [t]))).getLast (by simp) = t := by
          have h1 : (y :: (q ++ [t])).getLast? = some t := by
            rw [show y :: (q ++ [t]) = (y :: q) ++ [t] from rfl]
            exact List.getLast?_concat
          have h2 := List.getLast?_eq_getLast_of_ne_nil
            (l := y :: (q ++ [t])) (by simp)
          rw [h1] at h2
          exact (Option.some.inj h2).symm
        rw [hlast] at hL
        exact hL
      calc pairSum (fun a b => ω a b ^ θ) (x :: ((y :: q) ++ [t]))
          = ω x y ^ θ +
              pairSum (fun a b => ω a b ^ θ) (y :: (q ++ [t])) := rfl
        _ ≤ ε ^ (θ - 1) * ω x y + ε ^ (θ - 1) * ω y t :=
            add_le_add (hpow hxy.2) hrest
        _ = ε ^ (θ - 1) * (ω x y + ω y t) := by rw [mul_add]
        _ ≤ ε ^ (θ - 1) * ω x t :=
            mul_le_mul_right (ω.superadditive hxy.1 hyt) _

open scoped NNReal in
/-- **The sewing constant is finite for `θ > 1`**: the harmonic-power
series `Σ_j (2/(j+1))^θ` converges. -/
theorem sewingConst_lt_top {θ : ℝ} (hθ : 1 < θ) :
    (∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ) < ⊤ := by
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  -- rewrite the terms as coercions of nonnegative reals
  have hterm : ∀ j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ =
      (((2 / ((j : ℝ≥0) + 1)) ^ θ : ℝ≥0) : ENNReal) := by
    intro j
    rw [ENNReal.coe_rpow_of_nonneg _ hθ0]
    congr 1
    rw [ENNReal.coe_div (by exact_mod_cast Nat.succ_ne_zero j)]
    push_cast
    ring
  simp_rw [hterm]
  rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable]
  -- summability in ℝ
  rw [← NNReal.summable_coe]
  have hcoe : ∀ j : ℕ, (((2 / ((j : ℝ≥0) + 1)) ^ θ : ℝ≥0) : ℝ) =
      2 ^ θ * (((j : ℝ) + 1) ^ θ)⁻¹ := by
    intro j
    push_cast
    rw [Real.div_rpow (by norm_num) (by positivity), div_eq_mul_inv]
  simp_rw [hcoe]
  refine Summable.mul_left _ ?_
  have hsum : Summable (fun n : ℕ => (((n : ℝ)) ^ θ)⁻¹) :=
    Real.summable_nat_rpow_inv.2 hθ
  have := (summable_nat_add_iff 1).2 hsum
  simpa using this

/-- **Every chained partition admits a fine refinement**: given fine
partitions of the control, each interval can be interpolated by a chain
with control increments at most `ε`, assembling into a glued refinement of
the whole partition. -/
theorem exists_fine_refinement (ω : Control T)
    (hfine : HasFinePartitions ω) {ε : ENNReal} (hε : 0 < ε) :
    ∀ (q : List T) (x t : T), List.IsChain (· ≤ ·) (x :: (q ++ [t])) →
      ∃ ps : List (T × List T),
        basePoints ps t = x :: (q ++ [t]) ∧
        List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε) (glue ps t)
  | [], x, t, hchain => by
      have hxt : x ≤ t := List.isChain_pair.1 (by simpa using hchain)
      obtain ⟨r, hr⟩ := hfine hxt ε hε
      exact ⟨[(x, r)], rfl, by simpa using hr⟩
  | y :: q, x, t, hchain => by
      rw [List.cons_append, List.isChain_cons_cons] at hchain
      have hxy := hchain.1
      obtain ⟨ps', hbase', hglue'⟩ :=
        exists_fine_refinement ω hfine hε q y t hchain.2
      obtain ⟨r, hr⟩ := hfine hxy ε hε
      refine ⟨(x, r) :: ps', ?_, ?_⟩
      · rw [basePoints_cons, hbase']
        rfl
      · -- the glued chain splits at the head of `ps'`
        have hps'_ne : ps' ≠ [] := by
          intro h0
          rw [h0] at hbase'
          simp at hbase'
        obtain ⟨⟨z, rz⟩, ps'', rfl⟩ := List.exists_cons_of_ne_nil hps'_ne
        have hz : z = y := by
          have h1 : z :: basePoints ps'' t = y :: (q ++ [t]) := hbase'
          exact (List.cons_eq_cons.1 h1).1
        rw [← hz] at hr
        rw [glue_cons]
        rw [show glue ((z, rz) :: ps'') t = z :: (rz ++ glue ps'' t)
          from rfl]
        rw [show x :: (r ++ (z :: (rz ++ glue ps'' t))) =
          (x :: r) ++ z :: (rz ++ glue ps'' t) from rfl]
        rw [List.isChain_split]
        constructor
        · simpa using hr
        · simpa using hglue'

omit [Preorder T] in
/-- Every glued partition ends at its endpoint. -/
theorem glue_eq_concat : ∀ (ps : List (T × List T)) (t : T),
    ∃ mid : List T, glue ps t = mid ++ [t]
  | [], t => ⟨[], rfl⟩
  | (x, q) :: rest, t => by
      obtain ⟨mid', hmid'⟩ := glue_eq_concat rest t
      exact ⟨x :: (q ++ mid'), by simp [hmid']⟩

/-- **The combined refinement step**: a partition that is fine at level `ε`
admits a refinement fine at any level `ε' > 0` whose Riemann sum moves by
at most `K ε^{θ-1} ω(x,t)`. -/
theorem refine_step {E : Type v} [SeminormedAddCommGroup E]
    (ω : Control T) (Ξ : T → T → E) {θ : ℝ} (hθ1 : (0 : ℝ) ≤ θ - 1)
    (hθ0 : (0 : ℝ) ≤ θ)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ)
    (hfine : HasFinePartitions ω) {ε ε' : ENNReal} (hε' : 0 < ε')
    (q : List T) (x t : T)
    (hchain : List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε)
      (x :: (q ++ [t]))) :
    ∃ q' : List T,
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε') (x :: (q' ++ [t])) ∧
      ‖pairSum Ξ (x :: (q' ++ [t])) - pairSum Ξ (x :: (q ++ [t]))‖ₑ ≤
        (∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ) *
          (ε ^ (θ - 1) * ω x t) := by
  have hplain : List.IsChain (· ≤ ·) (x :: (q ++ [t])) :=
    hchain.imp fun _ _ h => h.1
  obtain ⟨ps, hbase, hglue⟩ :=
    exists_fine_refinement ω hfine hε' q x t hplain
  -- extract the shape of the refined partition
  have hps_ne : ps ≠ [] := by
    intro h0
    rw [h0] at hbase
    simp at hbase
  obtain ⟨⟨z, rz⟩, ps'', rfl⟩ := List.exists_cons_of_ne_nil hps_ne
  have hz : z = x := by
    have h1 : z :: basePoints ps'' t = x :: (q ++ [t]) := hbase
    exact (List.cons_eq_cons.1 h1).1
  obtain ⟨mid'', hmid''⟩ := glue_eq_concat ps'' t
  have hshape : glue ((z, rz) :: ps'') t =
      x :: ((rz ++ mid'') ++ [t]) := by
    rw [glue_cons, hmid'', hz]
    simp
  refine ⟨rz ++ mid'', ?_, ?_⟩
  · rw [← hshape]
    exact hglue
  · rw [← hshape, ← hbase]
    have hplain_glue : List.IsChain (· ≤ ·) (glue ((z, rz) :: ps'') t) :=
      hglue.imp fun _ _ h => h.1
    refine le_trans (refine_bound ω Ξ θ hθ0 hδ ((z, rz) :: ps'') t
      hplain_glue) ?_
    refine mul_le_mul_right ?_ _
    rw [hbase]
    exact pairSum_rpow_le_of_fine ω hθ1 x q t hchain

section Existence

variable {E : Type v} [NormedAddCommGroup E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem enorm_toReal_eq (a : E) : ‖a‖ₑ.toReal = ‖a‖ := by
  simp [enorm]

set_option maxHeartbeats 1000000 in
/-- **The sewing lemma, existence** (Friz–Hairer, Lemma 4.2; Cass–Salvi,
arXiv:2404.06583): if the Chen defect of `Ξ` is controlled by `ω^θ` with
`θ > 1` and the control admits fine partitions, then over every interval
the Riemann sums along a refining sequence of partitions converge to a
limit `L` — the rough integral — with the sewing remainder bound
`‖L - Ξ s t‖ ≤ K ω(s,t)^θ`. -/
theorem sewing_exists (ω : Control T) (Ξ : T → T → E) {θ : ℝ}
    (hθ : 1 < θ)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ ω a c ^ θ)
    (hfine : HasFinePartitions ω) {s t : T} (hst : s ≤ t)
    (hω : ω s t ≠ ⊤) :
    ∃ (L : E) (Q : ℕ → List T),
      (∀ n, ∃ q : List T, Q n = s :: (q ++ [t]) ∧
        List.IsChain (· ≤ ·) (Q n)) ∧
      Filter.Tendsto (fun n => pairSum Ξ (Q n)) Filter.atTop (nhds L) ∧
      ‖L - Ξ s t‖ₑ ≤
        (∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ) * ω s t ^ θ := by
  classical
  have hθ1 : (0 : ℝ) ≤ θ - 1 := by linarith
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  set K : ENNReal := ∑' j : ℕ, (2 / ((j : ENNReal) + 1)) ^ θ with hK
  have hKfin : K ≠ ⊤ := (sewingConst_lt_top hθ).ne
  set ε : ℕ → ENNReal := fun n => (ω s t + 1) * (2⁻¹ : ENNReal) ^ n
    with hε
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    rw [hε]
    refine ENNReal.mul_pos ?_ ?_
    · simp
    · exact pow_ne_zero n (by norm_num)
  -- the recursively refined partitions
  have hstep : ∀ (n : ℕ) (q : List T),
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε n) (s :: (q ++ [t])) →
      ∃ q' : List T,
        List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε (n + 1))
          (s :: (q' ++ [t])) ∧
        ‖pairSum Ξ (s :: (q' ++ [t])) - pairSum Ξ (s :: (q ++ [t]))‖ₑ ≤
          K * (ε n ^ (θ - 1) * ω s t) := fun n q hq =>
    refine_step ω Ξ hθ1 hθ0 hδ hfine (hεpos (n + 1)) q s t hq
  have hbase : List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε 0)
      (s :: (([] : List T) ++ [t])) := by
    refine List.isChain_pair.2 ⟨hst, ?_⟩
    rw [hε]
    simp only [pow_zero, mul_one]
    exact le_self_add
  let D : ∀ n : ℕ, {q : List T //
      List.IsChain (fun a b => a ≤ b ∧ ω a b ≤ ε n) (s :: (q ++ [t]))} :=
    fun n => Nat.rec ⟨[], hbase⟩
      (fun n d => ⟨(hstep n d.1 d.2).choose,
        (hstep n d.1 d.2).choose_spec.1⟩) n
  set Q : ℕ → List T := fun n => s :: ((D n).1 ++ [t]) with hQ
  have hDsucc : ∀ n, (D (n + 1)).1 = (hstep n (D n).1 (D n).2).choose :=
    fun n => rfl
  have hcost : ∀ n, ‖pairSum Ξ (Q (n + 1)) - pairSum Ξ (Q n)‖ₑ ≤
      K * (ε n ^ (θ - 1) * ω s t) := by
    intro n
    show ‖pairSum Ξ (s :: ((D (n + 1)).1 ++ [t])) -
      pairSum Ξ (s :: ((D n).1 ++ [t]))‖ₑ ≤ _
    rw [hDsucc n]
    exact (hstep n (D n).1 (D n).2).choose_spec.2
  -- geometric decay of the costs, in real form
  set B : ENNReal := K * ((ω s t + 1) ^ (θ - 1) * ω s t) with hB
  have hBfin : B ≠ ⊤ := by
    rw [hB]
    refine ENNReal.mul_ne_top hKfin (ENNReal.mul_ne_top ?_ hω)
    exact ENNReal.rpow_ne_top_of_nonneg hθ1 (by
      exact ENNReal.add_ne_top.2 ⟨hω, ENNReal.one_ne_top⟩)
  set x : ENNReal := (2⁻¹ : ENNReal) ^ (θ - 1) with hx
  have hxfin : x ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hθ1 (by norm_num)
  have hcost' : ∀ n, ‖pairSum Ξ (Q (n + 1)) - pairSum Ξ (Q n)‖ₑ ≤
      B * x ^ n := by
    intro n
    refine le_trans (hcost n) (le_of_eq ?_)
    rw [hB, hx, hε]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ1]
    rw [← ENNReal.rpow_natCast (2⁻¹ : ENNReal) n,
      ← ENNReal.rpow_mul, mul_comm (n : ℝ) (θ - 1),
      ENNReal.rpow_mul, ENNReal.rpow_natCast]
    ring
  have hdist : ∀ n, dist (pairSum Ξ (Q n)) (pairSum Ξ (Q (n + 1))) ≤
      B.toReal * x.toReal ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, ← enorm_toReal_eq]
    calc (‖pairSum Ξ (Q (n + 1)) - pairSum Ξ (Q n)‖ₑ).toReal
        ≤ (B * x ^ n).toReal := by
          refine ENNReal.toReal_mono ?_ (hcost' n)
          exact ENNReal.mul_ne_top hBfin (ENNReal.pow_ne_top hxfin)
      _ = B.toReal * x.toReal ^ n := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
  have hxlt : x.toReal < 1 := by
    have h1 : x < 1 := by
      rw [hx]
      refine ENNReal.rpow_lt_one ?_ (by linarith)
      simp [ENNReal.inv_lt_one]
    calc x.toReal < (1 : ENNReal).toReal := by
          exact ENNReal.toReal_strict_mono ENNReal.one_ne_top h1
      _ = 1 := by simp
  have hcauchy : CauchySeq (fun n => pairSum Ξ (Q n)) :=
    cauchySeq_of_le_geometric x.toReal B.toReal hxlt hdist
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- each partition satisfies the maximal inequality
  have hmax : ∀ n, ‖pairSum Ξ (Q n) - Ξ s t‖ₑ ≤ K * ω s t ^ θ := by
    intro n
    have hne : Q n ≠ [] := by rw [hQ]; simp
    have hlen : (Q n).length = (D n).1.length + 2 := by rw [hQ]; simp
    have hchain : List.IsChain (· ≤ ·) (Q n) := by
      rw [hQ]
      exact (D n).2.imp fun _ _ h => h.1
    have hb := maximal_inequality_tsum ω Ξ θ hθ0 hδ (D n).1.length
      (Q n) hne hlen hchain
    have hhead : (Q n).head hne = s := rfl
    have hlast : (Q n).getLast hne = t := by
      have h1 : (Q n).getLast? = some t := by
        show (s :: ((D n).1 ++ [t])).getLast? = some t
        rw [show s :: ((D n).1 ++ [t]) = (s :: (D n).1) ++ [t] from rfl]
        exact List.getLast?_concat
      have h2 := List.getLast?_eq_getLast_of_ne_nil (l := Q n) hne
      rw [h1] at h2
      exact (Option.some.inj h2).symm
    rw [hhead, hlast] at hb
    exact hb
  refine ⟨L, Q, fun n => ⟨(D n).1, rfl, by
    exact (D n).2.imp fun _ _ h => h.1⟩, hL, ?_⟩
  -- pass the maximal bound to the limit
  by_cases hKω : K * ω s t ^ θ = ⊤
  · rw [hKω]
    exact le_top
  · have hdistL : dist L (Ξ s t) ≤ (K * ω s t ^ θ).toReal := by
      refine le_of_tendsto (hL.dist tendsto_const_nhds) ?_
      refine Filter.Eventually.of_forall fun n => ?_
      rw [dist_eq_norm, ← enorm_toReal_eq]
      exact ENNReal.toReal_mono hKω (hmax n)
    have h1 : ‖L - Ξ s t‖ₑ = ENNReal.ofReal (dist L (Ξ s t)) := by
      rw [dist_eq_norm, ← enorm_toReal_eq, ENNReal.ofReal_toReal]
      simp [enorm]
    rw [h1]
    calc ENNReal.ofReal (dist L (Ξ s t))
        ≤ ENNReal.ofReal ((K * ω s t ^ θ).toReal) :=
          ENNReal.ofReal_le_ofReal hdistL
      _ = K * ω s t ^ θ := ENNReal.ofReal_toReal hKω

end Existence

end Refinement

end Sewing

end RoughPaths
