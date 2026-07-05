/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Words.Shuffle

/-!
# Word-level antipode combinatorics

The combinatorial content of the shuffle antipode `S(w) = (-1)^{|w|}wʳ`:
shuffles of reversed words (`shuffle_reverse_perm`) and the telescoping
**antipode identity** (`antipode_convolution`) — the signed sum of the
shuffles of reversed prefixes with suffixes over all deconcatenation
splits of a nonempty word vanishes, i.e. `m ∘ (S ⊗ id) ∘ Δ = η ∘ ε`
paired against arbitrary coefficients. These feed both the abstract
word Hopf algebra (`HopfAlgebras.Combinatorial.Shuffle`) and the
signature antipode in `RoughPaths`.
-/

namespace HopfAlgebras

universe u v

variable {α : Type u} {R : Type v}

namespace Word

/-- **Reversal is a shuffle morphism**: the reversals of the shuffles of
`u` and `v` are the shuffles of `uʳ` and `vʳ`, up to permutation. -/
theorem shuffle_reverse_perm :
    ∀ u v : List α,
      ((shuffle u v).map List.reverse).Perm
        (shuffle u.reverse v.reverse)
  | [], v => by
      rw [shuffle_nil_left, List.reverse_nil, shuffle_nil_left,
        List.map_cons, List.map_nil]
  | a :: u, [] => by
      rw [shuffle_nil_right, List.reverse_nil, shuffle_nil_right,
        List.map_cons, List.map_nil]
  | a :: u, b :: v => by
      rw [shuffle_cons_cons, List.map_append, List.map_map, List.map_map,
        List.reverse_cons, List.reverse_cons]
      have h1 : (List.reverse ∘ (a :: ·) : List α → List α) =
          (fun w => w ++ [a]) ∘ List.reverse := by
        funext x
        simp [List.reverse_cons]
      have h2 : (List.reverse ∘ (b :: ·) : List α → List α) =
          (fun w => w ++ [b]) ∘ List.reverse := by
        funext x
        simp [List.reverse_cons]
      rw [h1, h2, ← List.map_map, ← List.map_map]
      refine (List.Perm.append
        ((shuffle_reverse_perm u (b :: v)).map fun w => w ++ [a])
        ((shuffle_reverse_perm (a :: u) v).map fun w => w ++ [b])).trans
        ?_
      rw [List.reverse_cons, List.reverse_cons]
      exact (shuffle_concat_concat_perm a b u.reverse v.reverse).symm
  termination_by u v => (u.length, v.length)
  decreasing_by
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self u.length)
  · exact Prod.Lex.right _ (Nat.lt_succ_self v.length)

private theorem sum_map_neg' {β : Type*} [Ring R] (l : List β)
    (g : β → R) :
    (l.map fun x => -g x).sum = -(l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons,
        neg_add]

/-- Deconcatenation-split recursion for split-indexed sums, stated with
the split components as separate arguments so that instantiation leaves
no pair projections behind. -/
private theorem splits_sum_cons {M : Type*} [AddCommMonoid M]
    (H : List α → List α → M) (c : α) (t : List α) :
    ((Word.splits (c :: t)).map fun pq => H pq.1 pq.2).sum =
      H [] (c :: t) +
        ((Word.splits t).map fun pq => H (c :: pq.1) pq.2).sum := by
  rw [Word.splits_cons, List.map_cons, List.sum_cons, List.map_map]
  rfl

/-- The telescoping step of the antipode identity: with a nonempty
accumulated prefix `u ++ [c]`, the signed sum of shuffles along the
splits of `v` collapses to the single boundary shuffle. -/
private theorem antipode_step [CommRing R] (f : List α → R) :
    ∀ (v u : List α) (c : α),
      ((Word.splits v).map fun pq => (-1 : R) ^ pq.1.length *
        ((Word.shuffle ((u ++ [c]) ++ pq.1).reverse pq.2).map f).sum).sum =
      ((Word.shuffle u.reverse v).map fun x => f (c :: x)).sum
  | [], u, c => by
      rw [Word.splits_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      show (-1 : R) ^ ([] : List α).length *
        ((Word.shuffle ((u ++ [c]) ++ ([] : List α)).reverse
          ([] : List α)).map f).sum = _
      rw [List.length_nil, pow_zero, one_mul, List.append_nil,
        Word.shuffle_nil_right, Word.shuffle_nil_right,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, List.reverse_append]
      simp
  | b :: v', u, c => by
      rw [splits_sum_cons (fun p q => (-1 : R) ^ p.length *
        ((Word.shuffle ((u ++ [c]) ++ p).reverse q).map f).sum) b v']
      have htail : ((Word.splits v').map fun pq =>
          (-1 : R) ^ (b :: pq.1).length *
            ((Word.shuffle ((u ++ [c]) ++ (b :: pq.1)).reverse
              pq.2).map f).sum).sum =
          -(((Word.shuffle (u ++ [c]).reverse v').map fun x =>
            f (b :: x)).sum) := by
        have hcongr : ∀ pq ∈ Word.splits v',
            (-1 : R) ^ (b :: pq.1).length *
              ((Word.shuffle ((u ++ [c]) ++ (b :: pq.1)).reverse
                pq.2).map f).sum =
            -((-1 : R) ^ pq.1.length *
              ((Word.shuffle (((u ++ [c]) ++ [b]) ++ pq.1).reverse
                pq.2).map f).sum) := by
          intro pq _
          have heq : (u ++ [c]) ++ (b :: pq.1) =
              ((u ++ [c]) ++ [b]) ++ pq.1 := by simp
          rw [List.length_cons, pow_succ, heq]
          ring
        rw [List.map_congr_left hcongr, sum_map_neg',
          antipode_step f v' (u ++ [c]) b]
      rw [htail]
      show (-1 : R) ^ ([] : List α).length *
          ((Word.shuffle ((u ++ [c]) ++ ([] : List α)).reverse
            (b :: v')).map f).sum +
          -(((Word.shuffle (u ++ [c]).reverse v').map fun x =>
            f (b :: x)).sum) = _
      have hrev2 : (u ++ [c]).reverse = c :: u.reverse := by simp
      rw [List.length_nil, pow_zero, one_mul, List.append_nil, hrev2,
        Word.shuffle_cons_cons, List.map_append, List.sum_append,
        List.map_map, List.map_map]
      show ((Word.shuffle u.reverse (b :: v')).map fun x =>
          f (c :: x)).sum +
        ((Word.shuffle (c :: u.reverse) v').map fun x =>
          f (b :: x)).sum +
        -(((Word.shuffle (c :: u.reverse) v').map fun x =>
          f (b :: x)).sum) = _
      ring

/-- **The antipode identity**: the signed sum of the shuffles of the
reversed prefixes with the suffixes, over all deconcatenation splits of
a nonempty word, vanishes — `m ∘ (S ⊗ id) ∘ Δ = η ∘ ε` for the shuffle
Hopf algebra, paired against arbitrary coefficients. -/
theorem antipode_convolution [CommRing R] (f : List α → R) (c : α)
    (t : List α) :
    ((Word.splits (c :: t)).map fun pq => (-1 : R) ^ pq.1.length *
      ((Word.shuffle pq.1.reverse pq.2).map f).sum).sum = 0 := by
  rw [splits_sum_cons (fun p q => (-1 : R) ^ p.length *
    ((Word.shuffle p.reverse q).map f).sum) c t]
  have hcongr : ∀ pq ∈ Word.splits t,
      (-1 : R) ^ (c :: pq.1).length *
        ((Word.shuffle (c :: pq.1).reverse pq.2).map f).sum =
      -((-1 : R) ^ pq.1.length *
        ((Word.shuffle ((([] : List α) ++ [c]) ++ pq.1).reverse
          pq.2).map f).sum) := by
    intro pq _
    have heq : (c :: pq.1) = (([] : List α) ++ [c]) ++ pq.1 := by simp
    rw [List.length_cons, pow_succ, heq]
    ring
  rw [List.map_congr_left hcongr, sum_map_neg',
    antipode_step f t [] c]
  show (-1 : R) ^ ([] : List α).length *
      ((Word.shuffle ([] : List α).reverse (c :: t)).map f).sum +
      -(((Word.shuffle ([] : List α).reverse t).map fun x =>
        f (c :: x)).sum) = 0
  rw [List.reverse_nil, Word.shuffle_nil_left, Word.shuffle_nil_left,
    List.length_nil, pow_zero, one_mul, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ring

end Word

end HopfAlgebras
