/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Combinatorial.Basic
import HopfAlgebras.Words.SplitShuffle
import HopfAlgebras.Words.Antipode

/-!
# The word shuffle Hopf algebra

The combinatorial Hopf algebra of words over an alphabet `α`: shuffle
product, deconcatenation coproduct, and the signed-reversal antipode
`S(w) = (-1)^{|w|}·wʳ`. Its characters with values in `R` are exactly
the group-like signature series — the signatures of rough path theory
(see `RoughPaths.Signature.Character` for the identification) — and the
abstract character-group theory of `HopfAlgebras.Combinatorial.Basic`
yields their monoid and group structure.

All axioms are discharged from the word-combinatorics keystones already
in the library: `shuffle_splits_perm` (bialgebra compatibility),
`leftSplits3_perm_rightSplits3` (coassociativity),
`antipode_convolution` and
`shuffle_reverse_perm` (the antipode identities).
-/

namespace HopfAlgebras

universe u v

variable {α : Type u}

namespace Word

private theorem sum_flatMap'' {β γ : Type*} {R : Type*}
    [AddCommMonoid R] (l : List β) (f : β → List γ) (g : γ → R) :
    ((l.flatMap f).map g).sum =
      (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
        List.map_cons, List.sum_cons]

private theorem counit_left_aux {R : Type v} [CommSemiring R]
    (f : List α → R) :
    ∀ x : List α,
      ((Word.splits x).map fun p =>
        (if p.1.isEmpty then (1 : R) else 0) * f p.2).sum = f x
  | [] => by
      rw [Word.splits_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      show (1 : R) * f [] = f []
      rw [one_mul]
  | c :: t => by
      rw [Word.splits_cons, List.map_cons, List.sum_cons, List.map_map]
      have hz : ((Word.splits t).map
          ((fun p => (if p.1.isEmpty then (1 : R) else 0) *
            f p.2) ∘ fun p => (c :: p.1, p.2))).sum = 0 := by
        refine List.sum_eq_zero fun r hr => ?_
        obtain ⟨p, -, rfl⟩ := List.mem_map.mp hr
        show (if (c :: p.1).isEmpty then (1 : R) else 0) * f p.2 = 0
        rw [show ((c :: p.1).isEmpty) = false from rfl]
        show (0 : R) * f p.2 = 0
        rw [zero_mul]
      rw [hz, add_zero]
      show (1 : R) * f (c :: t) = f (c :: t)
      rw [one_mul]

private theorem counit_right_aux {R : Type v} [CommSemiring R]
    (f : List α → R) :
    ∀ x : List α,
      ((Word.splits x).map fun p =>
        f p.1 * (if p.2.isEmpty then (1 : R) else 0)).sum = f x
  | [] => by
      rw [Word.splits_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      show f [] * (1 : R) = f []
      rw [mul_one]
  | c :: t => by
      rw [Word.splits_cons, List.map_cons, List.sum_cons, List.map_map]
      have htail : ((Word.splits t).map
          ((fun p => f p.1 *
            (if p.2.isEmpty then (1 : R) else 0)) ∘
              fun p => (c :: p.1, p.2))).sum =
          ((Word.splits t).map fun p => f (c :: p.1) *
            (if p.2.isEmpty then (1 : R) else 0)).sum := rfl
      rw [htail, counit_right_aux (fun w => f (c :: w)) t]
      show f [] * (if (c :: t).isEmpty then (1 : R) else 0) +
        f (c :: t) = f (c :: t)
      rw [show ((c :: t).isEmpty) = false from rfl]
      show f [] * (0 : R) + f (c :: t) = f (c :: t)
      rw [mul_zero, zero_add]

end Word

namespace Word

/-- The sign of the shuffle antipode as a Boolean. -/
theorem sign_eq (n : ℕ) {R : Type v} [CommRing R] :
    (if (decide (n % 2 = 0) : Bool) then (1 : R) else -1) =
      (-1) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [if_pos (decide_eq_true (Nat.even_iff.mp h)), h.neg_one_pow]
  · rw [if_neg (by simp [Nat.odd_iff.mp h]), h.neg_one_pow]

end Word

/-- **The word shuffle Hopf algebra**: shuffle product, deconcatenation
coproduct, signed-reversal antipode. Its characters are the signatures. -/
noncomputable def wordHopf (α : Type u) :
    CombHopf.{u, v} (List α) where
  mul := Word.shuffle
  one := []
  coprod := Word.splits
  isOne := List.isEmpty
  isOne_iff := fun x => by simp
  antipode w := [(decide (w.length % 2 = 0), w.reverse)]
  mul_one_expand := Word.shuffle_nil_right
  one_mul_expand := Word.shuffle_nil_left
  coprod_one := rfl
  antipode_one := rfl
  coassoc := by
    intro R _ f g h x
    have hpair := ((Word.leftSplits3_perm_rightSplits3 x).map
      fun r => f r.1 * g r.2.1 * h r.2.2).sum_eq
    have hL : ((Word.leftSplits3 x).map
        fun r => f r.1 * g r.2.1 * h r.2.2).sum =
        ((Word.splits x).map fun p =>
          (((Word.splits p.1).map fun q =>
            ((q.1, q.2, p.2) : Word.TripleSplits α)).map
              fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum :=
      Word.sum_flatMap'' _ _ _
    have hR : ((Word.rightSplits3 x).map
        fun r => f r.1 * g r.2.1 * h r.2.2).sum =
        ((Word.splits x).map fun p =>
          (((Word.splits p.2).map fun q =>
            ((p.1, q.1, q.2) : Word.TripleSplits α)).map
              fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum :=
      Word.sum_flatMap'' _ _ _
    have hA : ((Word.splits x).map fun p =>
        ((Word.splits p.1).map fun q => f q.1 * g q.2).sum * h p.2).sum =
        ((Word.splits x).map fun p =>
          (((Word.splits p.1).map fun q =>
            ((q.1, q.2, p.2) : Word.TripleSplits α)).map
              fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum := by
      refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
      rw [← List.sum_map_mul_right, List.map_map]
      exact congrArg List.sum (List.map_congr_left fun q _ => rfl)
    have hB : ((Word.splits x).map fun p =>
        (((Word.splits p.2).map fun q =>
          ((p.1, q.1, q.2) : Word.TripleSplits α)).map
            fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum =
        ((Word.splits x).map fun p =>
          f p.1 * ((Word.splits p.2).map fun q => g q.1 * h q.2).sum).sum := by
      refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
      rw [← List.sum_map_mul_left, List.map_map]
      exact congrArg List.sum
        (List.map_congr_left fun q _ => mul_assoc _ _ _)
    exact hA.trans ((hL.symm.trans hpair).trans (hR.trans hB))
  counit_left := fun f x => Word.counit_left_aux f x
  counit_right := fun f x => Word.counit_right_aux f x
  mul_count_one := by
    intro R _ x y
    by_cases hx : x = ([] : List α)
    · by_cases hy : y = ([] : List α)
      · subst hx; subst hy
        simp
      · subst hx
        rw [Word.shuffle_nil_left, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero]
        show (if y.isEmpty then (1 : R) else 0) =
          (1 : R) * (if y.isEmpty then (1 : R) else 0)
        rw [one_mul]
    · rw [if_neg (fun hb => hx (List.isEmpty_iff.mp hb)), zero_mul]
      refine List.sum_eq_zero fun r hr => ?_
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
      by_cases hzn : z = ([] : List α)
      · exact absurd (Word.eq_nil_of_mem_shuffle hz hzn).1 hx
      · rw [if_neg (fun hb => hzn (List.isEmpty_iff.mp hb))]
  bialg := by
    intro R _ φ ψ x y
    have hL : ((Word.shuffle x y).map fun z =>
        ((Word.splits z).map fun p => φ p.1 * ψ p.2).sum).sum =
        (((Word.shuffle x y).flatMap Word.splits).map
          fun p => φ p.1 * ψ p.2).sum :=
      (Word.sum_flatMap'' _ _ _).symm
    have hperm := ((Word.shuffle_splits_perm x y).map
      fun p => φ p.1 * ψ p.2).sum_eq
    rw [hL, hperm, Word.splitShufflePairs_def, Word.sum_flatMap'']
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    rw [Word.sum_flatMap'']
    refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
    rw [Word.sum_flatMap'', ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
    rw [List.map_map, ← List.sum_map_mul_left]
    rfl
  antipode_conv := by
    intro R _ f x hx
    obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil hx
    have hcongr : ∀ p ∈ Word.splits (c :: t),
        (([(decide (p.1.length % 2 = 0), p.1.reverse)] :
          List (Bool × List α)).map fun sa =>
            (if sa.1 then (1 : R) else -1) *
              ((Word.shuffle sa.2 p.2).map f).sum).sum =
        (-1 : R) ^ p.1.length *
          ((Word.shuffle p.1.reverse p.2).map f).sum := by
      intro p _
      rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Word.sign_eq]
    rw [List.map_congr_left hcongr]
    exact Word.antipode_convolution f c t
  antipode_char := by
    intro R _ φ hφ x y
    show (([(decide (x.length % 2 = 0), x.reverse)] :
        List (Bool × List α)).map fun sa =>
          (if sa.1 then (1 : R) else -1) * φ sa.2).sum *
      (([(decide (y.length % 2 = 0), y.reverse)] :
        List (Bool × List α)).map fun sa =>
          (if sa.1 then (1 : R) else -1) * φ sa.2).sum = _
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, Word.sign_eq,
      Word.sign_eq]
    have hcongr : ∀ z ∈ Word.shuffle x y,
        (([(decide (z.length % 2 = 0), z.reverse)] :
          List (Bool × List α)).map fun sa =>
            (if sa.1 then (1 : R) else -1) * φ sa.2).sum =
        (-1 : R) ^ (x.length + y.length) * φ z.reverse := by
      intro z hz
      rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Word.sign_eq,
        Word.length_of_mem_shuffle hz]
    rw [List.map_congr_left hcongr, List.sum_map_mul_left]
    have hrevsum : ((Word.shuffle x y).map fun z => φ z.reverse).sum =
        ((Word.shuffle x.reverse y.reverse).map φ).sum := by
      have h1 : ((Word.shuffle x y).map fun z => φ z.reverse) =
          ((Word.shuffle x y).map List.reverse).map φ := by
        rw [List.map_map]
        rfl
      rw [h1]
      exact ((Word.shuffle_reverse_perm x y).map φ).sum_eq
    rw [hrevsum, ← hφ x.reverse y.reverse, pow_add]
    ring

end HopfAlgebras
