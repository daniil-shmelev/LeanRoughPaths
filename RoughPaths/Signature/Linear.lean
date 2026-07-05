/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Sum
import RoughPaths.Signature.Basic

/-!
# The signature of a linear path

The signature of the linear segment with increment `v : α → R` has word
coefficients `(∏ v(wᵢ)) / |w|!` — the tensor exponential of the increment.
It is group-like: the shuffle identity reduces to the counting identity
`|shuffle u w| = (|u|+|w|).choose |u|` together with the factorial
identity `choose · |u|! · |w|! = (|u|+|w|)!`.
-/

namespace RoughPaths

open HopfAlgebras

universe u v

variable {α : Type u} {R : Type v}

/-- Summing a function over `List.range` is a `Finset.range` sum. -/
theorem list_range_map_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → M) :
    ((List.range n).map F).sum = ∑ k ∈ Finset.range n, F k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]

/-- `1/(k!·(n-k)!)` regrouped through the binomial coefficient. -/
theorem div_factorial_mul_div_factorial [Field R] [CharZero R] {n k : ℕ}
    (hk : k ≤ n) (x y : R) :
    x / (k.factorial : R) * (y / ((n - k).factorial : R)) =
      x * y * ((n.choose k : R) / (n.factorial : R)) := by
  have hch : ((n.choose k : R)) * (k.factorial : R) * ((n - k).factorial : R) =
      (n.factorial : R) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have h1 : ((k.factorial : ℕ) : R) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h2 : (((n - k).factorial : ℕ) : R) ≠ 0 := by
    exact_mod_cast (n - k).factorial_ne_zero
  have h3 : ((n.factorial : ℕ) : R) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [div_mul_div_comm, ← mul_div_assoc,
    div_eq_div_iff (mul_ne_zero h1 h2) h3]
  linear_combination (-(x * y)) * hch

/-- The exponential binomial sum: `Σₖ aᵏ·b^{n-k}·C(n,k)/n! = (a+b)ⁿ/n!`. -/
theorem sum_pow_div_factorial [Field R] (a b : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      a ^ k * b ^ (n - k) * ((n.choose k : R) / (n.factorial : R)) =
      (a + b) ^ n / (n.factorial : R) := by
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div, ← add_pow]

namespace Word

/-- The prefix lengths of the splits of `w` are `0, 1, …, |w|` in order. -/
theorem splits_map_length_fst :
    ∀ w : List α,
      (Word.splits w).map (fun p => p.1.length) = List.range (w.length + 1)
  | [] => rfl
  | x :: w => by
      rw [Word.splits_cons, List.map_cons, List.map_map, List.length_cons,
        List.range_succ_eq_map, ← splits_map_length_fst w, List.map_map]
      rfl

/-- A sum over the splits of `w` that depends only on the prefix length is
a sum over `Finset.range (|w| + 1)`. -/
theorem sum_splits_length_fst {M : Type*} [AddCommMonoid M] (w : List α)
    (F : ℕ → M) :
    ((Word.splits w).map fun p => F p.1.length).sum =
      ∑ k ∈ Finset.range (w.length + 1), F k := by
  rw [show ((Word.splits w).map fun p => F p.1.length) =
      ((Word.splits w).map fun p => p.1.length).map F from
    List.map_map.symm, splits_map_length_fst, list_range_map_sum]

end Word

namespace Word

/-- The signature of a linear path with increment `v`: the tensor
exponential `w ↦ (∏ᵢ v(wᵢ)) / |w|!`. -/
def linearSignature [Field R] (v : α → R) :
    (List α → R) :=
  fun w => (w.map v).prod / Nat.factorial w.length

@[simp]
theorem linearSignature_coeff [Field R] (v : α → R) (w : List α) :
    coeff (linearSignature v) w = (w.map v).prod / Nat.factorial w.length :=
  rfl

@[simp]
theorem linearSignature_nil [Field R] (v : α → R) :
    coeff (linearSignature v) [] = 1 := by
  simp [linearSignature]

/-- The shuffle sum of a linear signature collapses to a binomial multiple:
every shuffle of `u` and `w` is a permutation of `u ++ w`, so all summands
agree. -/
theorem shuffleCoeff_linearSignature [Field R] (v : α → R) (u w : List α) :
    shuffleCoeff (linearSignature v) u w =
      ((u.length + w.length).choose u.length : R) *
        (((u ++ w).map v).prod / (Nat.factorial (u.length + w.length) : R)) := by
  rw [shuffleCoeff]
  have hmap : (Word.shuffle u w).map (linearSignature v) =
      (Word.shuffle u w).map (fun _ =>
        ((u ++ w).map v).prod / (Nat.factorial (u.length + w.length) : R)) := by
    apply List.map_congr_left
    intro x hx
    have hperm := Word.perm_append_of_mem_shuffle hx
    rw [linearSignature]
    rw [List.Perm.prod_eq (hperm.map v), hperm.length_eq]
    simp
  rw [hmap, List.map_const', List.sum_replicate, Word.length_shuffle,
    nsmul_eq_mul]

/-- **The linear signature is group-like** (its coefficients satisfy the
shuffle identity). -/
theorem isGroupLike_linearSignature [Field R] [CharZero R] (v : α → R) :
    IsGroupLike (linearSignature v) := by
  refine ⟨linearSignature_nil v, fun u w => ?_⟩
  rw [shuffleCoeff_linearSignature, linearSignature_coeff,
    linearSignature_coeff]
  have hu : (Nat.factorial u.length : R) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero u.length
  have hw : (Nat.factorial w.length : R) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero w.length
  have huw : (Nat.factorial (u.length + w.length) : R) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (u.length + w.length)
  have hnat := Nat.choose_mul_factorial_mul_factorial
    (Nat.le_add_right u.length w.length)
  rw [Nat.add_sub_cancel_left] at hnat
  have hchoose : ((u.length + w.length).choose u.length : R) *
      (Nat.factorial u.length : R) * (Nat.factorial w.length : R) = (Nat.factorial (u.length + w.length) : R) := by
    exact_mod_cast hnat
  have hprod : ((u ++ w).map v).prod = (u.map v).prod * (w.map v).prod := by
    rw [List.map_append, List.prod_append]
  rw [div_mul_div_comm, hprod, mul_div_assoc']
  rw [div_eq_div_iff (mul_ne_zero hu hw) huw]
  linear_combination (-((u.map v).prod * (w.map v).prod)) * hchoose

/-! ### The semigroup law and inverses -/

private theorem prod_map_smul [Field R] (v : α → R) (c : R) :
    ∀ l : List α, (l.map (c • v)).prod = c ^ l.length * (l.map v).prod
  | [] => by simp
  | x :: l => by
      rw [List.map_cons, List.prod_cons, prod_map_smul v c l, List.map_cons,
        List.prod_cons, List.length_cons, pow_succ, Pi.smul_apply,
        smul_eq_mul]
      ring

@[simp]
theorem linearSignature_zero [Field R] :
    linearSignature (0 : α → R) = unit α R := by
  funext w
  cases w with
  | nil => simp [linearSignature, unit]
  | cons x w => simp [linearSignature, unit]

@[simp]
theorem linearSignature_singleton [Field R] (v : α → R) (x : α) :
    linearSignature v [x] = v x := by
  simp [linearSignature]

@[simp]
theorem linearSignature_pair [Field R] (v : α → R) (x y : α) :
    linearSignature v [x, y] = v x * v y / 2 := by
  norm_num [linearSignature, Nat.factorial]

/-- **Semigroup law for linear signatures**: collinear segments concatenate
additively, `S(a·v) ⊗ S(b·v) = S((a+b)·v)` — the binomial identity for the
tensor exponential. -/
theorem tensorProduct_linearSignature_smul [Field R] [CharZero R]
    (v : α → R) (a b : R) :
    tensorProduct (linearSignature (a • v)) (linearSignature (b • v)) =
      linearSignature ((a + b) • v) := by
  funext w
  have hterm : ∀ p ∈ Word.splits w,
      coeff (linearSignature (a • v)) p.1 *
          coeff (linearSignature (b • v)) p.2 =
        (w.map v).prod * (a ^ p.1.length * b ^ (w.length - p.1.length) *
          ((w.length.choose p.1.length : R) / (w.length.factorial : R))) := by
    intro p hp
    have happ := Word.mem_splits_append hp
    have hlen : p.1.length + p.2.length = w.length := by
      rw [← happ, List.length_append]
    have hprod : (p.1.map v).prod * (p.2.map v).prod = (w.map v).prod := by
      rw [← happ, List.map_append, List.prod_append]
    show (p.1.map (a • v)).prod / (p.1.length.factorial : R) *
        ((p.2.map (b • v)).prod / (p.2.length.factorial : R)) = _
    rw [prod_map_smul, prod_map_smul,
      show p.2.length = w.length - p.1.length from by omega,
      div_factorial_mul_div_factorial (n := w.length) (k := p.1.length)
        (by omega)]
    linear_combination (a ^ p.1.length * b ^ (w.length - p.1.length) *
      ((w.length.choose p.1.length : R) / (w.length.factorial : R))) * hprod
  refine Eq.trans (congrArg List.sum (List.map_congr_left hterm)) ?_
  refine Eq.trans (Word.sum_splits_length_fst w fun k =>
    (w.map v).prod * (a ^ k * b ^ (w.length - k) *
      ((w.length.choose k : R) / (w.length.factorial : R)))) ?_
  calc ∑ k ∈ Finset.range (w.length + 1),
        (w.map v).prod * (a ^ k * b ^ (w.length - k) *
          ((w.length.choose k : R) / (w.length.factorial : R)))
      = (w.map v).prod * ∑ k ∈ Finset.range (w.length + 1),
          a ^ k * b ^ (w.length - k) *
            ((w.length.choose k : R) / (w.length.factorial : R)) := by
        rw [Finset.mul_sum]
    _ = (w.map v).prod * ((a + b) ^ w.length / (w.length.factorial : R)) := by
        rw [sum_pow_div_factorial]
    _ = linearSignature ((a + b) • v) w := by
        show _ = (w.map ((a + b) • v)).prod / (w.length.factorial : R)
        rw [prod_map_smul]
        ring

/-- **Inverse of a linear signature**: the reversed segment. -/
theorem tensorProduct_linearSignature_neg [Field R] [CharZero R]
    (v : α → R) :
    tensorProduct (linearSignature v) (linearSignature (-v)) = unit α R := by
  have h := tensorProduct_linearSignature_smul v 1 (-1)
  have e1 : (1 : R) • v = v := funext fun x => one_mul (v x)
  have e2 : (-1 : R) • v = -v := funext fun x => neg_one_mul (v x)
  have e3 : ((1 : R) + (-1 : R)) • v = (0 : α → R) := funext fun x => by
    show ((1 : R) + (-1 : R)) * v x = 0
    rw [add_neg_cancel, zero_mul]
  rwa [e1, e2, e3, linearSignature_zero] at h

theorem tensorProduct_linearSignature_neg' [Field R] [CharZero R]
    (v : α → R) :
    tensorProduct (linearSignature (-v)) (linearSignature v) = unit α R := by
  have h := tensorProduct_linearSignature_smul v (-1) 1
  have e1 : (1 : R) • v = v := funext fun x => one_mul (v x)
  have e2 : (-1 : R) • v = -v := funext fun x => neg_one_mul (v x)
  have e3 : ((-1 : R) + (1 : R)) • v = (0 : α → R) := funext fun x => by
    show ((-1 : R) + (1 : R)) * v x = 0
    rw [neg_add_cancel, zero_mul]
  rwa [e1, e2, e3, linearSignature_zero] at h

end Word

end RoughPaths
