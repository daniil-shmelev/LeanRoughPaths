/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Signature.Piecewise
import HopfAlgebras.Words.Antipode

/-!
# The shuffle antipode and the group of signatures

The words over `α` form the **shuffle Hopf algebra**: shuffle product,
deconcatenation coproduct, and antipode `S(w) = (-1)^{|w|}·wʳ`. A
group-like signature series (`IsGroupLike`) is precisely a **character**
of this Hopf algebra, and the characters of a Hopf algebra form a group
under convolution — here, the tensor (concatenation) product — with
inverse given by precomposition with the antipode:

`a⁻¹(w) = (-1)^{|w|} · a(w.reverse)`   (`Word.antipode`).

This file proves the two facts that make this work and upgrades the
bundled `Signature α R` from a monoid to a **group**:

* `Word.shuffle_reverse_perm` — reversal is a shuffle-algebra morphism
  (`(u ⧢ v)ʳ ∼ uʳ ⧢ vʳ`), whence characters are closed under the
  antipode (`IsGroupLike.antipode`);
* `antipode_convolution` — the defining identity of the antipode,
  `Σ_{uv=w} (-1)^{|u|}·(uʳ ⧢ v) = 0` for `w ≠ []`, by a telescoping
  induction along the deconcatenation splits;
* `Signature.instGroup` — the group instance, over a commutative ring;
* `Signature.inv_ofPiecewiseLinear` — the group inverse of a
  piecewise-linear signature is the signature of the reversed path.

## References

* C. Reutenauer, *Free Lie Algebras*, §1.5
* P. Friz, M. Hairer, *A Course on Rough Paths*, Ch. 2
-/

namespace RoughPaths

open HopfAlgebras

universe u v

variable {α : Type u} {R : Type v}

namespace Word

/-! ### The antipode of a signature series -/

/-- The **shuffle antipode** of a signature series:
`a ↦ (w ↦ (-1)^{|w|}·a(wʳ))`. For a character (group-like series) this
is the convolution inverse — for the signature of a path, the signature
of the time-reversed path. -/
def antipode [Ring R] (a : (List α → R)) : (List α → R) :=
  fun w => (-1) ^ w.length * a w.reverse

@[simp]
theorem antipode_coeff [Ring R] (a : (List α → R)) (w : List α) :
    coeff (antipode a) w = (-1) ^ w.length * coeff a w.reverse :=
  rfl

/-- **Characters are closed under the antipode**: the antipode of a
group-like series is group-like. The content is that reversal is a
morphism of the (commutative) shuffle algebra. -/
theorem IsGroupLike.antipode [CommRing R] {a : (List α → R)}
    (ha : IsGroupLike a) : IsGroupLike (Word.antipode a) := by
  constructor
  · show (-1 : R) ^ ([] : List α).length * a [].reverse = 1
    have h0 : a [] = 1 := ha.coeff_nil
    rw [List.reverse_nil, h0]
    simp
  · intro u v
    show ((-1 : R) ^ u.length * a u.reverse) *
        ((-1) ^ v.length * a v.reverse) =
      shuffleCoeff (Word.antipode a) u v
    have hR : shuffleCoeff (Word.antipode a) u v =
        (-1) ^ (u.length + v.length) *
          ((Word.shuffle u v).map fun y => a y.reverse).sum := by
      rw [shuffleCoeff]
      have hcongr : ∀ y ∈ Word.shuffle u v,
          Word.antipode a y =
            (-1) ^ (u.length + v.length) * a y.reverse := by
        intro y hy
        show (-1 : R) ^ y.length * a y.reverse = _
        rw [Word.length_of_mem_shuffle hy]
      rw [List.map_congr_left hcongr, ← List.sum_map_mul_left]
    have hrevsum : ((Word.shuffle u v).map fun y => a y.reverse).sum =
        ((Word.shuffle u.reverse v.reverse).map a).sum := by
      have h1 : ((Word.shuffle u v).map fun y => a y.reverse) =
          ((Word.shuffle u v).map List.reverse).map a := by
        rw [List.map_map]
        rfl
      rw [h1]
      exact ((Word.shuffle_reverse_perm u v).map a).sum_eq
    rw [hR, hrevsum]
    show _ = (-1 : R) ^ (u.length + v.length) *
      shuffleCoeff a u.reverse v.reverse
    rw [← ha.shuffle u.reverse v.reverse]
    simp only [coeff_apply]
    rw [pow_add]
    ring

/-- **The antipode is a left convolution inverse** on characters:
`S(a) ⊗ a = 1` for group-like `a`. -/
theorem IsGroupLike.antipode_tensorProduct [CommRing R]
    {a : (List α → R)} (ha : IsGroupLike a) :
    Word.tensorProduct (Word.antipode a) a =
      Word.unit α R := by
  funext w
  cases w with
  | nil =>
      show ((Word.splits ([] : List α)).map fun p =>
        Word.antipode a p.1 * a p.2).sum = 1
      rw [Word.splits_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      show ((-1 : R) ^ ([] : List α).length * a [].reverse) * a [] = 1
      have h0 : a [] = 1 := ha.coeff_nil
      rw [List.reverse_nil, h0]
      simp
  | cons c t =>
      show ((Word.splits (c :: t)).map fun p =>
        Word.antipode a p.1 * a p.2).sum = 0
      have hterm : ∀ p ∈ Word.splits (c :: t),
          Word.antipode a p.1 * a p.2 =
            (-1 : R) ^ p.1.length *
              ((Word.shuffle p.1.reverse p.2).map a).sum := by
        intro p _
        show ((-1 : R) ^ p.1.length * a p.1.reverse) * a p.2 = _
        have hs : a p.1.reverse * a p.2 =
            ((Word.shuffle p.1.reverse p.2).map a).sum :=
          ha.shuffle p.1.reverse p.2
        rw [mul_assoc, hs]
      rw [List.map_congr_left hterm]
      exact Word.antipode_convolution a c t

end Word

namespace Signature

variable [CommRing R]

-- The group structure on `Signature α R` is the abstract character
-- group of `HopfAlgebras.Combinatorial.Basic`: the inverse is
-- precomposition with the signed-reversal antipode of `wordHopf`.

/-- The underlying series of the group inverse is the shuffle antipode
`σ⁻¹(w) = (-1)^{|w|}·σ(wʳ)`. -/
theorem inv_val (σ : Signature α R) :
    ((σ⁻¹ : Signature α R) : (List α → R)) =
      Word.antipode σ.1 := by
  funext w
  show (([(decide (w.length % 2 = 0), w.reverse)] :
      List (Bool × List α)).map fun sa =>
        (if sa.1 then (1 : R) else -1) * σ.1 sa.2).sum =
    (-1 : R) ^ w.length * σ.1 w.reverse
  rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Word.sign_eq]

@[simp]
theorem inv_coeff (σ : Signature α R) (w : List α) :
    coeff σ⁻¹ w = (-1) ^ w.length * coeff σ w.reverse :=
  congrFun (inv_val σ) w

/-- **The antipode is a two-sided inverse** on characters:
`a ⊗ S(a) = 1` for group-like `a` (from the group structure). -/
theorem _root_.RoughPaths.Word.IsGroupLike.tensorProduct_antipode
    {a : (List α → R)} (ha : Word.IsGroupLike a) :
    Word.tensorProduct a (Word.antipode a) =
      Word.unit α R := by
  let σ : Signature α R := ⟨a, ha⟩
  have h := congrArg Subtype.val (mul_inv_cancel σ)
  rw [mul_val, inv_val] at h
  exact h.trans one_val

/-- The group inverse of a piecewise-linear signature is the signature
of the **reversed path**: the antipode and time reversal agree, by
uniqueness of inverses. -/
theorem inv_ofPiecewiseLinear {R : Type v} [Field R] [CharZero R]
    (segs : List (α → R)) :
    (ofPiecewiseLinear segs)⁻¹ =
      ofPiecewiseLinear (segs.reverse.map fun s => -s) :=
  inv_eq_of_mul_eq_one_right
    (Subtype.ext
      ((Word.piecewiseLinearSignature_reverse_neg
        segs).trans one_val.symm))

end Signature

end RoughPaths
