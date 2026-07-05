/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Words.SplitShuffle
import RoughPaths.Signature.Linear

/-!
# Piecewise-linear signatures and Chen's theorem

Group-likeness is closed under the tensor (Chen) product — via the
bialgebra keystone `Word.shuffle_splits_perm` from
`HopfAlgebras.Words.SplitShuffle` — giving the piecewise-linear
signature, Chen's theorem for concatenation, and the signature monoid.
-/

namespace RoughPaths

open HopfAlgebras

universe u v

variable {α : Type u}

/-! ### Group-likeness of the tensor product -/

namespace Word

variable {R : Type v}

theorem sum_map_flatMap {β γ : Type u} [AddCommMonoid R]
    (l : List β) (f : β → List γ) (g : γ → R) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
        List.map_cons, List.sum_cons]

/-- **The tensor (concatenation) product of group-like series is
group-like** — the summed form of shuffle–deconcatenation compatibility. -/
theorem IsGroupLike.tensorProduct [CommSemiring R]
    {a b : (List α → R)} (ha : IsGroupLike a) (hb : IsGroupLike b) :
    IsGroupLike (Word.tensorProduct a b) := by
  constructor
  · show ((Word.splits ([] : List α)).map fun p =>
        coeff a p.1 * coeff b p.2).sum = 1
    rw [Word.splits_nil, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    show coeff a [] * coeff b [] = 1
    rw [ha.coeff_nil, hb.coeff_nil, one_mul]
  · intro u v
    -- right side: fold shuffle-of-splits into a single flatMap sum
    have hR : shuffleCoeff (Word.tensorProduct a b) u v =
        (((Word.shuffle u v).flatMap Word.splits).map
          fun p => coeff a p.1 * coeff b p.2).sum := by
      rw [shuffleCoeff, sum_map_flatMap]
      rfl
    -- left side: expand the product of sums over the split-shuffle pairs
    have hL : coeff (Word.tensorProduct a b) u *
        coeff (Word.tensorProduct a b) v =
        ((Word.splitShufflePairs u v).map
          fun r => coeff a r.1 * coeff b r.2).sum := by
      show ((Word.splits u).map fun p => coeff a p.1 * coeff b p.2).sum *
          ((Word.splits v).map fun q => coeff a q.1 * coeff b q.2).sum = _
      rw [Word.splitShufflePairs_def, sum_map_flatMap,
        ← List.sum_map_mul_right]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p _
      rw [sum_map_flatMap, ← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro q _
      -- pointwise: (a p₁ b p₂)(a q₁ b q₂) = Σ_{x,y} a x · b y
      have hkey : (coeff a p.1 * coeff b p.2) * (coeff a q.1 * coeff b q.2) =
          ((Word.shuffle p.1 q.1).map fun x =>
            ((Word.shuffle p.2 q.2).map fun y => coeff a x * coeff b y).sum).sum := by
        have h1 : (coeff a p.1 * coeff b p.2) * (coeff a q.1 * coeff b q.2) =
            (coeff a p.1 * coeff a q.1) * (coeff b p.2 * coeff b q.2) := by
          ring
        rw [h1, ha.2, hb.2, shuffleCoeff, shuffleCoeff,
          ← List.sum_map_mul_right]
        apply congrArg List.sum
        apply List.map_congr_left
        intro x _
        rw [← List.sum_map_mul_left]
        rfl
      rw [hkey, sum_map_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro x _
      rw [List.map_map]
      rfl
    rw [hL, hR]
    exact (((Word.shuffle_splits_perm u v).map
      fun p => coeff a p.1 * coeff b p.2).sum_eq).symm

/-! ### Piecewise-linear signatures and Chen's theorem -/

/-- The signature of a piecewise-linear path: the ordered tensor product of
the segments' exponentials. -/
def piecewiseLinearSignature [Field R] (segs : List (α → R)) :
    (List α → R) :=
  segs.foldl (fun acc v => Word.tensorProduct acc
    (linearSignature v)) (unit α R)

@[simp]
theorem piecewiseLinearSignature_nil [Field R] :
    piecewiseLinearSignature ([] : List (α → R)) = unit α R :=
  rfl

private theorem foldl_tensorProduct_assoc [Field R]
    (A : (List α → R)) :
    ∀ (ys : List (α → R)) (B : (List α → R)),
      ys.foldl (fun acc v => Word.tensorProduct acc
          (linearSignature v)) (Word.tensorProduct A B) =
        Word.tensorProduct A
          (ys.foldl (fun acc v => Word.tensorProduct acc
            (linearSignature v)) B)
  | [], B => rfl
  | v :: ys, B => by
      rw [List.foldl_cons, List.foldl_cons, tensorProduct_assoc]
      exact foldl_tensorProduct_assoc A ys _

/-- **Chen's concatenation theorem** for piecewise-linear paths: the
signature of a concatenation is the tensor product of the signatures. -/
theorem piecewiseLinearSignature_append [Field R] (xs ys : List (α → R)) :
    piecewiseLinearSignature (xs ++ ys) =
      Word.tensorProduct (piecewiseLinearSignature xs)
        (piecewiseLinearSignature ys) := by
  rw [piecewiseLinearSignature, List.foldl_append]
  rw [show (xs.foldl (fun acc v => Word.tensorProduct acc
      (linearSignature v)) (unit α R)) = piecewiseLinearSignature xs from rfl]
  conv_lhs => rw [show piecewiseLinearSignature xs =
    Word.tensorProduct (piecewiseLinearSignature xs) (unit α R)
    from (tensorProduct_unit_right _).symm]
  exact foldl_tensorProduct_assoc _ ys _

/-- **The signature of a piecewise-linear path is group-like.** -/
theorem isGroupLike_piecewiseLinearSignature [Field R] [CharZero R]
    (segs : List (α → R)) :
    IsGroupLike (piecewiseLinearSignature segs) := by
  induction segs using List.reverseRecOn with
  | nil => exact unit_isGroupLike
  | append_singleton init v ih =>
      rw [piecewiseLinearSignature_append]
      have h1 : piecewiseLinearSignature [v] = linearSignature v := by
        rw [piecewiseLinearSignature, List.foldl_cons, List.foldl_nil,
          tensorProduct_unit_left]
      rw [h1]
      exact ih.tensorProduct (isGroupLike_linearSignature v)

/-- The signature of a single segment. -/
@[simp]
theorem piecewiseLinearSignature_singleton [Field R] (v : α → R) :
    piecewiseLinearSignature [v] = linearSignature v := by
  rw [piecewiseLinearSignature, List.foldl_cons, List.foldl_nil,
    tensorProduct_unit_left]

/-- **Group inverse of a piecewise-linear signature**: running the path
backwards — reversed, negated segments — inverts the signature. Together
with `piecewiseLinearSignature_append` (Chen), the piecewise-linear
signatures form a group, not just a monoid. -/
theorem piecewiseLinearSignature_reverse_neg [Field R] [CharZero R] :
    ∀ segs : List (α → R),
      Word.tensorProduct (piecewiseLinearSignature segs)
        (piecewiseLinearSignature (segs.reverse.map fun s => -s)) =
      unit α R
  | [] => by
      rw [List.reverse_nil, List.map_nil, piecewiseLinearSignature_nil,
        tensorProduct_unit_left]
  | s :: rest => by
      rw [show s :: rest = [s] ++ rest from rfl,
        piecewiseLinearSignature_append, List.reverse_append,
        List.map_append, piecewiseLinearSignature_append,
        tensorProduct_assoc,
        show Word.tensorProduct (piecewiseLinearSignature rest)
            (Word.tensorProduct
              (piecewiseLinearSignature (rest.reverse.map fun s => -s))
              (piecewiseLinearSignature ([s].reverse.map fun s => -s))) =
          Word.tensorProduct
            (Word.tensorProduct (piecewiseLinearSignature rest)
              (piecewiseLinearSignature (rest.reverse.map fun s => -s)))
            (piecewiseLinearSignature ([s].reverse.map fun s => -s)) from
          (tensorProduct_assoc _ _ _).symm,
        piecewiseLinearSignature_reverse_neg rest, tensorProduct_unit_left,
        show [s].reverse.map (fun s => -s) = [-s] from rfl,
        piecewiseLinearSignature_singleton,
        piecewiseLinearSignature_singleton,
        tensorProduct_linearSignature_neg]

end Word

namespace Signature

variable {R : Type v}

-- The monoid structure on `Signature α R` is the abstract character
-- monoid of `HopfAlgebras.Combinatorial.Basic`; the product is the
-- tensor (Chen) product (`Signature.mul_val`).

/-- The bundled signature of a piecewise-linear path. -/
noncomputable def ofPiecewiseLinear [Field R] [CharZero R]
    (segs : List (α → R)) : Signature α R :=
  ⟨Word.piecewiseLinearSignature segs,
    Word.isGroupLike_piecewiseLinearSignature segs⟩

/-- Chen's theorem, bundled: concatenation of paths multiplies signatures. -/
theorem ofPiecewiseLinear_append [Field R] [CharZero R]
    (xs ys : List (α → R)) :
    ofPiecewiseLinear (xs ++ ys) =
      ofPiecewiseLinear (α := α) xs * ofPiecewiseLinear ys :=
  Subtype.ext (Word.piecewiseLinearSignature_append xs ys)

end Signature

end RoughPaths

