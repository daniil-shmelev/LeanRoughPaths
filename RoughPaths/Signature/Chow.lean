/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import Mathlib.Algebra.BigOperators.Fin
import RoughPaths.Signature.Antipode

/-!
# Chow's theorem at level two

Group-like series are **exactly** the signatures of piecewise-linear
paths, to second order: over a finite alphabet, every character of the
word shuffle Hopf algebra agrees up to degree two with the signature of
an explicit piecewise-linear path
(`exists_piecewiseLinear_eq_of_isGroupLike_levelTwo`); conversely every
such signature is group-like (`isGroupLike_piecewiseLinearSignature`).

The construction is the classical one: a straight segment matches the
level-one data, and one rectangle loop per coordinate plane corrects the
antisymmetric part of the level-two data — the shuffle identity forces
the symmetric part, and loops contribute pure area. Degree two is the
order at which the library's rough path analysis operates; the
full-depth identification (Chow–Rashevskii) needs the free Lie algebra
and remains on the roadmap.
-/

namespace RoughPaths

open HopfAlgebras

universe u v

variable {α : Type u} {R : Type v}

namespace Word

/-! ### Low-degree expansion of the tensor product -/

private theorem tensor_single [Semiring R] (A B : (List α → R))
    (k : α) :
    coeff (tensorProduct A B) [k] =
      coeff A [] * coeff B [k] + coeff A [k] * coeff B [] := by
  rw [tensorProduct_cons, Word.splits_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

private theorem tensor_pair [Semiring R] (A B : (List α → R))
    (k l : α) :
    coeff (tensorProduct A B) [k, l] =
      coeff A [] * coeff B [k, l] + coeff A [k] * coeff B [l] +
        coeff A [k, l] * coeff B [] := by
  rw [tensorProduct_cons]
  show coeff A [] * coeff B [k, l] +
    (coeff A [k] * coeff B [l] + (coeff A [k, l] * coeff B [] + 0)) = _
  rw [add_zero, ← add_assoc]

private theorem sum_flatMap' {β γ : Type*} [AddCommMonoid R]
    (l : List β) (f : β → List γ) (g : γ → R) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
        List.map_cons, List.sum_cons]

/-! ### Rectangle loops -/

/-- The rectangle loop in the `(i,j)`-coordinate plane with area
parameter `c`: out, up, back, down. -/
def rectLoop [DecidableEq α] [Field R] (i j : α) (c : R) :
    List (α → R) :=
  [Pi.single i c, Pi.single j 1, -Pi.single i c, -Pi.single j 1]

private theorem tensor_nil' [Field R] (A B : (List α → R)) :
    tensorProduct A B [] = A [] * B [] :=
  tensorProduct_nil A B

private theorem lin_nil' [Field R] (w : α → R) :
    linearSignature w [] = 1 :=
  linearSignature_nil w

private theorem rect_single [DecidableEq α] [Field R] (i j : α) (c : R)
    (k : α) :
    coeff (piecewiseLinearSignature (rectLoop i j c)) [k] = 0 := by
  show coeff (tensorProduct (tensorProduct (tensorProduct (tensorProduct
    (unit α R) (linearSignature (Pi.single i c)))
    (linearSignature (Pi.single j 1)))
    (linearSignature (-Pi.single i c)))
    (linearSignature (-Pi.single j 1))) [k] = 0
  rw [tensorProduct_unit_left, tensor_single, tensor_single,
    tensor_single]
  simp only [coeff_apply, tensor_nil', lin_nil', linearSignature_singleton,
    Pi.neg_apply]
  ring

private theorem rect_pair [DecidableEq α] [Field R] [CharZero R]
    (i j : α) (c : R) (k l : α) :
    coeff (piecewiseLinearSignature (rectLoop i j c)) [k, l] =
      (Pi.single i c : α → R) k * (Pi.single j 1 : α → R) l -
        (Pi.single j 1 : α → R) k * (Pi.single i c : α → R) l := by
  show coeff (tensorProduct (tensorProduct (tensorProduct (tensorProduct
    (unit α R) (linearSignature (Pi.single i c)))
    (linearSignature (Pi.single j 1)))
    (linearSignature (-Pi.single i c)))
    (linearSignature (-Pi.single j 1))) [k, l] = _
  rw [tensorProduct_unit_left, tensor_pair, tensor_pair, tensor_pair,
    tensor_single, tensor_single]
  simp only [coeff_apply, tensor_nil', lin_nil', linearSignature_singleton,
    linearSignature_pair, Pi.neg_apply]
  field_simp
  ring

/-! ### Appending area loops -/

/-- Appending a list of loops (blocks with vanishing first level) leaves
the first level unchanged and adds the loops' areas at the second
level. -/
private theorem append_loops [Field R] [CharZero R] :
    ∀ (blocks : List (List (α → R))) (base : List (α → R)),
      (∀ b ∈ blocks, ∀ k : α,
        coeff (piecewiseLinearSignature b) [k] = 0) →
      (∀ k : α,
        coeff (piecewiseLinearSignature (base ++ blocks.flatten)) [k] =
          coeff (piecewiseLinearSignature base) [k]) ∧
      ∀ k l : α,
        coeff (piecewiseLinearSignature (base ++ blocks.flatten))
            [k, l] =
          coeff (piecewiseLinearSignature base) [k, l] +
            (blocks.map fun b =>
              coeff (piecewiseLinearSignature b) [k, l]).sum
  | [], base, _ => by simp
  | b :: rest, base, hb => by
      have hone : coeff (piecewiseLinearSignature b) [] = 1 :=
        (isGroupLike_piecewiseLinearSignature b).coeff_nil
      have hbase1 : ∀ k : α,
          coeff (piecewiseLinearSignature (base ++ b)) [k] =
            coeff (piecewiseLinearSignature base) [k] := by
        intro k
        rw [piecewiseLinearSignature_append, tensor_single, hone,
          hb b (List.mem_cons_self) k, mul_zero, mul_one, zero_add]
      have hbase2 : ∀ k l : α,
          coeff (piecewiseLinearSignature (base ++ b)) [k, l] =
            coeff (piecewiseLinearSignature base) [k, l] +
              coeff (piecewiseLinearSignature b) [k, l] := by
        intro k l
        rw [piecewiseLinearSignature_append, tensor_pair, hone,
          (isGroupLike_piecewiseLinearSignature base).coeff_nil,
          hb b (List.mem_cons_self) l, mul_zero, mul_one, one_mul,
          add_zero, add_comm]
      have IH := append_loops rest (base ++ b)
        (fun b' hb' k => hb b' (List.mem_cons_of_mem _ hb') k)
      constructor
      · intro k
        rw [List.flatten_cons, ← List.append_assoc, IH.1 k, hbase1 k]
      · intro k l
        rw [List.flatten_cons, ← List.append_assoc, IH.2 k l,
          hbase2 k l, List.map_cons, List.sum_cons]
        ring

/-! ### Chow's theorem at level two -/

/-- **Chow's theorem at level two**: over a finite alphabet, every
group-like series — every character of the word shuffle Hopf algebra —
agrees up to degree two with the signature of an explicit
piecewise-linear path: a straight segment for the first level, plus one
rectangle loop per coordinate plane for the antisymmetric second-level
part (the symmetric part is forced by the shuffle identity). Together
with `isGroupLike_piecewiseLinearSignature`, the group-like elements are
**exactly** the piecewise-linear signatures to second order. -/
theorem exists_piecewiseLinear_eq_of_isGroupLike_levelTwo {d : ℕ}
    [Field R] [CharZero R] {a : (List (Fin d) → R)}
    (ha : IsGroupLike a) :
    ∃ segs : List (Fin d → R), ∀ w : List (Fin d), w.length ≤ 2 →
      coeff (piecewiseLinearSignature segs) w = coeff a w := by
  classical
  -- level-one data and the corrected level-two data
  set v : Fin d → R := fun k => a [k] with hv
  set A : Fin d → Fin d → R := fun k l => a [k, l] - v k * v l / 2
    with hA
  -- the shuffle identity forces the symmetric part
  have hanti : ∀ k l : Fin d, A l k = -A k l := by
    intro k l
    have hs : a [k] * a [l] = a [k, l] + a [l, k] := by
      have h := ha.shuffle [k] [l]
      have hshuf : Word.shuffle [k] [l] = [[k, l], [l, k]] := by
        rw [Word.shuffle_cons_cons, Word.shuffle_nil_left,
          Word.shuffle_nil_right]
        rfl
      rw [shuffleCoeff, hshuf] at h
      simpa using h
    have hAkl : A k l = a [k, l] - v k * v l / 2 := rfl
    have hAlk : A l k = a [l, k] - v l * v k / 2 := rfl
    have hvk : v k = a [k] := rfl
    have hvl : v l = a [l] := rfl
    rw [hAkl, hAlk, hvk, hvl]
    linear_combination -hs
  -- the correcting loops
  set blocks : List (List (Fin d → R)) :=
    (List.finRange d).flatMap fun i =>
      (List.finRange d).map fun j => rectLoop i j (A i j / 2)
    with hblocks
  have hblock1 : ∀ b ∈ blocks, ∀ k : Fin d,
      coeff (piecewiseLinearSignature b) [k] = 0 := by
    intro b hb k
    rw [hblocks] at hb
    obtain ⟨i, -, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hb
    exact rect_single i j _ k
  obtain ⟨h1, h2⟩ := append_loops blocks [v] hblock1
  refine ⟨[v] ++ blocks.flatten, ?_⟩
  intro w hw
  rcases w with - | ⟨k, - | ⟨l, - | ⟨m, rest⟩⟩⟩
  · rw [(isGroupLike_piecewiseLinearSignature _).coeff_nil,
      ha.coeff_nil]
  · rw [h1 k, piecewiseLinearSignature_singleton]
    show linearSignature v [k] = a [k]
    rw [linearSignature_singleton]
  · -- the level-two coefficient
    rw [h2 k l, piecewiseLinearSignature_singleton]
    have hsum : (blocks.map fun b =>
        coeff (piecewiseLinearSignature b) [k, l]).sum = A k l := by
      rw [hblocks, sum_flatMap' (List.finRange d)
        (fun i => (List.finRange d).map fun j =>
          rectLoop i j (A i j / 2))
        (fun b => coeff (piecewiseLinearSignature b) [k, l])]
      have hinner : ∀ i : Fin d,
          (((List.finRange d).map fun j =>
            rectLoop i j (A i j / 2)).map fun b =>
              coeff (piecewiseLinearSignature b) [k, l]).sum =
          ∑ j : Fin d,
            ((Pi.single i (A i j / 2) : Fin d → R) k *
              (Pi.single j 1 : Fin d → R) l -
              (Pi.single j 1 : Fin d → R) k *
                (Pi.single i (A i j / 2) : Fin d → R) l) := by
        intro i
        rw [List.map_map, Fin.sum_univ_def]
        refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
        exact rect_pair i j (A i j / 2) k l
      rw [List.map_congr_left fun i _ => hinner i, ← Fin.sum_univ_def]
      simp only [Pi.single_apply, mul_ite, ite_mul, one_mul, mul_one,
        mul_zero, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [hanti l k, Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    rw [hsum]
    show linearSignature v [k, l] + A k l = a [k, l]
    have hAkl : A k l = a [k, l] - v k * v l / 2 := rfl
    rw [linearSignature_pair, hAkl]
    ring
  · simp at hw
