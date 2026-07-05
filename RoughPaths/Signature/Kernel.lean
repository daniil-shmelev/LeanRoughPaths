/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Signature.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Signature kernels

The truncated signature kernel `k_n(a, b) = Σ_{|w| ≤ n} a(w)·b(w)` (Salvi,
Cass, Foster, Lyons, Yang): symmetric, bilinear, and positive semidefinite
— its Gram quadratic form is a sum of squares of feature evaluations. The
word enumeration is parametrised by a listing of the alphabet, so it is
computable: for piecewise-linear paths over `ℚ` concrete kernel values can
be certified by `native_decide`.
-/

namespace RoughPaths

open HopfAlgebras

universe u v

variable {α : Type u} {R : Type v}

namespace Word

/-- All words of a given length over a listed alphabet. -/
def wordListOfLength (letters : List α) : ℕ → List (List α)
  | 0 => [[]]
  | n + 1 => letters.flatMap fun a =>
      (wordListOfLength letters n).map fun w => a :: w

/-- All words of length at most `n` over a listed alphabet. -/
def kernelWords (letters : List α) (n : ℕ) : List (List α) :=
  (List.range (n + 1)).flatMap (wordListOfLength letters)

/-- The truncated signature kernel: the `ℓ²`-pairing of word coefficients
through length `n`, the alphabet being listed by `letters`. -/
def sigKernelTruncated [CommSemiring R] (letters : List α)
    (a b : (List α → R)) (n : ℕ) : R :=
  ((kernelWords letters n).map fun w => coeff a w * coeff b w).sum

/-- The kernel is symmetric. -/
theorem sigKernelTruncated_comm [CommSemiring R] (letters : List α)
    (a b : (List α → R)) (n : ℕ) :
    sigKernelTruncated letters a b n = sigKernelTruncated letters b a n := by
  rw [sigKernelTruncated, sigKernelTruncated]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w _
  exact mul_comm _ _

private theorem sum_map_mul_add [CommSemiring R]
    (a a' b : (List α → R)) :
    ∀ l : List (List α),
      (l.map fun w => coeff (a + a') w * coeff b w).sum =
        (l.map fun w => coeff a w * coeff b w).sum +
          (l.map fun w => coeff a' w * coeff b w).sum
  | [] => by simp
  | w :: l => by
      simp only [List.map_cons, List.sum_cons, sum_map_mul_add a a' b l]
      have h1 : coeff (a + a') w = coeff a w + coeff a' w := rfl
      rw [h1]
      ring

/-- The kernel is additive on the left (bilinearity). -/
theorem sigKernelTruncated_add_left [CommSemiring R] (letters : List α)
    (a a' b : (List α → R)) (n : ℕ) :
    sigKernelTruncated letters (a + a') b n =
      sigKernelTruncated letters a b n + sigKernelTruncated letters a' b n :=
  sum_map_mul_add a a' b _

/-- The kernel scales on the left (bilinearity). -/
theorem sigKernelTruncated_smul_left [CommSemiring R] (letters : List α)
    (r : R) (a b : (List α → R)) (n : ℕ) :
    sigKernelTruncated letters (r • a) b n =
      r * sigKernelTruncated letters a b n := by
  rw [sigKernelTruncated, sigKernelTruncated, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w _
  have h1 : coeff (r • a) w = r * coeff a w := rfl
  rw [h1, mul_assoc]

/-- Exchange of a finite feature sum with the word sum. -/
private theorem finsetSum_listSum_swap {m : ℕ} [AddCommMonoid R]
    (l : List (List α)) (f : Fin m → List α → R) :
    (∑ i, ((l.map (f i)).sum)) = (l.map fun w => ∑ i, f i w).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

/-- **Positive semidefiniteness** of the truncated kernel: the Gram
quadratic form is a sum of squares of feature evaluations. -/
theorem sigKernelTruncated_quadratic_nonneg {K : Type v}
    [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (letters : List α)
    {m : ℕ} (S : Fin m → (List α → K)) (c : Fin m → K) (n : ℕ) :
    0 ≤ ∑ i, ∑ j, c i * c j * sigKernelTruncated letters (S i) (S j) n := by
  have key : (∑ i, ∑ j, c i * c j * sigKernelTruncated letters (S i) (S j) n) =
      ((kernelWords letters n).map fun w =>
        (∑ i, c i * coeff (S i) w) ^ 2).sum := by
    calc (∑ i, ∑ j, c i * c j * sigKernelTruncated letters (S i) (S j) n)
        = ∑ i, ∑ j, ((kernelWords letters n).map fun w =>
            (c i * coeff (S i) w) * (c j * coeff (S j) w)).sum := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [sigKernelTruncated, ← List.sum_map_mul_left]
          apply congrArg List.sum
          apply List.map_congr_left
          intro w _
          ring
      _ = ∑ i, ((kernelWords letters n).map fun w =>
            (c i * coeff (S i) w) * (∑ j, c j * coeff (S j) w)).sum := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [finsetSum_listSum_swap]
          apply congrArg List.sum
          apply List.map_congr_left
          intro w _
          rw [Finset.mul_sum]
      _ = ((kernelWords letters n).map fun w =>
            (∑ i, c i * coeff (S i) w) * (∑ j, c j * coeff (S j) w)).sum := by
          rw [finsetSum_listSum_swap]
          apply congrArg List.sum
          apply List.map_congr_left
          intro w _
          rw [Finset.sum_mul]
      _ = ((kernelWords letters n).map fun w =>
            (∑ i, c i * coeff (S i) w) ^ 2).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro w _
          rw [sq]
  rw [key]
  apply List.sum_nonneg
  intro x hx
  rcases List.mem_map.1 hx with ⟨w, _, rfl⟩
  exact sq_nonneg _

end Word

end RoughPaths
