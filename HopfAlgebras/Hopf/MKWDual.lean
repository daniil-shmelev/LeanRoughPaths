/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.MKWBialgebra

/-!
# The Dual of the MKW Hopf Algebra: the Grossman-Larson Convolution

This file defines the convolution product on linear functionals of ordered
forests induced by the MKW coproduct,

  `(α ∘ β)(ω) = ⟨α ⊗ β, Δ_N(ω)⟩ = Σ_{cuts} α(P^c(ω)) β(R^c(ω))`,

which by arXiv:math/0603023 (Section 3) is the Grossman-Larson product on the
graded dual of `H_N`. Associativity follows from coassociativity of `Δ_N`,
the unit laws from the counit laws, and the shuffle-multiplicative
functionals (the exponential Lie-Butcher series) are closed under the
product by the bialgebra law — the character group of Lie group integrators.

## Main definitions

* `PlanarForest.mkwConvolution` - the Grossman-Larson convolution
* `PlanarForest.mkwConvolution_assoc` - associativity, from coassociativity
* `PlanarForest.IsShuffleCharacter` - shuffle-multiplicative functionals
* `PlanarForest.IsShuffleCharacter.mkwConvolution` - the character group is
  closed under the Grossman-Larson convolution
-/

namespace HopfAlgebras

open HopfAlgebras

universe u

namespace PlanarForest

variable {R : Type u}

/-- The Grossman-Larson convolution of two functionals on ordered forests,
dual to the MKW coproduct (arXiv:math/0603023, Section 3). -/
def mkwConvolution [Semiring R] (f g : PlanarForest → R)
    (ω : PlanarForest) : R :=
  ((mkwTerms ω).map fun pr => f pr.1 * g pr.2).sum

private theorem map_flatMap'' {α β γ : Type*} (l : List α) (f : α → List β)
    (g : β → γ) :
    (l.flatMap f).map g = l.flatMap fun a => (f a).map g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem sum_flatMap'' {α : Type*} {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem sum_mul_sum'' {α β : Type*} {M : Type*}
    [NonUnitalNonAssocSemiring M] (xs : List α) (ys : List β)
    (f : α → M) (g : β → M) :
    (xs.map f).sum * (ys.map g).sum =
      (xs.map fun x => (ys.map fun y => f x * g y).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, add_mul, ih, List.map_cons,
        List.sum_cons, List.sum_map_mul_left]

@[simp]
theorem mkwConvolution_nil [Semiring R] (f g : PlanarForest → R) :
    mkwConvolution f g ([] : PlanarForest) = f [] * g [] := by
  simp [mkwConvolution]

/-- The counit is a left unit for the Grossman-Larson convolution. -/
theorem mkwConvolution_counit_left [CommSemiring R] (g : PlanarForest → R)
    (ω : PlanarForest) :
    mkwConvolution (PlanarForestAlgebra.counitCoeff (R := R)) g ω = g ω := by
  rw [mkwConvolution]
  have h := sum_map_counitCoeff_fst_smul_mkwTerms (R := R) (M := R) ω g
  simpa [smul_eq_mul] using h

/-- The counit is a right unit for the Grossman-Larson convolution. -/
theorem mkwConvolution_counit_right [CommSemiring R] (f : PlanarForest → R)
    (ω : PlanarForest) :
    mkwConvolution f (PlanarForestAlgebra.counitCoeff (R := R)) ω = f ω := by
  rw [mkwConvolution]
  have h := sum_map_counitCoeff_snd_smul_mkwTerms (R := R) (M := R) ω f
  have h' : ((mkwTerms ω).map fun pr =>
      f pr.1 * PlanarForestAlgebra.counitCoeff (R := R) pr.2).sum =
      ((mkwTerms ω).map fun pr =>
        PlanarForestAlgebra.counitCoeff (R := R) pr.2 • f pr.1).sum := by
    refine congrArg List.sum (List.map_congr_left fun pr _ => ?_)
    rw [smul_eq_mul, mul_comm]
  rw [h', h]

/-- Associativity of the Grossman-Larson convolution, dual to
coassociativity of the MKW coproduct. -/
theorem mkwConvolution_assoc [CommSemiring R] (f g h : PlanarForest → R)
    (ω : PlanarForest) :
    mkwConvolution (mkwConvolution f g) h ω =
      mkwConvolution f (mkwConvolution g h) ω := by
  have hleft : mkwConvolution (mkwConvolution f g) h ω =
      ((mkwLeftTriples ω).map fun tr =>
        f tr.1 * g tr.2.1 * h tr.2.2).sum := by
    rw [mkwConvolution, mkwLeftTriples, map_flatMap'', sum_flatMap'']
    refine congrArg List.sum (List.map_congr_left fun pr _ => ?_)
    rw [mkwConvolution, List.map_map]
    rw [← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
    simp
  have hright : mkwConvolution f (mkwConvolution g h) ω =
      ((mkwRightTriples ω).map fun tr =>
        f tr.1 * g tr.2.1 * h tr.2.2).sum := by
    rw [mkwConvolution, mkwRightTriples, map_flatMap'', sum_flatMap'']
    refine congrArg List.sum (List.map_congr_left fun pr _ => ?_)
    rw [mkwConvolution, List.map_map]
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
    simp [mul_assoc]
  rw [hleft, hright]
  exact List.Perm.sum_eq
    ((mkwLeftTriples_perm_mkwRightTriples ω).map fun tr =>
      f tr.1 * g tr.2.1 * h tr.2.2)

/-- A functional on ordered forests is a shuffle character if it is
normalized and multiplicative for the shuffle product: these are the
exponential Lie-Butcher series of arXiv:math/0603023, Lemma 2. -/
def IsShuffleCharacter [Semiring R] (f : PlanarForest → R) : Prop :=
  f [] = 1 ∧ ∀ ω₁ ω₂ : PlanarForest,
    ((Word.shuffle ω₁ ω₂).map f).sum = f ω₁ * f ω₂

/-- The Grossman-Larson convolution of shuffle characters is a shuffle
character: Lie group integrators form a group under composition
(arXiv:math/0603023, Section 3). -/
theorem IsShuffleCharacter.mkwConvolution [CommSemiring R]
    {f g : PlanarForest → R} (hf : IsShuffleCharacter f)
    (hg : IsShuffleCharacter g) :
    IsShuffleCharacter (PlanarForest.mkwConvolution f g) := by
  constructor
  · rw [mkwConvolution_nil, hf.1, hg.1, one_mul]
  · intro ω₁ ω₂
    -- expand the shuffle sum of convolutions via the bialgebra law
    have hexpand : ((Word.shuffle ω₁ ω₂).map
        (PlanarForest.mkwConvolution f g)).sum =
        (((Word.shuffle ω₁ ω₂).flatMap mkwTerms).map fun pr =>
          f pr.1 * g pr.2).sum := by
      rw [map_flatMap'', sum_flatMap'']
      rfl
    rw [hexpand,
      List.Perm.sum_eq ((shuffle_flatMap_mkwTerms_perm ω₁ ω₂).map fun pr =>
        f pr.1 * g pr.2)]
    -- evaluate the pairwise-shuffle sum using multiplicativity of f and g
    rw [pairShuffle, map_flatMap'', sum_flatMap'']
    have hpoint : ∀ t₁ : PlanarForest × PlanarForest,
        (((mkwTerms ω₂).flatMap fun t₂ =>
          (Word.shuffle t₁.1 t₂.1).flatMap fun p =>
            (Word.shuffle t₁.2 t₂.2).map fun r => (p, r)).map fun pr =>
              f pr.1 * g pr.2).sum =
        ((mkwTerms ω₂).map fun t₂ =>
          (f t₁.1 * f t₂.1) * (g t₁.2 * g t₂.2)).sum := by
      intro t₁
      rw [map_flatMap'', sum_flatMap'']
      refine congrArg List.sum (List.map_congr_left fun t₂ _ => ?_)
      rw [map_flatMap'', sum_flatMap'']
      have hinner : ∀ p : PlanarForest,
          ((((Word.shuffle t₁.2 t₂.2).map fun r => (p, r)).map fun pr =>
            f pr.1 * g pr.2).sum) =
          f p * (g t₁.2 * g t₂.2) := by
        intro p
        rw [List.map_map]
        have : ((Word.shuffle t₁.2 t₂.2).map
            ((fun pr : PlanarForest × PlanarForest => f pr.1 * g pr.2) ∘
              fun r => (p, r))).sum =
            ((Word.shuffle t₁.2 t₂.2).map fun r => f p * g r).sum := by
          refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
          simp
        rw [this, List.sum_map_mul_left, hg.2]
      rw [List.map_congr_left fun p _ => hinner p, List.sum_map_mul_right,
        hf.2]
    rw [List.map_congr_left fun t₁ _ => hpoint t₁]
    -- split the product of sums
    have hsplit : ((mkwTerms ω₁).map fun t₁ =>
        ((mkwTerms ω₂).map fun t₂ =>
          (f t₁.1 * f t₂.1) * (g t₁.2 * g t₂.2)).sum).sum =
        ((mkwTerms ω₁).map fun t₁ => f t₁.1 * g t₁.2).sum *
          ((mkwTerms ω₂).map fun t₂ => f t₂.1 * g t₂.2).sum := by
      rw [sum_mul_sum'']
      refine congrArg List.sum (List.map_congr_left fun t₁ _ => ?_)
      refine congrArg List.sum (List.map_congr_left fun t₂ _ => ?_)
      ring
    rw [hsplit]
    rfl

end PlanarForest

end HopfAlgebras
