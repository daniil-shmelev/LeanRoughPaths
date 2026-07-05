/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Combinatorial.Basic
import HopfAlgebras.Hopf.MKWDual

/-!
# The Munthe-Kaas–Wright bialgebra as a combinatorial bialgebra

The MKW Hopf algebra of ordered (planar) rooted forests, packaged as a
`CombBialg`: the product is the shuffle of forests, the coproduct the
MKW expansion `PlanarForest.mkwTerms` from `HopfAlgebras`. Its
characters — the shuffle-multiplicative functionals on ordered forests,
i.e. the Lie–Butcher series and the coefficient systems of planarly
branched rough paths — inherit the abstract convolution monoid of
`HopfAlgebra.Basic`, which coincides with the Grossman–Larson
convolution `PlanarForest.mkwConvolution`.

All axioms are discharged from the keystones in `HopfAlgebras`:
`shuffle_flatMap_mkwTerms_perm` (bialgebra compatibility),
`mkwLeftTriples_perm_mkwRightTriples` via `mkwConvolution_assoc`
(coassociativity), and `mkwConvolution_counit_left`/`_right`.
-/

namespace HopfAlgebras

open HopfAlgebras

universe v

namespace MKW

/-- Peel a sum over a `flatMap` into iterated sums. -/
private theorem sum_flatMap {β γ : Type*} {R : Type*}
    [AddCommMonoid R] (l : List β) (f : β → List γ) (g : γ → R) :
    ((l.flatMap f).map g).sum =
      (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
        List.map_cons, List.sum_cons]

/-- The planar counit coefficient as a Boolean if-then-else. -/
theorem counitCoeff_eq_boolIte {R : Type v} [CommSemiring R]
    (ts : PlanarForest) :
    PlanarForestAlgebra.counitCoeff (R := R) ts =
      (if ts.isEmpty then (1 : R) else 0) := by
  cases ts with
  | nil =>
      show PlanarForestAlgebra.counitCoeff (R := R)
        ([] : PlanarForest) = (1 : R)
      exact PlanarForestAlgebra.counitCoeff_nil
  | cons t ts =>
      show PlanarForestAlgebra.counitCoeff (R := R) (t :: ts) = (0 : R)
      exact PlanarForestAlgebra.counitCoeff_ne_nil (List.cons_ne_nil t ts)

end MKW

/-- **The MKW bialgebra of ordered forests** as a combinatorial
bialgebra: shuffle product and MKW (Grossman–Larson-dual) coproduct. -/
noncomputable def mkwBialg : CombBialg.{0, v} PlanarForest where
  mul := Word.shuffle
  one := []
  coprod := PlanarForest.mkwTerms
  isOne := List.isEmpty
  isOne_iff := fun x => by simp
  mul_one_expand := Word.shuffle_nil_right
  one_mul_expand := Word.shuffle_nil_left
  coprod_one := PlanarForest.mkwTerms_nil
  coassoc := fun f g h x => PlanarForest.mkwConvolution_assoc f g h x
  counit_left := by
    intro R _ f x
    refine Eq.trans ?_ (PlanarForest.mkwConvolution_counit_left (R := R) f x)
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    show (if p.1.isEmpty then (1 : R) else 0) * f p.2 =
      PlanarForestAlgebra.counitCoeff (R := R) p.1 * f p.2
    rw [MKW.counitCoeff_eq_boolIte]
  counit_right := by
    intro R _ f x
    refine Eq.trans ?_ (PlanarForest.mkwConvolution_counit_right (R := R) f x)
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    show f p.1 * (if p.2.isEmpty then (1 : R) else 0) =
      f p.1 * PlanarForestAlgebra.counitCoeff (R := R) p.2
    rw [MKW.counitCoeff_eq_boolIte]
  mul_count_one := by
    intro R _ x y
    by_cases hx : x = ([] : PlanarForest)
    · by_cases hy : y = ([] : PlanarForest)
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
      by_cases hzn : z = ([] : PlanarForest)
      · exact absurd (Word.eq_nil_of_mem_shuffle hz hzn).1 hx
      · rw [if_neg (fun hb => hzn (List.isEmpty_iff.mp hb))]
  bialg := by
    intro R _ φ ψ x y
    refine Eq.trans (MKW.sum_flatMap _ _ _).symm ?_
    refine Eq.trans (((PlanarForest.shuffle_flatMap_mkwTerms_perm x y).map
      fun p => φ p.1 * ψ p.2).sum_eq) ?_
    refine Eq.trans (MKW.sum_flatMap _ _ _) ?_
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    refine Eq.trans (MKW.sum_flatMap _ _ _) ?_
    refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
    refine Eq.trans (MKW.sum_flatMap _ _ _) ?_
    rw [← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun w _ => ?_)
    rw [List.map_map, ← List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left fun r _ => rfl)

/-- Shuffle characters on ordered forests are exactly the characters of
the MKW combinatorial bialgebra. -/
theorem isShuffleCharacter_iff_isCharacter {R : Type v} [CommSemiring R]
    (f : PlanarForest → R) :
    PlanarForest.IsShuffleCharacter f ↔ mkwBialg.IsCharacter f := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x y => (h2 x y).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x y => (h2 x y).symm⟩

/-- **The Grossman–Larson convolution is the abstract MKW convolution**
— definitionally. -/
theorem mkwConvolution_eq_conv {R : Type v} [CommSemiring R]
    (f g : PlanarForest → R) :
    PlanarForest.mkwConvolution f g =
      CombBialg.Character.conv (H := mkwBialg) f g :=
  rfl

end HopfAlgebras
