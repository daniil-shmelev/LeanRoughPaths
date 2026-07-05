/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Combinatorial Hopf algebras and their character groups

A **combinatorial Hopf algebra** (`CombHopf`) is a Hopf algebra given by
a distinguished basis `B` with finitary structure constants: the product
and coproduct of basis elements expand as finite lists of basis elements
(resp. pairs), and the antipode as a finite signed list. This is the
common shape of the Hopf algebras of rough path theory — the word
shuffle algebra, the Butcher–Connes–Kreimer algebra of rooted forests,
and the Munthe-Kaas–Wright algebra of planar forests — and it avoids
topological tensor products entirely: every axiom is a coefficientwise
finite-sum identity.

The payoff is proved once, abstractly: the `R`-valued **characters**
(`CombHopf.Character`) — multiplicative functionals on the basis — form
a monoid under the convolution product dual to the coproduct
(`Character.instMonoid`), and over a commutative ring a **group**, with
inverse given by precomposition with the antipode
(`Character.instGroup`). Signatures of paths, branched signatures, and
Lie–Butcher series are characters of the three instances above.
-/

namespace HopfAlgebras

universe u v

/-- A combinatorial bialgebra on a basis `B`: finitary expansions of the
product and coproduct of basis elements, with the bialgebra axioms
stated as coefficientwise finite-sum identities against arbitrary
coefficient functions. Its characters form a monoid under convolution
(`Character.instMonoid`). -/
structure CombBialg (B : Type u) : Type (max u (v + 1)) where
  /-- Product expansion of two basis elements. -/
  mul : B → B → List B
  /-- The unit basis element (empty word / empty forest). -/
  one : B
  /-- Coproduct expansion of a basis element. -/
  coprod : B → List (B × B)
  /-- Boolean test for the unit basis element (keeps the counit's
  case split free of `Decidable` instance mismatches). -/
  isOne : B → Bool
  isOne_iff : ∀ x, isOne x = true ↔ x = one
  mul_one_expand : ∀ x, mul x one = [x]
  one_mul_expand : ∀ x, mul one x = [x]
  coprod_one : coprod one = [(one, one)]
  /-- Coassociativity, paired against coefficients. -/
  coassoc : ∀ {R : Type v} [CommSemiring R] (f g h : B → R) (x : B),
    ((coprod x).map fun p =>
      ((coprod p.1).map fun q => f q.1 * g q.2).sum * h p.2).sum =
    ((coprod x).map fun p =>
      f p.1 * ((coprod p.2).map fun q => g q.1 * h q.2).sum).sum
  /-- Left counit law, paired against coefficients. -/
  counit_left : ∀ {R : Type v} [CommSemiring R] (f : B → R) (x : B),
    ((coprod x).map fun p =>
      (if isOne p.1 then (1 : R) else 0) * f p.2).sum = f x
  /-- Right counit law, paired against coefficients. -/
  counit_right : ∀ {R : Type v} [CommSemiring R] (f : B → R) (x : B),
    ((coprod x).map fun p =>
      f p.1 * (if isOne p.2 then (1 : R) else 0)).sum = f x
  /-- The counit is multiplicative: the unit occurs in a product
  expansion exactly when both factors are the unit. -/
  mul_count_one : ∀ {R : Type v} [CommSemiring R] (x y : B),
    ((mul x y).map fun z => if isOne z then (1 : R) else 0).sum =
      (if isOne x then (1 : R) else 0) * (if isOne y then 1 else 0)
  /-- Product–coproduct (bialgebra) compatibility, paired against a pair
  of coefficient functions. -/
  bialg : ∀ {R : Type v} [CommSemiring R] (φ ψ : B → R) (x y : B),
    ((mul x y).map fun z =>
      ((coprod z).map fun p => φ p.1 * ψ p.2).sum).sum =
    ((coprod x).map fun p =>
      ((coprod y).map fun q =>
        ((mul p.1 q.1).map φ).sum * ((mul p.2 q.2).map ψ).sum).sum).sum

/-- A combinatorial Hopf algebra: a combinatorial bialgebra together
with a finitary **signed antipode expansion** and its defining
identities. Its characters form a group under convolution
(`Character.instGroup`). -/
structure CombHopf (B : Type u) :
    Type (max u (v + 1)) extends CombBialg.{u, v} B where
  /-- Signed antipode expansion (`true` = `+1`, `false` = `-1`). -/
  antipode : B → List (Bool × B)
  antipode_one : antipode one = [(true, one)]
  /-- The antipode identity `m ∘ (S ⊗ id) ∘ Δ = η ∘ ε`, paired against
  coefficients. -/
  antipode_conv : ∀ {R : Type v} [CommRing R] (f : B → R) (x : B),
    x ≠ one →
    ((coprod x).map fun p =>
      ((antipode p.1).map fun sa =>
        (if sa.1 then (1 : R) else -1) *
          ((mul sa.2 p.2).map f).sum).sum).sum = 0
  /-- Precomposition with the antipode preserves multiplicativity (the
  antipode is an algebra morphism for a commutative product). -/
  antipode_char : ∀ {R : Type v} [CommRing R] (φ : B → R),
    (∀ x y, φ x * φ y = ((mul x y).map φ).sum) →
    ∀ x y : B,
      ((antipode x).map fun sa =>
        (if sa.1 then (1 : R) else -1) * φ sa.2).sum *
      ((antipode y).map fun sa =>
        (if sa.1 then (1 : R) else -1) * φ sa.2).sum =
      ((mul x y).map fun z =>
        ((antipode z).map fun sa =>
          (if sa.1 then (1 : R) else -1) * φ sa.2).sum).sum

namespace CombBialg

variable {B : Type u} (H : CombBialg.{u, v} B)

/-- A character of a combinatorial Hopf algebra: a multiplicative
`R`-valued functional on the basis, sending the unit to `1`. -/
def IsCharacter {R : Type v} [CommSemiring R] (φ : B → R) : Prop :=
  φ H.one = 1 ∧ ∀ x y : B, φ x * φ y = ((H.mul x y).map φ).sum

/-- The characters of a combinatorial Hopf algebra with values in `R`. -/
def Character (R : Type v) [CommSemiring R] : Type (max u v) :=
  {φ : B → R // H.IsCharacter φ}

namespace Character

variable {H} {R : Type v} [CommSemiring R]

instance : CoeFun (H.Character R) (fun _ => B → R) where
  coe φ := φ.1

theorem map_one (φ : H.Character R) : φ H.one = 1 :=
  φ.2.1

theorem map_mul (φ : H.Character R) (x y : B) :
    φ x * φ y = ((H.mul x y).map φ.1).sum :=
  φ.2.2 x y

@[ext]
theorem ext {φ ψ : H.Character R} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  Subtype.ext (funext h)

/-- The convolution product of functionals, dual to the coproduct. -/
def conv (φ ψ : B → R) : B → R :=
  fun x => ((H.coprod x).map fun p => φ p.1 * ψ p.2).sum

/-- The counit character `ε(x) = δ_{x,1}`, the convolution unit. -/
def counit : B → R :=
  fun x => if H.isOne x then 1 else 0

variable (H)

theorem counit_isCharacter : H.IsCharacter (counit (H := H) (R := R)) := by
  constructor
  · show (if H.isOne H.one then (1 : R) else 0) = 1
    rw [if_pos ((H.isOne_iff H.one).mpr rfl)]
  · intro x y
    exact (H.mul_count_one x y).symm

variable {H}

/-- Convolution of characters is a character (the bialgebra axiom). -/
theorem conv_isCharacter (φ ψ : H.Character R) :
    H.IsCharacter (conv (H := H) φ.1 ψ.1) := by
  constructor
  · show ((H.coprod H.one).map fun p => φ p.1 * ψ p.2).sum = 1
    rw [H.coprod_one]
    show φ H.one * ψ H.one + 0 = 1
    rw [φ.map_one, ψ.map_one, one_mul, add_zero]
  · intro x y
    show conv (H := H) φ.1 ψ.1 x * conv (H := H) φ.1 ψ.1 y = _
    calc conv (H := H) φ.1 ψ.1 x * conv (H := H) φ.1 ψ.1 y
        = ((H.coprod x).map fun p =>
            ((H.coprod y).map fun q =>
              (φ p.1 * ψ p.2) * (φ q.1 * ψ q.2)).sum).sum := by
          rw [conv, conv, ← List.sum_map_mul_right]
          refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
          rw [← List.sum_map_mul_left]
      _ = ((H.coprod x).map fun p =>
            ((H.coprod y).map fun q =>
              ((H.mul p.1 q.1).map φ.1).sum *
                ((H.mul p.2 q.2).map ψ.1).sum).sum).sum := by
          refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
          refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
          rw [← φ.map_mul, ← ψ.map_mul]
          ring
      _ = ((H.mul x y).map fun z =>
            ((H.coprod z).map fun p => φ p.1 * ψ p.2).sum).sum :=
          (H.bialg φ.1 ψ.1 x y).symm

/-- **The character monoid**: characters under convolution. -/
noncomputable instance instMonoid : Monoid (H.Character R) where
  mul φ ψ := ⟨conv (H := H) φ.1 ψ.1, conv_isCharacter φ ψ⟩
  one := ⟨counit (H := H), counit_isCharacter H⟩
  mul_assoc φ ψ ρ := by
    refine ext fun x => ?_
    show ((H.coprod x).map fun p =>
        ((H.coprod p.1).map fun q => φ q.1 * ψ q.2).sum * ρ p.2).sum =
      ((H.coprod x).map fun p =>
        φ p.1 * ((H.coprod p.2).map fun q => ψ q.1 * ρ q.2).sum).sum
    exact H.coassoc φ.1 ψ.1 ρ.1 x
  one_mul φ := by
    refine ext fun x => ?_
    show ((H.coprod x).map fun p =>
      (if H.isOne p.1 then (1 : R) else 0) * φ p.2).sum = φ x
    exact H.counit_left φ.1 x
  mul_one φ := by
    refine ext fun x => ?_
    show ((H.coprod x).map fun p =>
      φ p.1 * (if H.isOne p.2 then (1 : R) else 0)).sum = φ x
    exact H.counit_right φ.1 x

@[simp]
theorem mul_apply (φ ψ : H.Character R) (x : B) :
    (φ * ψ) x = ((H.coprod x).map fun p => φ p.1 * ψ p.2).sum :=
  rfl

@[simp]
theorem one_apply (x : B) :
    (1 : H.Character R) x = if H.isOne x then 1 else 0 :=
  rfl

end Character

end CombBialg

namespace CombHopf

variable {B : Type u}

/-- Characters of the underlying bialgebra. -/
abbrev Character (H : CombHopf.{u, v} B) (R : Type v) [CommSemiring R] :=
  H.toCombBialg.Character R

namespace Character

open CombBialg.Character

variable {H : CombHopf.{u, v} B}

section Group

variable {R : Type v} [CommRing R]

/-- Precomposition with the (signed) antipode. -/
def antipodeComp (φ : B → R) : B → R :=
  fun x => ((H.antipode x).map fun sa =>
    (if sa.1 then (1 : R) else -1) * φ sa.2).sum

theorem antipodeComp_isCharacter (φ : H.Character R) :
    H.IsCharacter (antipodeComp (H := H) φ.1) := by
  constructor
  · show ((H.antipode H.one).map fun sa =>
      (if sa.1 then (1 : R) else -1) * φ sa.2).sum = 1
    rw [H.antipode_one]
    show (if true then (1 : R) else -1) * φ H.one + 0 = 1
    rw [if_pos rfl, φ.map_one, one_mul, add_zero]
  · exact H.antipode_char φ.1 φ.map_mul

/-- The antipode inverts characters on the left. -/
theorem antipodeComp_conv (φ : H.Character R) :
    (⟨antipodeComp (H := H) φ.1, antipodeComp_isCharacter φ⟩ *
      φ : H.Character R) = 1 := by
  refine ext fun x => ?_
  by_cases hx : x = H.one
  · subst hx
    show ((H.coprod H.one).map fun p =>
      antipodeComp (H := H) φ.1 p.1 * φ p.2).sum = _
    rw [H.coprod_one]
    show antipodeComp (H := H) φ.1 H.one * φ H.one + 0 =
      if H.toCombBialg.isOne H.one then 1 else 0
    rw [(antipodeComp_isCharacter φ).1, φ.map_one, one_mul, add_zero,
      if_pos ((H.toCombBialg.isOne_iff _).mpr rfl)]
  · show ((H.coprod x).map fun p =>
      antipodeComp (H := H) φ.1 p.1 * φ p.2).sum = _
    rw [one_apply, if_neg (fun hb =>
      hx ((H.toCombBialg.isOne_iff x).mp hb))]
    have hkey := H.antipode_conv φ.1 x hx
    refine Eq.trans ?_ hkey
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    show antipodeComp (H := H) φ.1 p.1 * φ p.2 = _
    rw [antipodeComp, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun sa _ => ?_)
    rw [mul_assoc, φ.map_mul]

/-- **The character group**: over a commutative ring, the characters of
a combinatorial Hopf algebra form a group under convolution, with
inverse given by precomposition with the antipode. -/
noncomputable instance instGroup : Group (H.Character R) :=
  { (inferInstance : Monoid (H.Character R)) with
    inv := fun φ =>
      ⟨antipodeComp (H := H) φ.1, antipodeComp_isCharacter φ⟩
    inv_mul_cancel := fun φ => antipodeComp_conv φ }

@[simp]
theorem inv_apply (φ : H.Character R) (x : B) :
    (φ⁻¹ : H.Character R) x = ((H.antipode x).map fun sa =>
      (if sa.1 then (1 : R) else -1) * φ sa.2).sum :=
  rfl

end Group

end Character

end CombHopf

end HopfAlgebras
