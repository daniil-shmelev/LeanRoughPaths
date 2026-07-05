/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Combinatorial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rough paths over a combinatorial Hopf algebra

The abstract `H`-rough path of L. Rahm, *Planar Regularity Structures*
(Found. Comput. Math. 2026), Definition 2.2: a two-parameter family of
**characters** of a combinatorial (Hopf) bialgebra `H`, equal to the
counit on the diagonal and satisfying **Chen's identity** — the
increment over `[s, u]` is the convolution of the increments over
`[s, t]` and `[t, u]`. In our character monoid this is simply

* `increment t t = 1`, and
* `increment s u = increment s t * increment t u`.

This single structure subsumes classical (weakly geometric) rough
paths (`H = wordHopf`, the shuffle algebra of words), branched rough
paths (`H = bckBialg`, Butcher–Connes–Kreimer) and planarly branched
rough paths (`H = mkwBialg`, Munthe-Kaas–Wright) — the identifications
are in `RoughPaths.HopfRoughPathInstances`.

The theory shared by all instances is proved here once:

* coefficient-level Chen expansion (`chen_coeff`), unit and
  multiplicativity of coefficients;
* the constant unit rough path and time reparametrisation;
* **increments are units of the character monoid**: the reverse
  increment is a two-sided convolution inverse, purely from Chen and
  the diagonal identity — no antipode needed
  (`increment_mul_reverse`); over a genuine Hopf algebra the reverse
  increment is the group inverse, i.e. antipode precomposition
  (`increment_reverse_eq_inv`);
* Chen along a chain of intermediate times (`increment_eq_prod`);
* agreement up to a degree, for any grading of the basis
  (`AgreeUpTo`);
* γ-regularity in the sense of Definition 2.2.3: every graded basis
  coefficient is `γ·deg`-Hölder (`IsHolderRegular`).
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z

/-- A **rough path over a combinatorial Hopf algebra** `H` (Rahm,
Definition 2.2, algebraic part): a two-parameter family of characters
of `H` which is the counit on the diagonal and satisfies Chen's
identity, i.e. a multiplicative two-parameter family in the character
monoid of `H`. -/
structure HopfRoughPath {B : Type u} (H : CombBialg.{u, v} B)
    (T : Type w) (R : Type v) [CommSemiring R] where
  /-- The increment character over the interval `[s, t]`. -/
  increment : T → T → H.Character R
  /-- Diagonal increments are the convolution unit (the counit). -/
  identity : ∀ t : T, increment t t = 1
  /-- Chen's identity: convolution of adjacent increments. -/
  chen : ∀ s t u : T, increment s u = increment s t * increment t u

namespace HopfRoughPath

variable {B : Type u} {H : CombBialg.{u, v} B} {T : Type w}
  {R : Type v} [CommSemiring R]

/-- The coefficient of a basis element in an increment. -/
def coeff (X : HopfRoughPath H T R) (s t : T) (x : B) : R :=
  (X.increment s t : B → R) x

@[simp]
theorem coeff_apply (X : HopfRoughPath H T R) (s t : T) (x : B) :
    X.coeff s t x = (X.increment s t : B → R) x :=
  rfl

@[ext]
theorem ext {X Y : HopfRoughPath H T R}
    (h : ∀ s t, X.increment s t = Y.increment s t) : X = Y := by
  cases X
  cases Y
  simp only [mk.injEq]
  funext s t
  exact h s t

theorem ext_coeff {X Y : HopfRoughPath H T R}
    (h : ∀ s t x, X.coeff s t x = Y.coeff s t x) : X = Y :=
  ext fun s t => CombBialg.Character.ext fun x => h s t x

/-- The coefficient of the unit basis element is `1` — the increments
are normalized linear forms. -/
@[simp]
theorem coeff_one (X : HopfRoughPath H T R) (s t : T) :
    X.coeff s t H.one = 1 :=
  (X.increment s t).map_one

/-- Increments are multiplicative on basis products — the linear forms
are characters (Definition 2.2.1). -/
theorem coeff_mul (X : HopfRoughPath H T R) (s t : T) (x y : B) :
    X.coeff s t x * X.coeff s t y =
      ((H.mul x y).map (X.coeff s t)).sum :=
  (X.increment s t).map_mul x y

/-- For a monomial product expansion `mul x y = [z]` — as in the BCK
and MKW forest bialgebras — coefficients are multiplicative on the
product: `⟨X, z⟩ = ⟨X, x⟩·⟨X, y⟩`. -/
theorem coeff_mul_single (X : HopfRoughPath H T R) {x y z : B}
    (h : H.mul x y = [z]) (s t : T) :
    X.coeff s t z = X.coeff s t x * X.coeff s t y := by
  have hm := X.coeff_mul s t x y
  rw [h, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at hm
  exact hm.symm

/-- Diagonal coefficients are the counit. -/
theorem coeff_diagonal (X : HopfRoughPath H T R) (t : T) (x : B) :
    X.coeff t t x = if H.isOne x then 1 else 0 :=
  congrFun (congrArg Subtype.val (X.identity t)) x

/-- **Chen's identity at the level of coefficients**: the coproduct
expansion of the increment over `[s, u]` (Definition 2.2.2). -/
theorem chen_coeff (X : HopfRoughPath H T R) (s t u : T) (x : B) :
    X.coeff s u x =
      ((H.coprod x).map fun p =>
        X.coeff s t p.1 * X.coeff t u p.2).sum :=
  congrFun (congrArg Subtype.val (X.chen s t u)) x

/-! ### The unit rough path and reparametrisation -/

/-- The constant unit rough path: every increment is the counit. -/
noncomputable def unit (H : CombBialg.{u, v} B) (T : Type w) (R : Type v)
    [CommSemiring R] : HopfRoughPath H T R where
  increment _ _ := 1
  identity _ := rfl
  chen _ _ _ := (one_mul 1).symm

@[simp]
theorem unit_increment (s t : T) :
    (unit H T R).increment s t = 1 :=
  rfl

theorem unit_coeff (s t : T) (x : B) :
    (unit H T R).coeff s t x = if H.isOne x then 1 else 0 :=
  rfl

/-- Reparametrise time along a map `f : S → T`. -/
def comapTime {S : Type z} (f : S → T) (X : HopfRoughPath H T R) :
    HopfRoughPath H S R where
  increment s t := X.increment (f s) (f t)
  identity t := X.identity (f t)
  chen s t u := X.chen (f s) (f t) (f u)

@[simp]
theorem comapTime_increment {S : Type z} (f : S → T)
    (X : HopfRoughPath H T R) (s t : S) :
    (X.comapTime f).increment s t = X.increment (f s) (f t) :=
  rfl

@[simp]
theorem coeff_comapTime {S : Type z} (f : S → T)
    (X : HopfRoughPath H T R) (s t : S) (x : B) :
    (X.comapTime f).coeff s t x = X.coeff (f s) (f t) x :=
  rfl

theorem comapTime_id (X : HopfRoughPath H T R) :
    X.comapTime id = X :=
  rfl

theorem comapTime_comp {S : Type z} {U : Type z} (f : S → T)
    (g : U → S) (X : HopfRoughPath H T R) :
    (X.comapTime f).comapTime g = X.comapTime (f ∘ g) :=
  rfl

theorem comapTime_unit {S : Type z} (f : S → T) :
    (unit H T R).comapTime f = unit H S R :=
  rfl

/-! ### Increments are units of the character monoid

The reverse increment is a two-sided convolution inverse, purely from
Chen's identity and the diagonal condition — no antipode is needed. -/

theorem increment_mul_reverse (X : HopfRoughPath H T R) (s t : T) :
    X.increment s t * X.increment t s = 1 := by
  rw [← X.chen s t s, X.identity s]

theorem reverse_mul_increment (X : HopfRoughPath H T R) (s t : T) :
    X.increment t s * X.increment s t = 1 :=
  X.increment_mul_reverse t s

theorem isUnit_increment (X : HopfRoughPath H T R) (s t : T) :
    IsUnit (X.increment s t) :=
  ⟨⟨X.increment s t, X.increment t s, X.increment_mul_reverse s t,
    X.reverse_mul_increment s t⟩, rfl⟩

/-- Over a genuine **Hopf** algebra the reverse increment is the group
inverse of the character group — precomposition with the antipode. -/
theorem increment_reverse_eq_inv {H : CombHopf.{u, v} B}
    {R' : Type v} [CommRing R']
    (X : HopfRoughPath H.toCombBialg T R') (s t : T) :
    X.increment t s = (X.increment s t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (X.reverse_mul_increment s t)

/-! ### Chen along a chain -/

/-- **Chen's identity along a chain of intermediate times**: the
increment over `[s, t]` is the ordered convolution product of the
increments along `s, p₁, …, pₙ, t`. -/
theorem increment_eq_prod (X : HopfRoughPath H T R) :
    ∀ (mid : List T) (s t : T),
      X.increment s t =
        (((s :: mid).zip (mid ++ [t])).map fun q =>
          X.increment q.1 q.2).prod
  | [], s, t => by
      rw [List.nil_append, List.zip_cons_cons, List.zip_nil_left,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
  | m :: mid, s, t => by
      rw [List.cons_append, List.zip_cons_cons, List.map_cons,
        List.prod_cons, ← increment_eq_prod X mid m t, ← X.chen s m t]

/-! ### Agreement up to a degree -/

/-- Two Hopf rough paths agree up to degree `n`, with respect to a
grading `deg` of the basis. -/
def AgreeUpTo (deg : B → ℕ) (X Y : HopfRoughPath H T R) (n : ℕ) :
    Prop :=
  ∀ s t, ∀ x : B, deg x ≤ n → X.coeff s t x = Y.coeff s t x

theorem agreeUpTo_refl (deg : B → ℕ) (X : HopfRoughPath H T R)
    (n : ℕ) : AgreeUpTo deg X X n :=
  fun _ _ _ _ => rfl

theorem AgreeUpTo.symm {deg : B → ℕ} {X Y : HopfRoughPath H T R}
    {n : ℕ} (h : AgreeUpTo deg X Y n) : AgreeUpTo deg Y X n :=
  fun s t x hx => (h s t x hx).symm

theorem AgreeUpTo.trans {deg : B → ℕ} {X Y Z : HopfRoughPath H T R}
    {n : ℕ} (h₁ : AgreeUpTo deg X Y n) (h₂ : AgreeUpTo deg Y Z n) :
    AgreeUpTo deg X Z n :=
  fun s t x hx => (h₁ s t x hx).trans (h₂ s t x hx)

theorem AgreeUpTo.mono {deg : B → ℕ} {X Y : HopfRoughPath H T R}
    {m n : ℕ} (hmn : m ≤ n) (h : AgreeUpTo deg X Y n) :
    AgreeUpTo deg X Y m :=
  fun s t x hx => h s t x (hx.trans hmn)

theorem AgreeUpTo.comapTime {S : Type z} {deg : B → ℕ}
    {X Y : HopfRoughPath H T R} {n : ℕ} (f : S → T)
    (h : AgreeUpTo deg X Y n) :
    AgreeUpTo deg (X.comapTime f) (Y.comapTime f) n :=
  fun s t x hx => h (f s) (f t) x hx

theorem eq_of_agreeUpTo_all {deg : B → ℕ}
    {X Y : HopfRoughPath H T R}
    (h : ∀ n, AgreeUpTo deg X Y n) : X = Y :=
  ext_coeff fun s t x => h (deg x) s t x le_rfl

/-! ### γ-regularity (Definition 2.2.3) -/

section Regularity

variable {B₀ : Type u} {H₀ : CombBialg.{u, 0} B₀}

/-- A Hopf rough path over the real line is **`γ`-regular** for a
grading `deg` of the basis when every basis coefficient is
`γ·deg`-Hölder: `|⟨X_{st}, x⟩| ≤ C_x·|t - s|^{γ·|x|}`. This is
condition 3 of Definition 2.2 (the finite-supremum form, stated as the
existence of a constant per basis element). -/
def IsHolderRegular (X : HopfRoughPath H₀ ℝ ℝ) (deg : B₀ → ℕ)
    (γ : ℝ) : Prop :=
  ∀ x : B₀, ∃ C : ℝ, ∀ s t : ℝ,
    |X.coeff s t x| ≤ C * |t - s| ^ (γ * (deg x : ℝ))

/-- The unit rough path is `γ`-regular for every grading that puts the
unit basis element in degree zero. -/
theorem unit_isHolderRegular {deg : B₀ → ℕ} (h1 : deg H₀.one = 0)
    (γ : ℝ) : (unit H₀ ℝ ℝ).IsHolderRegular deg γ := by
  intro x
  refine ⟨1, fun s t => ?_⟩
  show |(if H₀.isOne x then (1 : ℝ) else 0)| ≤ _
  by_cases hx : H₀.isOne x = true
  · rw [if_pos hx, (H₀.isOne_iff x).mp hx, h1]
    rw [Nat.cast_zero, mul_zero, Real.rpow_zero, abs_one, mul_one]
  · rw [if_neg hx, abs_zero, one_mul]
    exact Real.rpow_nonneg (abs_nonneg _) _

/-- γ-regularity is inherited along contracting reparametrisations of
the line; in particular it is invariant under restriction. -/
theorem IsHolderRegular.comapTime {X : HopfRoughPath H₀ ℝ ℝ}
    {deg : B₀ → ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (f : ℝ → ℝ) (hf : ∀ s t, |f t - f s| ≤ |t - s|)
    (h : X.IsHolderRegular deg γ) :
    (X.comapTime f).IsHolderRegular deg γ := by
  intro x
  obtain ⟨C, hC⟩ := h x
  by_cases hCpos : 0 ≤ C
  · refine ⟨C, fun s t => ?_⟩
    refine (hC (f s) (f t)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (hf s t)
        (mul_nonneg hγ (Nat.cast_nonneg _))) hCpos
  · refine ⟨0, fun s t => ?_⟩
    refine (hC (f s) (f t)).trans ?_
    rw [zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hCpos)
      (Real.rpow_nonneg (abs_nonneg _) _)

end Regularity

end HopfRoughPath

end RoughPaths
