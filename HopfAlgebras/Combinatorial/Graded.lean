/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Combinatorial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Graded combinatorial bialgebras: the character group

A **connected grading** on a combinatorial bialgebra `H` (as in
Definition 2.1 of Rahm, *Planar Regularity Structures*): a degree
function on the basis for which the unit is the unique degree-zero
element, degrees add along the product expansion, and every coproduct
term splits the degree.

The main theorem is the classical one: **over a connected graded
bialgebra the characters form a group** under convolution
(`CombBialg.Grading.characterGroup`) — no antipode is needed. The
inverse is the geometric series `φ⁻¹ = ∑ₖ (ε − φ)^{*k}`, a finite sum
in each degree because `(ε − φ)^{*k}` vanishes below degree `k`
(`convPow_vanish`); the convolution-inverse identities follow by
telescoping (`conv_gradedInv`, `gradedInv_conv`), and multiplicativity
of the inverse (`gradedInv_isCharacter`) by strong induction on total
degree, splitting the counit as `ε = φ + (ε − φ)` and extracting the
diagonal with the counit laws.

This equips the characters of the BCK, labelled BCK and MKW forest
bialgebras with group structure (see
`HopfAlgebras.Combinatorial.GradedInstances`).
-/

namespace HopfAlgebras

universe u v

variable {B : Type u}

namespace CombBialg

/-- A **connected grading** of a combinatorial bialgebra: the unit is
the unique basis element of degree zero, degrees are additive along the
product expansion, and each coproduct term splits the degree. -/
structure Grading (H : CombBialg.{u, v} B) where
  /-- The degree of a basis element. -/
  deg : B → ℕ
  /-- Connectedness: the unit is the only degree-zero element. -/
  deg_eq_zero_iff : ∀ x, deg x = 0 ↔ x = H.one
  /-- Coproduct terms split the degree. -/
  deg_coprod : ∀ x : B, ∀ p ∈ H.coprod x, deg p.1 + deg p.2 = deg x
  /-- Degrees are additive along the product expansion. -/
  deg_mul : ∀ x y : B, ∀ z ∈ H.mul x y, deg z = deg x + deg y

variable {R : Type v}

/-- Convolution powers of a functional, with the counit as the zeroth
power. -/
def convPow (H : CombBialg.{u, v} B) [CommSemiring R] (φ : B → R) :
    ℕ → B → R
  | 0 => Character.counit (H := H)
  | k + 1 => Character.conv (H := H) φ (convPow H φ k)

/-- The counit defect `ε − φ` of a functional. -/
def counitSub (H : CombBialg.{u, v} B) [CommRing R] (φ : B → R) :
    B → R :=
  fun x => Character.counit (H := H) x - φ x

namespace Grading

variable {H : CombBialg.{u, v} B} (G : H.Grading)

/-! ### Sum plumbing -/

private theorem sum_map_sub {β : Type*} [CommRing R]
    (l : List β) (f g : β → R) :
    (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons]
      ring

private theorem sum_map_finsetSum {β : Type*} [CommRing R]
    (l : List β) (s : Finset ℕ) (F : ℕ → β → R) :
    (l.map fun a => ∑ k ∈ s, F k a).sum =
      ∑ k ∈ s, (l.map fun a => F k a).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-! ### Degree bookkeeping -/

theorem deg_one : G.deg H.one = 0 :=
  (G.deg_eq_zero_iff H.one).mpr rfl

theorem deg_pos_of_ne_one {x : B} (hx : x ≠ H.one) : 0 < G.deg x :=
  Nat.pos_of_ne_zero fun hz => hx ((G.deg_eq_zero_iff x).mp hz)

/-! ### Vanishing of convolution powers -/

/-- If `φ` kills the unit, its `k`-th convolution power vanishes below
degree `k`. -/
theorem convPow_vanish [CommSemiring R] {φ : B → R}
    (hφ0 : φ H.one = 0) :
    ∀ k, ∀ x : B, G.deg x < k → H.convPow φ k x = 0
  | 0, x, h => absurd h (Nat.not_lt_zero _)
  | k + 1, x, h => by
      show ((H.coprod x).map fun p =>
        φ p.1 * H.convPow φ k p.2).sum = 0
      refine List.sum_eq_zero fun r hr => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      by_cases h1 : p.1 = H.one
      · rw [h1, hφ0, zero_mul]
      · have hlt : G.deg p.2 < k := by
          have hsum := G.deg_coprod x p hp
          have hpos := G.deg_pos_of_ne_one h1
          omega
        rw [convPow_vanish hφ0 k p.2 hlt, mul_zero]

/-! ### The geometric-series inverse -/

/-- The convolution inverse of a character over a connected graded
bialgebra: the geometric series `∑ₖ (ε − φ)^{*k}`, truncated at the
degree of the argument. -/
noncomputable def gradedInv [CommRing R] (φ : B → R) : B → R :=
  fun x => ∑ k ∈ Finset.range (G.deg x + 1), H.convPow (H.counitSub φ) k x

section CommRing

variable [CommRing R] {φ : B → R}

theorem counitSub_one (hφ1 : φ H.one = 1) :
    H.counitSub φ H.one = 0 := by
  show Character.counit (H := H) H.one - φ H.one = 0
  rw [hφ1]
  show (if H.isOne H.one then (1 : R) else 0) - 1 = 0
  rw [if_pos ((H.isOne_iff H.one).mpr rfl), sub_self]

/-- The truncation in `gradedInv` can be extended to any bound on the
degree. -/
theorem gradedInv_eq_sum (hφ1 : φ H.one = 1) {x : B} {n : ℕ}
    (hn : G.deg x ≤ n) :
    G.gradedInv φ x =
      ∑ k ∈ Finset.range (n + 1), H.convPow (H.counitSub φ) k x := by
  refine Finset.sum_subset
    (fun k hk => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hn)))
    fun k _ hk' => ?_
  rw [Finset.mem_range] at hk'
  exact G.convPow_vanish (counitSub_one hφ1) k x (by omega)

/-- Convolution with the counit on the left is the identity. -/
theorem conv_counit_left (F : B → R) :
    Character.conv (H := H) (Character.counit (H := H)) F = F :=
  funext fun x => H.counit_left F x

/-- Convolution with the counit on the right is the identity. -/
theorem conv_counit_right (F : B → R) :
    Character.conv (H := H) F (Character.counit (H := H)) = F :=
  funext fun x => H.counit_right F x

/-- Convolution is associative on arbitrary functionals. -/
theorem conv_assoc (f g h : B → R) :
    Character.conv (H := H) (Character.conv (H := H) f g) h =
      Character.conv (H := H) f (Character.conv (H := H) g h) :=
  funext fun x => H.coassoc f g h x

/-- `φ` commutes with its own convolution powers. -/
theorem conv_convPow_comm (φ : B → R) :
    ∀ k, Character.conv (H := H) φ (H.convPow φ k) =
      Character.conv (H := H) (H.convPow φ k) φ
  | 0 => by
      show Character.conv (H := H) φ (Character.counit (H := H)) =
        Character.conv (H := H) (Character.counit (H := H)) φ
      rw [conv_counit_right, conv_counit_left]
  | k + 1 => by
      show Character.conv (H := H) φ
          (Character.conv (H := H) φ (H.convPow φ k)) =
        Character.conv (H := H)
          (Character.conv (H := H) φ (H.convPow φ k)) φ
      rw [conv_convPow_comm φ k, ← conv_assoc, conv_convPow_comm φ k]

private theorem conv_sub_left (f g h : B → R) (x : B) :
    Character.conv (H := H) (fun z => f z - g z) h x =
      Character.conv (H := H) f h x - Character.conv (H := H) g h x := by
  show ((H.coprod x).map fun p => (f p.1 - g p.1) * h p.2).sum = _
  rw [show (fun p : B × B => (f p.1 - g p.1) * h p.2) =
    (fun p : B × B => f p.1 * h p.2 - g p.1 * h p.2) from
    funext fun p => sub_mul _ _ _]
  exact sum_map_sub _ _ _

private theorem conv_sub_right (f g h : B → R) (x : B) :
    Character.conv (H := H) f (fun z => g z - h z) x =
      Character.conv (H := H) f g x - Character.conv (H := H) f h x := by
  show ((H.coprod x).map fun p => f p.1 * (g p.2 - h p.2)).sum = _
  rw [show (fun p : B × B => f p.1 * (g p.2 - h p.2)) =
    (fun p : B × B => f p.1 * g p.2 - f p.1 * h p.2) from
    funext fun p => mul_sub _ _ _]
  exact sum_map_sub _ _ _

/-- Telescoping sum: `∑_{k ≤ n} (aₖ − aₖ₊₁) = a₀ − aₙ₊₁`. -/
private theorem sum_range_telescope (a : ℕ → R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), a k -
      ∑ k ∈ Finset.range (n + 1), a (k + 1) = a 0 - a (n + 1) := by
  rw [Finset.sum_range_succ' a n, Finset.sum_range_succ (fun k => a (k + 1)) n]
  ring

/-- **Left inverse identity**: `φ * φ⁻¹ = ε` for a character `φ`. -/
theorem conv_gradedInv (hφ : H.IsCharacter φ) :
    Character.conv (H := H) φ (G.gradedInv φ) =
      Character.counit (H := H) := by
  funext x
  have hη0 : H.counitSub φ H.one = 0 := counitSub_one hφ.1
  -- φ = ε − (ε − φ), applied in the left slot only
  have hsub := conv_sub_left (H := H) (Character.counit (H := H))
    (H.counitSub φ) (G.gradedInv φ) x
  have hfun : (fun z => Character.counit (H := H) z -
      H.counitSub φ z) = φ := funext fun z => by
    show Character.counit (H := H) z -
      (Character.counit (H := H) z - φ z) = φ z
    ring
  rw [hfun] at hsub
  rw [hsub, congrFun (conv_counit_left (G.gradedInv φ)) x]
  -- expand the inverse under the η-convolution, uniformly truncated
  have hstep : Character.conv (H := H) (H.counitSub φ)
      (G.gradedInv φ) x =
      ∑ k ∈ Finset.range (G.deg x + 1),
        H.convPow (H.counitSub φ) (k + 1) x := by
    show ((H.coprod x).map fun p =>
      H.counitSub φ p.1 * G.gradedInv φ p.2).sum = _
    rw [List.map_congr_left (fun p hp => by
      rw [G.gradedInv_eq_sum hφ.1 (n := G.deg x)
        (by have := G.deg_coprod x p hp; omega), Finset.mul_sum])]
    rw [sum_map_finsetSum]
    rfl
  rw [hstep]
  have htel := sum_range_telescope
    (fun k => H.convPow (H.counitSub φ) k x) (G.deg x)
  have hvan : H.convPow (H.counitSub φ) (G.deg x + 1) x = 0 :=
    G.convPow_vanish hη0 _ x (by omega)
  rw [hvan] at htel
  rw [show G.gradedInv φ x = ∑ k ∈ Finset.range (G.deg x + 1),
    H.convPow (H.counitSub φ) k x from rfl, htel]
  show Character.counit (H := H) x - 0 = _
  rw [sub_zero]

/-- **Right inverse identity**: `φ⁻¹ * φ = ε` for a character `φ`. -/
theorem gradedInv_conv (hφ : H.IsCharacter φ) :
    Character.conv (H := H) (G.gradedInv φ) φ =
      Character.counit (H := H) := by
  funext x
  have hη0 : H.counitSub φ H.one = 0 := counitSub_one hφ.1
  have hsub := conv_sub_right (H := H) (G.gradedInv φ)
    (Character.counit (H := H)) (H.counitSub φ) x
  have hfun : (fun z => Character.counit (H := H) z -
      H.counitSub φ z) = φ := funext fun z => by
    show Character.counit (H := H) z -
      (Character.counit (H := H) z - φ z) = φ z
    ring
  rw [hfun] at hsub
  rw [hsub, congrFun (conv_counit_right (G.gradedInv φ)) x]
  have hstep : Character.conv (H := H) (G.gradedInv φ)
      (H.counitSub φ) x =
      ∑ k ∈ Finset.range (G.deg x + 1),
        H.convPow (H.counitSub φ) (k + 1) x := by
    show ((H.coprod x).map fun p =>
      G.gradedInv φ p.1 * H.counitSub φ p.2).sum = _
    rw [List.map_congr_left (fun p hp => by
      rw [G.gradedInv_eq_sum hφ.1 (n := G.deg x)
        (by have := G.deg_coprod x p hp; omega), Finset.sum_mul])]
    rw [sum_map_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((H.coprod x).map fun p =>
      H.convPow (H.counitSub φ) k p.1 * H.counitSub φ p.2).sum = _
    have := congrFun (conv_convPow_comm (H := H) (H.counitSub φ) k) x
    exact this.symm.trans rfl
  rw [hstep]
  have htel := sum_range_telescope
    (fun k => H.convPow (H.counitSub φ) k x) (G.deg x)
  have hvan : H.convPow (H.counitSub φ) (G.deg x + 1) x = 0 :=
    G.convPow_vanish hη0 _ x (by omega)
  rw [hvan] at htel
  rw [show G.gradedInv φ x = ∑ k ∈ Finset.range (G.deg x + 1),
    H.convPow (H.counitSub φ) k x from rfl, htel]
  show Character.counit (H := H) x - 0 = _
  rw [sub_zero]

/-- The inverse takes the value `1` on the unit. -/
theorem gradedInv_one :
    G.gradedInv φ H.one = 1 := by
  show ∑ k ∈ Finset.range (G.deg H.one + 1),
    H.convPow (H.counitSub φ) k H.one = 1
  rw [G.deg_one, Finset.sum_range_one]
  show (if H.isOne H.one then (1 : R) else 0) = 1
  rw [if_pos ((H.isOne_iff H.one).mpr rfl)]

/-! ### Multiplicativity of the inverse -/

/-- **The inverse of a character is a character.** Proved by strong
induction on total degree: the counit splits as `ε = φ + (ε − φ)`, the
`φφ`-part collapses by the bialgebra axiom and the inverse identities,
every term containing an `ε − φ` factor dies by the inductive
hypothesis, and the `εε`-part extracts the claim via the counit laws. -/
theorem gradedInv_isCharacter (hφ : H.IsCharacter φ) :
    H.IsCharacter (G.gradedInv φ) := by
  constructor
  · exact G.gradedInv_one
  · -- multiplicativity, by strong induction on `deg x + deg y`
    suffices hD : ∀ n, ∀ x y : B, G.deg x + G.deg y ≤ n →
        ((H.mul x y).map (G.gradedInv φ)).sum =
          G.gradedInv φ x * G.gradedInv φ y by
      intro x y
      exact (hD (G.deg x + G.deg y) x y le_rfl).symm
    intro n
    induction n with
    | zero =>
        intro x y hxy
        have hx : x = H.one := (G.deg_eq_zero_iff x).mp (by omega)
        have hy : y = H.one := (G.deg_eq_zero_iff y).mp (by omega)
        subst hx; subst hy
        rw [H.mul_one_expand H.one, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero,
          G.gradedInv_one, one_mul]
    | succ n ih =>
        intro x y hxy
        by_cases h : G.deg x + G.deg y ≤ n
        · exact ih x y h
        · -- the critical case `deg x + deg y = n + 1`
          set ψ := G.gradedInv φ with hψ
          set η := H.counitSub φ with hη
          -- the defect of multiplicativity
          set D : B → B → R := fun u v =>
            ((H.mul u v).map ψ).sum - ψ u * ψ v with hD
          -- every defect of smaller total degree vanishes
          have hIH : ∀ u v : B, G.deg u + G.deg v ≤ n → D u v = 0 := by
            intro u v huv
            show _ - _ = 0
            rw [ih u v huv, sub_self]
          -- Step 1: the φφ-weighted defect sum vanishes
          have hkey : ((H.coprod x).map fun p =>
              ((H.coprod y).map fun q =>
                φ p.1 * φ q.1 * D p.2 q.2).sum).sum = 0 := by
            have h1 : ((H.coprod x).map fun p =>
                ((H.coprod y).map fun q =>
                  φ p.1 * φ q.1 * ((H.mul p.2 q.2).map ψ).sum).sum).sum =
                Character.counit (H := H) x *
                  Character.counit (H := H) y := by
              have hstep1 : ((H.coprod x).map fun p =>
                  ((H.coprod y).map fun q =>
                    φ p.1 * φ q.1 * ((H.mul p.2 q.2).map ψ).sum).sum).sum =
                  ((H.coprod x).map fun p =>
                    ((H.coprod y).map fun q =>
                      ((H.mul p.1 q.1).map φ).sum *
                        ((H.mul p.2 q.2).map ψ).sum).sum).sum := by
                refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
                refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
                rw [hφ.2 p.1 q.1]
              rw [hstep1, ← H.bialg φ ψ x y]
              have hconv : (fun z => ((H.coprod z).map fun r =>
                  φ r.1 * ψ r.2).sum) = Character.counit (H := H) := by
                have := G.conv_gradedInv hφ
                exact this
              rw [show (fun z : B => ((H.coprod z).map fun r =>
                φ r.1 * ψ r.2).sum) = Character.counit (H := H) from hconv]
              exact H.mul_count_one x y
            have h2 : ((H.coprod x).map fun p =>
                ((H.coprod y).map fun q =>
                  φ p.1 * φ q.1 * (ψ p.2 * ψ q.2)).sum).sum =
                Character.counit (H := H) x *
                  Character.counit (H := H) y := by
              have hfac : ((H.coprod x).map fun p =>
                  ((H.coprod y).map fun q =>
                    φ p.1 * φ q.1 * (ψ p.2 * ψ q.2)).sum).sum =
                  ((H.coprod x).map fun p => φ p.1 * ψ p.2).sum *
                    ((H.coprod y).map fun q => φ q.1 * ψ q.2).sum := by
                rw [← List.sum_map_mul_right]
                refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
                rw [← List.sum_map_mul_left]
                refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
                ring
              rw [hfac]
              have hx' := congrFun (G.conv_gradedInv hφ) x
              have hy' := congrFun (G.conv_gradedInv hφ) y
              rw [show ((H.coprod x).map fun p =>
                  φ p.1 * ψ p.2).sum = Character.counit (H := H) x from hx',
                show ((H.coprod y).map fun q =>
                  φ q.1 * ψ q.2).sum = Character.counit (H := H) y from hy']
            calc ((H.coprod x).map fun p => ((H.coprod y).map fun q =>
                φ p.1 * φ q.1 * D p.2 q.2).sum).sum
                = ((H.coprod x).map fun p => ((H.coprod y).map fun q =>
                    φ p.1 * φ q.1 * ((H.mul p.2 q.2).map ψ).sum).sum).sum -
                  ((H.coprod x).map fun p => ((H.coprod y).map fun q =>
                    φ p.1 * φ q.1 * (ψ p.2 * ψ q.2)).sum).sum := by
                  rw [← sum_map_sub]
                  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
                  rw [← sum_map_sub]
                  refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
                  show φ p.1 * φ q.1 * D p.2 q.2 = _
                  rw [hD]
                  ring
              _ = 0 := by rw [h1, h2, sub_self]
          -- Step 2: terms with an `η` factor die by induction
          have hkill : ∀ (p q : B × B), p ∈ H.coprod x → q ∈ H.coprod y →
              (p.1 ≠ H.one ∨ q.1 ≠ H.one) → D p.2 q.2 = 0 := by
            intro p q hp hq hne
            refine hIH p.2 q.2 ?_
            have hp' := G.deg_coprod x p hp
            have hq' := G.deg_coprod y q hq
            rcases hne with h1 | h1
            · have := G.deg_pos_of_ne_one h1
              omega
            · have := G.deg_pos_of_ne_one h1
              omega
          -- Step 3: extract the diagonal defect via the counit split
          -- `ε(p₁)ε(q₁) = (φ + η)(p₁)(φ + η)(q₁)`
          have hsplit : D x y = ((H.coprod x).map fun p =>
              ((H.coprod y).map fun q =>
                φ p.1 * φ q.1 * D p.2 q.2).sum).sum := by
            -- first: the εε-weighted sum extracts `D x y`
            have hextract : ((H.coprod x).map fun p =>
                ((H.coprod y).map fun q =>
                  (if H.isOne p.1 then (1 : R) else 0) *
                    (if H.isOne q.1 then (1 : R) else 0) *
                      D p.2 q.2).sum).sum = D x y := by
              have hinner : ∀ p ∈ H.coprod x,
                  ((H.coprod y).map fun q =>
                    (if H.isOne p.1 then (1 : R) else 0) *
                      (if H.isOne q.1 then (1 : R) else 0) *
                        D p.2 q.2).sum =
                  (if H.isOne p.1 then (1 : R) else 0) * D p.2 y := by
                intro p _
                rw [show (fun q : B × B =>
                    (if H.isOne p.1 then (1 : R) else 0) *
                      (if H.isOne q.1 then (1 : R) else 0) * D p.2 q.2) =
                    (fun q : B × B =>
                      (if H.isOne p.1 then (1 : R) else 0) *
                        ((if H.isOne q.1 then (1 : R) else 0) *
                          D p.2 q.2)) from funext fun q => mul_assoc _ _ _]
                rw [List.sum_map_mul_left]
                rw [H.counit_left (fun b => D p.2 b) y]
              rw [List.map_congr_left hinner]
              exact H.counit_left (fun b => D b y) x
            -- next: replace each ε by `φ + η` and kill the η-parts
            have hper : ∀ p ∈ H.coprod x, ∀ q ∈ H.coprod y,
                (if H.isOne p.1 then (1 : R) else 0) *
                  (if H.isOne q.1 then (1 : R) else 0) * D p.2 q.2 =
                φ p.1 * φ q.1 * D p.2 q.2 := by
              intro p hp q hq
              by_cases h1 : p.1 = H.one
              · by_cases h2 : q.1 = H.one
                · rw [h1, h2, if_pos ((H.isOne_iff H.one).mpr rfl),
                    hφ.1]
                · have hd : D p.2 q.2 = 0 :=
                    hkill p q hp hq (Or.inr h2)
                  rw [hd, mul_zero, mul_zero]
              · have hd : D p.2 q.2 = 0 :=
                  hkill p q hp hq (Or.inl h1)
                rw [hd, mul_zero, mul_zero]
            rw [← hextract]
            refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
            exact congrArg List.sum
              (List.map_congr_left fun q hq => hper p hp q hq)
          -- conclude
          have : D x y = 0 := by rw [hsplit, hkey]
          exact sub_eq_zero.mp this

end CommRing

/-! ### The character group -/

/-- **The character group of a connected graded combinatorial
bialgebra**: characters form a group under convolution, with the
geometric-series inverse. -/
@[reducible] noncomputable def characterGroup [CommRing R] :
    Group (H.Character R) :=
  { Character.instMonoid with
    inv := fun φ => ⟨G.gradedInv φ.1, G.gradedInv_isCharacter φ.2⟩
    inv_mul_cancel := fun φ => Subtype.ext (G.gradedInv_conv φ.2) }

include G in
/-- Every character of a connected graded combinatorial bialgebra is a
unit of the convolution monoid. -/
theorem isUnit_character [CommRing R] (φ : H.Character R) :
    IsUnit φ := by
  letI := G.characterGroup (R := R)
  exact Group.isUnit φ

end Grading

end CombBialg

end HopfAlgebras
