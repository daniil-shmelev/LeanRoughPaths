/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.RDE.ItoLyons

/-!
# Explicit Picard parameters

The arithmetic side of RDE well-posedness: for every `C³_b` vector field
there **exist** box constants, contraction weights, a window size `δα`
and an offset constant `Koff` satisfying all the side conditions of the
Picard theory — the box-closure inequalities of `picardMap_inBox` and
the weighted contraction of the distance step, in its two-driver form
with a `(ρ₁+ρ₂)`-linear offset (`PicardParams.contr`).

The construction is hierarchical: the structural (non-`δα`) couplings of
the distance step form the acyclic chain `a → b → e → c`, so the weights
are solved greedily (`wc = 1`, then `we`, `wb`, `wa`) and every residual
coupling carries a factor `δα`, absorbed by choosing `δα` as the inverse
of the total residual coefficient.

`pT`/`pR…` below are the coefficients of the distance-step slots
collected as linear forms in the certificate tuple `(a,b,c,e,ρ₁,ρ₂)`;
the bridge to the literal slot formulas of `solutionDriverStep` and
`picardDist` is pure `ring` and is performed in the well-posedness
wrappers.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ} {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace RDEVectorField3

/-! ### Collected coefficients of the distance step at box constants -/

/-- `a`-coefficient of the germ-constant block `mixedRoughConstN`. -/
noncomputable def pTa (V : RDEVectorField3 d E) (Bb Bd By : ℝ≥0) : ℝ≥0 :=
  d * (V.C3 * (d * Bb + By) ^ 2 + V.C2 * By) +
    d ^ 2 * (V.C2 * Bd + V.C3 * Bb * (d * Bb + By))

/-- `b`-coefficient of the germ-constant block. -/
noncomputable def pTb (V : RDEVectorField3 d E) (Bb By : ℝ≥0) : ℝ≥0 :=
  d ^ 2 * (2 * V.C2 * (d * Bb + By) + V.C3 * (d * Bb + By) ^ 2) +
    d ^ 2 * V.C2 * (d * Bb + By) +
    d ^ 3 * (V.C2 + V.C3 * (d * Bb + By)) * Bb

/-- `c`-coefficient of the germ-constant block. -/
noncomputable def pTc (V : RDEVectorField3 d E) : ℝ≥0 :=
  d ^ 2 * V.C1

/-- `e`-coefficient of the germ-constant block. -/
noncomputable def pTe (V : RDEVectorField3 d E) (Bb By : ℝ≥0) : ℝ≥0 :=
  d * (2 * V.C2 * (d * Bb + By) + V.C3 * (d * Bb + By) ^ 2) + d * V.C1 +
    d ^ 2 * (V.C2 + V.C3 * (d * Bb + By)) * Bb

/-- `ρ₁`-coefficient of the germ-constant block. -/
noncomputable def pTr1 (V : RDEVectorField3 d E) (Bb By : ℝ≥0) : ℝ≥0 :=
  d ^ 2 * Bb * (2 * V.C2 * (d * Bb + By) + V.C3 * (d * Bb + By) ^ 2) +
    d * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2) +
    d ^ 3 * (V.C2 + V.C3 * (d * Bb + By)) * Bb ^ 2

/-- `ρ₂`-coefficient of the germ-constant block. -/
noncomputable def pTr2 (V : RDEVectorField3 d E) (Bb Bd By : ℝ≥0) : ℝ≥0 :=
  d ^ 2 * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By))

/-- The germ-constant block `mixedRoughConstN` of the composed distance,
collected as a linear form of the certificate tuple. -/
noncomputable def pT (V : RDEVectorField3 d E) (Bb Bd By : ℝ≥0)
    (a b c e ρ₁ ρ₂ : ℝ≥0) : ℝ≥0 :=
  V.pTa Bb Bd By * a + V.pTb Bb By * b + V.pTc * c + V.pTe Bb By * e +
    V.pTr1 Bb By * ρ₁ + V.pTr2 Bb Bd By * ρ₂

/-- `a`-coefficient of the derivative-Hölder slot. -/
noncomputable def pRa (V : RDEVectorField3 d E) (Bb By : ℝ≥0) : ℝ≥0 :=
  d * V.C2 * Bb + V.C3 * (d * Bb + By) ^ 2 + V.C2 * By

/-- `b`-coefficient of the derivative-Hölder slot. -/
noncomputable def pRb (V : RDEVectorField3 d E) (Bb By : ℝ≥0) : ℝ≥0 :=
  d * V.C1 + d * (2 * V.C2 * (d * Bb + By) + V.C3 * (d * Bb + By) ^ 2)

/-- `e`-coefficient of the derivative-Hölder slot. -/
noncomputable def pRe (V : RDEVectorField3 d E) (Bb By : ℝ≥0) : ℝ≥0 :=
  2 * V.C2 * (d * Bb + By) + V.C3 * (d * Bb + By) ^ 2 + V.C1

/-- `ρ₁`-coefficient of the derivative-Hölder slot. -/
noncomputable def pRr1 (V : RDEVectorField3 d E) (Bb By : ℝ≥0) : ℝ≥0 :=
  d * V.C1 * Bb + d * Bb * (2 * V.C2 * (d * Bb + By) + V.C3 * (d * Bb + By) ^ 2)

/-! ### The distance-step slot formulas at box constants -/

/-- The remainder slot of the composed mixed distance (`compMixedDist`)
at box constants. -/
noncomputable def pCMy (V : RDEVectorField3 d E) (Bb By : ℝ≥0)
    (a b e ρ₁ : ℝ≥0) : ℝ≥0 :=
  V.C2 * (d * (b + ρ₁ * Bb) + e) * ((d * Bb + By) + (d * Bb + By)) +
    V.C3 * (a + (d * (b + ρ₁ * Bb) + e)) * (d * Bb + By) ^ 2 +
    V.C1 * e + V.C2 * a * By

/-- The derivative-Hölder slot of the composed mixed distance at box
constants. -/
noncomputable def pCMd (V : RDEVectorField3 d E) (Bb Bd By : ℝ≥0)
    (a b c e ρ₁ : ℝ≥0) : ℝ≥0 :=
  V.C1 * c + V.C2 * a * Bd + V.C2 * (d * Bb + By) * b +
    (V.C2 * (d * (b + ρ₁ * Bb) + e) +
      V.C3 * (a + (d * (b + ρ₁ * Bb) + e)) * (d * Bb + By)) * Bb

/-- The mixed germ constant `mixedRoughConstN` of the composed distance
at box constants. -/
noncomputable def pRCN (V : RDEVectorField3 d E) (Bb Bd By : ℝ≥0)
    (a b c e ρ₁ ρ₂ : ℝ≥0) : ℝ≥0 :=
  d * (V.pCMy Bb By a b e ρ₁ +
      ρ₁ * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2)) +
    d ^ 2 * (V.pCMd Bb Bd By a b c e ρ₁ +
      ρ₂ * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By)))

/-- The sup slot of the two-driver distance step at box constants. -/
noncomputable def pS0 (V : RDEVectorField3 d E) (Bb Bd By K δα : ℝ≥0)
    (a b c e ρ₁ ρ₂ : ℝ≥0) : ℝ≥0 :=
  (d * (V.C1 * a + ρ₁ * V.C0) +
    d ^ 2 * ((V.C1 * b + V.C2 * a * Bb) + ρ₂ * (V.C1 * Bb)) +
    K * V.pRCN Bb Bd By a b c e ρ₁ ρ₂) * δα

/-- The derivative-Hölder slot of the two-driver distance step at box
constants. -/
noncomputable def pSc (V : RDEVectorField3 d E) (Bb By : ℝ≥0)
    (a b e ρ₁ : ℝ≥0) : ℝ≥0 :=
  d * ((V.C1 * b + V.C2 * a * Bb) + ρ₁ * (V.C1 * Bb)) +
    V.pCMy Bb By a b e ρ₁

/-- The remainder slot of the two-driver distance step at box
constants. -/
noncomputable def pSe (V : RDEVectorField3 d E) (Bb Bd By K δα : ℝ≥0)
    (a b c e ρ₁ ρ₂ : ℝ≥0) : ℝ≥0 :=
  K * V.pRCN Bb Bd By a b c e ρ₁ ρ₂ * δα +
    d ^ 2 * ((V.C1 * b + V.C2 * a * Bb) + ρ₂ * (V.C1 * Bb))

/-- A full set of Picard parameters for the vector field `V` at Hölder
exponent `α`: box constants closed under the Picard map, hierarchical
contraction weights, a window size and a driver-distance offset. The
`contr` field is the weighted contraction of the (two-driver) distance
step, stated against the collected slot coefficients; at
`ρ₁ = ρ₂ = 0` it is the contraction hypothesis of `rde_exists` and
`rde_unique`, and in general it feeds `itoLyons_dist_le`. -/
structure PicardParams (V : RDEVectorField3 d E) (α : ℝ) where
  /-- Box constant for the derivative sup. -/
  Bb : ℝ≥0
  /-- Box constant for the derivative Hölder norm. -/
  Bd : ℝ≥0
  /-- Box constant for the remainder. -/
  By : ℝ≥0
  /-- Weight of the sup slot. -/
  wa : ℝ≥0
  /-- Weight of the derivative-sup slot. -/
  wb : ℝ≥0
  /-- Weight of the derivative-Hölder slot. -/
  wc : ℝ≥0
  /-- Weight of the remainder slot. -/
  we : ℝ≥0
  /-- The window size. -/
  δα : ℝ≥0
  /-- The driver-distance offset. -/
  Koff : ℝ≥0
  wa_pos : 0 < wa
  δα_pos : 0 < δα
  δα_le_one : δα ≤ 1
  box_b : V.C0 ≤ Bb
  box_d : V.C1 * (d * Bb + By) ≤ Bd
  box_y : (Sewing.sewingConst (3 * α)).toNNReal *
      (d * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2) +
        d ^ 2 * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By))) * δα +
    d ^ 2 * (V.C1 * Bb) ≤ By
  contr : ∀ a b c e ρ₁ ρ₂ : ℝ≥0,
    2 * (wa * V.pS0 Bb Bd By (Sewing.sewingConst (3 * α)).toNNReal δα
          a b c e ρ₁ ρ₂ +
        wb * (V.C1 * a) +
        wc * V.pSc Bb By a b e ρ₁ +
        we * V.pSe Bb Bd By (Sewing.sewingConst (3 * α)).toNNReal δα
          a b c e ρ₁ ρ₂) ≤
      wa * a + wb * b + wc * c + we * e + Koff * (ρ₁ + ρ₂)

/-- **Existence of Picard parameters**: every `C³_b` vector field admits
box constants, weights, a window size and an offset satisfying all side
conditions of the Picard theory. -/
theorem exists_picardParams (V : RDEVectorField3 d E) (α : ℝ) :
    Nonempty (PicardParams V α) := by
  set K := (Sewing.sewingConst (3 * α)).toNNReal with hK
  set Bb := V.C0 with hBb
  set By := d ^ 2 * (V.C1 * V.C0) + 1 with hBy
  set Bd := V.C1 * (d * Bb + By) with hBd
  set Tsum := V.pTa Bb Bd By + V.pTb Bb By + V.pTc + V.pTe Bb By
    with hTsum
  set we := 2 * V.pRe Bb By + 1 with hwe
  set wb := 2 * (V.pRb Bb By + we * (d ^ 2 * V.C1)) + 1 with hwb
  set wa := 2 * (wb * V.C1 + V.pRa Bb By + we * (d ^ 2 * V.C2 * Bb)) + 1
    with hwa
  set BIGy := d * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2) +
    d ^ 2 * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By)) with hBIGy
  set X := 2 * (wa * ((d * V.C1 + d ^ 2 * V.C2 * Bb) +
      (d ^ 2 * V.C1 + K * Tsum)) + we * (K * Tsum)) + K * BIGy + 1
    with hX
  have hX1 : 1 ≤ X := by rw [hX]; exact le_add_self
  have hX0 : X ≠ 0 := fun h => by
    rw [h] at hX1
    exact absurd hX1 (by norm_num)
  set δα := X⁻¹ with hδα
  -- residual absorption: anything `≤ X` becomes `≤ 1` after multiplying by `δα`
  have hres : ∀ y : ℝ≥0, y ≤ X → δα * y ≤ 1 := by
    intro y hy
    rw [hδα]
    calc X⁻¹ * y ≤ X⁻¹ * X := mul_le_mul' le_rfl hy
      _ = 1 := by rw [inv_mul_cancel₀ hX0]
  have hδα1 : δα ≤ 1 := by
    have h := hres 1 hX1
    rwa [mul_one] at h
  have hδmul : ∀ y : ℝ≥0, δα * y ≤ y := fun y =>
    le_trans (mul_le_mul' hδα1 le_rfl) (le_of_eq (one_mul _))
  -- the `T`-coefficients are dominated by their sum
  have hTa : V.pTa Bb Bd By ≤ Tsum := by
    rw [hTsum]; exact le_add_right (le_add_right le_self_add)
  have hTb : V.pTb Bb By ≤ Tsum := by
    rw [hTsum]; exact le_add_right (le_add_right le_add_self)
  have hTcs : V.pTc (E := E) ≤ Tsum := by
    rw [hTsum]; exact le_add_right le_add_self
  have hTe : V.pTe Bb By ≤ Tsum := by rw [hTsum]; exact le_add_self
  have hXge : 2 * (wa * ((d * V.C1 + d ^ 2 * V.C2 * Bb) +
      (d ^ 2 * V.C1 + K * Tsum)) + we * (K * Tsum)) ≤ X := by
    rw [hX]; exact le_trans le_self_add le_self_add
  set Koff := 2 * (wa * ((d * V.C0 + K * V.pTr1 Bb By) +
      (d ^ 2 * V.C1 * Bb + K * V.pTr2 Bb Bd By)) + V.pRr1 Bb By +
      we * (K * (V.pTr1 Bb By + V.pTr2 Bb Bd By) + d ^ 2 * V.C1 * Bb))
    with hKoff
  clear_value Koff δα X BIGy wa wb we Tsum Bd By Bb K
  refine ⟨{ Bb := Bb, Bd := Bd, By := By, wa := wa, wb := wb, wc := 1,
            we := we, δα := δα, Koff := Koff,
            wa_pos := ?_, δα_pos := ?_, δα_le_one := hδα1,
            box_b := hBb.ge, box_d := hBd.ge, box_y := ?_,
            contr := ?_ }⟩
  · -- wa positive
    rw [hwa]
    exact lt_of_lt_of_le zero_lt_one le_add_self
  · -- δα positive
    rw [hδα]
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hX1)
  · -- box closure for the remainder slot
    rw [← hK]
    have h1 : K * BIGy * δα ≤ 1 := by
      rw [mul_comm]
      refine hres _ ?_
      rw [hX]
      exact le_trans le_add_self le_self_add
    calc K * (d * (V.C1 * By + V.C2 * (d * Bb + By) ^ 2) +
          d ^ 2 * (V.C1 * Bd + V.C2 * Bb * (d * Bb + By))) * δα +
          d ^ 2 * (V.C1 * Bb)
        = K * BIGy * δα + d ^ 2 * (V.C1 * Bb) := by rw [hBIGy]
      _ ≤ 1 + d ^ 2 * (V.C1 * Bb) := add_le_add h1 le_rfl
      _ = By := by rw [hBy, hBb]; ring
  · -- the weighted contraction with offset
    intro a b c e ρ₁ ρ₂
    rw [← hK]
    have hcoefA : 2 * (wa * (δα * ((d * V.C1 + d ^ 2 * V.C2 * Bb) +
        K * V.pTa Bb Bd By)) + wb * V.C1 + V.pRa Bb By +
        we * (δα * (K * V.pTa Bb Bd By) + d ^ 2 * V.C2 * Bb)) ≤ wa := by
      have hbound : 2 * (wa * ((d * V.C1 + d ^ 2 * V.C2 * Bb) +
          K * V.pTa Bb Bd By) + we * (K * V.pTa Bb Bd By)) ≤ X :=
        le_trans (mul_le_mul' le_rfl (add_le_add
          (mul_le_mul' le_rfl (add_le_add le_rfl
            (le_trans (mul_le_mul' le_rfl hTa) le_add_self)))
          (mul_le_mul' le_rfl (mul_le_mul' le_rfl hTa)))) hXge
      calc 2 * (wa * (δα * ((d * V.C1 + d ^ 2 * V.C2 * Bb) +
            K * V.pTa Bb Bd By)) + wb * V.C1 + V.pRa Bb By +
            we * (δα * (K * V.pTa Bb Bd By) + d ^ 2 * V.C2 * Bb))
          = 2 * (wb * V.C1 + V.pRa Bb By + we * (d ^ 2 * V.C2 * Bb)) +
            δα * (2 * (wa * ((d * V.C1 + d ^ 2 * V.C2 * Bb) +
              K * V.pTa Bb Bd By) + we * (K * V.pTa Bb Bd By))) := by
            ring
        _ ≤ 2 * (wb * V.C1 + V.pRa Bb By + we * (d ^ 2 * V.C2 * Bb)) +
            1 := add_le_add le_rfl (hres _ hbound)
        _ = wa := hwa.symm
    have hcoefB : 2 * (wa * (δα * (d ^ 2 * V.C1 + K * V.pTb Bb By)) +
        V.pRb Bb By + we * (δα * (K * V.pTb Bb By) + d ^ 2 * V.C1)) ≤
        wb := by
      have hbound : 2 * (wa * (d ^ 2 * V.C1 + K * V.pTb Bb By) +
          we * (K * V.pTb Bb By)) ≤ X :=
        le_trans (mul_le_mul' le_rfl (add_le_add
          (mul_le_mul' le_rfl (le_trans (add_le_add le_rfl
            (mul_le_mul' le_rfl hTb)) le_add_self))
          (mul_le_mul' le_rfl (mul_le_mul' le_rfl hTb)))) hXge
      calc 2 * (wa * (δα * (d ^ 2 * V.C1 + K * V.pTb Bb By)) +
            V.pRb Bb By + we * (δα * (K * V.pTb Bb By) + d ^ 2 * V.C1))
          = 2 * (V.pRb Bb By + we * (d ^ 2 * V.C1)) +
            δα * (2 * (wa * (d ^ 2 * V.C1 + K * V.pTb Bb By) +
              we * (K * V.pTb Bb By))) := by ring
        _ ≤ 2 * (V.pRb Bb By + we * (d ^ 2 * V.C1)) + 1 :=
            add_le_add le_rfl (hres _ hbound)
        _ = wb := hwb.symm
    have hcoefC : 2 * (wa * (δα * (K * V.pTc)) +
        we * (δα * (K * V.pTc))) ≤ 1 := by
      have hbound : 2 * (wa * (K * V.pTc (E := E)) +
          we * (K * V.pTc (E := E))) ≤ X :=
        le_trans (mul_le_mul' le_rfl (add_le_add
          (mul_le_mul' le_rfl (le_trans (le_trans
            (mul_le_mul' le_rfl hTcs) le_add_self) le_add_self))
          (mul_le_mul' le_rfl (mul_le_mul' le_rfl hTcs)))) hXge
      calc 2 * (wa * (δα * (K * V.pTc)) + we * (δα * (K * V.pTc)))
          = δα * (2 * (wa * (K * V.pTc) + we * (K * V.pTc))) := by ring
        _ ≤ 1 := hres _ hbound
    have hcoefE : 2 * (wa * (δα * (K * V.pTe Bb By)) + V.pRe Bb By +
        we * (δα * (K * V.pTe Bb By))) ≤ we := by
      have hbound : 2 * (wa * (K * V.pTe Bb By) +
          we * (K * V.pTe Bb By)) ≤ X :=
        le_trans (mul_le_mul' le_rfl (add_le_add
          (mul_le_mul' le_rfl (le_trans (le_trans
            (mul_le_mul' le_rfl hTe) le_add_self) le_add_self))
          (mul_le_mul' le_rfl (mul_le_mul' le_rfl hTe)))) hXge
      calc 2 * (wa * (δα * (K * V.pTe Bb By)) + V.pRe Bb By +
            we * (δα * (K * V.pTe Bb By)))
          = 2 * V.pRe Bb By + δα * (2 * (wa * (K * V.pTe Bb By) +
              we * (K * V.pTe Bb By))) := by ring
        _ ≤ 2 * V.pRe Bb By + 1 := add_le_add le_rfl (hres _ hbound)
        _ = we := hwe.symm
    have hcoefR1 : 2 * (wa * (δα * (d * V.C0 + K * V.pTr1 Bb By)) +
        V.pRr1 Bb By + we * (δα * (K * V.pTr1 Bb By))) ≤ Koff := by
      rw [hKoff]
      refine mul_le_mul' le_rfl (add_le_add (add_le_add ?_ le_rfl) ?_)
      · exact mul_le_mul' le_rfl (le_trans (hδmul _) le_self_add)
      · refine mul_le_mul' le_rfl (le_trans (hδmul _) ?_)
        exact le_trans (mul_le_mul' le_rfl le_self_add) le_self_add
    have hcoefR2 : 2 * (wa * (δα * (d ^ 2 * V.C1 * Bb +
        K * V.pTr2 Bb Bd By)) +
        we * (δα * (K * V.pTr2 Bb Bd By) + d ^ 2 * V.C1 * Bb)) ≤
        Koff := by
      rw [hKoff]
      refine mul_le_mul' le_rfl ?_
      have h1 : wa * (δα * (d ^ 2 * V.C1 * Bb + K * V.pTr2 Bb Bd By)) ≤
          wa * ((d * V.C0 + K * V.pTr1 Bb By) +
            (d ^ 2 * V.C1 * Bb + K * V.pTr2 Bb Bd By)) + V.pRr1 Bb By :=
        le_trans (mul_le_mul' le_rfl (le_trans (hδmul _) le_add_self))
          le_self_add
      have h2 : we * (δα * (K * V.pTr2 Bb Bd By) + d ^ 2 * V.C1 * Bb) ≤
          we * (K * (V.pTr1 Bb By + V.pTr2 Bb Bd By) +
            d ^ 2 * V.C1 * Bb) := by
        refine mul_le_mul' le_rfl (add_le_add ?_ le_rfl)
        exact le_trans (hδmul _) (mul_le_mul' le_rfl le_add_self)
      exact add_le_add h1 h2
    calc 2 * (wa * V.pS0 Bb Bd By K δα a b c e ρ₁ ρ₂ +
          wb * (V.C1 * a) +
          1 * V.pSc Bb By a b e ρ₁ +
          we * V.pSe Bb Bd By K δα a b c e ρ₁ ρ₂)
        = (2 * (wa * (δα * ((d * V.C1 + d ^ 2 * V.C2 * Bb) +
              K * V.pTa Bb Bd By)) + wb * V.C1 + V.pRa Bb By +
              we * (δα * (K * V.pTa Bb Bd By) +
                d ^ 2 * V.C2 * Bb))) * a +
          (2 * (wa * (δα * (d ^ 2 * V.C1 + K * V.pTb Bb By)) +
              V.pRb Bb By +
              we * (δα * (K * V.pTb Bb By) + d ^ 2 * V.C1))) * b +
          (2 * (wa * (δα * (K * V.pTc)) +
            we * (δα * (K * V.pTc)))) * c +
          (2 * (wa * (δα * (K * V.pTe Bb By)) + V.pRe Bb By +
              we * (δα * (K * V.pTe Bb By)))) * e +
          (2 * (wa * (δα * (d * V.C0 + K * V.pTr1 Bb By)) +
              V.pRr1 Bb By + we * (δα * (K * V.pTr1 Bb By)))) * ρ₁ +
          (2 * (wa * (δα * (d ^ 2 * V.C1 * Bb + K * V.pTr2 Bb Bd By)) +
              we * (δα * (K * V.pTr2 Bb Bd By) +
                d ^ 2 * V.C1 * Bb))) * ρ₂ := by
          simp only [pS0, pSc, pSe, pRCN, pCMy, pCMd, pTa, pTb,
            pTc, pTe, pTr1, pTr2, pRa, pRb, pRe, pRr1]
          ring
      _ ≤ wa * a + wb * b + 1 * c + we * e + Koff * ρ₁ + Koff * ρ₂ :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
            (mul_le_mul' hcoefA le_rfl) (mul_le_mul' hcoefB le_rfl))
            (mul_le_mul' hcoefC le_rfl)) (mul_le_mul' hcoefE le_rfl))
            (mul_le_mul' hcoefR1 le_rfl)) (mul_le_mul' hcoefR2 le_rfl)
      _ = wa * a + wb * b + 1 * c + we * e + Koff * (ρ₁ + ρ₂) := by
          ring

/-! ### Hypothesis-light well-posedness and Itô–Lyons continuity -/

variable {X X₁ X₂ : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ}
variable {α : ℝ} {ρ₁ ρ₂ : ℝ≥0}

/-- An RDE solution stays a solution after weakening its certificates to
box constants. -/
theorem _root_.RoughPaths.RDEVectorField.IsRDESolution.weaken
    {V' : RDEVectorField d E} {hX : IsLevel2RoughPath X ω α}
    {hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1}
    {Z : ControlledPath X ω α E} {I : ℝ → ℝ → E}
    (hsol : V'.IsRDESolution hX hω1 Z I) {Bb Bd By : ℝ≥0}
    (h1 : Z.Cb ≤ Bb) (h2 : Z.Cd ≤ Bd) (h3 : Z.Cy ≤ By) :
    V'.IsRDESolution hX hω1 (Z.weaken h1 h2 h3) I where
  deriv_eq := hsol.deriv_eq
  additive := hsol.additive
  germ_bound := by
    intro s t hst
    have hrc : roughConst (V'.compControlled hX hω1 Z) ≤
        roughConst (V'.compControlled hX hω1 (Z.weaken h1 h2 h3)) := by
      rw [roughConst_eq_coe, roughConst_eq_coe]
      refine ENNReal.coe_le_coe.2 ?_
      show (d : ℝ≥0) * (V'.C1 * Z.Cy + V'.C2 * (d * Z.Cb + Z.Cy) ^ 2) +
          (d : ℝ≥0) ^ 2 *
            (V'.C1 * Z.Cd + V'.C2 * Z.Cb * (d * Z.Cb + Z.Cy)) ≤
        (d : ℝ≥0) * (V'.C1 * By + V'.C2 * (d * Bb + By) ^ 2) +
          (d : ℝ≥0) ^ 2 * (V'.C1 * Bd + V'.C2 * Bb * (d * Bb + By))
      gcongr
    exact le_trans (hsol.germ_bound hst)
      (mul_le_mul' le_rfl (mul_le_mul' hrc le_rfl))
  increment_eq := hsol.increment_eq

section Wrappers

variable [CompleteSpace E]
variable (V : RDEVectorField3 d E)

/-- **RDE well-posedness with constructed parameters** (Friz–Hairer
Thms 8.3/8.4, hypothesis-light form): on any window where
`ω^α ≤ P.δα` and `ω ≤ 1`, the RDE `dY = f(Y)·dX` started at `y₀` has a
box-certified solution, unique among box-certified solutions. All
arithmetic side conditions are discharged by `P : PicardParams V α`,
which exists for every `C³_b` vector field (`exists_picardParams`). -/
theorem rde_wellposed (hX : IsLevel2RoughPath X ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (hfine : Sewing.HasFinePartitions ω)
    (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    (y₀ : E) (P : PicardParams V α)
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (P.δα : ℝ≥0∞)) :
    ∃ (Z : ControlledPath X ω α E) (I : ℝ → ℝ → E),
      V.IsRDESolution hX hω1 Z I ∧ Z.Y 0 = y₀ ∧
      InBox P.Bb P.Bd P.By Z ∧
      ∀ (Z' : ControlledPath X ω α E) (I' : ℝ → ℝ → E),
        V.IsRDESolution hX hω1 Z' I' → Z'.Y 0 = y₀ →
        InBox P.Bb P.Bd P.By Z' → ∀ u : ℝ, Z'.Y u = Z.Y u := by
  -- the contraction hypothesis for box-exact pairs, from `P.contr`
  have hcontrP : ∀ (Z₁ Z₂ : ControlledPath X ω α E),
      Z₁.Cb = P.Bb → Z₁.Cd = P.Bd → Z₁.Cy = P.By →
      Z₂.Cb = P.Bb → Z₂.Cd = P.Bd → Z₂.Cy = P.By →
      ∀ D : ControlledDist Z₁ Z₂,
        2 * (P.wa * (picardDist V hX hω1 hfine hωne y₀ hδα P.δα_le_one
              D).D0 +
          P.wb * (picardDist V hX hω1 hfine hωne y₀ hδα P.δα_le_one
              D).Db +
          P.wc * (picardDist V hX hω1 hfine hωne y₀ hδα P.δα_le_one
              D).Dd +
          P.we * (picardDist V hX hω1 hfine hωne y₀ hδα P.δα_le_one
              D).Dy) ≤
        P.wa * D.D0 + P.wb * D.Db + P.wc * D.Dd + P.we * D.Dy := by
    intro Z₁ Z₂ h1 _h2 h3 h1' h2' h3' D
    have key := P.contr D.D0 D.Db D.Dd D.Dy 0 0
    simp only [add_zero, mul_zero] at key
    refine le_trans (le_of_eq ?_) key
    simp only [picardDist, compControlledDist, pS0, pSc, pSe, pRCN,
      pCMy, pCMd]
    rw [h1, h3, h1', h2', h3']
    ring
  obtain ⟨Z, I, hsol, hY0, hbox⟩ := rde_exists V hX hω1 hfine hωne y₀
    hδα P.δα_le_one P.box_b P.box_d P.box_y P.wa_pos
    (fun Z₁ Z₂ h1 h2 h3 h1' h2' h3' D =>
      hcontrP Z₁ Z₂ h1 h2 h3 h1' h2' h3' D)
  refine ⟨Z, I, hsol, hY0, hbox, ?_⟩
  intro Z' I' hsol' hY0' hbox' u
  -- weaken both solutions to literal box constants and apply uniqueness
  have hu := rde_unique V hX hω1 hfine hωne hδα P.δα_le_one P.wa_pos
    (hsol'.weaken hbox'.1 hbox'.2.1 hbox'.2.2)
    (hsol.weaken hbox.1 hbox.2.1 hbox.2.2)
    (show (Z'.weaken hbox'.1 hbox'.2.1 hbox'.2.2).Y 0 =
        (Z.weaken hbox.1 hbox.2.1 hbox.2.2).Y 0 from
      hY0'.trans hY0.symm)
    ⟨le_rfl, le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl, le_rfl⟩
    (by
      intro D
      have key := P.contr D.D0 D.Db D.Dd D.Dy 0 0
      simp only [add_zero, mul_zero] at key
      refine le_trans (le_of_eq ?_) key
      simp only [solutionDistStep, compControlledDist, pS0, pSc, pSe,
        pRCN, pCMy, pCMd, ControlledPath.weaken]
      ring)
  exact hu u

/-- **Continuity of the Itô–Lyons map, packaged** (universal-limit-type
statement): box-exact solutions of the same RDE along two drivers at
certified distance `(ρ₁, ρ₂)`, from the same initial condition, are
uniformly `P.Koff·(ρ₁+ρ₂)/P.wa`-close — a local Lipschitz estimate for
the solution map in the rough path metric. -/
theorem itoLyons_continuity (hX₁ : IsLevel2RoughPath X₁ ω α)
    (hX₂ : IsLevel2RoughPath X₂ ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (hXd : RoughPathDist X₁ X₂ ω α ρ₁ ρ₂)
    (hfine : Sewing.HasFinePartitions ω)
    (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    (P : PicardParams V α)
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (P.δα : ℝ≥0∞))
    {Z₁ : ControlledPath X₁ ω α E} {Z₂ : ControlledPath X₂ ω α E}
    {I₁ I₂ : ℝ → ℝ → E}
    (hsol₁ : V.IsRDESolution hX₁ hω1 Z₁ I₁)
    (hsol₂ : V.IsRDESolution hX₂ hω1 Z₂ I₂)
    (h0 : Z₁.Y 0 = Z₂.Y 0)
    (h1 : Z₁.Cb = P.Bb) (h2 : Z₁.Cd = P.Bd) (h3 : Z₁.Cy = P.By)
    (h1' : Z₂.Cb = P.Bb) (h2' : Z₂.Cd = P.Bd) (h3' : Z₂.Cy = P.By) :
    ∀ u : ℝ, dist (Z₁.Y u) (Z₂.Y u) ≤
      ((P.Koff * (ρ₁ + ρ₂) : ℝ≥0) : ℝ) / (P.wa : ℝ) := by
  refine itoLyons_dist_le (wb := P.wb) (wc := P.wc) (we := P.we)
    V hX₁ hX₂ hω1 hXd hfine hωne hδα P.δα_le_one
    P.wa_pos hsol₁ hsol₂ h0
    ⟨le_of_eq h1, le_of_eq h2, le_of_eq h3⟩
    ⟨le_of_eq h1', le_of_eq h2', le_of_eq h3'⟩ ?_
  intro D
  have key := P.contr D.D0 D.Db D.Dd D.Dy ρ₁ ρ₂
  refine le_trans (le_of_eq ?_) key
  have hc1 : (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cb =
      V.C1 * Z₁.Cb := rfl
  have hcy : (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cy =
      V.C1 * Z₁.Cy + V.C2 * (d * Z₁.Cb + Z₁.Cy) ^ 2 := rfl
  have hcd : (V.toRDEVectorField.compControlled hX₁ hω1 Z₁).Cd =
      V.C1 * Z₁.Cd + V.C2 * Z₁.Cb * (d * Z₁.Cb + Z₁.Cy) := rfl
  simp only [solutionDriverStep, compMixedDist, mixedRoughConstN,
    pS0, pSc, pSe, pRCN, pCMy, pCMd]
  rw [hc1, hcy, hcd, h1, h2, h3, h1', h2', h3']

/-- **Continuity of the Itô–Lyons map in the rough path metric**: for
drivers at metric distance at most `ρ` in the space of level-2 rough
paths, the corresponding solutions are uniformly `2·P.Koff·ρ/P.wa`-close.
The Itô–Lyons map is thus locally Lipschitz — in particular continuous —
from the rough path topology to uniform convergence of solutions. -/
theorem itoLyons_continuity_edist (A B : Level2RoughPath ω α d) {ρ : ℝ≥0}
    (hAB : edist A B ≤ (ρ : ℝ≥0∞))
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (hfine : Sewing.HasFinePartitions ω)
    (hωne : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    (P : PicardParams V α)
    (hδα : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ^ α ≤ (P.δα : ℝ≥0∞))
    {Z₁ : ControlledPath A.X ω α E} {Z₂ : ControlledPath B.X ω α E}
    {I₁ I₂ : ℝ → ℝ → E}
    (hsol₁ : V.IsRDESolution A.level2 hω1 Z₁ I₁)
    (hsol₂ : V.IsRDESolution B.level2 hω1 Z₂ I₂)
    (h0 : Z₁.Y 0 = Z₂.Y 0)
    (h1 : Z₁.Cb = P.Bb) (h2 : Z₁.Cd = P.Bd) (h3 : Z₁.Cy = P.By)
    (h1' : Z₂.Cb = P.Bb) (h2' : Z₂.Cd = P.Bd) (h3' : Z₂.Cy = P.By) :
    ∀ u : ℝ, dist (Z₁.Y u) (Z₂.Y u) ≤
      ((P.Koff * (ρ + ρ) : ℝ≥0) : ℝ) / (P.wa : ℝ) :=
  itoLyons_continuity V A.level2 B.level2 hω1
    (Level2RoughPath.RoughPathDist.of_edist_le A.level2.alpha_pos.le
      hωne hAB)
    hfine hωne P hδα hsol₁ hsol₂ h0 h1 h2 h3 h1' h2' h3'

end Wrappers

end RDEVectorField3

end RoughPaths
