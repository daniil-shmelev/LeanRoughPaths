/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Integration.ControlledPath

/-!
# The topology on level-2 rough paths

The space `Level2RoughPath ω α d` of rough paths carrying level-2 bounds
against a fixed control `ω`, with the inhomogeneous rough path distance

`ϱ(X,X') = sup_{s≤t} max( ‖X¹-X'¹‖ₑ/ω^α , ‖X²-X'²‖ₑ/ω^{2α} )`.

This is a *pseudo*-emetric: two rough paths at distance zero agree at
levels one and two wherever `ω` is positive but may differ at higher
levels. Since both arguments obey the same level-2 bounds the distance
is bounded by `2` on the whole space.

`RoughPathDist` is the certified-constants form of the same distance
used by the quantitative stability theory; the two are interchangeable
via `edist_le_of_roughPathDist` and `RoughPathDist.of_edist_le`.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ}

/-- Certified distance between two rough paths over the same control:
`ρ₁·ω^α` at the first level and `ρ₂·ω^{2α}` at the second. -/
structure RoughPathDist (X X' : AlgebraicRoughPath ℝ (Fin d) ℝ)
    (ω : Control ℝ) (α : ℝ) (ρ₁ ρ₂ : ℝ≥0) : Prop where
  bound_one : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ i : Fin d,
    ‖X.coeff s t [i] - X'.coeff s t [i]‖ₑ ≤ ρ₁ * ω s t ^ α
  bound_two : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ i j : Fin d,
    ‖X.coeff s t [i, j] - X'.coeff s t [i, j]‖ₑ ≤ ρ₂ * ω s t ^ (2 * α)

/-- The space of level-2 rough paths over a fixed control and exponent:
the carrier of the rough path topology. -/
structure Level2RoughPath (ω : Control ℝ) (α : ℝ) (d : ℕ) where
  /-- The underlying algebraic rough path. -/
  X : AlgebraicRoughPath ℝ (Fin d) ℝ
  /-- The level-2 Hölder certificate. -/
  level2 : IsLevel2RoughPath X ω α

namespace Level2RoughPath

variable {ω : Control ℝ} {α : ℝ}

/-- The inhomogeneous rough path distance. -/
noncomputable def roughDist (A B : Level2RoughPath ω α d) : ℝ≥0∞ :=
  (⨆ (s : ℝ) (t : ℝ) (_ : s ≤ t) (i : Fin d),
      ‖A.X.coeff s t [i] - B.X.coeff s t [i]‖ₑ / ω s t ^ α) ⊔
    ⨆ (s : ℝ) (t : ℝ) (_ : s ≤ t) (i : Fin d) (j : Fin d),
      ‖A.X.coeff s t [i, j] - B.X.coeff s t [i, j]‖ₑ / ω s t ^ (2 * α)

theorem term_le_roughDist_one (A B : Level2RoughPath ω α d) {s t : ℝ}
    (hst : s ≤ t) (i : Fin d) :
    ‖A.X.coeff s t [i] - B.X.coeff s t [i]‖ₑ / ω s t ^ α ≤
      roughDist A B :=
  le_sup_of_le_left <| le_iSup_of_le s <| le_iSup_of_le t <|
    le_iSup_of_le hst <| le_iSup_of_le i le_rfl

theorem term_le_roughDist_two (A B : Level2RoughPath ω α d) {s t : ℝ}
    (hst : s ≤ t) (i j : Fin d) :
    ‖A.X.coeff s t [i, j] - B.X.coeff s t [i, j]‖ₑ / ω s t ^ (2 * α) ≤
      roughDist A B :=
  le_sup_of_le_right <| le_iSup_of_le s <| le_iSup_of_le t <|
    le_iSup_of_le hst <| le_iSup_of_le i <| le_iSup_of_le j le_rfl

/-- **The rough path topology**: the space of level-2 rough paths is a
pseudo-emetric space under the inhomogeneous rough path distance. -/
noncomputable instance : PseudoEMetricSpace (Level2RoughPath ω α d) where
  edist := roughDist
  edist_self A := by
    simp [roughDist]
  edist_comm A B := by
    have h : ∀ x y : ℝ, ‖x - y‖ₑ = ‖y - x‖ₑ := fun x y => by
      rw [← neg_sub, enorm_neg]
    show roughDist A B = roughDist B A
    unfold roughDist
    congr 1
    · exact iSup_congr fun s => iSup_congr fun t => iSup_congr fun _ =>
        iSup_congr fun i => by rw [h]
    · exact iSup_congr fun s => iSup_congr fun t => iSup_congr fun _ =>
        iSup_congr fun i => iSup_congr fun j => by rw [h]
  edist_triangle A B C := by
    show roughDist A C ≤ roughDist A B + roughDist B C
    refine sup_le ?_ ?_
    · refine iSup_le fun s => iSup_le fun t => iSup_le fun hst =>
        iSup_le fun i => ?_
      have hnum : ‖A.X.coeff s t [i] - C.X.coeff s t [i]‖ₑ ≤
          ‖A.X.coeff s t [i] - B.X.coeff s t [i]‖ₑ +
            ‖B.X.coeff s t [i] - C.X.coeff s t [i]‖ₑ := by
        refine le_trans (le_of_eq (congrArg (‖·‖ₑ) ?_)) (enorm_add_le _ _)
        abel
      calc ‖A.X.coeff s t [i] - C.X.coeff s t [i]‖ₑ / ω s t ^ α
          ≤ (‖A.X.coeff s t [i] - B.X.coeff s t [i]‖ₑ +
              ‖B.X.coeff s t [i] - C.X.coeff s t [i]‖ₑ) / ω s t ^ α :=
            ENNReal.div_le_div_right hnum _
        _ = ‖A.X.coeff s t [i] - B.X.coeff s t [i]‖ₑ / ω s t ^ α +
              ‖B.X.coeff s t [i] - C.X.coeff s t [i]‖ₑ / ω s t ^ α :=
            ENNReal.add_div
        _ ≤ roughDist A B + roughDist B C :=
            add_le_add (term_le_roughDist_one A B hst i)
              (term_le_roughDist_one B C hst i)
    · refine iSup_le fun s => iSup_le fun t => iSup_le fun hst =>
        iSup_le fun i => iSup_le fun j => ?_
      have hnum : ‖A.X.coeff s t [i, j] - C.X.coeff s t [i, j]‖ₑ ≤
          ‖A.X.coeff s t [i, j] - B.X.coeff s t [i, j]‖ₑ +
            ‖B.X.coeff s t [i, j] - C.X.coeff s t [i, j]‖ₑ := by
        refine le_trans (le_of_eq (congrArg (‖·‖ₑ) ?_)) (enorm_add_le _ _)
        abel
      calc ‖A.X.coeff s t [i, j] - C.X.coeff s t [i, j]‖ₑ / ω s t ^ (2 * α)
          ≤ (‖A.X.coeff s t [i, j] - B.X.coeff s t [i, j]‖ₑ +
              ‖B.X.coeff s t [i, j] - C.X.coeff s t [i, j]‖ₑ) /
              ω s t ^ (2 * α) := ENNReal.div_le_div_right hnum _
        _ = ‖A.X.coeff s t [i, j] - B.X.coeff s t [i, j]‖ₑ / ω s t ^ (2 * α) +
              ‖B.X.coeff s t [i, j] - C.X.coeff s t [i, j]‖ₑ /
                ω s t ^ (2 * α) := ENNReal.add_div
        _ ≤ roughDist A B + roughDist B C :=
            add_le_add (term_le_roughDist_two A B hst i j)
              (term_le_roughDist_two B C hst i j)

theorem edist_def (A B : Level2RoughPath ω α d) :
    edist A B = roughDist A B :=
  rfl

/-- The rough path distance is bounded by `2` on the whole space: both
arguments obey the same level-2 bounds. -/
theorem edist_le_two (A B : Level2RoughPath ω α d) :
    edist A B ≤ 2 := by
  show roughDist A B ≤ 2
  refine sup_le ?_ ?_
  · refine iSup_le fun s => iSup_le fun t => iSup_le fun hst =>
      iSup_le fun i => ?_
    refine ENNReal.div_le_of_le_mul (le_trans enorm_sub_le ?_)
    calc ‖A.X.coeff s t [i]‖ₑ + ‖B.X.coeff s t [i]‖ₑ
        ≤ ω s t ^ α + ω s t ^ α :=
          add_le_add (A.level2.bound_one hst i) (B.level2.bound_one hst i)
      _ = 2 * ω s t ^ α := (two_mul _).symm
  · refine iSup_le fun s => iSup_le fun t => iSup_le fun hst =>
      iSup_le fun i => iSup_le fun j => ?_
    refine ENNReal.div_le_of_le_mul (le_trans enorm_sub_le ?_)
    calc ‖A.X.coeff s t [i, j]‖ₑ + ‖B.X.coeff s t [i, j]‖ₑ
        ≤ ω s t ^ (2 * α) + ω s t ^ (2 * α) :=
          add_le_add (A.level2.bound_two hst i j)
            (B.level2.bound_two hst i j)
      _ = 2 * ω s t ^ (2 * α) := (two_mul _).symm

theorem edist_ne_top (A B : Level2RoughPath ω α d) :
    edist A B ≠ ⊤ := by
  intro h
  have h2 := edist_le_two A B
  rw [h, top_le_iff] at h2
  simp at h2

/-- A certified rough path distance bounds the metric distance. -/
theorem edist_le_of_roughPathDist {A B : Level2RoughPath ω α d}
    {ρ₁ ρ₂ : ℝ≥0} (h : RoughPathDist A.X B.X ω α ρ₁ ρ₂) :
    edist A B ≤ (ρ₁ : ℝ≥0∞) ⊔ (ρ₂ : ℝ≥0∞) := by
  show roughDist A B ≤ _
  refine sup_le ?_ ?_
  · refine iSup_le fun s => iSup_le fun t => iSup_le fun hst =>
      iSup_le fun i => ?_
    exact le_trans (ENNReal.div_le_of_le_mul (h.bound_one hst i))
      le_sup_left
  · refine iSup_le fun s => iSup_le fun t => iSup_le fun hst =>
      iSup_le fun i => iSup_le fun j => ?_
    exact le_trans (ENNReal.div_le_of_le_mul (h.bound_two hst i j))
      le_sup_right

/-- A metric distance bound certifies the rough path distance (the
control must be finite to unfold the division). -/
theorem RoughPathDist.of_edist_le {A B : Level2RoughPath ω α d} {ρ : ℝ≥0}
    (hα : 0 ≤ α) (hω : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    (h : edist A B ≤ ρ) :
    RoughPathDist A.X B.X ω α ρ ρ := by
  constructor
  · intro s t hst i
    have h1 : ‖A.X.coeff s t [i] - B.X.coeff s t [i]‖ₑ / ω s t ^ α ≤ ρ :=
      le_trans (term_le_roughDist_one A B hst i) h
    rwa [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.coe_ne_top)
      (Or.inl (ENNReal.rpow_ne_top_of_nonneg hα (hω hst)))] at h1
  · intro s t hst i j
    have h1 : ‖A.X.coeff s t [i, j] - B.X.coeff s t [i, j]‖ₑ /
        ω s t ^ (2 * α) ≤ ρ :=
      le_trans (term_le_roughDist_two A B hst i j) h
    rwa [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.coe_ne_top)
      (Or.inl (ENNReal.rpow_ne_top_of_nonneg (by linarith) (hω hst)))] at h1

end Level2RoughPath

end RoughPaths
