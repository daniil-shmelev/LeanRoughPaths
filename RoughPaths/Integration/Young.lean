/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Sewing.Unique
import RoughPaths.Integration.Controls

/-!
# Young integration

For `f` an `α`-Hölder family of operators and `g` a `β`-Hölder path with
`α + β > 1`, the germ `Ξ s t = f s (g t − g s)` sews into an additive
Young integral `∫ f dg` with the Young–Loève estimate
`‖∫_s^t f dg − f s (g t − g s)‖ₑ ≤ K·Cf·Cg·(t−s)^{α+β}`, characterised as
the limit of Riemann sums along any mesh-fine sequence of partitions, and
unique among additive maps with such a germ bound.
-/

namespace RoughPaths

open scoped ENNReal NNReal

universe v w

variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Young germ `Ξ s t = f s (g t − g s)`. -/
noncomputable def youngGerm (f : ℝ → E →L[ℝ] F) (g : ℝ → E) :
    ℝ → ℝ → F :=
  fun s t => f s (g t - g s)

@[simp]
theorem youngGerm_apply (f : ℝ → E →L[ℝ] F) (g : ℝ → E) (s t : ℝ) :
    youngGerm f g s t = f s (g t - g s) :=
  rfl

/-- The Young control: linear with rate `(Cf·Cg)^{1/(α+β)}`. -/
noncomputable def youngControl (Cf Cg : ℝ≥0) (θ : ℝ) : Control ℝ :=
  Control.ofReal (((Cf : ℝ≥0∞) * Cg) ^ (1 / θ))

theorem youngControl_ne_top {Cf Cg : ℝ≥0} {θ : ℝ} (hθ : 0 < θ) {s t : ℝ} :
    youngControl Cf Cg θ s t ≠ ⊤ :=
  ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top))
    ENNReal.ofReal_ne_top

theorem youngControl_hasFinePartitions {Cf Cg : ℝ≥0} {θ : ℝ} (hθ : 0 < θ) :
    Sewing.HasFinePartitions (youngControl Cf Cg θ) :=
  Control.ofReal_hasFinePartitions
    (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top))

/-- The `θ`-th power of the Young control in closed form. -/
theorem youngControl_rpow {Cf Cg : ℝ≥0} {θ : ℝ} (hθ : 0 < θ) (s t : ℝ) :
    youngControl Cf Cg θ s t ^ θ =
      ((Cf : ℝ≥0∞) * Cg) * ENNReal.ofReal (t - s) ^ θ := by
  rw [youngControl, Control.ofReal_apply,
    ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hθ), ← ENNReal.rpow_mul,
    one_div, inv_mul_cancel₀ hθ.ne', ENNReal.rpow_one]

/-- Operator application is submultiplicative in extended norms. -/
private theorem enorm_clm_apply_le (L : E →L[ℝ] F) (x : E) :
    ‖L x‖ₑ ≤ ‖L‖ₑ * ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (L.le_opNorm x)

/-- A Hölder bound in extended norms against any dominating radius. -/
private theorem holder_enorm_le {F' : Type*} [SeminormedAddCommGroup F']
    {C γ : ℝ≥0} {h : ℝ → F'} (hh : HolderWith C γ h) (hγ : 0 < γ)
    {x y : ℝ} {r : ℝ≥0∞} (hd : edist x y ≤ r) :
    ‖h x - h y‖ₑ ≤ (C : ℝ≥0∞) * r ^ (γ : ℝ) := by
  have hle := hh.edist_le x y
  rw [edist_eq_enorm_sub] at hle
  exact le_trans hle (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hd
    (le_of_lt (by exact_mod_cast hγ))))

section Defect

variable {f : ℝ → E →L[ℝ] F} {g : ℝ → E} {Cf Cg : ℝ≥0} {α β : ℝ≥0}

/-- **The Chen defect of the Young germ**: `δΞ a b c = (f a − f b)(g c − g b)`
is bounded by the Young control to the power `θ = α + β`. -/
theorem youngGerm_defect (hf : HolderWith Cf α f) (hg : HolderWith Cg β g)
    (hα : 0 < α) (hβ : 0 < β) :
    ∀ ⦃a b c : ℝ⦄, a ≤ b → b ≤ c →
      ‖youngGerm f g a c - youngGerm f g a b - youngGerm f g b c‖ₑ ≤
        youngControl Cf Cg ((α : ℝ) + β) a c ^ ((α : ℝ) + β) := by
  intro a b c hab hbc
  have hθ : (0 : ℝ) < (α : ℝ) + β := by positivity
  -- algebraic identity for the defect
  have hdefect : youngGerm f g a c - youngGerm f g a b - youngGerm f g b c =
      (f a - f b) (g c - g b) := by
    simp only [youngGerm_apply, sub_apply]
    have h1 : f a (g c - g a) - f a (g b - g a) = f a (g c - g b) := by
      rw [← map_sub]
      congr 1
      abel
    rw [← h1]
  rw [hdefect]
  -- Hölder bounds on the two factors
  have h1 := holder_enorm_le hf hα (x := a) (y := b)
    (r := ENNReal.ofReal (c - a)) (by
      rw [edist_dist, Real.dist_eq, abs_of_nonpos (by linarith)]
      exact ENNReal.ofReal_le_ofReal (by linarith))
  have h2 := holder_enorm_le hg hβ (x := c) (y := b)
    (r := ENNReal.ofReal (c - a)) (by
      rw [edist_dist, Real.dist_eq, abs_of_nonneg (by linarith)]
      exact ENNReal.ofReal_le_ofReal (by linarith))
  calc ‖(f a - f b) (g c - g b)‖ₑ
      ≤ ‖f a - f b‖ₑ * ‖g c - g b‖ₑ := enorm_clm_apply_le _ _
    _ ≤ ((Cf : ℝ≥0∞) * ENNReal.ofReal (c - a) ^ (α : ℝ)) *
          ((Cg : ℝ≥0∞) * ENNReal.ofReal (c - a) ^ (β : ℝ)) :=
        mul_le_mul' h1 h2
    _ = ((Cf : ℝ≥0∞) * Cg) *
          (ENNReal.ofReal (c - a) ^ (α : ℝ) *
            ENNReal.ofReal (c - a) ^ (β : ℝ)) := by ring
    _ = ((Cf : ℝ≥0∞) * Cg) * ENNReal.ofReal (c - a) ^ ((α : ℝ) + β) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _
          (le_of_lt (by exact_mod_cast hα))
          (le_of_lt (by exact_mod_cast hβ))]
    _ = youngControl Cf Cg ((α : ℝ) + β) a c ^ ((α : ℝ) + β) :=
        (youngControl_rpow hθ a c).symm

end Defect

section Integral

variable [CompleteSpace F]
variable {f : ℝ → E →L[ℝ] F} {g : ℝ → E} {Cf Cg : ℝ≥0} {α β : ℝ≥0}

/-- **Existence of the Young integral** (Young 1936; Lyons–Caruana–Lévy
Ch. 1): an additive `I` with the Young–Loève bound
`‖I s t − f s (g t − g s)‖ₑ ≤ K·Cf·Cg·(t−s)^{α+β}`, approximating the
Riemann sums of every fine partition. -/
theorem exists_youngIntegral
    (hf : HolderWith Cf α f) (hg : HolderWith Cg β g)
    (hα : 0 < α) (hβ : 0 < β) (hθ : 1 < (α : ℝ) + β) :
    ∃ I : ℝ → ℝ → F,
      (∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I s u + I u t = I s t) ∧
      (∀ ⦃s t : ℝ⦄, s ≤ t →
        ‖I s t - f s (g t - g s)‖ₑ ≤
          Sewing.sewingConst ((α : ℝ) + β) *
            (((Cf : ℝ≥0∞) * Cg) *
              ENNReal.ofReal (t - s) ^ ((α : ℝ) + β))) ∧
      (∀ ⦃s t : ℝ⦄, s ≤ t → ∀ (ε : ℝ≥0∞) (mid : List ℝ),
        List.IsChain (fun a b => a ≤ b ∧
          youngControl Cf Cg ((α : ℝ) + β) a b ≤ ε) (s :: (mid ++ [t])) →
        ‖I s t - Sewing.pairSum (youngGerm f g) (s :: (mid ++ [t]))‖ₑ ≤
          Sewing.sewingConst ((α : ℝ) + β) *
            (ε ^ ((α : ℝ) + β - 1) *
              youngControl Cf Cg ((α : ℝ) + β) s t)) := by
  have hθ0 : (0 : ℝ) < (α : ℝ) + β := by positivity
  obtain ⟨I, hadd, hgerm, hmesh⟩ := Sewing.sewing
    (youngControl Cf Cg ((α : ℝ) + β)) (youngGerm f g) hθ
    (youngGerm_defect hf hg hα hβ) (youngControl_hasFinePartitions hθ0)
    (fun s t _ => youngControl_ne_top hθ0)
  refine ⟨I, hadd, fun s t hst => ?_, hmesh⟩
  have h1 := hgerm hst
  rw [youngControl_rpow hθ0] at h1
  exact h1

omit [CompleteSpace F] in
/-- **Uniqueness of the Young integral** among additive maps with a
Young–Loève-type germ bound. -/
theorem youngIntegral_unique
    (hθ : 1 < (α : ℝ) + β)
    {C C' : ℝ≥0∞} (hC : C ≠ ⊤) (hC' : C' ≠ ⊤)
    {I I' : ℝ → ℝ → F}
    (hadd : ∀ ⦃a u b : ℝ⦄, a ≤ u → u ≤ b → I a u + I u b = I a b)
    (hadd' : ∀ ⦃a u b : ℝ⦄, a ≤ u → u ≤ b → I' a u + I' u b = I' a b)
    (hI : ∀ ⦃a b : ℝ⦄, a ≤ b → ‖I a b - youngGerm f g a b‖ₑ ≤
      C * youngControl Cf Cg ((α : ℝ) + β) a b ^ ((α : ℝ) + β))
    (hI' : ∀ ⦃a b : ℝ⦄, a ≤ b → ‖I' a b - youngGerm f g a b‖ₑ ≤
      C' * youngControl Cf Cg ((α : ℝ) + β) a b ^ ((α : ℝ) + β))
    {s t : ℝ} (hst : s ≤ t) :
    I s t = I' s t :=
  Sewing.eq_of_additive_of_germ_bound
    (youngControl Cf Cg ((α : ℝ) + β)) (youngGerm f g) hθ hC hC'
    (youngControl_hasFinePartitions (by linarith)) hadd hadd' hI hI' hst
    (youngControl_ne_top (by linarith))

end Integral

end RoughPaths
