/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.RDE.Composition

/-!
# Solutions of rough differential equations

A controlled path `Z` *solves* `dY = f(Y)·dX` when its Gubinelli
derivative is the vector field along the path and its increments are an
additive primitive of the Gubinelli germ of the composed integrand
`f(Y)` — the sewing formulation of Davie/Gubinelli. The composed
integrand always admits such a primitive (`exists_roughIntegral` applied
to `compControlled`), and every solution satisfies **Davie's local
expansion**: the increment agrees with the second-order
Euler/Milstein scheme
`Y_t - Y_s ≈ Σᵢ X¹ᵢ·fᵢ(Y_s) + Σᵢⱼ X²ᵢⱼ·Dfⱼ(Y_s)(fᵢ(Y_s))`
to order `ω^{3α}`, `3α > 1`.
-/

namespace RoughPaths

open scoped ENNReal NNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : AlgebraicRoughPath ℝ (Fin d) ℝ} {ω : Control ℝ} {α : ℝ}

namespace RDEVectorField

/-- A controlled path `Z` together with an increment family `I` solves
`dY = f(Y)·dX` when the derivative of `Z` is `f` along the path, `I` is
additive with the sewing germ bound for the composed integrand, and the
increments of `Z` are `I`. -/
structure IsRDESolution (V : RDEVectorField d E)
    (hX : IsLevel2RoughPath X ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (Z : ControlledPath X ω α E) (I : ℝ → ℝ → E) : Prop where
  deriv_eq : ∀ (s : ℝ) (i : Fin d), Z.Yd s i = V.f i (Z.Y s)
  additive : ∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I s u + I u t = I s t
  germ_bound : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖I s t - gubinelliGerm (V.compControlled hX hω1 Z) s t‖ₑ ≤
      Sewing.sewingConst (3 * α) *
        (roughConst (V.compControlled hX hω1 Z) * ω s t ^ (3 * α))
  increment_eq : ∀ ⦃s t : ℝ⦄, s ≤ t → Z.Y t - Z.Y s = I s t

/-- The composed integrand of any controlled path admits a rough
integral: the candidate increments for the Picard iteration exist. -/
theorem exists_roughIntegral_comp [CompleteSpace E]
    (V : RDEVectorField d E) (hX : IsLevel2RoughPath X ω α)
    (hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1)
    (hfine : Sewing.HasFinePartitions ω)
    (hω : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤)
    (Z : ControlledPath X ω α E) :
    ∃ I : ℝ → ℝ → E,
      (∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I s u + I u t = I s t) ∧
      (∀ ⦃s t : ℝ⦄, s ≤ t →
        ‖I s t - gubinelliGerm (V.compControlled hX hω1 Z) s t‖ₑ ≤
          Sewing.sewingConst (3 * α) *
            (roughConst (V.compControlled hX hω1 Z) *
              ω s t ^ (3 * α))) := by
  obtain ⟨I, hadd, hgerm, _⟩ :=
    exists_roughIntegral hX (V.compControlled hX hω1 Z) hfine hω
  exact ⟨I, hadd, hgerm⟩

/-- **Davie's local expansion**: a solution of `dY = f(Y)·dX` agrees
with the second-order Euler (Milstein) scheme to order `ω^{3α}`. -/
theorem IsRDESolution.davie_expansion {V : RDEVectorField d E}
    {hX : IsLevel2RoughPath X ω α}
    {hω1 : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≤ 1}
    {Z : ControlledPath X ω α E} {I : ℝ → ℝ → E}
    (hsol : V.IsRDESolution hX hω1 Z I) ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖Z.Y t - Z.Y s -
        ((∑ i, X.coeff s t [i] • V.f i (Z.Y s)) +
          ∑ i, ∑ j, X.coeff s t [i, j] •
            V.deriv j (Z.Y s) (V.f i (Z.Y s)))‖ₑ ≤
      Sewing.sewingConst (3 * α) *
        (roughConst (V.compControlled hX hω1 Z) * ω s t ^ (3 * α)) := by
  have hgerm : gubinelliGerm (V.compControlled hX hω1 Z) s t =
      (∑ i, X.coeff s t [i] • V.f i (Z.Y s)) +
        ∑ i, ∑ j, X.coeff s t [i, j] •
          V.deriv j (Z.Y s) (V.f i (Z.Y s)) := by
    have h2 : ∑ i, ∑ j, X.coeff s t [i, j] •
        (V.compControlled hX hω1 Z).Yd s i j =
        ∑ i, ∑ j, X.coeff s t [i, j] •
          V.deriv j (Z.Y s) (V.f i (Z.Y s)) := by
      refine Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => ?_
      rw [compControlled_Yd, hsol.deriv_eq s i]
    rw [gubinelliGerm_apply, h2]
    rfl
  rw [hsol.increment_eq hst, ← hgerm]
  exact hsol.germ_bound hst

end RDEVectorField

end RoughPaths
