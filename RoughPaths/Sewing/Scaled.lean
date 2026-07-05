/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Integration.FinePartitions
import RoughPaths.Sewing.AdditiveLimit

/-!
# Sewing with a constant-scaled control

The additive sewing lemma packaged for germs whose defect is bounded by
`C·ω^θ`: the scaling constant is absorbed into the control, so all three
rough-integral constructions (word, branched, planarly branched) reduce
to one application.
-/

namespace RoughPaths

open scoped ENNReal

variable {T : Type*} [LinearOrder T] {E : Type*} [NormedAddCommGroup E]

/-- **Scaled sewing**: a germ with defect bound `C·ω^θ`, `θ > 1`, sews
into an additive primitive with the correspondingly scaled estimates. -/
theorem Sewing.sewing_const_mul [CompleteSpace E] (ω : Control T)
    (Ξ : T → T → E) {θ : ℝ} {C : ℝ≥0∞}
    (hθ : 1 < θ) (hθ0 : θ ≠ 0) (hC : C ≠ ⊤)
    (hδ : ∀ ⦃a b c : T⦄, a ≤ b → b ≤ c →
      ‖Ξ a c - Ξ a b - Ξ b c‖ₑ ≤ C * ω a c ^ θ)
    (hfine : HasFinePartitions ω)
    (hω : ∀ ⦃s t : T⦄, s ≤ t → ω s t ≠ ⊤) :
    ∃ I : T → T → E,
      (∀ ⦃s u t : T⦄, s ≤ u → u ≤ t → I s u + I u t = I s t) ∧
      (∀ ⦃s t : T⦄, s ≤ t →
        ‖I s t - Ξ s t‖ₑ ≤ sewingConst θ * (C * ω s t ^ θ)) ∧
      (∀ ⦃s t : T⦄, s ≤ t → ∀ (ε : ℝ≥0∞) (mid : List T),
        List.IsChain (fun a b => a ≤ b ∧
          Control.constMul (C ^ θ⁻¹) ω a b ≤ ε) (s :: (mid ++ [t])) →
        ‖I s t - pairSum Ξ (s :: (mid ++ [t]))‖ₑ ≤
          sewingConst θ *
            (ε ^ (θ - 1) * Control.constMul (C ^ θ⁻¹) ω s t)) := by
  have hc : C ^ θ⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hC
  have hpow : ∀ s t : T,
      Control.constMul (C ^ θ⁻¹) ω s t ^ θ = C * ω s t ^ θ := by
    intro s t
    rw [Control.constMul_apply,
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ← ENNReal.rpow_mul, inv_mul_cancel₀ hθ0, ENNReal.rpow_one]
  obtain ⟨I, hadd, hgerm, hmesh⟩ := sewing
    (Control.constMul (C ^ θ⁻¹) ω) Ξ hθ
    (fun a b c hab hbc => by rw [hpow a c]; exact hδ hab hbc)
    (hfine.constMul hc)
    (fun s t hst => by
      rw [Control.constMul_apply]
      exact ENNReal.mul_ne_top hc (hω hst))
  refine ⟨I, hadd, fun s t hst => ?_, hmesh⟩
  have h1 := hgerm hst
  rwa [hpow s t] at h1

end RoughPaths
