/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Branched.Basic
import RoughPaths.Integration.ControlledPath
import RoughPaths.Sewing.Scaled
import RoughPaths.Sewing.Unique

/-!
# The branched rough integral (level 2)

Gubinelli's controlled integration against a branched rough path
(Gubinelli, *Ramification of rough paths*, math/0610300 §7–8), at level 2
over unlabelled trees: the only trees of order at most two are `•` and
the 2-chain, so a level-2 branched rough path is the data
`(X^•, X^chain2)` and Chen's identity for the Butcher–Connes–Kreimer
convolution reduces on them to the classical relations
`X^•(s,u) = X^•(s,t) + X^•(t,u)` and
`X^ch(s,u) = X^ch(s,t) + X^•(s,t)·X^•(t,u) + X^ch(t,u)`. The germ
`Ξ s t = X^•(s,t)·Y(s) + X^ch(s,t)·Y'(s)` then has defect of order
`ω^{3α}` and sews into the branched rough integral. Since only Chen's
identity is used, non-geometric branched (Itô-type) data is covered.
-/

namespace RoughPaths

open scoped ENNReal NNReal
open HopfAlgebras

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Chen's identity on trees of order at most two -/

section ChenSmall

variable {T : Type*} {R : Type*} [CommSemiring R]

private theorem ptree_convolutionCoeff_bullet
    (χ ψ : ForestAlgebra.Character R) :
    PTree.convolutionCoeff χ ψ PTree.bullet =
      χ.evalForest (RootedForest.singleton RootedTree.bullet) *
          ψ.evalForest RootedForest.empty +
        χ.evalForest RootedForest.empty *
          ψ.evalForest (RootedForest.singleton RootedTree.bullet) := by
  simp [PTree.convolutionCoeff, PTree.coproductTerms, PTree.cuts,
    PTree.rootCuts, PTree.Cut.prunedForest, PTree.Cut.trunkForest,
    PTree.evalCoproductTerms, PTree.evalCoproductTerm,
    RootedForest.singleton, RootedForest.empty, RootedTree.bullet,
    PTree.bullet]
  ring

private theorem ptree_convolutionCoeff_chain2
    (χ ψ : ForestAlgebra.Character R) :
    PTree.convolutionCoeff χ ψ PTree.chain2 =
      χ.evalForest (RootedForest.singleton RootedTree.chain2) *
          ψ.evalForest RootedForest.empty +
        χ.evalForest (RootedForest.singleton RootedTree.bullet) *
          ψ.evalForest (RootedForest.singleton RootedTree.bullet) +
        χ.evalForest RootedForest.empty *
          ψ.evalForest (RootedForest.singleton RootedTree.chain2) := by
  simp [PTree.convolutionCoeff, PTree.coproductTerms, PTree.cuts,
    PTree.rootCuts, PTree.rootCutsList, PTree.childCuts,
    PTree.RootCutList.consChild, PTree.Cut.prunedForest,
    PTree.Cut.trunkForest, PTree.evalCoproductTerms,
    PTree.evalCoproductTerm, RootedForest.singleton, RootedForest.empty,
    RootedTree.bullet, RootedTree.chain2, PTree.bullet, PTree.chain2]
  ring

/-- Chen's identity at the single-node tree: the first level is
additive. -/
theorem AlgebraicBranchedRoughPath.chen_treeCoeff_bullet
    (X : AlgebraicBranchedRoughPath T R) (s t u : T) :
    X.treeCoeff s u RootedTree.bullet =
      X.treeCoeff s t RootedTree.bullet +
        X.treeCoeff t u RootedTree.bullet := by
  rw [X.chen_treeCoeff s t u, RootedTree.bullet,
    RootedTree.convolutionCoeff_ofPTree, ptree_convolutionCoeff_bullet]
  simp [AlgebraicBranchedRoughPath.treeCoeff,
    HopfRoughPath.coeff, RootedTree.bullet]

/-- Chen's identity at the 2-chain: the classical level-2 relation. -/
theorem AlgebraicBranchedRoughPath.chen_treeCoeff_chain2
    (X : AlgebraicBranchedRoughPath T R) (s t u : T) :
    X.treeCoeff s u RootedTree.chain2 =
      X.treeCoeff s t RootedTree.chain2 +
        X.treeCoeff s t RootedTree.bullet *
          X.treeCoeff t u RootedTree.bullet +
        X.treeCoeff t u RootedTree.chain2 := by
  rw [X.chen_treeCoeff s t u, RootedTree.chain2,
    RootedTree.convolutionCoeff_ofPTree, ptree_convolutionCoeff_chain2]
  simp [AlgebraicBranchedRoughPath.treeCoeff,
    HopfRoughPath.coeff, RootedTree.bullet, RootedTree.chain2]

end ChenSmall

/-! ### Level-2 branched rough paths and controlled paths -/

/-- Level-2 Hölder-type bounds for a real branched rough path: the
single-node coefficient of order `ω^α`, the 2-chain of order `ω^{2α}`. -/
structure IsLevel2BranchedRoughPath (X : AlgebraicBranchedRoughPath ℝ ℝ)
    (ω : Control ℝ) (α : ℝ) : Prop where
  one_third_lt : 1 / 3 < α
  le_half : α ≤ 1 / 2
  bound_bullet : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖X.treeCoeff s t RootedTree.bullet‖ₑ ≤ ω s t ^ α
  bound_chain2 : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖X.treeCoeff s t RootedTree.chain2‖ₑ ≤ ω s t ^ (2 * α)

theorem IsLevel2BranchedRoughPath.alpha_pos
    {X : AlgebraicBranchedRoughPath ℝ ℝ} {ω : Control ℝ} {α : ℝ}
    (hX : IsLevel2BranchedRoughPath X ω α) : 0 < α :=
  lt_trans (by norm_num) hX.one_third_lt

theorem IsLevel2BranchedRoughPath.one_lt_three_alpha
    {X : AlgebraicBranchedRoughPath ℝ ℝ} {ω : Control ℝ} {α : ℝ}
    (hX : IsLevel2BranchedRoughPath X ω α) : 1 < 3 * α := by
  have := hX.one_third_lt
  linarith

/-- A path controlled by a level-2 branched rough path: a Gubinelli
derivative along the single-node coefficient with `ω^{2α}` remainder. -/
structure BranchedControlledPath (X : AlgebraicBranchedRoughPath ℝ ℝ)
    (ω : Control ℝ) (α : ℝ) (W : Type*)
    [NormedAddCommGroup W] [NormedSpace ℝ W] where
  /-- The underlying path. -/
  Y : ℝ → W
  /-- The Gubinelli derivative. -/
  Yd : ℝ → W
  /-- Sup bound for the derivative. -/
  Cb : ℝ≥0
  /-- Hölder constant of the derivative. -/
  Cd : ℝ≥0
  /-- Remainder constant. -/
  Cy : ℝ≥0
  bound_Yd : ∀ s : ℝ, ‖Yd s‖ₑ ≤ Cb
  holder_Yd : ∀ ⦃s t : ℝ⦄, s ≤ t → ‖Yd t - Yd s‖ₑ ≤ Cd * ω s t ^ α
  remainder : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖Y t - Y s - X.treeCoeff s t RootedTree.bullet • Yd s‖ₑ ≤
      Cy * ω s t ^ (2 * α)

/-! ### The branched Gubinelli germ -/

variable {X : AlgebraicBranchedRoughPath ℝ ℝ} {ω : Control ℝ} {α : ℝ}

/-- The branched Gubinelli germ: the two-term local expansion of
`∫_s^t Y dX^•` using the 2-chain as second-level data. -/
noncomputable def branchedGerm (Z : BranchedControlledPath X ω α E) :
    ℝ → ℝ → E :=
  fun s t => X.treeCoeff s t RootedTree.bullet • Z.Y s +
    X.treeCoeff s t RootedTree.chain2 • Z.Yd s

theorem branchedGerm_apply (Z : BranchedControlledPath X ω α E)
    (s t : ℝ) :
    branchedGerm Z s t = X.treeCoeff s t RootedTree.bullet • Z.Y s +
      X.treeCoeff s t RootedTree.chain2 • Z.Yd s :=
  rfl

/-- **The algebraic defect identity** from Chen's relations on small
trees. -/
theorem branchedGerm_defect_eq (Z : BranchedControlledPath X ω α E)
    (a b c : ℝ) :
    branchedGerm Z a c - branchedGerm Z a b - branchedGerm Z b c =
      X.treeCoeff b c RootedTree.bullet •
        (Z.Y a - Z.Y b + X.treeCoeff a b RootedTree.bullet • Z.Yd a) +
      X.treeCoeff b c RootedTree.chain2 • (Z.Yd a - Z.Yd b) := by
  rw [branchedGerm_apply, branchedGerm_apply, branchedGerm_apply,
    X.chen_treeCoeff_bullet a b c, X.chen_treeCoeff_chain2 a b c]
  module

/-- **The analytic defect bound**: order `ω^{3α}` with constant
`Cy + Cd`. -/
theorem branchedGerm_defect (hX : IsLevel2BranchedRoughPath X ω α)
    (Z : BranchedControlledPath X ω α E) :
    ∀ ⦃a b c : ℝ⦄, a ≤ b → b ≤ c →
      ‖branchedGerm Z a c - branchedGerm Z a b - branchedGerm Z b c‖ₑ ≤
        ((Z.Cy : ℝ≥0∞) + Z.Cd) * ω a c ^ (3 * α) := by
  intro a b c hab hbc
  have hα := hX.alpha_pos
  rw [branchedGerm_defect_eq Z a b c]
  refine le_trans (enorm_add_le _ _) ?_
  have hac_ab : ω a b ≤ ω a c := Sewing.control_mono ω le_rfl hab hbc
  have hac_bc : ω b c ≤ ω a c := Sewing.control_mono ω hab hbc le_rfl
  have h1 : ‖X.treeCoeff b c RootedTree.bullet •
      (Z.Y a - Z.Y b + X.treeCoeff a b RootedTree.bullet • Z.Yd a)‖ₑ ≤
      (Z.Cy : ℝ≥0∞) * ω a c ^ (3 * α) := by
    rw [ControlledPath.enorm_real_smul]
    have hneg : Z.Y a - Z.Y b + X.treeCoeff a b RootedTree.bullet • Z.Yd a =
        -(Z.Y b - Z.Y a - X.treeCoeff a b RootedTree.bullet • Z.Yd a) := by
      abel
    calc ‖X.treeCoeff b c RootedTree.bullet‖ₑ *
        ‖Z.Y a - Z.Y b + X.treeCoeff a b RootedTree.bullet • Z.Yd a‖ₑ
        ≤ ω b c ^ α * (Z.Cy * ω a b ^ (2 * α)) := by
          refine mul_le_mul' (hX.bound_bullet hbc) ?_
          rw [hneg, enorm_neg]
          exact Z.remainder hab
      _ ≤ ω a c ^ α * (Z.Cy * ω a c ^ (2 * α)) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hac_bc hα.le)
            (mul_le_mul' le_rfl
              (ENNReal.rpow_le_rpow hac_ab (by positivity)))
      _ = (Z.Cy : ℝ≥0∞) * (ω a c ^ α * ω a c ^ (2 * α)) := by ring
      _ = (Z.Cy : ℝ≥0∞) * ω a c ^ (3 * α) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ hα.le (by positivity)]
          ring_nf
  have h2 : ‖X.treeCoeff b c RootedTree.chain2 • (Z.Yd a - Z.Yd b)‖ₑ ≤
      (Z.Cd : ℝ≥0∞) * ω a c ^ (3 * α) := by
    rw [ControlledPath.enorm_real_smul]
    have hYd : ‖Z.Yd a - Z.Yd b‖ₑ ≤ Z.Cd * ω a b ^ α := by
      rw [← enorm_neg]
      have : -(Z.Yd a - Z.Yd b) = Z.Yd b - Z.Yd a := by abel
      rw [this]
      exact Z.holder_Yd hab
    calc ‖X.treeCoeff b c RootedTree.chain2‖ₑ * ‖Z.Yd a - Z.Yd b‖ₑ
        ≤ ω b c ^ (2 * α) * (Z.Cd * ω a b ^ α) :=
          mul_le_mul' (hX.bound_chain2 hbc) hYd
      _ ≤ ω a c ^ (2 * α) * (Z.Cd * ω a c ^ α) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hac_bc (by positivity))
            (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hac_ab hα.le))
      _ = (Z.Cd : ℝ≥0∞) * (ω a c ^ (2 * α) * ω a c ^ α) := by ring
      _ = (Z.Cd : ℝ≥0∞) * ω a c ^ (3 * α) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) hα.le]
          ring_nf
  calc ‖X.treeCoeff b c RootedTree.bullet •
        (Z.Y a - Z.Y b + X.treeCoeff a b RootedTree.bullet • Z.Yd a)‖ₑ +
      ‖X.treeCoeff b c RootedTree.chain2 • (Z.Yd a - Z.Yd b)‖ₑ
      ≤ (Z.Cy : ℝ≥0∞) * ω a c ^ (3 * α) +
          (Z.Cd : ℝ≥0∞) * ω a c ^ (3 * α) := add_le_add h1 h2
    _ = ((Z.Cy : ℝ≥0∞) + Z.Cd) * ω a c ^ (3 * α) := by ring

/-! ### Existence and uniqueness of the branched rough integral -/

/-- **Existence of the branched rough integral** (Gubinelli math/0610300,
level-2 case): an additive `∫ Y dX` with germ estimate of order
`ω^{3α}`, approximating compensated Riemann sums of fine partitions. -/
theorem exists_branchedRoughIntegral [CompleteSpace E]
    (hX : IsLevel2BranchedRoughPath X ω α)
    (Z : BranchedControlledPath X ω α E)
    (hfine : Sewing.HasFinePartitions ω)
    (hω : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤) :
    ∃ I : ℝ → ℝ → E,
      (∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I s u + I u t = I s t) ∧
      (∀ ⦃s t : ℝ⦄, s ≤ t →
        ‖I s t - branchedGerm Z s t‖ₑ ≤
          Sewing.sewingConst (3 * α) *
            (((Z.Cy : ℝ≥0∞) + Z.Cd) * ω s t ^ (3 * α))) ∧
      (∀ ⦃s t : ℝ⦄, s ≤ t → ∀ (ε : ℝ≥0∞) (mid : List ℝ),
        List.IsChain (fun a b => a ≤ b ∧
          Control.constMul (((Z.Cy : ℝ≥0∞) + Z.Cd) ^ (3 * α)⁻¹) ω a b ≤ ε)
          (s :: (mid ++ [t])) →
        ‖I s t - Sewing.pairSum (branchedGerm Z) (s :: (mid ++ [t]))‖ₑ ≤
          Sewing.sewingConst (3 * α) *
            (ε ^ (3 * α - 1) *
              Control.constMul (((Z.Cy : ℝ≥0∞) + Z.Cd) ^ (3 * α)⁻¹)
                ω s t)) := by
  have hα := hX.alpha_pos
  exact Sewing.sewing_const_mul ω (branchedGerm Z) hX.one_lt_three_alpha
    (by positivity)
    (ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩)
    (branchedGerm_defect hX Z) hfine hω

/-- **Uniqueness of the branched rough integral** among additive maps
with a germ bound of order `3α > 1`. -/
theorem branchedRoughIntegral_unique (hX : IsLevel2BranchedRoughPath X ω α)
    (Z : BranchedControlledPath X ω α E)
    {C C' : ℝ≥0∞} (hC : C ≠ ⊤) (hC' : C' ≠ ⊤)
    (hfine : Sewing.HasFinePartitions ω)
    {I I' : ℝ → ℝ → E}
    (hadd : ∀ ⦃a u b : ℝ⦄, a ≤ u → u ≤ b → I a u + I u b = I a b)
    (hadd' : ∀ ⦃a u b : ℝ⦄, a ≤ u → u ≤ b → I' a u + I' u b = I' a b)
    (hI : ∀ ⦃a b : ℝ⦄, a ≤ b → ‖I a b - branchedGerm Z a b‖ₑ ≤
      C * ω a b ^ (3 * α))
    (hI' : ∀ ⦃a b : ℝ⦄, a ≤ b → ‖I' a b - branchedGerm Z a b‖ₑ ≤
      C' * ω a b ^ (3 * α))
    {s t : ℝ} (hst : s ≤ t) (hω : ω s t ≠ ⊤) :
    I s t = I' s t :=
  Sewing.eq_of_additive_of_germ_bound ω (branchedGerm Z)
    hX.one_lt_three_alpha hC hC' hfine hadd hadd' hI hI' hst hω

/-- **The branched rough integral is controlled with Gubinelli derivative
`Y`**: subtracting the first-level part leaves `ω^{2α}` order plus the
sewing error. -/
theorem branchedRoughIntegral_sub_linear
    (hX : IsLevel2BranchedRoughPath X ω α)
    (Z : BranchedControlledPath X ω α E) {I : ℝ → ℝ → E}
    (hgerm : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ‖I s t - branchedGerm Z s t‖ₑ ≤
        Sewing.sewingConst (3 * α) *
          (((Z.Cy : ℝ≥0∞) + Z.Cd) * ω s t ^ (3 * α)))
    ⦃s t : ℝ⦄ (hst : s ≤ t) :
    ‖I s t - X.treeCoeff s t RootedTree.bullet • Z.Y s‖ₑ ≤
      Sewing.sewingConst (3 * α) *
        (((Z.Cy : ℝ≥0∞) + Z.Cd) * ω s t ^ (3 * α)) +
        (Z.Cb : ℝ≥0∞) * ω s t ^ (2 * α) := by
  have hsplit : I s t - X.treeCoeff s t RootedTree.bullet • Z.Y s =
      (I s t - branchedGerm Z s t) +
        X.treeCoeff s t RootedTree.chain2 • Z.Yd s := by
    rw [branchedGerm_apply]
    abel
  rw [hsplit]
  refine le_trans (enorm_add_le _ _) (add_le_add (hgerm hst) ?_)
  rw [ControlledPath.enorm_real_smul]
  calc ‖X.treeCoeff s t RootedTree.chain2‖ₑ * ‖Z.Yd s‖ₑ
      ≤ ω s t ^ (2 * α) * Z.Cb :=
        mul_le_mul' (hX.bound_chain2 hst) (Z.bound_Yd s)
    _ = (Z.Cb : ℝ≥0∞) * ω s t ^ (2 * α) := mul_comm _ _

end RoughPaths
