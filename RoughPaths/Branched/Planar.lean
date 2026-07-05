/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.MKWDual
import HopfAlgebras.Combinatorial.MKW
import RoughPaths.HopfRoughPath.Basic
import RoughPaths.Integration.ControlledPath
import RoughPaths.Sewing.Scaled
import RoughPaths.Sewing.Unique

/-!
# Planarly branched rough paths via the MKW Hopf algebra

Planarly branched rough paths (Curry–Ebrahimi-Fard–Manchon–Munthe-Kaas,
*Planarly branched rough paths and rough differential equations on
homogeneous spaces*) are **defined as Hopf rough paths over the MKW
bialgebra**: increments are characters of `mkwBialg` — equivalently,
shuffle characters on ordered forests
(`isShuffleCharacter_iff_isCharacter`) — and Chen's identity is
convolution in the character monoid, i.e. the Grossman–Larson
convolution dual to the Munthe-Kaas–Wright coproduct
(`mkwConvolution_eq_conv`). The generic theory (unit path, time
reparametrisation, reverse increments, coefficient Chen) comes from
`RoughPaths.HopfRoughPath`.

At level 2 the ordered forests of order at most two are `[•]`, `[chain2]`
and `[•,•]`, and the MKW coproduct on them yields the Chen relations
`X^{[•]}(s,u) = X^{[•]}(s,t) + X^{[•]}(t,u)` and
`X^ω(s,u) = X^ω(s,t) + X^{[•]}(s,t)·X^{[•]}(t,u) + X^ω(t,u)` for
`ω ∈ {[chain2], [•,•]}`. The controlled-path germ
`Ξ = X^{[•]}·Y + X^{[chain2]}·Y' + X^{[•,•]}·Y''` therefore has defect of
order `ω^{3α}` — with Gubinelli derivative `Y' + Y''` — and sews into the
planarly branched rough integral.
-/

namespace RoughPaths

open scoped ENNReal NNReal
open HopfAlgebras

universe u v

/-! ### Planarly branched rough paths -/

/-- A planarly branched rough path **is** a Hopf rough path over the
Munthe-Kaas–Wright bialgebra: increments are shuffle characters on
ordered forests and Chen's identity is Grossman–Larson convolution. -/
abbrev PlanarBranchedRoughPath (T : Type u) (R : Type v)
    [CommSemiring R] : Type (max u v) :=
  HopfRoughPath mkwBialg T R

namespace PlanarBranchedRoughPath

variable {T : Type u} {R : Type v} [CommSemiring R]

/-- Increments are shuffle characters on ordered forests. -/
theorem isShuffleCharacter (X : PlanarBranchedRoughPath T R) (s t : T) :
    PlanarForest.IsShuffleCharacter
      (X.increment s t : PlanarForest → R) :=
  (isShuffleCharacter_iff_isCharacter _).mpr (X.increment s t).2

@[simp]
theorem coeff_nil (X : PlanarBranchedRoughPath T R) (s t : T) :
    (X.increment s t : PlanarForest → R) ([] : PlanarForest) = 1 :=
  X.coeff_one s t

/-- The counit is a shuffle character. -/
theorem counitCoeff_isShuffleCharacter :
    PlanarForest.IsShuffleCharacter
      (PlanarForestAlgebra.counitCoeff (R := R)) := by
  constructor
  · exact PlanarForestAlgebra.counitCoeff_nil
  · intro ω₁ ω₂
    rcases ω₁ with _ | ⟨t₁, ω₁⟩
    · rw [Word.shuffle_nil_left]
      simp
    · have hzero : ∀ x ∈ Word.shuffle (t₁ :: ω₁) ω₂,
          PlanarForestAlgebra.counitCoeff (R := R) x = 0 := by
        intro x hx
        have hperm := Word.perm_append_of_mem_shuffle hx
        have hlen : x.length = (t₁ :: ω₁ ++ ω₂).length := hperm.length_eq
        refine PlanarForestAlgebra.counitCoeff_ne_nil fun hnil => ?_
        rw [hnil] at hlen
        simp at hlen
      rw [List.sum_eq_zero fun x hx => by
        rcases List.mem_map.1 hx with ⟨w, hw, rfl⟩
        exact hzero w hw]
      rw [PlanarForestAlgebra.counitCoeff_ne_nil (List.cons_ne_nil _ _),
        zero_mul]

-- The unit rough path and time reparametrisation are inherited from
-- `HopfRoughPath.unit` and `HopfRoughPath.comapTime`.

/-- Chen's identity in MKW coefficient form. -/
theorem chen_coeff (X : PlanarBranchedRoughPath T R) (s t u : T)
    (ω : PlanarForest) :
    X.coeff s u ω =
      ((PlanarForest.mkwTerms ω).map fun pr =>
        X.coeff s t pr.1 * X.coeff t u pr.2).sum :=
  HopfRoughPath.chen_coeff X s t u ω

/-! ### Chen's identity on forests of order at most two -/

/-- Chen at the single-bullet forest: additivity of the first level. -/
theorem chen_coeff_bullet (X : PlanarBranchedRoughPath T R) (s t u : T) :
    X.coeff s u [PTree.bullet] =
      X.coeff s t [PTree.bullet] + X.coeff t u [PTree.bullet] := by
  rw [chen_coeff X s t u, PlanarForest.mkwTerms_bullet_forest]
  simp

/-- Chen at the 2-chain forest. -/
theorem chen_coeff_chain2 (X : PlanarBranchedRoughPath T R) (s t u : T) :
    X.coeff s u [PTree.chain2] =
      X.coeff s t [PTree.chain2] +
        X.coeff s t [PTree.bullet] * X.coeff t u [PTree.bullet] +
        X.coeff t u [PTree.chain2] := by
  rw [chen_coeff X s t u, PlanarForest.mkwTerms_chain2_forest]
  simp [add_assoc]

/-- Chen at the two-bullet forest. -/
theorem chen_coeff_bullet_bullet (X : PlanarBranchedRoughPath T R)
    (s t u : T) :
    X.coeff s u [PTree.bullet, PTree.bullet] =
      X.coeff s t [PTree.bullet, PTree.bullet] +
        X.coeff s t [PTree.bullet] * X.coeff t u [PTree.bullet] +
        X.coeff t u [PTree.bullet, PTree.bullet] := by
  rw [chen_coeff X s t u, PlanarForest.mkwTerms_bullet_bullet_forest]
  simp [add_assoc]

/-- For shuffle characters, the two-bullet coefficient is determined by
the first level: `2·X^{[•,•]} = (X^{[•]})²`. -/
theorem two_mul_coeff_bullet_bullet (X : PlanarBranchedRoughPath T R)
    (s t : T) :
    2 * X.coeff s t [PTree.bullet, PTree.bullet] =
      X.coeff s t [PTree.bullet] * X.coeff s t [PTree.bullet] := by
  have h := (isShuffleCharacter X s t).2 [PTree.bullet] [PTree.bullet]
  have hs : Word.shuffle [PTree.bullet] [PTree.bullet] =
      [[PTree.bullet, PTree.bullet], [PTree.bullet, PTree.bullet]] := by
    simp
  rw [hs] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at h
  show 2 * (X.increment s t : PlanarForest → R)
      [PTree.bullet, PTree.bullet] =
    (X.increment s t : PlanarForest → R) [PTree.bullet] *
      (X.increment s t : PlanarForest → R) [PTree.bullet]
  rw [two_mul]
  exact h

end PlanarBranchedRoughPath

/-! ### Level-2 analytic bounds and controlled paths -/

/-- Level-2 Hölder-type bounds for a real planarly branched rough path:
order-one forests of size `ω^α`, order-two forests of size `ω^{2α}`. -/
structure IsLevel2PlanarBranchedRoughPath
    (X : PlanarBranchedRoughPath ℝ ℝ) (ω : Control ℝ) (α : ℝ) : Prop where
  one_third_lt : 1 / 3 < α
  le_half : α ≤ 1 / 2
  bound_bullet : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖X.coeff s t [PTree.bullet]‖ₑ ≤ ω s t ^ α
  bound_chain2 : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖X.coeff s t [PTree.chain2]‖ₑ ≤ ω s t ^ (2 * α)
  bound_bullet_bullet : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖X.coeff s t [PTree.bullet, PTree.bullet]‖ₑ ≤ ω s t ^ (2 * α)

theorem IsLevel2PlanarBranchedRoughPath.alpha_pos
    {X : PlanarBranchedRoughPath ℝ ℝ} {ω : Control ℝ} {α : ℝ}
    (hX : IsLevel2PlanarBranchedRoughPath X ω α) : 0 < α :=
  lt_trans (by norm_num) hX.one_third_lt

theorem IsLevel2PlanarBranchedRoughPath.one_lt_three_alpha
    {X : PlanarBranchedRoughPath ℝ ℝ} {ω : Control ℝ} {α : ℝ}
    (hX : IsLevel2PlanarBranchedRoughPath X ω α) : 1 < 3 * α := by
  have := hX.one_third_lt
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : PlanarBranchedRoughPath ℝ ℝ} {ω : Control ℝ} {α : ℝ}

/-- A path controlled by a level-2 planarly branched rough path, with one
derivative slot per order-two forest; the Gubinelli derivative pairing
the first level is their sum. -/
structure PlanarControlledPath (X : PlanarBranchedRoughPath ℝ ℝ)
    (ω : Control ℝ) (α : ℝ) (W : Type*)
    [NormedAddCommGroup W] [NormedSpace ℝ W] where
  /-- The underlying path. -/
  Y : ℝ → W
  /-- The derivative slot paired with the 2-chain forest. -/
  Yd : ℝ → W
  /-- The derivative slot paired with the two-bullet forest. -/
  Ye : ℝ → W
  /-- Sup bound for the derivative slots. -/
  Cb : ℝ≥0
  /-- Hölder constant of the derivative slots. -/
  Cd : ℝ≥0
  /-- Remainder constant. -/
  Cy : ℝ≥0
  bound_Yd : ∀ s : ℝ, ‖Yd s‖ₑ ≤ Cb
  bound_Ye : ∀ s : ℝ, ‖Ye s‖ₑ ≤ Cb
  holder_Yd : ∀ ⦃s t : ℝ⦄, s ≤ t → ‖Yd t - Yd s‖ₑ ≤ Cd * ω s t ^ α
  holder_Ye : ∀ ⦃s t : ℝ⦄, s ≤ t → ‖Ye t - Ye s‖ₑ ≤ Cd * ω s t ^ α
  remainder : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ‖Y t - Y s - X.coeff s t [PTree.bullet] • (Yd s + Ye s)‖ₑ ≤
      Cy * ω s t ^ (2 * α)

/-! ### The planarly branched Gubinelli germ -/

/-- The planarly branched Gubinelli germ: one term per forest of order
at most two. -/
noncomputable def planarGerm (Z : PlanarControlledPath X ω α E) :
    ℝ → ℝ → E :=
  fun s t => X.coeff s t [PTree.bullet] • Z.Y s +
    X.coeff s t [PTree.chain2] • Z.Yd s +
    X.coeff s t [PTree.bullet, PTree.bullet] • Z.Ye s

theorem planarGerm_apply (Z : PlanarControlledPath X ω α E) (s t : ℝ) :
    planarGerm Z s t = X.coeff s t [PTree.bullet] • Z.Y s +
      X.coeff s t [PTree.chain2] • Z.Yd s +
      X.coeff s t [PTree.bullet, PTree.bullet] • Z.Ye s :=
  rfl

/-- **The algebraic defect identity** from the MKW Chen relations on
small forests. -/
theorem planarGerm_defect_eq (Z : PlanarControlledPath X ω α E)
    (a b c : ℝ) :
    planarGerm Z a c - planarGerm Z a b - planarGerm Z b c =
      X.coeff b c [PTree.bullet] •
        (Z.Y a - Z.Y b + X.coeff a b [PTree.bullet] • (Z.Yd a + Z.Ye a)) +
      X.coeff b c [PTree.chain2] • (Z.Yd a - Z.Yd b) +
      X.coeff b c [PTree.bullet, PTree.bullet] • (Z.Ye a - Z.Ye b) := by
  rw [planarGerm_apply, planarGerm_apply, planarGerm_apply,
    PlanarBranchedRoughPath.chen_coeff_bullet X a b c,
    PlanarBranchedRoughPath.chen_coeff_chain2 X a b c,
    PlanarBranchedRoughPath.chen_coeff_bullet_bullet X a b c]
  module

/-- **The analytic defect bound**: order `ω^{3α}` with constant
`Cy + 2·Cd`. -/
theorem planarGerm_defect (hX : IsLevel2PlanarBranchedRoughPath X ω α)
    (Z : PlanarControlledPath X ω α E) :
    ∀ ⦃a b c : ℝ⦄, a ≤ b → b ≤ c →
      ‖planarGerm Z a c - planarGerm Z a b - planarGerm Z b c‖ₑ ≤
        ((Z.Cy : ℝ≥0∞) + 2 * Z.Cd) * ω a c ^ (3 * α) := by
  intro a b c hab hbc
  have hα := hX.alpha_pos
  rw [planarGerm_defect_eq Z a b c]
  have hac_ab : ω a b ≤ ω a c := Sewing.control_mono ω le_rfl hab hbc
  have hac_bc : ω b c ≤ ω a c := Sewing.control_mono ω hab hbc le_rfl
  have h1 : ‖X.coeff b c [PTree.bullet] •
      (Z.Y a - Z.Y b + X.coeff a b [PTree.bullet] •
        (Z.Yd a + Z.Ye a))‖ₑ ≤ (Z.Cy : ℝ≥0∞) * ω a c ^ (3 * α) := by
    rw [ControlledPath.enorm_real_smul]
    have hneg : Z.Y a - Z.Y b + X.coeff a b [PTree.bullet] •
        (Z.Yd a + Z.Ye a) =
        -(Z.Y b - Z.Y a - X.coeff a b [PTree.bullet] •
          (Z.Yd a + Z.Ye a)) := by abel
    calc ‖X.coeff b c [PTree.bullet]‖ₑ *
        ‖Z.Y a - Z.Y b + X.coeff a b [PTree.bullet] •
          (Z.Yd a + Z.Ye a)‖ₑ
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
  have hsecond : ∀ (x : ℝ) (V : ℝ → E),
      (∀ ⦃s t : ℝ⦄, s ≤ t → ‖V t - V s‖ₑ ≤ Z.Cd * ω s t ^ α) →
      ‖x‖ₑ ≤ ω b c ^ (2 * α) →
      ‖x • (V a - V b)‖ₑ ≤ (Z.Cd : ℝ≥0∞) * ω a c ^ (3 * α) := by
    intro x V hV hx
    rw [ControlledPath.enorm_real_smul]
    have hVab : ‖V a - V b‖ₑ ≤ Z.Cd * ω a b ^ α := by
      rw [← enorm_neg, show -(V a - V b) = V b - V a by abel]
      exact hV hab
    calc ‖x‖ₑ * ‖V a - V b‖ₑ
        ≤ ω b c ^ (2 * α) * (Z.Cd * ω a b ^ α) := mul_le_mul' hx hVab
      _ ≤ ω a c ^ (2 * α) * (Z.Cd * ω a c ^ α) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hac_bc (by positivity))
            (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hac_ab hα.le))
      _ = (Z.Cd : ℝ≥0∞) * (ω a c ^ (2 * α) * ω a c ^ α) := by ring
      _ = (Z.Cd : ℝ≥0∞) * ω a c ^ (3 * α) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) hα.le]
          ring_nf
  have h2 : ‖X.coeff b c [PTree.chain2] • (Z.Yd a - Z.Yd b)‖ₑ ≤
      (Z.Cd : ℝ≥0∞) * ω a c ^ (3 * α) :=
    hsecond _ Z.Yd Z.holder_Yd (hX.bound_chain2 hbc)
  have h3 : ‖X.coeff b c [PTree.bullet, PTree.bullet] •
      (Z.Ye a - Z.Ye b)‖ₑ ≤ (Z.Cd : ℝ≥0∞) * ω a c ^ (3 * α) :=
    hsecond _ Z.Ye Z.holder_Ye (hX.bound_bullet_bullet hbc)
  calc ‖X.coeff b c [PTree.bullet] •
        (Z.Y a - Z.Y b + X.coeff a b [PTree.bullet] •
          (Z.Yd a + Z.Ye a)) +
      X.coeff b c [PTree.chain2] • (Z.Yd a - Z.Yd b) +
      X.coeff b c [PTree.bullet, PTree.bullet] • (Z.Ye a - Z.Ye b)‖ₑ
      ≤ ‖X.coeff b c [PTree.bullet] •
          (Z.Y a - Z.Y b + X.coeff a b [PTree.bullet] •
            (Z.Yd a + Z.Ye a)) +
          X.coeff b c [PTree.chain2] • (Z.Yd a - Z.Yd b)‖ₑ +
        ‖X.coeff b c [PTree.bullet, PTree.bullet] •
          (Z.Ye a - Z.Ye b)‖ₑ := enorm_add_le _ _
    _ ≤ (‖X.coeff b c [PTree.bullet] •
          (Z.Y a - Z.Y b + X.coeff a b [PTree.bullet] •
            (Z.Yd a + Z.Ye a))‖ₑ +
        ‖X.coeff b c [PTree.chain2] • (Z.Yd a - Z.Yd b)‖ₑ) +
        ‖X.coeff b c [PTree.bullet, PTree.bullet] •
          (Z.Ye a - Z.Ye b)‖ₑ :=
        add_le_add (enorm_add_le _ _) le_rfl
    _ ≤ ((Z.Cy : ℝ≥0∞) * ω a c ^ (3 * α) +
          (Z.Cd : ℝ≥0∞) * ω a c ^ (3 * α)) +
        (Z.Cd : ℝ≥0∞) * ω a c ^ (3 * α) :=
        add_le_add (add_le_add h1 h2) h3
    _ = ((Z.Cy : ℝ≥0∞) + 2 * Z.Cd) * ω a c ^ (3 * α) := by ring

/-! ### Existence and uniqueness of the planarly branched rough
integral -/

/-- **Existence of the planarly branched rough integral**: an additive
`∫ Y dX` with germ estimate of order `ω^{3α}`, approximating compensated
Riemann sums of fine partitions. -/
theorem exists_planarBranchedRoughIntegral [CompleteSpace E]
    (hX : IsLevel2PlanarBranchedRoughPath X ω α)
    (Z : PlanarControlledPath X ω α E)
    (hfine : Sewing.HasFinePartitions ω)
    (hω : ∀ ⦃s t : ℝ⦄, s ≤ t → ω s t ≠ ⊤) :
    ∃ I : ℝ → ℝ → E,
      (∀ ⦃s u t : ℝ⦄, s ≤ u → u ≤ t → I s u + I u t = I s t) ∧
      (∀ ⦃s t : ℝ⦄, s ≤ t →
        ‖I s t - planarGerm Z s t‖ₑ ≤
          Sewing.sewingConst (3 * α) *
            (((Z.Cy : ℝ≥0∞) + 2 * Z.Cd) * ω s t ^ (3 * α))) ∧
      (∀ ⦃s t : ℝ⦄, s ≤ t → ∀ (ε : ℝ≥0∞) (mid : List ℝ),
        List.IsChain (fun a b => a ≤ b ∧
          Control.constMul (((Z.Cy : ℝ≥0∞) + 2 * Z.Cd) ^ (3 * α)⁻¹) ω
            a b ≤ ε) (s :: (mid ++ [t])) →
        ‖I s t - Sewing.pairSum (planarGerm Z) (s :: (mid ++ [t]))‖ₑ ≤
          Sewing.sewingConst (3 * α) *
            (ε ^ (3 * α - 1) *
              Control.constMul (((Z.Cy : ℝ≥0∞) + 2 * Z.Cd) ^ (3 * α)⁻¹)
                ω s t)) := by
  have hα := hX.alpha_pos
  exact Sewing.sewing_const_mul ω (planarGerm Z) hX.one_lt_three_alpha
    (by positivity)
    (ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top,
      ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top⟩)
    (planarGerm_defect hX Z) hfine hω

/-- **Uniqueness of the planarly branched rough integral** among additive
maps with a germ bound of order `3α > 1`. -/
theorem planarBranchedRoughIntegral_unique
    (hX : IsLevel2PlanarBranchedRoughPath X ω α)
    (Z : PlanarControlledPath X ω α E)
    {C C' : ℝ≥0∞} (hC : C ≠ ⊤) (hC' : C' ≠ ⊤)
    (hfine : Sewing.HasFinePartitions ω)
    {I I' : ℝ → ℝ → E}
    (hadd : ∀ ⦃a u b : ℝ⦄, a ≤ u → u ≤ b → I a u + I u b = I a b)
    (hadd' : ∀ ⦃a u b : ℝ⦄, a ≤ u → u ≤ b → I' a u + I' u b = I' a b)
    (hI : ∀ ⦃a b : ℝ⦄, a ≤ b → ‖I a b - planarGerm Z a b‖ₑ ≤
      C * ω a b ^ (3 * α))
    (hI' : ∀ ⦃a b : ℝ⦄, a ≤ b → ‖I' a b - planarGerm Z a b‖ₑ ≤
      C' * ω a b ^ (3 * α))
    {s t : ℝ} (hst : s ≤ t) (hω : ω s t ≠ ⊤) :
    I s t = I' s t :=
  Sewing.eq_of_additive_of_germ_bound ω (planarGerm Z)
    hX.one_lt_three_alpha hC hC' hfine hadd hadd' hI hI' hst hω

end RoughPaths
