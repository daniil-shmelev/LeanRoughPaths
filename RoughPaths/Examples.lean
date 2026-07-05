/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.CharacterConvolution
import RoughPaths.Integration.FinePartitions
import RoughPaths.Signature.Linear
import RoughPaths.Signature.Piecewise
import RoughPaths.Signature.Primitive
import RoughPaths.Signature.Kernel
import RoughPaths.Integration.Instances
import RoughPaths.Integration.RoughIntegral

/-!
# Smoke tests

Concrete instances certifying the formalisation: computable signature and
kernel values over `ℚ` checked by `native_decide`, together with
instantiations of the main abstract theorems.
-/

namespace RoughPaths.Examples

open RoughPaths RoughPaths.Word

/-! ### Tree algebras: the convolution unit is the counit -/

example : HopfAlgebras.ForestAlgebra.Character.unit ℚ =
    HopfAlgebras.ForestAlgebra.counit ℚ := rfl

/-! ### Controls: the linear control admits fine partitions -/

example : Sewing.HasFinePartitions (Control.ofReal 1) :=
  Control.ofReal_hasFinePartitions ENNReal.one_ne_top

/-! ### Linear-path signatures -/

/-- The linear segment with increments `(2, 3)` in two coordinates. -/
private def v₀ : Fin 2 → ℚ := ![2, 3]

example : IsGroupLike (linearSignature v₀) :=
  isGroupLike_linearSignature v₀

-- first-level coefficient: the increment itself
example : linearSignature v₀ [0] = 2 := by native_decide
-- second-level coefficient: `v(0)·v(1)/2!`
example : linearSignature v₀ [0, 1] = 3 := by native_decide
example : linearSignature v₀ [1, 0] = 3 := by native_decide
example : linearSignature v₀ [0, 0, 1] = 2 := by native_decide

-- the reversed segment inverts the signature (semigroup law at `a+b=0`)
example : IsGroupLike (linearSignature (-v₀)) :=
  isGroupLike_linearSignature _
example : Word.tensorProduct (linearSignature v₀)
    (linearSignature (-v₀)) [0, 1] = 0 := by native_decide

/-! ### The rough-path lift of a linear path -/

-- Chen increments of the lift `t ↦ t·(1,1)` over ℚ, evaluated
example : (AlgebraicRoughPath.ofLinear (fun _ : Fin 2 => (1 : ℚ))).coeff
    0 2 [0, 1] = 2 := by native_decide
example : (AlgebraicRoughPath.ofLinear (fun _ : Fin 2 => (1 : ℚ))).coeff
    (-1) 1 [0, 1, 1] = 4 / 3 := by native_decide

/-! ### Piecewise-linear signatures and Chen's theorem -/

/-- The two unit-axis segments: right, then up. -/
private def seg₁ : Fin 2 → ℚ := ![1, 0]
private def seg₂ : Fin 2 → ℚ := ![0, 1]

-- the L-shaped path has full "ordered area" in the `xy` slot …
example : piecewiseLinearSignature [seg₁, seg₂] [0, 1] = 1 := by
  native_decide
-- … and none in the `yx` slot
example : piecewiseLinearSignature [seg₁, seg₂] [1, 0] = 0 := by
  native_decide
-- Lévy area of the L-path: antisymmetrised second level
example : piecewiseLinearSignature [seg₁, seg₂] [0, 1] -
    piecewiseLinearSignature [seg₁, seg₂] [1, 0] = 1 := by native_decide

example : IsGroupLike (piecewiseLinearSignature [seg₁, seg₂]) :=
  isGroupLike_piecewiseLinearSignature _

/-! ### Primitivity of the truncated log-signature -/

example (v : Fin 2 → ℚ) :
    IsPrimitiveUpToDegree
      (logSignatureTruncated (linearSignature v) 3) 3 :=
  isPrimitiveUpToDegree_logSignatureTruncated
    (isGroupLike_linearSignature v) 3

-- a concrete vanishing mixed shuffle sum, evaluated numerically
example : shuffleCoeff
    (logSignatureTruncated (piecewiseLinearSignature [seg₁, seg₂]) 4)
    [0] [1] = 0 := by native_decide
example : shuffleCoeff
    (logSignatureTruncated (piecewiseLinearSignature [seg₁, seg₂]) 4)
    [0, 1] [1] = 0 := by native_decide

/-! ### Signature kernels -/

-- the kernel of the L-path with itself through level 2:
-- `1 + 1 + 1 + (1/2)² + 1² + 0² + (1/2)² = 9/2`
example : sigKernelTruncated [0, 1]
    (piecewiseLinearSignature [seg₁, seg₂])
    (piecewiseLinearSignature [seg₁, seg₂]) 2 = 9 / 2 := by native_decide

-- kernel between the L-path and the single diagonal segment
example : sigKernelTruncated [0, 1]
    (piecewiseLinearSignature [seg₁, seg₂])
    (linearSignature ![1, 1]) 2 = 4 := by native_decide

example (a b : List (Fin 2) → ℚ) (n : ℕ) :
    sigKernelTruncated [0, 1] a b n = sigKernelTruncated [0, 1] b a n :=
  sigKernelTruncated_comm _ a b n

/-! ### Rough integration against the trivial rough path -/

-- the unit rough path is level-2 bounded by any control
example : IsLevel2RoughPath (AlgebraicRoughPath.unit ℝ (Fin 2) ℝ)
    (Control.ofReal 1) (1 / 2) where
  one_third_lt := by norm_num
  le_half := le_rfl
  bound_one _ _ _ i := by
    show ‖(0 : ℝ)‖ₑ ≤ _
    simp
  bound_two _ _ _ i j := by
    show ‖(0 : ℝ)‖ₑ ≤ _
    simp

-- the Gubinelli germ of any constant integrand against it vanishes
example (w : Fin 2 → Fin 2 → ℝ) (s t : ℝ) :
    gubinelliGerm (ControlledPath.const
      (AlgebraicRoughPath.unit ℝ (Fin 2) ℝ) (Control.ofReal 1) (1 / 2) w)
      s t = 0 := by
  rw [gubinelliGerm_apply]
  show (∑ i, (0 : ℝ) • _) + (∑ i : Fin 2, ∑ j : Fin 2, (0 : ℝ) • _) = 0
  simp

end RoughPaths.Examples
