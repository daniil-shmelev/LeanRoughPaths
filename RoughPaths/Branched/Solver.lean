/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.Solver
import RoughPaths.Branched.RDE

/-!
# One-step solvers for branched RDEs

Log-ODE steps along branched (labelled) rough paths, extending the
geometric solvers of `RoughPaths.Solver`.
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z y x

noncomputable section


namespace BranchedIteratedVectorFields

variable {R : Type u} {E : Type v} {T : Type w}

/-- One branched log-ODE step over a finite forest support. -/
def logODEStepOn [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : BranchedIteratedVectorFields E)
    (X : AlgebraicBranchedRoughPath T R) (n : Nat)
    (terms : List RootedForest) (s t : T) (y : E) : E :=
  Φ.step (V.logODEVectorFieldOn X n terms s t) y

@[simp]
theorem logODEStepOn_self [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : BranchedIteratedVectorFields E)
    (X : AlgebraicBranchedRoughPath T R) (n : Nat)
    (terms : List RootedForest) (t : T) (y : E) :
    V.logODEStepOn Φ X n terms t t y = y := by
  rw [logODEStepOn]
  rw [show V.logODEVectorFieldOn X n terms t t = fun _ => 0 by
    funext z
    simp]
  rw [VectorFieldFlow.step]
  exact Φ.timeOne_zero y

@[simp]
theorem logODEStepOn_zero [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : BranchedIteratedVectorFields E)
    (X : AlgebraicBranchedRoughPath T R)
    (terms : List RootedForest) (s t : T) (y : E) :
    V.logODEStepOn Φ X 0 terms s t y = y := by
  rw [logODEStepOn]
  rw [show V.logODEVectorFieldOn X 0 terms s t = fun _ => 0 by
    funext z
    simp]
  rw [VectorFieldFlow.step]
  exact Φ.timeOne_zero y

@[simp]
theorem logODEStepOn_comapTime [Field R] [AddCommMonoid E] [Module R E]
    {S : Type z} (f : S → T) (Φ : VectorFieldFlow E)
    (V : BranchedIteratedVectorFields E) (X : AlgebraicBranchedRoughPath T R)
    (n : Nat) (terms : List RootedForest) (s t : S) (y : E) :
    V.logODEStepOn Φ (AlgebraicBranchedRoughPath.comapTime f X) n terms s t y =
      V.logODEStepOn Φ X n terms (f s) (f t) y :=
  rfl

theorem logODEStepOn_eq_of_agreeUpToOrder
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : BranchedIteratedVectorFields E)
    {X Y : AlgebraicBranchedRoughPath T R} {terms : List RootedForest} {n : Nat}
    (h : AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n)
    (hterms : ∀ φ, φ ∈ terms → RootedForest.order φ ≤ n)
    (s t : T) (y : E) :
    V.logODEStepOn Φ X n terms s t y = V.logODEStepOn Φ Y n terms s t y := by
  unfold logODEStepOn VectorFieldFlow.step
  apply congrArg (fun F => Φ.timeOne F y)
  funext z
  exact V.logODEVectorFieldOn_eq_of_agreeUpToOrder h hterms s t z

/-- The branched log-ODE solver along a time mesh. -/
def logODESolverOn [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : BranchedIteratedVectorFields E)
    (X : AlgebraicBranchedRoughPath T R) (n : Nat)
    (terms : List RootedForest) (mesh : List T) (y : E) : E :=
  OneStepMap.solveAlong (fun s t y => V.logODEStepOn Φ X n terms s t y) mesh y

theorem logODESolverOn_eq_of_agreeUpToOrder
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : BranchedIteratedVectorFields E)
    {X Y : AlgebraicBranchedRoughPath T R} {terms : List RootedForest} {n : Nat}
    (h : AlgebraicBranchedRoughPath.AgreeUpToOrder X Y n)
    (hterms : ∀ φ, φ ∈ terms → RootedForest.order φ ≤ n)
    (mesh : List T) (y : E) :
    V.logODESolverOn Φ X n terms mesh y =
      V.logODESolverOn Φ Y n terms mesh y := by
  unfold logODESolverOn
  apply OneStepMap.solveAlong_congr
  intro s t y
  exact V.logODEStepOn_eq_of_agreeUpToOrder Φ h hterms s t y

end BranchedIteratedVectorFields

namespace LabelledBranchedIteratedVectorFields

variable {α : Type u} {R : Type v} {E : Type w} {T : Type z}

/-- One labelled branched log-ODE step over a finite labelled forest support. -/
def logODEStepOn [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R) (n : Nat)
    (terms : List (LRootedForest α)) (s t : T) (y : E) : E :=
  Φ.step (V.logODEVectorFieldOn X n terms s t) y

@[simp]
theorem logODEStepOn_self [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R) (n : Nat)
    (terms : List (LRootedForest α)) (t : T) (y : E) :
    V.logODEStepOn Φ X n terms t t y = y := by
  rw [logODEStepOn]
  rw [show V.logODEVectorFieldOn X n terms t t = fun _ => 0 by
    funext z
    simp]
  rw [VectorFieldFlow.step]
  exact Φ.timeOne_zero y

@[simp]
theorem logODEStepOn_zero [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (terms : List (LRootedForest α)) (s t : T) (y : E) :
    V.logODEStepOn Φ X 0 terms s t y = y := by
  rw [logODEStepOn]
  rw [show V.logODEVectorFieldOn X 0 terms s t = fun _ => 0 by
    funext z
    simp]
  rw [VectorFieldFlow.step]
  exact Φ.timeOne_zero y

@[simp]
theorem logODEStepOn_comapTime [Field R] [AddCommMonoid E] [Module R E]
    {S : Type y} (f : S → T) (Φ : VectorFieldFlow E)
    (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R)
    (n : Nat) (terms : List (LRootedForest α)) (s t : S) (y : E) :
    V.logODEStepOn Φ
        (AlgebraicLabelledBranchedRoughPath.comapTime f X) n terms s t y =
      V.logODEStepOn Φ X n terms (f s) (f t) y :=
  rfl

theorem logODEStepOn_eq_of_agreeUpToOrder
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : LabelledBranchedIteratedVectorFields α E)
    {X Y : AlgebraicLabelledBranchedRoughPath T α R}
    {terms : List (LRootedForest α)} {n : Nat}
    (h : AlgebraicLabelledBranchedRoughPath.AgreeUpToOrder X Y n)
    (hterms : ∀ φ, φ ∈ terms → LRootedForest.order φ ≤ n)
    (s t : T) (y : E) :
    V.logODEStepOn Φ X n terms s t y =
      V.logODEStepOn Φ Y n terms s t y := by
  unfold logODEStepOn VectorFieldFlow.step
  apply congrArg (fun F => Φ.timeOne F y)
  funext z
  exact V.logODEVectorFieldOn_eq_of_agreeUpToOrder h hterms s t z

/-- The labelled branched log-ODE solver along a time mesh. -/
def logODESolverOn [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : LabelledBranchedIteratedVectorFields α E)
    (X : AlgebraicLabelledBranchedRoughPath T α R) (n : Nat)
    (terms : List (LRootedForest α)) (mesh : List T) (y : E) : E :=
  OneStepMap.solveAlong (fun s t y => V.logODEStepOn Φ X n terms s t y) mesh y

theorem logODESolverOn_eq_of_agreeUpToOrder
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : LabelledBranchedIteratedVectorFields α E)
    {X Y : AlgebraicLabelledBranchedRoughPath T α R}
    {terms : List (LRootedForest α)} {n : Nat}
    (h : AlgebraicLabelledBranchedRoughPath.AgreeUpToOrder X Y n)
    (hterms : ∀ φ, φ ∈ terms → LRootedForest.order φ ≤ n)
    (mesh : List T) (y : E) :
    V.logODESolverOn Φ X n terms mesh y =
      V.logODESolverOn Φ Y n terms mesh y := by
  unfold logODESolverOn
  apply OneStepMap.solveAlong_congr
  intro s t y
  exact V.logODEStepOn_eq_of_agreeUpToOrder Φ h hterms s t y

end LabelledBranchedIteratedVectorFields

end

end RoughPaths
