/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.RDE

/-!
# Log-ODE Solvers

This file adds the algebraic skeleton of log-ODE solvers for rough differential
equations. The actual ODE solve is represented by an abstract time-one flow map,
so the definitions do not assume an analytic existence theorem.

## Main definitions

* `VectorFieldFlow` - an abstract time-one flow for vector fields
* `OneStepMap.solveAlong` - composition of one-step updates along a mesh
* `IteratedVectorFields.logODEStep` - geometric log-ODE step

## References

* Terry Lyons, Michael Caruana, Thierry Levy,
  *Differential Equations Driven by Rough Paths*
* Peter Friz, Nicolas Victoir, *Multidimensional Stochastic Processes as Rough Paths*
* Castell, Gaines, *An efficient approximation method for stochastic differential equations
  by means of the exponential Lie series*

Branched (forest-indexed) analogues live downstream in LeanBSeries.
-/

namespace RoughPaths

universe u v w z y x

noncomputable section

/-- An abstract time-one flow map for vector fields. -/
structure VectorFieldFlow (E : Type u) [Zero E] where
  timeOne : (E → E) → E → E
  timeOne_zero : ∀ y, timeOne (fun _ => 0) y = y

namespace VectorFieldFlow

variable {E : Type u} [Zero E]

/-- Apply the time-one flow of a vector field. -/
def step (Φ : VectorFieldFlow E) (F : E → E) (y : E) : E :=
  Φ.timeOne F y

@[simp]
theorem step_zero (Φ : VectorFieldFlow E) (y : E) :
    Φ.step (fun _ => 0) y = y :=
  Φ.timeOne_zero y

end VectorFieldFlow

/-- A one-step method on a time domain `T` and state space `E`. -/
abbrev OneStepMap (T : Type u) (E : Type v) : Type (max u v) :=
  T → T → E → E

namespace OneStepMap

variable {T : Type u} {E : Type v}

/-- Compose one-step updates along consecutive points of a mesh. -/
def solveAlong (step : OneStepMap T E) : List T → E → E
  | [], y => y
  | _ :: [], y => y
  | s :: t :: mesh, y => solveAlong step (t :: mesh) (step s t y)

@[simp]
theorem solveAlong_nil (step : OneStepMap T E) (y : E) :
    solveAlong step [] y = y :=
  rfl

@[simp]
theorem solveAlong_singleton (step : OneStepMap T E) (t : T) (y : E) :
    solveAlong step [t] y = y :=
  rfl

@[simp]
theorem solveAlong_cons_cons
    (step : OneStepMap T E) (s t : T) (mesh : List T) (y : E) :
    solveAlong step (s :: t :: mesh) y =
      solveAlong step (t :: mesh) (step s t y) :=
  rfl

theorem solveAlong_congr {step step' : OneStepMap T E}
    (h : ∀ s t y, step s t y = step' s t y) :
    ∀ mesh y, solveAlong step mesh y = solveAlong step' mesh y
  | [], y => rfl
  | _ :: [], y => rfl
  | s :: t :: mesh, y => by
      rw [solveAlong_cons_cons, solveAlong_cons_cons, h s t y]
      exact solveAlong_congr h (t :: mesh) (step' s t y)

@[simp]
theorem solveAlong_id :
    ∀ (mesh : List T) (y : E), solveAlong (fun _ _ y => y) mesh y = y
  | [], y => rfl
  | _ :: [], y => rfl
  | s :: t :: mesh, y => by
      rw [solveAlong_cons_cons, solveAlong_id (t :: mesh) y]

end OneStepMap

namespace IteratedVectorFields

variable {α : Type u} {R : Type v} {E : Type w} {T : Type z}

/-- One geometric log-ODE step over a rough path increment. -/
def logODEStep [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : IteratedVectorFields α E)
    (X : AlgebraicRoughPath T α R) (n : Nat) (s t : T) (y : E) : E :=
  Φ.step (V.logODEVectorField X n s t) y

@[simp]
theorem logODEStep_self [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : IteratedVectorFields α E)
    (X : AlgebraicRoughPath T α R) (n : Nat) (t : T) (y : E) :
    V.logODEStep Φ X n t t y = y := by
  rw [logODEStep]
  rw [show V.logODEVectorField X n t t = fun _ => 0 by
    funext z
    simp]
  rw [VectorFieldFlow.step]
  exact Φ.timeOne_zero y

@[simp]
theorem logODEStep_zero [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : IteratedVectorFields α E)
    (X : AlgebraicRoughPath T α R) (s t : T) (y : E) :
    V.logODEStep Φ X 0 s t y = y := by
  rw [logODEStep]
  rw [show V.logODEVectorField X 0 s t = fun _ => 0 by
    funext z
    simp]
  rw [VectorFieldFlow.step]
  exact Φ.timeOne_zero y

@[simp]
theorem logODEStep_comapTime [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    {S : Type y} (f : S → T) (Φ : VectorFieldFlow E)
    (V : IteratedVectorFields α E) (X : AlgebraicRoughPath T α R)
    (n : Nat) (s t : S) (y : E) :
    V.logODEStep Φ (AlgebraicRoughPath.comapTime f X) n s t y =
      V.logODEStep Φ X n (f s) (f t) y :=
  rfl

theorem logODEStep_eq_of_agreeUpToDegree [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : IteratedVectorFields α E)
    {X Y : AlgebraicRoughPath T α R} {n : Nat}
    (h : AlgebraicRoughPath.AgreeUpToDegree X Y n)
    (s t : T) (y : E) :
    V.logODEStep Φ X n s t y = V.logODEStep Φ Y n s t y := by
  unfold logODEStep VectorFieldFlow.step
  apply congrArg (fun F => Φ.timeOne F y)
  funext z
  exact V.logODEVectorField_eq_of_agreeUpToDegree h s t z

/-- The geometric log-ODE solver along a time mesh. -/
def logODESolver [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : IteratedVectorFields α E)
    (X : AlgebraicRoughPath T α R) (n : Nat) (mesh : List T) (y : E) : E :=
  OneStepMap.solveAlong (fun s t y => V.logODEStep Φ X n s t y) mesh y

theorem logODESolver_eq_of_agreeUpToDegree [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (Φ : VectorFieldFlow E) (V : IteratedVectorFields α E)
    {X Y : AlgebraicRoughPath T α R} {n : Nat}
    (h : AlgebraicRoughPath.AgreeUpToDegree X Y n)
    (mesh : List T) (y : E) :
    V.logODESolver Φ X n mesh y = V.logODESolver Φ Y n mesh y := by
  unfold logODESolver
  apply OneStepMap.solveAlong_congr
  intro s t y
  exact V.logODEStep_eq_of_agreeUpToDegree Φ h s t y

end IteratedVectorFields

end

end RoughPaths
