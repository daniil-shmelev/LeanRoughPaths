/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.Analytic
import RoughPaths.HopfRoughPath.Instances
import RoughPaths.Signature.Log

/-!
# Weakly Geometric Rough Paths

This file gives the named weakly geometric rough path layer. In the current
library this is the algebraic, group-like signature-valued notion: increments
satisfy Chen's identity and the shuffle identities. The metric closure
definition of geometric rough paths can be added once the corresponding
topology on truncated tensor algebras is available.

## Main definitions

* `WeakGeometricRoughPath` - weakly geometric rough paths as group-like word
  signature increments
* `ControlledWeakGeometricRoughPath` - weakly geometric rough paths equipped
  with coordinate bounds by a control
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z y

/-- A weakly geometric rough path **is** a Hopf rough path over the word
shuffle Hopf algebra: increments are characters — group-like signature
series — and Chen's identity is convolution in the character monoid. -/
abbrev WeakGeometricRoughPath (T : Type u) (α : Type v) (R : Type w)
    [CommSemiring R] : Type (max u v w) :=
  HopfRoughPath (wordHopf α).toCombBialg T R

namespace WeakGeometricRoughPath

section Semiring

variable {T : Type u} {α : Type v} {R : Type w} [CommSemiring R]

/-- The underlying group-like algebraic rough path. -/
def toAlgebraic (X : WeakGeometricRoughPath T α R) :
    AlgebraicRoughPath T α R :=
  HopfRoughPath.toWord X

theorem isWeaklyGeometric (X : WeakGeometricRoughPath T α R) :
    X.toAlgebraic.IsWeaklyGeometric :=
  HopfRoughPath.toWord_isWeaklyGeometric X

instance : Coe (WeakGeometricRoughPath T α R) (AlgebraicRoughPath T α R) where
  coe X := X.toAlgebraic

/-- Regard an algebraic group-like rough path as weakly geometric. -/
def ofAlgebraic (X : AlgebraicRoughPath T α R) (hX : X.IsWeaklyGeometric) :
    WeakGeometricRoughPath T α R :=
  AlgebraicRoughPath.toHopf X hX

@[simp]
theorem toAlgebraic_ofAlgebraic (X : AlgebraicRoughPath T α R)
    (hX : X.IsWeaklyGeometric) :
    (ofAlgebraic X hX).toAlgebraic = X :=
  rfl

@[simp]
theorem ofAlgebraic_toAlgebraic (X : WeakGeometricRoughPath T α R)
    (h : X.toAlgebraic.IsWeaklyGeometric) :
    ofAlgebraic X.toAlgebraic h = X :=
  HopfRoughPath.toWord_toHopf X

@[ext]
theorem ext {X Y : WeakGeometricRoughPath T α R}
    (h : X.toAlgebraic = Y.toAlgebraic) : X = Y :=
  HopfRoughPath.ext fun s t => Subtype.ext
    (congrFun (congrFun (congrArg AlgebraicRoughPath.increment h) s) t)

/-- Weakly geometric rough paths are equivalent to group-like algebraic ones. -/
def equivAlgebraic :
    WeakGeometricRoughPath T α R ≃
      {X : AlgebraicRoughPath T α R // X.IsWeaklyGeometric} where
  toFun X := ⟨X.toAlgebraic, X.isWeaklyGeometric⟩
  invFun X := ofAlgebraic X.1 X.2
  left_inv X := ofAlgebraic_toAlgebraic X X.isWeaklyGeometric
  right_inv _ := rfl

/-- The constant identity weakly geometric rough path. -/
def unit (T : Type u) (α : Type v) (R : Type w) [CommSemiring R] :
    WeakGeometricRoughPath T α R :=
  ofAlgebraic (AlgebraicRoughPath.unit T α R)
    AlgebraicRoughPath.unit_isWeaklyGeometric

/-- Pull a weakly geometric rough path back along a map of time domains. -/
def comapTime {S : Type z} (f : S → T)
    (X : WeakGeometricRoughPath T α R) : WeakGeometricRoughPath S α R :=
  ofAlgebraic (AlgebraicRoughPath.comapTime f X.toAlgebraic)
    (X.isWeaklyGeometric.comapTime f)

/-- Pull a weakly geometric rough path back along a map of alphabets. -/
def comapMapLetters {β : Type z} (f : α → β)
    (X : WeakGeometricRoughPath T β R) : WeakGeometricRoughPath T α R :=
  ofAlgebraic (AlgebraicRoughPath.comapMapLetters f X.toAlgebraic)
    (X.isWeaklyGeometric.comapMapLetters f)

/-- Signature increment of a weakly geometric rough path. -/
def increment (X : WeakGeometricRoughPath T α R) (s t : T) : (List α → R) :=
  X.toAlgebraic.increment s t

/-- Coordinate of a weakly geometric rough path increment on a word. -/
def coeff (X : WeakGeometricRoughPath T α R) (s t : T) (word : List α) : R :=
  AlgebraicRoughPath.coeff X.toAlgebraic s t word

/-- Truncated signature increment of a weakly geometric rough path. -/
def truncatedIncrement (X : WeakGeometricRoughPath T α R)
    (n : Nat) (s t : T) : Word.Truncation α R n :=
  AlgebraicRoughPath.truncatedIncrement X.toAlgebraic n s t

@[simp]
theorem toAlgebraic_unit :
    (unit T α R).toAlgebraic = AlgebraicRoughPath.unit T α R :=
  rfl

@[simp]
theorem toAlgebraic_comapTime {S : Type z} (f : S → T)
    (X : WeakGeometricRoughPath T α R) :
    (comapTime f X).toAlgebraic = AlgebraicRoughPath.comapTime f X.toAlgebraic :=
  rfl

@[simp]
theorem toAlgebraic_comapMapLetters {β : Type z} (f : α → β)
    (X : WeakGeometricRoughPath T β R) :
    (comapMapLetters f X).toAlgebraic =
      AlgebraicRoughPath.comapMapLetters f X.toAlgebraic :=
  rfl

@[simp]
theorem increment_apply (X : WeakGeometricRoughPath T α R) (s t : T) :
    X.increment s t = X.toAlgebraic.increment s t :=
  rfl

@[simp]
theorem coeff_apply (X : WeakGeometricRoughPath T α R) (s t : T) (word : List α) :
    X.coeff s t word = AlgebraicRoughPath.coeff X.toAlgebraic s t word :=
  rfl

@[simp]
theorem truncatedIncrement_apply
    (X : WeakGeometricRoughPath T α R) (n : Nat) (s t : T)
    (word : {word : List α // word.length ≤ n}) :
    X.truncatedIncrement n s t word = X.coeff s t word.1 :=
  rfl

@[simp]
theorem unit_increment (s t : T) :
    (unit T α R).increment s t = Word.unit α R :=
  rfl

@[simp]
theorem unit_coeff_nil (s t : T) :
    (unit T α R).coeff s t [] = 1 :=
  rfl

@[simp]
theorem unit_coeff_cons (s t : T) (a : α) (word : List α) :
    (unit T α R).coeff s t (a :: word) = 0 :=
  rfl

@[simp]
theorem coeff_comapTime {S : Type z} (f : S → T)
    (X : WeakGeometricRoughPath T α R) (s t : S) (word : List α) :
    (comapTime f X).coeff s t word = X.coeff (f s) (f t) word :=
  rfl

@[simp]
theorem coeff_comapMapLetters {β : Type z} (f : α → β)
    (X : WeakGeometricRoughPath T β R) (s t : T) (word : List α) :
    (comapMapLetters f X).coeff s t word = X.coeff s t (word.map f) :=
  rfl

@[simp]
theorem truncatedIncrement_comapTime {S : Type z} (f : S → T)
    (X : WeakGeometricRoughPath T α R) (n : Nat) (s t : S) :
    truncatedIncrement (comapTime f X) n s t =
      truncatedIncrement X n (f s) (f t) :=
  rfl

@[simp]
theorem truncatedIncrement_comapMapLetters {β : Type z} (f : α → β)
    (X : WeakGeometricRoughPath T β R) (n : Nat) (s t : T) :
    truncatedIncrement (comapMapLetters f X) n s t =
      fun word : {word : List α // word.length ≤ n} =>
        X.coeff s t (word.1.map f) :=
  rfl

@[simp]
theorem increment_self (X : WeakGeometricRoughPath T α R) (t : T) :
    X.increment t t = Word.unit α R :=
  X.toAlgebraic.identity t

@[simp]
theorem coeff_self_nil (X : WeakGeometricRoughPath T α R) (t : T) :
    X.coeff t t [] = 1 :=
  AlgebraicRoughPath.coeff_self_nil X.toAlgebraic t

@[simp]
theorem coeff_self_cons
    (X : WeakGeometricRoughPath T α R) (t : T) (a : α) (word : List α) :
    X.coeff t t (a :: word) = 0 :=
  AlgebraicRoughPath.coeff_self_cons X.toAlgebraic t a word

@[simp]
theorem coeff_nil (X : WeakGeometricRoughPath T α R) (s t : T) :
    X.coeff s t [] = 1 :=
  AlgebraicRoughPath.coeff_nil X.toAlgebraic s t

theorem groupLike (X : WeakGeometricRoughPath T α R) (s t : T) :
    Word.IsGroupLike (X.increment s t) :=
  X.isWeaklyGeometric s t

theorem shuffle (X : WeakGeometricRoughPath T α R) (s t : T)
    (u v : List α) :
    X.coeff s t u * X.coeff s t v =
      Word.shuffleCoeff (X.increment s t) u v :=
  X.isWeaklyGeometric.shuffle s t u v

theorem chen_eq (X : WeakGeometricRoughPath T α R) (s t u : T) :
    X.increment s u =
      Word.tensorProduct (X.increment s t) (X.increment t u) :=
  X.toAlgebraic.chen s t u

/-- Agreement of weakly geometric rough paths through word degree `n` —
the generic graded agreement of Hopf rough paths for the word-length
grading. -/
abbrev AgreeUpToDegree (X Y : WeakGeometricRoughPath T α R) (n : Nat) :
    Prop :=
  HopfRoughPath.AgreeUpTo List.length X Y n

theorem agreeUpToDegree_iff_toAlgebraic
    (X Y : WeakGeometricRoughPath T α R) (n : Nat) :
    AgreeUpToDegree X Y n ↔
      AlgebraicRoughPath.AgreeUpToDegree X.toAlgebraic Y.toAlgebraic n :=
  Iff.rfl

theorem agreeUpToDegree_refl (X : WeakGeometricRoughPath T α R) (n : Nat) :
    AgreeUpToDegree X X n :=
  HopfRoughPath.agreeUpTo_refl _ X n

theorem agreeUpToDegree_iff_coeff
    (X Y : WeakGeometricRoughPath T α R) (n : Nat) :
    AgreeUpToDegree X Y n ↔
      ∀ s t word, word.length ≤ n → X.coeff s t word = Y.coeff s t word :=
  Iff.rfl

theorem eq_of_agreeUpToDegree_all {X Y : WeakGeometricRoughPath T α R}
    (h : ∀ n, AgreeUpToDegree X Y n) : X = Y :=
  HopfRoughPath.eq_of_agreeUpTo_all h

@[simp]
theorem comapTime_id (X : WeakGeometricRoughPath T α R) :
    comapTime id X = X := by
  apply WeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.comapTime_id X.toAlgebraic

theorem comapTime_comp {S : Type z} {U : Type y} (f : S → T) (g : U → S)
    (X : WeakGeometricRoughPath T α R) :
    comapTime g (comapTime f X) = comapTime (f ∘ g) X := by
  apply WeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.comapTime_comp f g X.toAlgebraic

@[simp]
theorem comapTime_unit {S : Type z} (f : S → T) :
    comapTime f (unit T α R) = unit S α R := by
  apply WeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.comapTime_unit (α := α) (R := R) f

@[simp]
theorem comapMapLetters_id (X : WeakGeometricRoughPath T α R) :
    comapMapLetters id X = X := by
  apply WeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.comapMapLetters_id X.toAlgebraic

theorem comapMapLetters_comp {β : Type z} {γ : Type y}
    (f : α → β) (g : β → γ) (X : WeakGeometricRoughPath T γ R) :
    comapMapLetters f (comapMapLetters g X) = comapMapLetters (g ∘ f) X := by
  apply WeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.comapMapLetters_comp f g X.toAlgebraic

@[simp]
theorem comapMapLetters_unit {β : Type z} (f : α → β) :
    comapMapLetters f (unit T β R) = unit T α R := by
  apply WeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.comapMapLetters_unit (T := T) (R := R) f

end Semiring

section Log

variable {T : Type u} {α : Type v} {R : Type w} [Field R]

/-- Truncated log-signature increment of a weakly geometric rough path. -/
def logIncrementTruncated (X : WeakGeometricRoughPath T α R)
    (s t : T) (n : Nat) : (List α → R) :=
  AlgebraicRoughPath.logIncrementTruncated X.toAlgebraic s t n

@[simp]
theorem logIncrementTruncated_zero
    (X : WeakGeometricRoughPath T α R) (s t : T) :
    X.logIncrementTruncated s t 0 = Word.zero α R :=
  AlgebraicRoughPath.logIncrementTruncated_zero X.toAlgebraic s t

@[simp]
theorem logIncrementTruncated_self
    (X : WeakGeometricRoughPath T α R) (t : T) (n : Nat) :
    X.logIncrementTruncated t t n = Word.zero α R :=
  AlgebraicRoughPath.logIncrementTruncated_self X.toAlgebraic t n

theorem AgreeUpToDegree.logIncrementTruncated
    {X Y : WeakGeometricRoughPath T α R} {m n : Nat}
    (h : AgreeUpToDegree X Y n) (s t : T) :
    Word.AgreeUpToDegree
      (X.logIncrementTruncated s t m) (Y.logIncrementTruncated s t m) n :=
  AlgebraicRoughPath.AgreeUpToDegree.logIncrementTruncated
    ((agreeUpToDegree_iff_toAlgebraic X Y n).mp h) s t

theorem logIncrementTruncated_comapMapLetters {β : Type z} (f : α → β)
    (X : WeakGeometricRoughPath T β R) (s t : T) (n : Nat) :
    logIncrementTruncated (comapMapLetters f X) s t n =
      Word.comapMapLetters f (logIncrementTruncated X s t n) :=
  AlgebraicRoughPath.logIncrementTruncated_comapMapLetters f X.toAlgebraic s t n

theorem logIncrementTruncated_comapMapLetters_coeff {β : Type z} (f : α → β)
    (X : WeakGeometricRoughPath T β R) (s t : T) (n : Nat) (word : List α) :
    Word.coeff
        (logIncrementTruncated (comapMapLetters f X) s t n) word =
      Word.coeff (logIncrementTruncated X s t n) (word.map f) :=
  AlgebraicRoughPath.logIncrementTruncated_comapMapLetters_coeff
    f X.toAlgebraic s t n word

end Log

end WeakGeometricRoughPath

/-- A controlled weakly geometric rough path with a word-coordinate bound. -/
structure ControlledWeakGeometricRoughPath (T : Type u) (α : Type v) (R : Type w)
    [Preorder T] [CommSemiring R]
    (size : R → ENNReal) (gauge : Nat → ENNReal → ENNReal) where
  toControlled : AlgebraicRoughPath.Controlled T α R size gauge
  isWeaklyGeometric : toControlled.toAlgebraic.IsWeaklyGeometric

namespace ControlledWeakGeometricRoughPath

variable {T : Type u} {α : Type v} {R : Type w} [Preorder T] [CommSemiring R]
variable {size : R → ENNReal} {gauge : Nat → ENNReal → ENNReal}

instance :
    Coe (ControlledWeakGeometricRoughPath T α R size gauge)
      (AlgebraicRoughPath.Controlled T α R size gauge) where
  coe X := X.toControlled

/-- Regard an algebraically controlled rough path as controlled weakly geometric. -/
def ofControlled (X : AlgebraicRoughPath.Controlled T α R size gauge)
    (hX : X.toAlgebraic.IsWeaklyGeometric) :
    ControlledWeakGeometricRoughPath T α R size gauge where
  toControlled := X
  isWeaklyGeometric := hX

@[simp]
theorem toControlled_ofControlled
    (X : AlgebraicRoughPath.Controlled T α R size gauge)
    (hX : X.toAlgebraic.IsWeaklyGeometric) :
    (ofControlled X hX).toControlled = X :=
  rfl

@[ext]
theorem ext {X Y : ControlledWeakGeometricRoughPath T α R size gauge}
    (h : X.toControlled = Y.toControlled) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

/-- Controlled weakly geometric rough paths are equivalent to controlled
group-like algebraic ones. -/
def equivControlled :
    ControlledWeakGeometricRoughPath T α R size gauge ≃
      {X : AlgebraicRoughPath.Controlled T α R size gauge //
        X.toAlgebraic.IsWeaklyGeometric} where
  toFun X := ⟨X.toControlled, X.isWeaklyGeometric⟩
  invFun X := ofControlled X.1 X.2
  left_inv X := by
    cases X
    rfl
  right_inv _ := rfl

/-- Forget the analytic control and keep the weakly geometric rough path. -/
def toWeakGeometric (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    WeakGeometricRoughPath T α R :=
  WeakGeometricRoughPath.ofAlgebraic X.toControlled.toAlgebraic
    X.isWeaklyGeometric

/-- Underlying algebraic rough path. -/
def toAlgebraic (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    AlgebraicRoughPath T α R :=
  X.toControlled.toAlgebraic

/-- The control attached to a controlled weakly geometric rough path. -/
def control (X : ControlledWeakGeometricRoughPath T α R size gauge) : Control T :=
  X.toControlled.control

theorem controlled (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    X.toAlgebraic.HasCoordinateControl X.control size gauge :=
  X.toControlled.controlled

/-- Signature coordinate of a controlled weakly geometric rough path. -/
def coeff (X : ControlledWeakGeometricRoughPath T α R size gauge)
    (s t : T) (word : List α) : R :=
  X.toControlled.coeff s t word

/-- Truncated increment of a controlled weakly geometric rough path. -/
def truncatedIncrement (X : ControlledWeakGeometricRoughPath T α R size gauge)
    (n : Nat) (s t : T) : Word.Truncation α R n :=
  X.toWeakGeometric.truncatedIncrement n s t

/-- Pull a controlled weakly geometric rough path back along a map of alphabets. -/
def comapMapLetters {β : Type z} (f : α → β)
    (X : ControlledWeakGeometricRoughPath T β R size gauge) :
    ControlledWeakGeometricRoughPath T α R size gauge :=
  ofControlled (AlgebraicRoughPath.Controlled.comapMapLetters f X.toControlled)
    (X.isWeaklyGeometric.comapMapLetters f)

/-- Pull a controlled weakly geometric rough path back along a monotone time map. -/
def comapTime {S : Type z} [Preorder S] (f : S → T) (hf : Monotone f)
    (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    ControlledWeakGeometricRoughPath S α R size gauge :=
  ofControlled (AlgebraicRoughPath.Controlled.comapTime f hf X.toControlled)
    (X.isWeaklyGeometric.comapTime f)

@[simp]
theorem toWeakGeometric_toAlgebraic
    (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    X.toWeakGeometric.toAlgebraic = X.toAlgebraic :=
  rfl

@[simp]
theorem coeff_apply
    (X : ControlledWeakGeometricRoughPath T α R size gauge)
    (s t : T) (word : List α) :
    X.coeff s t word = AlgebraicRoughPath.coeff X.toAlgebraic s t word :=
  rfl

@[simp]
theorem truncatedIncrement_apply
    (X : ControlledWeakGeometricRoughPath T α R size gauge)
    (n : Nat) (s t : T) (word : {word : List α // word.length ≤ n}) :
    X.truncatedIncrement n s t word = X.coeff s t word.1 :=
  rfl

theorem coordinate_bound (X : ControlledWeakGeometricRoughPath T α R size gauge)
    {s t : T} (hst : s ≤ t) (word : List α) :
    size (X.coeff s t word) ≤ gauge word.length (X.control s t) :=
  X.toControlled.coordinate_bound hst word

@[simp]
theorem toControlled_comapMapLetters {β : Type z} (f : α → β)
    (X : ControlledWeakGeometricRoughPath T β R size gauge) :
    (comapMapLetters f X).toControlled =
      AlgebraicRoughPath.Controlled.comapMapLetters f X.toControlled :=
  rfl

@[simp]
theorem coeff_comapMapLetters {β : Type z} (f : α → β)
    (X : ControlledWeakGeometricRoughPath T β R size gauge)
    (s t : T) (word : List α) :
    (comapMapLetters f X).coeff s t word = X.coeff s t (word.map f) :=
  rfl

@[simp]
theorem toControlled_comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f)
    (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    (comapTime f hf X).toControlled =
      AlgebraicRoughPath.Controlled.comapTime f hf X.toControlled :=
  rfl

@[simp]
theorem coeff_comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f)
    (X : ControlledWeakGeometricRoughPath T α R size gauge)
    (s t : S) (word : List α) :
    (comapTime f hf X).coeff s t word = X.coeff (f s) (f t) word :=
  rfl

@[simp]
theorem control_comapMapLetters {β : Type z} (f : α → β)
    (X : ControlledWeakGeometricRoughPath T β R size gauge) :
    (comapMapLetters f X).control = X.control :=
  rfl

@[simp]
theorem control_comapTime {S : Type z} [Preorder S]
    (f : S → T) (hf : Monotone f)
    (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    (comapTime f hf X).control = X.control.comap f hf :=
  rfl

@[simp]
theorem comapMapLetters_id
    (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    comapMapLetters id X = X := by
  apply ControlledWeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.Controlled.comapMapLetters_id X.toControlled

theorem comapMapLetters_comp {β : Type z} {γ : Type y}
    (f : α → β) (g : β → γ)
    (X : ControlledWeakGeometricRoughPath T γ R size gauge) :
    comapMapLetters f (comapMapLetters g X) = comapMapLetters (g ∘ f) X := by
  apply ControlledWeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.Controlled.comapMapLetters_comp f g X.toControlled

@[simp]
theorem comapTime_id (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    comapTime id (fun _ _ h => h) X = X := by
  apply ControlledWeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.Controlled.comapTime_id X.toControlled

theorem comapTime_comp {S : Type z} {U : Type y} [Preorder S] [Preorder U]
    (f : S → T) (hf : Monotone f) (g : U → S) (hg : Monotone g)
    (X : ControlledWeakGeometricRoughPath T α R size gauge) :
    comapTime g hg (comapTime f hf X) =
      comapTime (f ∘ g) (fun _ _ h => hf (hg h)) X := by
  apply ControlledWeakGeometricRoughPath.ext
  exact AlgebraicRoughPath.Controlled.comapTime_comp f hf g hg X.toControlled

/-- Agreement through degree `n` for the underlying weakly geometric rough paths. -/
def AgreeUpToDegree
    (X Y : ControlledWeakGeometricRoughPath T α R size gauge) (n : Nat) : Prop :=
  WeakGeometricRoughPath.AgreeUpToDegree X.toWeakGeometric Y.toWeakGeometric n

theorem agreeUpToDegree_refl
    (X : ControlledWeakGeometricRoughPath T α R size gauge) (n : Nat) :
    AgreeUpToDegree X X n :=
  WeakGeometricRoughPath.agreeUpToDegree_refl X.toWeakGeometric n

theorem agreeUpToDegree_iff_coeff
    (X Y : ControlledWeakGeometricRoughPath T α R size gauge) (n : Nat) :
    AgreeUpToDegree X Y n ↔
      ∀ s t word, word.length ≤ n → X.coeff s t word = Y.coeff s t word := by
  simpa [AgreeUpToDegree, coeff, toWeakGeometric, toAlgebraic] using
    WeakGeometricRoughPath.agreeUpToDegree_iff_coeff
      X.toWeakGeometric Y.toWeakGeometric n

theorem toWeakGeometric_eq_of_agreeUpToDegree_all
    {X Y : ControlledWeakGeometricRoughPath T α R size gauge}
    (h : ∀ n, AgreeUpToDegree X Y n) :
    X.toWeakGeometric = Y.toWeakGeometric :=
  WeakGeometricRoughPath.eq_of_agreeUpToDegree_all h

theorem agreeUpToDegree_all_iff_toWeakGeometric_eq
    {X Y : ControlledWeakGeometricRoughPath T α R size gauge} :
    (∀ n, AgreeUpToDegree X Y n) ↔ X.toWeakGeometric = Y.toWeakGeometric := by
  constructor
  · exact toWeakGeometric_eq_of_agreeUpToDegree_all
  · intro h n
    change WeakGeometricRoughPath.AgreeUpToDegree
      X.toWeakGeometric Y.toWeakGeometric n
    rw [h]
    exact WeakGeometricRoughPath.agreeUpToDegree_refl Y.toWeakGeometric n

end ControlledWeakGeometricRoughPath

end RoughPaths
