/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Word.Algebraic

/-!
# Truncated Log-Signatures

This file adds tensor powers and finite tensor exponential/logarithm series for
word-indexed signatures. The logarithm is defined by applying the usual
finite `log (1 + x)` polynomial to the augmentation part of a signature.
The finite tensor exponential and logarithm are natural under relabelling of
the alphabet.
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z

namespace Word

variable {α : Type u} {R : Type v}

/-- The zero word-indexed series. -/
def zero (α : Type u) (R : Type v) [Zero R] : (List α → R) :=
  fun _ => 0

@[simp]
theorem coeff_zero [Zero R] (w : List α) :
    coeff (zero α R) w = 0 :=
  rfl

@[simp]
theorem tensorProduct_zero_left [Semiring R] (a : (List α → R)) :
    tensorProduct (zero α R) a = zero α R := by
  ext w
  simp [tensorProduct, zero]

@[simp]
theorem tensorProduct_zero_right [Semiring R] (a : (List α → R)) :
    tensorProduct a (zero α R) = zero α R := by
  ext w
  simp [tensorProduct, zero]

/-- Tensor powers for the concatenation product. -/
def tensorPower [Semiring R] (a : (List α → R)) : Nat → (List α → R)
  | 0 => unit α R
  | n + 1 => tensorProduct a (tensorPower a n)

@[simp]
theorem tensorPower_zero [Semiring R] (a : (List α → R)) :
    tensorPower a 0 = unit α R :=
  rfl

@[simp]
theorem tensorPower_succ [Semiring R] (a : (List α → R)) (n : Nat) :
    tensorPower a (n + 1) = tensorProduct a (tensorPower a n) :=
  rfl

@[simp]
theorem tensorPower_one [Semiring R] (a : (List α → R)) :
    tensorPower a 1 = a := by
  simp [tensorPower]

theorem tensorPower_add [Semiring R] (a : (List α → R)) (m n : Nat) :
    tensorPower a (m + n) = tensorProduct (tensorPower a m) (tensorPower a n) := by
  induction m with
  | zero =>
      simp [tensorPower]
  | succ m ih =>
      simp only [Nat.succ_add, tensorPower_succ]
      rw [ih, ← tensorProduct_assoc]

theorem tensorPower_succ_right [Semiring R] (a : (List α → R)) (n : Nat) :
    tensorPower a (n + 1) = tensorProduct (tensorPower a n) a := by
  rw [show n + 1 = n + 1 by rfl, tensorPower_add]
  simp

@[simp]
theorem tensorPower_unit [Semiring R] (n : Nat) :
    tensorPower (unit α R) n = unit α R := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [ih]

@[simp]
theorem tensorPower_zero_succ [Semiring R] (n : Nat) :
    tensorPower (zero α R) (n + 1) = zero α R := by
  simp [tensorPower]

theorem tensorPower_coeff_nil [Semiring R] (a : (List α → R)) (n : Nat) :
    coeff (tensorPower a n) [] = coeff a [] ^ n := by
  induction n with
  | zero =>
      simp [tensorPower, coeff, unit]
  | succ n ih =>
      rw [tensorPower_succ, tensorProduct_nil, ih, pow_succ']

theorem tensorPower_hasUnitEmpty [Semiring R] {a : (List α → R)}
    (ha : HasUnitEmpty a) (n : Nat) :
    HasUnitEmpty (tensorPower a n) := by
  induction n with
  | zero =>
      exact unit_hasUnitEmpty
  | succ n ih =>
      exact tensorProduct_hasUnitEmpty ha ih

theorem agreeUpToDegree_tensorPower [Semiring R]
    {a b : (List α → R)} {n : Nat}
    (h : AgreeUpToDegree a b n) (k : Nat) :
    AgreeUpToDegree (tensorPower a k) (tensorPower b k) n := by
  induction k with
  | zero =>
      exact agreeUpToDegree_refl (unit α R) n
  | succ k ih =>
      exact agreeUpToDegree_tensorProduct h ih

theorem tensorPower_comapMapLetters {γ : Type u} {δ : Type w} [Semiring R]
    (f : γ → δ) (a : (List δ → R)) (n : Nat) :
    tensorPower (comapMapLetters f a) n = comapMapLetters f (tensorPower a n) := by
  induction n with
  | zero =>
      exact (comapMapLetters_unit f).symm
  | succ n ih =>
      rw [tensorPower_succ, ih, Word.tensorProduct_comapMapLetters]
      rfl

/-- The augmentation part `a - 1` of a series. -/
def augmentationPart [Sub R] [Zero R] [One R]
    (a : (List α → R)) : (List α → R) :=
  fun w => coeff a w - coeff (unit α R) w

@[simp]
theorem coeff_augmentationPart [Sub R] [Zero R] [One R]
    (a : (List α → R)) (w : List α) :
    coeff (augmentationPart a) w = coeff a w - coeff (unit α R) w :=
  rfl

theorem coeff_augmentationPart_nil [Ring R] {a : (List α → R)}
    (ha : HasUnitEmpty a) :
    coeff (augmentationPart a) [] = 0 := by
  change coeff a [] - (1 : R) = 0
  rw [ha.coeff_nil]
  simp

@[simp]
theorem augmentationPart_unit [Ring R] :
    augmentationPart (unit α R) = zero α R := by
  ext word
  cases word <;> simp [augmentationPart, zero, unit]

theorem agreeUpToDegree_augmentationPart [Ring R]
    {a b : (List α → R)} {n : Nat}
    (h : AgreeUpToDegree a b n) :
    AgreeUpToDegree (augmentationPart a) (augmentationPart b) n := by
  intro w hw
  change coeff a w - coeff (unit α R) w = coeff b w - coeff (unit α R) w
  rw [h w hw]

theorem augmentationPart_comapMapLetters {γ : Type u} {δ : Type w} [Ring R]
    (f : γ → δ) (a : (List δ → R)) :
    augmentationPart (comapMapLetters f a) = comapMapLetters f (augmentationPart a) := by
  ext word
  cases word <;> simp [augmentationPart, comapMapLetters, unit]

/-- Finite tensor exponential `∑_{k=0}^n a^{⊗k}/k!`. -/
def tensorExpTruncated [Field R] (a : (List α → R)) (n : Nat) :
    (List α → R) :=
  fun w =>
    ((List.range (n + 1)).map fun k =>
      (Nat.factorial k : R)⁻¹ * coeff (tensorPower a k) w).sum

@[simp]
theorem coeff_tensorExpTruncated [Field R]
    (a : (List α → R)) (n : Nat) (w : List α) :
    coeff (tensorExpTruncated a n) w =
      ((List.range (n + 1)).map fun k =>
        (Nat.factorial k : R)⁻¹ * coeff (tensorPower a k) w).sum :=
  rfl

@[simp]
theorem tensorExpTruncated_zero [Field R] (a : (List α → R)) :
    tensorExpTruncated a 0 = unit α R := by
  ext w
  simp [tensorExpTruncated]

theorem agreeUpToDegree_tensorExpTruncated [Field R]
    {a b : (List α → R)} {m n : Nat}
    (h : AgreeUpToDegree a b n) :
    AgreeUpToDegree (tensorExpTruncated a m) (tensorExpTruncated b m) n := by
  intro w hw
  change
    ((List.range (m + 1)).map fun k =>
      (Nat.factorial k : R)⁻¹ * coeff (tensorPower a k) w).sum =
        ((List.range (m + 1)).map fun k =>
          (Nat.factorial k : R)⁻¹ * coeff (tensorPower b k) w).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _hk
  rw [(agreeUpToDegree_tensorPower h k) w hw]

theorem tensorExpTruncated_comapMapLetters {γ : Type u} {δ : Type w} [Field R]
    (f : γ → δ) (a : (List δ → R)) (n : Nat) :
    tensorExpTruncated (comapMapLetters f a) n =
      comapMapLetters f (tensorExpTruncated a n) := by
  ext word
  change
    ((List.range (n + 1)).map fun k =>
      (Nat.factorial k : R)⁻¹ * coeff (tensorPower (comapMapLetters f a) k) word).sum =
        ((List.range (n + 1)).map fun k =>
          (Nat.factorial k : R)⁻¹ * coeff (tensorPower a k) (word.map f)).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _hk
  rw [tensorPower_comapMapLetters f a k, coeff_comapMapLetters]

/-- Finite tensor logarithm `∑_{k=1}^n (-1)^{k+1} a^{⊗k}/k`. -/
def tensorLogOnePlusTruncated [Field R] (a : (List α → R)) (n : Nat) :
    (List α → R) :=
  fun w =>
    ((List.range n).map fun i =>
      let k : Nat := i + 1
      ((-1 : R) ^ (k + 1)) * (k : R)⁻¹ * coeff (tensorPower a k) w).sum

@[simp]
theorem coeff_tensorLogOnePlusTruncated [Field R]
    (a : (List α → R)) (n : Nat) (w : List α) :
    coeff (tensorLogOnePlusTruncated a n) w =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        ((-1 : R) ^ (k + 1)) * (k : R)⁻¹ * coeff (tensorPower a k) w).sum :=
  rfl

@[simp]
theorem tensorLogOnePlusTruncated_zero [Field R] (a : (List α → R)) :
    tensorLogOnePlusTruncated a 0 = zero α R := by
  ext w
  simp [tensorLogOnePlusTruncated, zero]

@[simp]
theorem tensorLogOnePlusTruncated_zero_series [Field R] (n : Nat) :
    tensorLogOnePlusTruncated (zero α R) n = zero α R := by
  ext w
  simp [tensorLogOnePlusTruncated, zero]

theorem agreeUpToDegree_tensorLogOnePlusTruncated [Field R]
    {a b : (List α → R)} {m n : Nat}
    (h : AgreeUpToDegree a b n) :
    AgreeUpToDegree
      (tensorLogOnePlusTruncated a m) (tensorLogOnePlusTruncated b m) n := by
  intro w hw
  change
    ((List.range m).map fun i =>
      let k : Nat := i + 1
      ((-1 : R) ^ (k + 1)) * (k : R)⁻¹ * coeff (tensorPower a k) w).sum =
        ((List.range m).map fun i =>
          let k : Nat := i + 1
          ((-1 : R) ^ (k + 1)) * (k : R)⁻¹ * coeff (tensorPower b k) w).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _hi
  dsimp
  have hp :
      tensorProduct a (tensorPower a i) w =
        tensorProduct b (tensorPower b i) w := by
    simpa [coeff] using
      (agreeUpToDegree_tensorProduct h (agreeUpToDegree_tensorPower h i)) w hw
  rw [hp]

theorem tensorLogOnePlusTruncated_comapMapLetters {γ : Type u} {δ : Type w} [Field R]
    (f : γ → δ) (a : (List δ → R)) (n : Nat) :
    tensorLogOnePlusTruncated (comapMapLetters f a) n =
      comapMapLetters f (tensorLogOnePlusTruncated a n) := by
  ext word
  change
    ((List.range n).map fun i =>
      let k : Nat := i + 1
      ((-1 : R) ^ (k + 1)) * (k : R)⁻¹ *
        coeff (tensorPower (comapMapLetters f a) k) word).sum =
        ((List.range n).map fun i =>
          let k : Nat := i + 1
          ((-1 : R) ^ (k + 1)) * (k : R)⁻¹ *
            coeff (tensorPower a k) (word.map f)).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _hi
  dsimp
  have hp :
      tensorProduct (comapMapLetters f a) (tensorPower (comapMapLetters f a) i) word =
        tensorProduct a (tensorPower a i) (word.map f) := by
    rw [tensorPower_comapMapLetters f a i]
    rw [Word.tensorProduct_comapMapLetters f a (tensorPower a i)]
    rfl
  rw [hp]

/-- Truncated log-signature, defined as `log (1 + (a - 1))`. -/
def logSignatureTruncated [Field R] (a : (List α → R)) (n : Nat) :
    (List α → R) :=
  tensorLogOnePlusTruncated (augmentationPart a) n

@[simp]
theorem coeff_logSignatureTruncated [Field R]
    (a : (List α → R)) (n : Nat) (w : List α) :
    coeff (logSignatureTruncated a n) w =
      coeff (tensorLogOnePlusTruncated (augmentationPart a) n) w :=
  rfl

@[simp]
theorem logSignatureTruncated_zero [Field R] (a : (List α → R)) :
    logSignatureTruncated a 0 = zero α R :=
  tensorLogOnePlusTruncated_zero (augmentationPart a)

@[simp]
theorem logSignatureTruncated_unit [Field R] (n : Nat) :
    logSignatureTruncated (unit α R) n = zero α R := by
  rw [logSignatureTruncated, augmentationPart_unit, tensorLogOnePlusTruncated_zero_series]

theorem agreeUpToDegree_logSignatureTruncated [Field R]
    {a b : (List α → R)} {m n : Nat}
    (h : AgreeUpToDegree a b n) :
    AgreeUpToDegree (logSignatureTruncated a m) (logSignatureTruncated b m) n :=
  agreeUpToDegree_tensorLogOnePlusTruncated
    (agreeUpToDegree_augmentationPart h)

theorem logSignatureTruncated_comapMapLetters {γ : Type u} {δ : Type w} [Field R]
    (f : γ → δ) (a : (List δ → R)) (n : Nat) :
    logSignatureTruncated (comapMapLetters f a) n =
      comapMapLetters f (logSignatureTruncated a n) := by
  rw [logSignatureTruncated, augmentationPart_comapMapLetters,
    tensorLogOnePlusTruncated_comapMapLetters]
  rfl

end Word

namespace Signature

variable {α : Type u} {R : Type v} [Field R]

/-- The truncated log-signature of a bundled signature. -/
def logTruncated (σ : Signature α R) (n : Nat) : (List α → R) :=
  Word.logSignatureTruncated σ.1 n

@[simp]
theorem coeff_logTruncated (σ : Signature α R) (n : Nat) (w : List α) :
    Word.coeff (logTruncated σ n) w =
      Word.coeff (Word.logSignatureTruncated σ.1 n) w :=
  rfl

@[simp]
theorem logTruncated_zero (σ : Signature α R) :
    logTruncated σ 0 = Word.zero α R :=
  Word.logSignatureTruncated_zero σ.1

theorem logTruncated_comapMapLetters {γ : Type u} {δ : Type w}
    (f : γ → δ) (σ : Signature δ R) (n : Nat) :
    logTruncated (Signature.comapMapLetters f σ) n =
      Word.comapMapLetters f (logTruncated σ n) :=
  Word.logSignatureTruncated_comapMapLetters f σ.1 n

end Signature

namespace AlgebraicRoughPath

variable {T : Type u} {α : Type v} {R : Type w} [Field R]

/-- The truncated log-signature of an algebraic rough path increment. -/
def logIncrementTruncated (X : AlgebraicRoughPath T α R) (s t : T) (n : Nat) :
    (List α → R) :=
  Word.logSignatureTruncated (X.increment s t) n

@[simp]
theorem coeff_logIncrementTruncated
    (X : AlgebraicRoughPath T α R) (s t : T) (n : Nat) (word : List α) :
    Word.coeff (logIncrementTruncated X s t n) word =
      Word.coeff
        (Word.logSignatureTruncated (X.increment s t) n) word :=
  rfl

@[simp]
theorem logIncrementTruncated_zero (X : AlgebraicRoughPath T α R) (s t : T) :
    logIncrementTruncated X s t 0 = Word.zero α R :=
  Word.logSignatureTruncated_zero (X.increment s t)

@[simp]
theorem logIncrementTruncated_self
    (X : AlgebraicRoughPath T α R) (t : T) (n : Nat) :
    logIncrementTruncated X t t n = Word.zero α R := by
  rw [logIncrementTruncated, X.identity]
  exact Word.logSignatureTruncated_unit n

@[simp]
theorem coeff_logIncrementTruncated_self
    (X : AlgebraicRoughPath T α R) (t : T) (n : Nat) (word : List α) :
    Word.coeff (logIncrementTruncated X t t n) word = 0 := by
  rw [logIncrementTruncated_self]
  rfl

theorem AgreeUpToDegree.logIncrementTruncated
    {X Y : AlgebraicRoughPath T α R} {m n : Nat}
    (h : AgreeUpToDegree X Y n) (s t : T) :
    Word.AgreeUpToDegree
      (AlgebraicRoughPath.logIncrementTruncated X s t m)
      (AlgebraicRoughPath.logIncrementTruncated Y s t m) n :=
  Word.agreeUpToDegree_logSignatureTruncated (h s t)

theorem AgreeUpToDegree.logIncrementTruncated_coeff
    {X Y : AlgebraicRoughPath T α R} {m n : Nat}
    (h : AgreeUpToDegree X Y n) (s t : T) (word : List α)
    (hword : word.length ≤ n) :
    Word.coeff (AlgebraicRoughPath.logIncrementTruncated X s t m) word =
      Word.coeff (AlgebraicRoughPath.logIncrementTruncated Y s t m) word :=
  (h.logIncrementTruncated (m := m) s t) word hword

theorem logIncrementTruncated_comapMapLetters {β : Type z} (f : α → β)
    (X : AlgebraicRoughPath T β R) (s t : T) (n : Nat) :
    logIncrementTruncated (AlgebraicRoughPath.comapMapLetters f X) s t n =
      Word.comapMapLetters f (logIncrementTruncated X s t n) :=
  Word.logSignatureTruncated_comapMapLetters f (X.increment s t) n

theorem logIncrementTruncated_comapMapLetters_coeff {β : Type z} (f : α → β)
    (X : AlgebraicRoughPath T β R) (s t : T) (n : Nat) (word : List α) :
    Word.coeff
        (logIncrementTruncated (AlgebraicRoughPath.comapMapLetters f X) s t n) word =
      Word.coeff (logIncrementTruncated X s t n) (word.map f) := by
  rw [logIncrementTruncated_comapMapLetters]
  rfl

end AlgebraicRoughPath

end RoughPaths
