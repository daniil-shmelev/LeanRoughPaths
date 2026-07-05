/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Signature.Basic

/-!
# Algebraic Rough Paths

This file defines the algebraic part of a rough path: a two-parameter family of
word signatures satisfying Chen's identity. Analytic regularity, such as
finite `p`-variation or Holder bounds, is deliberately left for later files.

## Main definitions

* `AlgebraicRoughPath` - group-like signature increments satisfying Chen's identity
* `AlgebraicRoughPath.unit` - the constant identity rough path
* `AlgebraicRoughPath.coeff` - coordinate of an increment on a word
* `AlgebraicRoughPath.chen_coeff` - coefficient form of Chen's identity
* `AlgebraicRoughPath.increment_tensorProduct_reverse` - reverse increments multiply to the unit

## References

* Terry Lyons, Michael Caruana, Thierry Levy,
  *Differential Equations Driven by Rough Paths*
* Peter Friz, Nicolas Victoir, *Multidimensional Stochastic Processes as Rough Paths*
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z y

/-- Algebraic rough path increments: a multiplicative functional on words.
`identity` and `chen` are Chen's relations and `unitEmpty` normalises the
degree-zero coefficient. Geometricity (the shuffle identity) is the separate
mixin `IsWeaklyGeometric`, so general non-geometric (e.g. Itô-type) rough
paths are included. -/
structure AlgebraicRoughPath (T : Type u) (α : Type v) (R : Type w) [Semiring R] where
  increment : T → T → (List α → R)
  identity : ∀ t : T, increment t t = Word.unit α R
  chen :
    ∀ s t u : T,
      increment s u =
        Word.tensorProduct (increment s t) (increment t u)
  unitEmpty : ∀ s t : T, Word.coeff (increment s t) [] = 1

namespace AlgebraicRoughPath

variable {T : Type u} {α : Type v} {R : Type w} [Semiring R]

/-- A rough path is weakly geometric when every increment is group-like,
i.e. satisfies the shuffle identity. -/
def IsWeaklyGeometric (X : AlgebraicRoughPath T α R) : Prop :=
  ∀ s t : T, Word.IsGroupLike (X.increment s t)

/-- The constant identity word-signature rough path. -/
def unit (T : Type u) (α : Type v) (R : Type w) [Semiring R] :
    AlgebraicRoughPath T α R where
  increment _ _ := Word.unit α R
  identity _ := rfl
  chen _ _ _ := by
    exact (Word.tensorProduct_unit_left (Word.unit α R)).symm
  unitEmpty _ _ := rfl

theorem unit_isWeaklyGeometric : (unit T α R).IsWeaklyGeometric :=
  fun _ _ => Word.unit_isGroupLike

/-- Pull an algebraic rough path back along a map of time domains. -/
def comapTime {S : Type z} (f : S → T)
    (X : AlgebraicRoughPath T α R) : AlgebraicRoughPath S α R where
  increment s t := X.increment (f s) (f t)
  identity s := X.identity (f s)
  chen s t u := X.chen (f s) (f t) (f u)
  unitEmpty s t := X.unitEmpty (f s) (f t)

/-- Pull an algebraic rough path back along a map of alphabets. -/
def comapMapLetters {β : Type z} (f : α → β)
    (X : AlgebraicRoughPath T β R) : AlgebraicRoughPath T α R where
  increment s t := Word.comapMapLetters f (X.increment s t)
  identity t := by
    rw [X.identity t]
    exact Word.comapMapLetters_unit f
  chen s t u := by
    rw [X.chen s t u]
    exact (Word.tensorProduct_comapMapLetters f
      (X.increment s t) (X.increment t u)).symm
  unitEmpty s t := X.unitEmpty s t

theorem IsWeaklyGeometric.comapTime {S : Type z} (f : S → T)
    {X : AlgebraicRoughPath T α R} (hX : X.IsWeaklyGeometric) :
    (comapTime f X).IsWeaklyGeometric :=
  fun s t => hX (f s) (f t)

theorem IsWeaklyGeometric.comapMapLetters {β : Type z} (f : α → β)
    {X : AlgebraicRoughPath T β R} (hX : X.IsWeaklyGeometric) :
    (comapMapLetters f X).IsWeaklyGeometric :=
  fun s t => (hX s t).comapMapLetters f

@[simp]
theorem comapMapLetters_increment {β : Type z} (f : α → β)
    (X : AlgebraicRoughPath T β R) (s t : T) :
    (comapMapLetters f X).increment s t =
      Word.comapMapLetters f (X.increment s t) :=
  rfl

@[simp]
theorem comapTime_increment {S : Type z} (f : S → T)
    (X : AlgebraicRoughPath T α R) (s t : S) :
    (comapTime f X).increment s t = X.increment (f s) (f t) :=
  rfl

/-- Coordinate of an algebraic rough path increment on a word. -/
def coeff (X : AlgebraicRoughPath T α R) (s t : T) (word : List α) : R :=
  Word.coeff (X.increment s t) word

def truncatedIncrement (X : AlgebraicRoughPath T α R)
    (n : Nat) (s t : T) : Word.Truncation α R n :=
  Word.truncate (X.increment s t) n

@[ext]
theorem ext {X Y : AlgebraicRoughPath T α R}
    (h : ∀ s t word, coeff X s t word = coeff Y s t word) : X = Y := by
  cases X with
  | mk incX idX chenX ueX =>
    cases Y with
    | mk incY idY chenY ueY =>
      have hinc : incX = incY := by
        funext s t word
        simpa [coeff] using h s t word
      subst incY
      congr

@[simp]
theorem unit_increment (s t : T) :
    (unit T α R).increment s t = Word.unit α R :=
  rfl

theorem unit_coeff (s t : T) (word : List α) :
    coeff (unit T α R) s t word = Word.coeff (Word.unit α R) word :=
  rfl

@[simp]
theorem unit_coeff_nil (s t : T) :
    coeff (unit T α R) s t [] = 1 :=
  rfl

@[simp]
theorem unit_coeff_cons (s t : T) (x : α) (word : List α) :
    coeff (unit T α R) s t (x :: word) = 0 :=
  rfl

@[simp]
theorem coeff_comapMapLetters {β : Type z} (f : α → β)
    (X : AlgebraicRoughPath T β R) (s t : T) (word : List α) :
    coeff (comapMapLetters f X) s t word = coeff X s t (word.map f) :=
  rfl

@[simp]
theorem coeff_comapTime {S : Type z} (f : S → T)
    (X : AlgebraicRoughPath T α R) (s t : S) (word : List α) :
    coeff (comapTime f X) s t word = coeff X (f s) (f t) word :=
  rfl

@[simp]
theorem truncatedIncrement_apply
    (X : AlgebraicRoughPath T α R) (n : Nat) (s t : T)
    (word : {word : List α // word.length ≤ n}) :
    truncatedIncrement X n s t word = coeff X s t word.1 :=
  rfl

@[simp]
theorem truncatedIncrement_comapMapLetters {β : Type z} (f : α → β)
    (X : AlgebraicRoughPath T β R) (n : Nat) (s t : T) :
    truncatedIncrement (comapMapLetters f X) n s t =
      fun word : {word : List α // word.length ≤ n} =>
        coeff X s t (word.1.map f) := rfl

@[simp]
theorem truncatedIncrement_comapTime {S : Type z} (f : S → T)
    (X : AlgebraicRoughPath T α R) (n : Nat) (s t : S) :
    truncatedIncrement (comapTime f X) n s t =
      truncatedIncrement X n (f s) (f t) := rfl

/-- Two algebraic rough paths agree through word degree `n` if all increments do. -/
def AgreeUpToDegree (X Y : AlgebraicRoughPath T α R) (n : Nat) : Prop :=
  ∀ s t : T, Word.AgreeUpToDegree (X.increment s t) (Y.increment s t) n

theorem agreeUpToDegree_refl (X : AlgebraicRoughPath T α R) (n : Nat) :
    AgreeUpToDegree X X n := by
  intro s t
  exact Word.agreeUpToDegree_refl (X.increment s t) n

theorem agreeUpToDegree_iff_coeff
    (X Y : AlgebraicRoughPath T α R) (n : Nat) :
    AgreeUpToDegree X Y n ↔
      ∀ s t word, word.length ≤ n → coeff X s t word = coeff Y s t word := by
  constructor
  · intro h s t word hword
    exact h s t word hword
  · intro h s t word hword
    exact h s t word hword

theorem eq_of_agreeUpToDegree_all {X Y : AlgebraicRoughPath T α R}
    (h : ∀ n, AgreeUpToDegree X Y n) : X = Y := by
  ext s t word
  exact h word.length s t word le_rfl

@[simp]
theorem comapTime_id (X : AlgebraicRoughPath T α R) :
    comapTime id X = X := by
  ext s t word
  rfl

theorem comapTime_comp {S : Type z} {U : Type y} (f : S → T) (g : U → S)
    (X : AlgebraicRoughPath T α R) :
    comapTime g (comapTime f X) = comapTime (f ∘ g) X := by
  ext s t word
  rfl

@[simp]
theorem comapTime_unit {S : Type z} (f : S → T) :
    comapTime f (unit T α R) = unit S α R := by
  ext s t word
  cases word <;> rfl

@[simp]
theorem comapMapLetters_id (X : AlgebraicRoughPath T α R) :
    comapMapLetters id X = X := by
  ext s t word
  simp [coeff_comapMapLetters]

theorem comapMapLetters_comp {β : Type z} {γ : Type y}
    (f : α → β) (g : β → γ) (X : AlgebraicRoughPath T γ R) :
    comapMapLetters f (comapMapLetters g X) = comapMapLetters (g ∘ f) X := by
  ext s t word
  simp [coeff_comapMapLetters, List.map_map, Function.comp_def]

@[simp]
theorem comapMapLetters_unit {β : Type z} (f : α → β) :
    comapMapLetters f (unit T β R) = unit T α R := by
  ext s t word
  cases word <;> rfl

@[simp]
theorem coeff_apply (X : AlgebraicRoughPath T α R) (s t : T) (word : List α) :
    coeff X s t word = X.increment s t word :=
  rfl

@[simp]
theorem increment_self (X : AlgebraicRoughPath T α R) (t : T) :
    X.increment t t = Word.unit α R :=
  X.identity t

@[simp]
theorem coeff_self_nil (X : AlgebraicRoughPath T α R) (t : T) :
    coeff X t t [] = 1 := by
  rw [coeff, X.identity]
  rfl

@[simp]
theorem coeff_self_cons
    (X : AlgebraicRoughPath T α R) (t : T) (x : α) (word : List α) :
    coeff X t t (x :: word) = 0 := by
  rw [coeff, X.identity]
  rfl

theorem increment_hasUnitEmpty (X : AlgebraicRoughPath T α R) (s t : T) :
    Word.HasUnitEmpty (X.increment s t) :=
  X.unitEmpty s t

@[simp]
theorem coeff_nil (X : AlgebraicRoughPath T α R) (s t : T) :
    coeff X s t [] = 1 :=
  X.unitEmpty s t

theorem IsWeaklyGeometric.shuffle {X : AlgebraicRoughPath T α R}
    (hX : X.IsWeaklyGeometric) (s t : T) (u v : List α) :
    coeff X s t u * coeff X s t v =
      Word.shuffleCoeff (X.increment s t) u v :=
  (hX s t).shuffle u v

theorem IsWeaklyGeometric.satisfiesShuffleUpToDegree
    {X : AlgebraicRoughPath T α R} (hX : X.IsWeaklyGeometric) (s t : T) (n : Nat) :
    Word.SatisfiesShuffleUpToDegree (X.increment s t) n :=
  (hX s t).satisfiesShuffleUpToDegree n

theorem chen_eq (X : AlgebraicRoughPath T α R) (s t u : T) :
    X.increment s u =
      Word.tensorProduct (X.increment s t) (X.increment t u) :=
  X.chen s t u

theorem increment_tensorProduct_reverse (X : AlgebraicRoughPath T α R) (s t : T) :
    Word.tensorProduct (X.increment s t) (X.increment t s) =
      Word.unit α R := by
  rw [← X.chen s t s, X.identity s]

theorem reverse_tensorProduct_increment (X : AlgebraicRoughPath T α R) (s t : T) :
    Word.tensorProduct (X.increment t s) (X.increment s t) =
      Word.unit α R := by
  rw [← X.chen t s t, X.identity t]

theorem chen_eq_left_assoc (X : AlgebraicRoughPath T α R) (s t u v : T) :
    X.increment s v =
      Word.tensorProduct
        (Word.tensorProduct (X.increment s t) (X.increment t u))
        (X.increment u v) := by
  rw [X.chen s u v, X.chen s t u]

theorem chen_eq_right_assoc (X : AlgebraicRoughPath T α R) (s t u v : T) :
    X.increment s v =
      Word.tensorProduct (X.increment s t)
        (Word.tensorProduct (X.increment t u) (X.increment u v)) := by
  rw [X.chen s t v, X.chen t u v]

theorem chen_tensorProduct_assoc_on_increments
    (X : AlgebraicRoughPath T α R) (s t u v : T) :
    Word.tensorProduct
        (Word.tensorProduct (X.increment s t) (X.increment t u))
        (X.increment u v) =
      Word.tensorProduct (X.increment s t)
        (Word.tensorProduct (X.increment t u) (X.increment u v)) := by
  rw [← chen_eq_left_assoc X s t u v, ← chen_eq_right_assoc X s t u v]

theorem chen_coeff
    (X : AlgebraicRoughPath T α R) (s t u : T) (word : List α) :
    coeff X s u word =
      Word.coeff
        (Word.tensorProduct (X.increment s t) (X.increment t u)) word := by
  rw [coeff, X.chen s t u]

theorem increment_tensorProduct_reverse_coeff
    (X : AlgebraicRoughPath T α R) (s t : T) (word : List α) :
    Word.coeff
        (Word.tensorProduct (X.increment s t) (X.increment t s)) word =
      Word.coeff (Word.unit α R) word := by
  rw [increment_tensorProduct_reverse X s t]

theorem reverse_tensorProduct_increment_coeff
    (X : AlgebraicRoughPath T α R) (s t : T) (word : List α) :
    Word.coeff
        (Word.tensorProduct (X.increment t s) (X.increment s t)) word =
      Word.coeff (Word.unit α R) word := by
  rw [reverse_tensorProduct_increment X s t]

@[simp]
theorem increment_tensorProduct_reverse_coeff_nil
    (X : AlgebraicRoughPath T α R) (s t : T) :
    Word.coeff
        (Word.tensorProduct (X.increment s t) (X.increment t s)) [] = 1 := by
  rw [increment_tensorProduct_reverse X s t]
  rfl

@[simp]
theorem increment_tensorProduct_reverse_coeff_cons
    (X : AlgebraicRoughPath T α R) (s t : T) (x : α) (word : List α) :
    Word.coeff
        (Word.tensorProduct (X.increment s t) (X.increment t s))
        (x :: word) = 0 := by
  rw [increment_tensorProduct_reverse X s t]
  rfl

@[simp]
theorem reverse_tensorProduct_increment_coeff_nil
    (X : AlgebraicRoughPath T α R) (s t : T) :
    Word.coeff
        (Word.tensorProduct (X.increment t s) (X.increment s t)) [] = 1 := by
  rw [reverse_tensorProduct_increment X s t]
  rfl

@[simp]
theorem reverse_tensorProduct_increment_coeff_cons
    (X : AlgebraicRoughPath T α R) (s t : T) (x : α) (word : List α) :
    Word.coeff
        (Word.tensorProduct (X.increment t s) (X.increment s t))
        (x :: word) = 0 := by
  rw [reverse_tensorProduct_increment X s t]
  rfl

theorem chen_coeff_left_assoc
    (X : AlgebraicRoughPath T α R) (s t u v : T) (word : List α) :
    coeff X s v word =
      Word.coeff
        (Word.tensorProduct
          (Word.tensorProduct (X.increment s t) (X.increment t u))
          (X.increment u v)) word := by
  rw [coeff, chen_eq_left_assoc X s t u v]

theorem chen_coeff_right_assoc
    (X : AlgebraicRoughPath T α R) (s t u v : T) (word : List α) :
    coeff X s v word =
      Word.coeff
        (Word.tensorProduct (X.increment s t)
          (Word.tensorProduct (X.increment t u) (X.increment u v))) word := by
  rw [coeff, chen_eq_right_assoc X s t u v]

theorem chen_coeff_nil (X : AlgebraicRoughPath T α R) (s t u : T) :
    coeff X s u [] = coeff X s t [] * coeff X t u [] := by
  rw [chen_coeff X s t u []]
  exact Word.tensorProduct_nil (X.increment s t) (X.increment t u)

theorem chen_coeff_cons
    (X : AlgebraicRoughPath T α R) (s t u : T) (x : α) (word : List α) :
    coeff X s u (x :: word) =
      Word.coeff (X.increment s t) [] *
        Word.coeff (X.increment t u) (x :: word) +
        ((Word.splits word).map fun p =>
          Word.coeff (X.increment s t) (x :: p.1) *
            Word.coeff (X.increment t u) p.2).sum := by
  rw [chen_coeff]
  exact Word.tensorProduct_cons (X.increment s t) (X.increment t u) x word

theorem chen_agreeUpToDegree
    (X : AlgebraicRoughPath T α R) (s t u : T) (n : Nat) :
    Word.AgreeUpToDegree (X.increment s u)
      (Word.tensorProduct (X.increment s t) (X.increment t u)) n :=
  Word.agreeUpToDegree_of_eq (X.chen s t u) n

theorem chen_truncatedIncrement
    (X : AlgebraicRoughPath T α R) (s t u : T) (n : Nat) :
    truncatedIncrement X n s u =
      Word.truncate
        (Word.tensorProduct (X.increment s t) (X.increment t u)) n := by
  exact (Word.truncate_eq_iff
    (X.increment s u)
    (Word.tensorProduct (X.increment s t) (X.increment t u)) n).2
      (chen_agreeUpToDegree X s t u n)

@[simp]
theorem truncatedIncrement_self
    (X : AlgebraicRoughPath T α R) (t : T) (n : Nat) :
    truncatedIncrement X n t t =
      Word.truncate (Word.unit α R) n := by
  rw [truncatedIncrement, X.identity]

theorem truncatedIncrement_tensorProduct_reverse
    (X : AlgebraicRoughPath T α R) (s t : T) (n : Nat) :
    Word.truncate
        (Word.tensorProduct (X.increment s t) (X.increment t s)) n =
      Word.truncate (Word.unit α R) n := by
  rw [increment_tensorProduct_reverse X s t]

theorem reverse_truncatedIncrement_tensorProduct
    (X : AlgebraicRoughPath T α R) (s t : T) (n : Nat) :
    Word.truncate
        (Word.tensorProduct (X.increment t s) (X.increment s t)) n =
      Word.truncate (Word.unit α R) n := by
  rw [reverse_tensorProduct_increment X s t]

end AlgebraicRoughPath

end RoughPaths
