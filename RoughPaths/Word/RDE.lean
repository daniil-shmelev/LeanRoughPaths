/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Signature.Log

/-!
# Rough Differential Equation Expansions

This file records the algebraic part of rough differential equation expansions.
The iterated vector fields are kept abstract, so the API applies to ordinary
Taylor expansions, RDE Taylor expansions, and log-ODE vector fields.

## Main definitions

* `Word.wordsOfLength` - all words of a fixed length over a finite alphabet
* `Word.wordsUpToLength` - all words up to a fixed length
* `IteratedVectorFields` - abstract iterated vector fields indexed by words
* `IteratedVectorFields.applySeriesTruncated` - finite series action
* `IteratedVectorFields.taylorIncrement` - truncated RDE Taylor increment
* `IteratedVectorFields.logODEVectorField` - log-signature-driven vector field

## References

* Terry Lyons, Michael Caruana, Thierry Levy,
  *Differential Equations Driven by Rough Paths*
* Peter Friz, Nicolas Victoir, *Multidimensional Stochastic Processes as Rough Paths*
* Martin Hairer, Kelly, *Geometric versus non-geometric rough paths*

Branched (forest-indexed) analogues live downstream in LeanBSeries.
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z y x

open scoped BigOperators

noncomputable section

namespace Word

variable {α : Type u}

/-- List form of all words of a fixed length over a finite alphabet. -/
def wordsOfLengthList (α : Type u) [Fintype α] : Nat → List (List α)
  | 0 => [[]]
  | n + 1 =>
      (Finset.univ : Finset α).toList.flatMap fun a =>
        (wordsOfLengthList α n).map fun word => a :: word

theorem mem_wordsOfLengthList_iff [Fintype α]
    {word : List α} {n : Nat} :
    word ∈ wordsOfLengthList α n ↔ word.length = n := by
  induction n generalizing word with
  | zero =>
      cases word <;> simp [wordsOfLengthList]
  | succ n ih =>
      cases word with
      | nil =>
          constructor
          · intro h
            rw [wordsOfLengthList, List.mem_flatMap] at h
            rcases h with ⟨a, _ha, hmem⟩
            rw [List.mem_map] at hmem
            rcases hmem with ⟨tail, _htail, htail⟩
            cases htail
          · intro h
            exact False.elim
              ((Nat.succ_ne_zero n) (by simpa [Nat.succ_eq_add_one] using h.symm))
      | cons a word =>
          constructor
          · intro h
            rw [wordsOfLengthList, List.mem_flatMap] at h
            rcases h with ⟨b, _hb, hmem⟩
            rw [List.mem_map] at hmem
            rcases hmem with ⟨tail, htail, hbtail⟩
            cases hbtail
            simp [ih.mp htail]
          · intro h
            rw [wordsOfLengthList, List.mem_flatMap]
            refine ⟨a, ?_, ?_⟩
            · rw [Finset.mem_toList]
              exact Finset.mem_univ a
            · rw [List.mem_map]
              exact ⟨word, ih.mpr (by simpa using h), rfl⟩

/-- All words of a fixed length over a finite alphabet. -/
def wordsOfLength (α : Type u) [Fintype α] [DecidableEq α] :
    Nat → Finset (List α) :=
  fun n => (wordsOfLengthList α n).toFinset

@[simp]
theorem mem_wordsOfLength_iff [Fintype α] [DecidableEq α]
    {word : List α} {n : Nat} :
    word ∈ wordsOfLength α n ↔ word.length = n := by
  rw [wordsOfLength, List.mem_toFinset, mem_wordsOfLengthList_iff]

/-- All words whose length is at most `n`. -/
def wordsUpToLength (α : Type u) [Fintype α] [DecidableEq α]
    (n : Nat) : Finset (List α) :=
  (Finset.range (n + 1)).biUnion fun k => wordsOfLength α k

@[simp]
theorem mem_wordsUpToLength_iff [Fintype α] [DecidableEq α]
    {word : List α} {n : Nat} :
    word ∈ wordsUpToLength α n ↔ word.length ≤ n := by
  rw [wordsUpToLength]
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_wordsOfLength_iff]
  constructor
  · rintro ⟨k, hk, hword⟩
    omega
  · intro hword
    exact ⟨word.length, by omega, rfl⟩

@[simp]
theorem wordsUpToLength_zero [Fintype α] [DecidableEq α] :
    wordsUpToLength α 0 = {[]} := by
  ext word
  simp

end Word

/-- Abstract iterated vector fields indexed by words. -/
structure IteratedVectorFields (α : Type u) (E : Type v) where
  eval : List α → E → E
  eval_empty : ∀ y, eval [] y = y

namespace IteratedVectorFields

variable {α : Type u} {β : Type v} {R : Type w} {E : Type z}

@[ext]
theorem ext {V W : IteratedVectorFields α E}
    (h : ∀ word y, V.eval word y = W.eval word y) : V = W := by
  cases V with
  | mk evalV hV =>
    cases W with
    | mk evalW hW =>
      have heval : evalV = evalW := by
        funext word y
        exact h word y
      subst evalW
      rfl

@[simp]
theorem eval_empty_apply (V : IteratedVectorFields α E) (y : E) :
    V.eval [] y = y :=
  V.eval_empty y

/-- Pull iterated vector fields back along a map of alphabets. -/
def comapMapLetters (f : α → β) (V : IteratedVectorFields β E) :
    IteratedVectorFields α E where
  eval word y := V.eval (word.map f) y
  eval_empty y := by
    simp

@[simp]
theorem comapMapLetters_eval (f : α → β)
    (V : IteratedVectorFields β E) (word : List α) (y : E) :
    (comapMapLetters f V).eval word y = V.eval (word.map f) y :=
  rfl

@[simp]
theorem comapMapLetters_id (V : IteratedVectorFields α E) :
    comapMapLetters id V = V := by
  ext word y
  simp [comapMapLetters]

theorem comapMapLetters_comp {γ : Type u}
    (f : α → β) (g : β → γ) (V : IteratedVectorFields γ E) :
    comapMapLetters f (comapMapLetters g V) = comapMapLetters (g ∘ f) V := by
  ext word y
  simp [comapMapLetters, List.map_map, Function.comp_def]

/-- Apply a word-indexed series through degree `n` to iterated vector fields. -/
def applySeriesTruncated [Fintype α] [DecidableEq α]
    [Semiring R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (a : (List α → R))
    (n : Nat) (y : E) : E :=
  (Word.wordsUpToLength α n).sum fun word =>
    Word.coeff a word • V.eval word y

theorem applySeriesTruncated_congr [Fintype α] [DecidableEq α]
    [Semiring R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) {a b : (List α → R)} {n : Nat}
    (h : Word.AgreeUpToDegree a b n) (y : E) :
    V.applySeriesTruncated a n y = V.applySeriesTruncated b n y := by
  unfold applySeriesTruncated
  apply Finset.sum_congr rfl
  intro word hword
  rw [h word (Word.mem_wordsUpToLength_iff.mp hword)]

@[simp]
theorem applySeriesTruncated_zero_series [Fintype α] [DecidableEq α]
    [Semiring R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (n : Nat) (y : E) :
    V.applySeriesTruncated (Word.zero α R) n y = 0 := by
  unfold applySeriesTruncated
  apply Finset.sum_eq_zero
  intro word _hword
  simp [Word.zero]

@[simp]
theorem applySeriesTruncated_unit [Fintype α] [DecidableEq α]
    [Semiring R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (n : Nat) (y : E) :
    V.applySeriesTruncated (Word.unit α R) n y = y := by
  unfold applySeriesTruncated
  have hsingle :
      (Word.wordsUpToLength α n).sum
          (fun word => Word.coeff (Word.unit α R) word • V.eval word y) =
          Word.coeff (Word.unit α R) [] • V.eval [] y := by
    refine Finset.sum_eq_single [] ?_ ?_
    · intro word hword hne
      cases word with
      | nil =>
          exact (hne rfl).elim
      | cons x word =>
          simp [Word.unit]
    · intro hnot
      exact (hnot (by simp)).elim
  simpa [Word.unit] using hsingle

variable {T : Type y}

/-- The truncated Taylor increment driven by a rough path signature. -/
def taylorIncrement [Fintype α] [DecidableEq α]
    [Semiring R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (X : AlgebraicRoughPath T α R)
    (n : Nat) (s t : T) (y : E) : E :=
  V.applySeriesTruncated (X.increment s t) n y

@[simp]
theorem taylorIncrement_self [Fintype α] [DecidableEq α]
    [Semiring R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (X : AlgebraicRoughPath T α R)
    (n : Nat) (t : T) (y : E) :
    V.taylorIncrement X n t t y = y := by
  simp [taylorIncrement]

@[simp]
theorem taylorIncrement_unit [Fintype α] [DecidableEq α]
    [Semiring R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (n : Nat) (s t : T) (y : E) :
    V.taylorIncrement (AlgebraicRoughPath.unit T α R) n s t y = y := by
  simp [taylorIncrement]

@[simp]
theorem taylorIncrement_comapTime [Fintype α] [DecidableEq α]
    [Semiring R] [AddCommMonoid E] [Module R E]
    {S : Type x} (f : S → T) (V : IteratedVectorFields α E)
    (X : AlgebraicRoughPath T α R) (n : Nat) (s t : S) (y : E) :
    V.taylorIncrement (AlgebraicRoughPath.comapTime f X) n s t y =
      V.taylorIncrement X n (f s) (f t) y :=
  rfl

theorem taylorIncrement_eq_of_agreeUpToDegree [Fintype α] [DecidableEq α]
    [Semiring R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) {X Y : AlgebraicRoughPath T α R}
    {n : Nat} (h : AlgebraicRoughPath.AgreeUpToDegree X Y n)
    (s t : T) (y : E) :
    V.taylorIncrement X n s t y = V.taylorIncrement Y n s t y :=
  V.applySeriesTruncated_congr (h s t) y

/-- The log-signature vector field used by the log-ODE method. -/
def logODEVectorField [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (X : AlgebraicRoughPath T α R)
    (n : Nat) (s t : T) : E → E :=
  fun y => V.applySeriesTruncated (AlgebraicRoughPath.logIncrementTruncated X s t n) n y

@[simp]
theorem logODEVectorField_apply [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (X : AlgebraicRoughPath T α R)
    (n : Nat) (s t : T) (y : E) :
    V.logODEVectorField X n s t y =
      V.applySeriesTruncated (AlgebraicRoughPath.logIncrementTruncated X s t n) n y :=
  rfl

@[simp]
theorem logODEVectorField_self [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (X : AlgebraicRoughPath T α R)
    (n : Nat) (t : T) (y : E) :
    V.logODEVectorField X n t t y = 0 := by
  simp [logODEVectorField]

@[simp]
theorem logODEVectorField_zero [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) (X : AlgebraicRoughPath T α R)
    (s t : T) (y : E) :
    V.logODEVectorField X 0 s t y = 0 := by
  simp [logODEVectorField]

@[simp]
theorem logODEVectorField_comapTime [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    {S : Type x} (f : S → T) (V : IteratedVectorFields α E)
    (X : AlgebraicRoughPath T α R) (n : Nat) (s t : S) (y : E) :
    V.logODEVectorField (AlgebraicRoughPath.comapTime f X) n s t y =
      V.logODEVectorField X n (f s) (f t) y :=
  rfl

theorem logODEVectorField_eq_of_agreeUpToDegree [Fintype α] [DecidableEq α]
    [Field R] [AddCommMonoid E] [Module R E]
    (V : IteratedVectorFields α E) {X Y : AlgebraicRoughPath T α R}
    {n : Nat} (h : AlgebraicRoughPath.AgreeUpToDegree X Y n)
    (s t : T) (y : E) :
    V.logODEVectorField X n s t y = V.logODEVectorField Y n s t y :=
  V.applySeriesTruncated_congr (h.logIncrementTruncated (m := n) s t) y

end IteratedVectorFields

end

end RoughPaths
