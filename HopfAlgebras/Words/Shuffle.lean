/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

/-!
# Word Combinatorics: Shuffles and Splits

This file defines the shuffle of two words and prefix-suffix splits of a word,
counted with multiplicity, as lists. These are shared between the rough-path
signature theory (shuffle identities) and the Munthe-Kaas-Wright Hopf algebra
of ordered forests, whose product is a shuffle of forests.

## Main definitions

* `Word.shuffle` - all shuffles of two words, counted with multiplicity
* `Word.splits` - all prefix-suffix decompositions of a word
-/

namespace HopfAlgebras

universe u v

namespace Word

/-- All shuffles of two words, with multiplicity. -/
def shuffle {α : Type u} : List α → List α → List (List α)
  | [], v => [v]
  | u, [] => [u]
  | a :: u, b :: v =>
      ((shuffle u (b :: v)).map fun w => a :: w) ++
        ((shuffle (a :: u) v).map fun w => b :: w)
termination_by u v => (u.length, v.length)
decreasing_by
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self u.length)
  · exact Prod.Lex.right _ (Nat.lt_succ_self v.length)

@[simp]
theorem shuffle_nil_left {α : Type u} (v : List α) :
    shuffle [] v = [v] := by
  simp [shuffle]

@[simp]
theorem shuffle_nil_right {α : Type u} : ∀ u : List α, shuffle u [] = [u]
  | [] => by
      unfold shuffle
      rfl
  | _ :: _ => by
      unfold shuffle
      rfl

@[simp]
theorem shuffle_cons_cons {α : Type u} (a b : α) (u v : List α) :
    shuffle (a :: u) (b :: v) =
      ((shuffle u (b :: v)).map fun w => a :: w) ++
        ((shuffle (a :: u) v).map fun w => b :: w) :=
  by simp [shuffle]

/-- The number of shuffles of two words is the binomial coefficient. -/
theorem length_shuffle {α : Type u} :
    ∀ u v : List α, (shuffle u v).length =
      (u.length + v.length).choose u.length
  | [], v => by
      simp
  | a :: u, [] => by
      simp
  | a :: u, b :: v => by
      rw [shuffle_cons_cons, List.length_append, List.length_map,
        List.length_map, length_shuffle u (b :: v),
        length_shuffle (a :: u) v]
      simp only [List.length_cons]
      have h1 : u.length + (v.length + 1) = u.length + v.length + 1 := by
        omega
      have h2 : u.length + 1 + v.length = u.length + v.length + 1 := by
        omega
      have h3 : u.length + 1 + (v.length + 1) =
          (u.length + v.length + 1) + 1 := by omega
      rw [h1, h2, h3]
      conv_rhs => rw [Nat.choose_succ_succ]
termination_by u v => (u.length, v.length)
decreasing_by
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self u.length)
  · exact Prod.Lex.right _ (Nat.lt_succ_self v.length)

theorem shuffle_map {α : Type u} {β : Type v} (f : α → β) :
    ∀ u v : List α, (shuffle u v).map (List.map f) = shuffle (u.map f) (v.map f)
  | [], v => by simp
  | u, [] => by simp
  | a :: u, b :: v => by
      rw [shuffle_cons_cons]
      change
        ((((shuffle u (b :: v)).map fun w => a :: w) ++
            ((shuffle (a :: u) v).map fun w => b :: w)).map (List.map f)) =
          shuffle (f a :: u.map f) (f b :: v.map f)
      rw [shuffle_cons_cons]
      simp only [List.map_append, List.map_map]
      have hleft :
          shuffle (u.map f) (f b :: v.map f) =
            (shuffle u (b :: v)).map (List.map f) := by
        simpa using (shuffle_map f u (b :: v)).symm
      have hright :
          shuffle (f a :: u.map f) (v.map f) =
            (shuffle (a :: u) v).map (List.map f) := by
        simpa using (shuffle_map f (a :: u) v).symm
      rw [hleft, hright]
      simp [List.map_map, Function.comp_def]

theorem shuffle_ne_nil {α : Type u} : ∀ u v : List α, shuffle u v ≠ []
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: u, b :: v => by
      rw [shuffle_cons_cons]
      intro h
      rcases List.append_eq_nil_iff.1 h with ⟨h₁, -⟩
      exact shuffle_ne_nil u (b :: v) (List.map_eq_nil_iff.1 h₁)
termination_by u v => (u.length, v.length)
decreasing_by
  exact Prod.Lex.left _ _ (Nat.lt_succ_self u.length)

/-- Every shuffle of `u` and `v` is a permutation of `u ++ v`. -/
theorem perm_append_of_mem_shuffle {α : Type u} :
    ∀ {u v w : List α}, w ∈ shuffle u v → w.Perm (u ++ v)
  | [], v, w => by
      intro hw
      simp only [shuffle_nil_left, List.mem_singleton] at hw
      simp [hw]
  | a :: u, [], w => by
      intro hw
      simp only [shuffle_nil_right, List.mem_singleton] at hw
      simp [hw]
  | a :: u, b :: v, w => by
      intro hw
      rw [shuffle_cons_cons] at hw
      rcases List.mem_append.1 hw with hw | hw
      · rcases List.mem_map.1 hw with ⟨w', hw', rfl⟩
        exact (perm_append_of_mem_shuffle hw').cons a
      · rcases List.mem_map.1 hw with ⟨w', hw', rfl⟩
        refine ((perm_append_of_mem_shuffle hw').cons b).trans ?_
        exact (List.perm_middle (a := b) (l₁ := a :: u) (l₂ := v)).symm
  termination_by u v => (u.length, v.length)
  decreasing_by
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self u.length)
  · exact Prod.Lex.right _ (Nat.lt_succ_self v.length)

theorem length_of_mem_shuffle {α : Type u} {u v w : List α}
    (hw : w ∈ shuffle u v) : w.length = u.length + v.length := by
  simpa using (perm_append_of_mem_shuffle hw).length_eq

theorem eq_nil_of_mem_shuffle {α : Type u} {u v w : List α}
    (hw : w ∈ shuffle u v) (hnil : w = []) : u = [] ∧ v = [] := by
  subst hnil
  have h := (perm_append_of_mem_shuffle hw).symm.eq_nil
  exact List.append_eq_nil_iff.1 h

theorem ne_nil_of_mem_shuffle_left {α : Type u} {u v w : List α}
    (hw : w ∈ shuffle u v) (hu : u ≠ []) : w ≠ [] :=
  fun hnil => hu (eq_nil_of_mem_shuffle hw hnil).1

theorem ne_nil_of_mem_shuffle_right {α : Type u} {u v w : List α}
    (hw : w ∈ shuffle u v) (hv : v ≠ []) : w ≠ [] :=
  fun hnil => hv (eq_nil_of_mem_shuffle hw hnil).2

private theorem cons_comp_append_eq {α : Type u} (c e : α) :
    ((fun w : List α => c :: w) ∘ fun w => w ++ [e]) =
      ((fun w => w ++ [e]) ∘ fun w : List α => c :: w) := by
  funext w
  simp

/-- Shuffling a single letter into a word ending in `b`: either `a` lands at
the very end, or it shuffles into the prefix. -/
theorem shuffle_singleton_concat_perm {α : Type u} (a b : α) :
    ∀ v : List α,
      (shuffle [a] (v ++ [b])).Perm
        ((v ++ [b] ++ [a]) :: (shuffle [a] v).map fun w => w ++ [b])
  | [] => by
      simp only [List.nil_append, shuffle_cons_cons, shuffle_nil_left,
        shuffle_nil_right, List.map_cons, List.map_nil, List.nil_append,
        shuffle_nil_right, List.singleton_append]
      exact List.Perm.swap _ _ _
  | c :: v => by
      have hexp :
          shuffle [a] ((c :: v) ++ [b]) =
            (a :: ((c :: v) ++ [b])) ::
              (shuffle [a] (v ++ [b])).map fun w => c :: w := by
        rw [List.cons_append, shuffle_cons_cons, shuffle_nil_left]
        rfl
      rw [hexp]
      refine (List.Perm.cons _
        ((shuffle_singleton_concat_perm a b v).map fun w => c :: w)).trans ?_
      have hexp₂ :
          shuffle [a] (c :: v) =
            (a :: c :: v) :: (shuffle [a] v).map fun w => c :: w := by
        rw [shuffle_cons_cons, shuffle_nil_left]
        rfl
      rw [hexp₂]
      simp only [List.map_cons, List.map_map]
      rw [cons_comp_append_eq c b]
      have h₁ : a :: ((c :: v) ++ [b]) = (a :: c :: v) ++ [b] := by simp
      have h₂ : c :: (v ++ [b] ++ [a]) = (c :: v) ++ [b] ++ [a] := by simp
      rw [h₁, h₂]
      exact List.Perm.swap _ _ _

/-- Shuffling a word ending in `a` with a single letter `b`: either `b` lands
at the very end, or it shuffles into the prefix. -/
theorem shuffle_concat_singleton_perm {α : Type u} (a b : α) :
    ∀ u : List α,
      (shuffle (u ++ [a]) [b]).Perm
        ((u ++ [a] ++ [b]) :: (shuffle u [b]).map fun w => w ++ [a])
  | [] => by
      simp only [List.nil_append, shuffle_cons_cons, shuffle_nil_left,
        shuffle_nil_right, List.map_cons, List.map_nil, List.nil_append,
        List.singleton_append]
      exact List.Perm.refl _
  | c :: u => by
      have hexp :
          shuffle ((c :: u) ++ [a]) [b] =
            ((shuffle (u ++ [a]) [b]).map fun w => c :: w) ++
              [b :: ((c :: u) ++ [a])] := by
        rw [List.cons_append, shuffle_cons_cons, shuffle_nil_right]
        rfl
      rw [hexp]
      refine (List.Perm.append_right _
        ((shuffle_concat_singleton_perm a b u).map fun w => c :: w)).trans ?_
      have hexp₂ :
          shuffle (c :: u) [b] =
            ((shuffle u [b]).map fun w => c :: w) ++ [b :: c :: u] := by
        rw [shuffle_cons_cons, shuffle_nil_right]
        rfl
      rw [hexp₂]
      simp only [List.map_cons, List.map_nil, List.map_append, List.map_map,
        List.cons_append]
      rw [cons_comp_append_eq c a]

/-- The right-end recursion for shuffles: every shuffle of `u ++ [a]` and
`v ++ [b]` ends in either `a` or `b`. -/
theorem shuffle_concat_concat_perm {α : Type u} (a b : α) :
    ∀ u v : List α,
      (shuffle (u ++ [a]) (v ++ [b])).Perm
        (((shuffle u (v ++ [b])).map fun w => w ++ [a]) ++
          ((shuffle (u ++ [a]) v).map fun w => w ++ [b]))
  | [], v => by
      rw [List.nil_append, shuffle_nil_left]
      refine (shuffle_singleton_concat_perm a b v).trans ?_
      simp only [List.map_cons, List.map_nil, List.singleton_append]
      exact List.Perm.refl _
  | c :: u, [] => by
      rw [List.nil_append, shuffle_nil_right]
      refine (shuffle_concat_singleton_perm a b (c :: u)).trans ?_
      simp only [List.map_cons, List.map_nil]
      simpa using
        (List.perm_append_comm
          (l₁ := [(c :: u) ++ [a] ++ [b]])
          (l₂ := (shuffle (c :: u) [b]).map fun w => w ++ [a]))
  | c :: u, d :: v => by
      rw [List.cons_append, List.cons_append, shuffle_cons_cons]
      refine (List.Perm.append
        ((shuffle_concat_concat_perm a b u (d :: v)).map fun w => c :: w)
        ((shuffle_concat_concat_perm a b (c :: u) v).map fun w => d :: w)).trans
        ?_
      rw [List.cons_append, List.cons_append, shuffle_cons_cons,
        shuffle_cons_cons]
      simp only [List.map_append, List.map_map]
      rw [cons_comp_append_eq c a, cons_comp_append_eq c b,
        cons_comp_append_eq d a, cons_comp_append_eq d b]
      rw [List.append_assoc, List.append_assoc]
      refine List.Perm.append_left _ ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm
  termination_by u v => (u.length, v.length)
  decreasing_by
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self u.length)
  · exact Prod.Lex.right _ (Nat.lt_succ_self v.length)

/-- Shuffling is commutative up to permutation. -/
theorem shuffle_comm_perm {α : Type u} :
    ∀ u v : List α, (shuffle u v).Perm (shuffle v u)
  | [], v => by
      rw [shuffle_nil_left, shuffle_nil_right]
  | a :: u, [] => by
      rw [shuffle_nil_left, shuffle_nil_right]
  | a :: u, b :: v => by
      rw [shuffle_cons_cons, shuffle_cons_cons]
      refine (List.Perm.append
        ((shuffle_comm_perm u (b :: v)).map fun w => a :: w)
        ((shuffle_comm_perm (a :: u) v).map fun w => b :: w)).trans ?_
      exact List.perm_append_comm
  termination_by u v => (u.length, v.length)
  decreasing_by
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self u.length)
  · exact Prod.Lex.right _ (Nat.lt_succ_self v.length)

private theorem flatMap_id_singleton {α : Type u} (l : List α) :
    (l.flatMap fun x => [x]) = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem flatMap_map' {α β γ : Type u} (l : List α) (g : α → β)
    (f : β → List γ) :
    (l.map g).flatMap f = l.flatMap fun a => f (g a) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem map_flatMap' {α β γ : Type u} (l : List α) (f : α → List β)
    (g : β → γ) :
    (l.flatMap f).map g = l.flatMap fun a => (f a).map g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

/--
Shuffle associativity at the level of multisets of words: shuffling `x ⧢ y`
against `z` produces the same words, with multiplicity, as shuffling `x`
against `y ⧢ z`.
-/
theorem shuffle_flatMap_shuffle_perm {α : Type u} :
    ∀ x y z : List α,
      ((shuffle x y).flatMap fun w => shuffle w z).Perm
        ((shuffle y z).flatMap fun w => shuffle x w)
  | [], y, z => by
      rw [shuffle_nil_left, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      have h : ((shuffle y z).flatMap fun w => shuffle [] w) =
          (shuffle y z).flatMap fun w => [w] := by
        simp only [shuffle_nil_left]
      rw [h, flatMap_id_singleton]
  | x, [], z => by
      rw [shuffle_nil_right, shuffle_nil_left, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
  | x, y, [] => by
      have h : ((shuffle x y).flatMap fun w => shuffle w []) =
          (shuffle x y).flatMap fun w => [w] := by
        simp only [shuffle_nil_right]
      rw [h, flatMap_id_singleton, shuffle_nil_right, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
  | a :: x, b :: y, c :: z => by
      have hL :
          ((shuffle (a :: x) (b :: y)).flatMap fun w =>
              shuffle w (c :: z)).Perm
            ((((shuffle x (b :: y)).flatMap fun w =>
                shuffle w (c :: z)).map fun w => a :: w) ++
              ((((shuffle (a :: x) y).flatMap fun w =>
                shuffle w (c :: z)).map fun w => b :: w) ++
                (((shuffle (a :: x) (b :: y)).flatMap fun w =>
                  shuffle w z).map fun w => c :: w))) := by
        rw [shuffle_cons_cons (a := a) (b := b)]
        simp only [List.flatMap_append, flatMap_map', List.map_append]
        simp only [shuffle_cons_cons]
        refine ((List.flatMap_append_perm _ _ _).symm.append
          (List.flatMap_append_perm _ _ _).symm).trans ?_
        rw [← map_flatMap', ← map_flatMap', ← map_flatMap', ← map_flatMap']
        simp only [List.append_assoc]
        refine List.Perm.append_left _ ?_
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.Perm.append_right _ List.perm_append_comm
      have hR :
          ((shuffle (b :: y) (c :: z)).flatMap fun w =>
              shuffle (a :: x) w).Perm
            ((((shuffle (b :: y) (c :: z)).flatMap fun w =>
                shuffle x w).map fun w => a :: w) ++
              ((((shuffle y (c :: z)).flatMap fun w =>
                shuffle (a :: x) w).map fun w => b :: w) ++
                (((shuffle (b :: y) z).flatMap fun w =>
                  shuffle (a :: x) w).map fun w => c :: w))) := by
        rw [shuffle_cons_cons (a := b) (b := c)]
        simp only [List.flatMap_append, flatMap_map', List.map_append]
        simp only [shuffle_cons_cons]
        refine ((List.flatMap_append_perm _ _ _).symm.append
          (List.flatMap_append_perm _ _ _).symm).trans ?_
        rw [← map_flatMap', ← map_flatMap', ← map_flatMap', ← map_flatMap']
        simp only [List.append_assoc]
        refine List.Perm.append_left _ ?_
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.Perm.append_right _ List.perm_append_comm
      refine hL.trans (List.Perm.trans ?_ hR.symm)
      exact List.Perm.append
        ((shuffle_flatMap_shuffle_perm x (b :: y) (c :: z)).map _)
        (List.Perm.append
          ((shuffle_flatMap_shuffle_perm (a :: x) y (c :: z)).map _)
          ((shuffle_flatMap_shuffle_perm (a :: x) (b :: y) z).map _))
  termination_by x y z => x.length + y.length + z.length
  decreasing_by
  all_goals
    simp only [List.length_cons]
    omega

/-- Exchange of the shuffle arguments: shuffling `x ⧢ y` against `z` gives
the same multiset of words as shuffling `x ⧢ z` against `y`. -/
theorem shuffle_exchange_perm {α : Type u} (x y z : List α) :
    ((shuffle x y).flatMap fun w => shuffle w z).Perm
      ((shuffle x z).flatMap fun w => shuffle w y) :=
  (shuffle_flatMap_shuffle_perm x y z).trans
    ((List.Perm.flatMap_right _ (shuffle_comm_perm y z)).trans
      (shuffle_flatMap_shuffle_perm x z y).symm)

/-- Independent `flatMap`s commute up to permutation. -/
theorem flatMap_comm_perm {α β γ : Type u} (l : List α) (m : List β)
    (f : α → β → List γ) :
    (l.flatMap fun a => m.flatMap fun b => f a b).Perm
      (m.flatMap fun b => l.flatMap fun a => f a b) := by
  induction l with
  | nil =>
      have h : (m.flatMap fun b => ([] : List α).flatMap fun a => f a b) =
          m.flatMap fun _ => ([] : List γ) := by
        simp only [List.flatMap_nil]
      rw [List.flatMap_nil, h, List.flatMap_eq_nil_iff.2 fun _ _ => rfl]
  | cons x l ih =>
      rw [List.flatMap_cons]
      have h : (m.flatMap fun b => (x :: l).flatMap fun a => f a b) =
          m.flatMap fun b => f x b ++ l.flatMap fun a => f a b := by
        simp only [List.flatMap_cons]
      rw [h]
      exact (List.Perm.append_left _ ih).trans
        (List.flatMap_append_perm m (f x) fun b => l.flatMap fun a => f a b)

/-- All prefix-suffix decompositions of a word. -/
def splits {α : Type u} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: w => ([], x :: w) :: (splits w).map fun p => (x :: p.1, p.2)

@[simp]
theorem splits_nil {α : Type u} :
    splits ([] : List α) = [([], [])] :=
  rfl

@[simp]
theorem splits_cons {α : Type u} (x : α) (w : List α) :
    splits (x :: w) = ([], x :: w) :: (splits w).map fun p => (x :: p.1, p.2) :=
  rfl

theorem splits_map {α : Type u} {β : Type v} (f : α → β) :
    ∀ w : List α,
      (splits w).map (fun p => (p.1.map f, p.2.map f)) = splits (w.map f)
  | [] => by simp
  | x :: w => by
      rw [splits_cons]
      change
        List.map (fun p => (p.1.map f, p.2.map f))
            (([], x :: w) :: (splits w).map fun p => (x :: p.1, p.2)) =
          splits (f x :: w.map f)
      rw [splits_cons]
      simp only [List.map_cons, List.map_map]
      rw [← splits_map f w]
      simp [List.map_map, Function.comp_def]

theorem mem_splits_append {α : Type u} {w : List α} :
    ∀ {p : List α × List α}, p ∈ splits w → p.1 ++ p.2 = w := by
  induction w with
  | nil =>
      intro p hp
      rcases p with ⟨p₁, p₂⟩
      simp at hp
      rcases hp with ⟨hp₁, hp₂⟩
      simp [hp₁, hp₂]
  | cons x w ih =>
      intro p hp
      simp only [splits_cons, List.mem_cons, List.mem_map] at hp
      rcases hp with hp | ⟨q, hq, hp⟩
      · cases hp
        rfl
      · cases hp
        simp [ih hq]

theorem flatMap_cons_perm_map_flatMap {α : Type u} {β : Type v}
    (xs : List α) (head : α → β) (tail : α → List β) :
    (xs.flatMap fun x => head x :: tail x).Perm
      (xs.map head ++ xs.flatMap tail) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_cons]
      apply List.Perm.cons
      refine (List.Perm.append (List.Perm.refl (tail x)) ih).trans ?_
      simpa [List.append_assoc] using
        (List.Perm.append (@List.perm_append_comm _ (tail x) (xs.map head))
          (List.Perm.refl (xs.flatMap tail)))

abbrev TripleSplits (α : Type u) :=
  List α × List α × List α

def leftSplits3 {α : Type u} (w : List α) : List (TripleSplits α) :=
  (splits w).flatMap fun p => (splits p.1).map fun q => (q.1, q.2, p.2)

def rightSplits3 {α : Type u} (w : List α) : List (TripleSplits α) :=
  (splits w).flatMap fun p => (splits p.2).map fun q => (p.1, q.1, q.2)

private theorem leftSplits3_cons_perm_canonical {α : Type u} (x : α) (w : List α) :
    (leftSplits3 (x :: w)).Perm
      (([], [], x :: w) ::
        ((splits w).map fun p => ([], x :: p.1, p.2)) ++
          ((leftSplits3 w).map fun p => (x :: p.1, p.2.1, p.2.2))) := by
  simp only [leftSplits3, splits_cons, List.flatMap_cons]
  apply List.Perm.cons
  convert
    flatMap_cons_perm_map_flatMap (splits w)
      (fun p : List α × List α => ([], x :: p.1, p.2))
      (fun p : List α × List α =>
        (splits p.1).map fun q => (x :: q.1, q.2, p.2))
    using 1 <;>
    simp [List.map_flatMap, List.flatMap_map, Function.comp_def]

private theorem rightSplits3_cons_perm_canonical {α : Type u} (x : α) (w : List α) :
    (rightSplits3 (x :: w)).Perm
      (([], [], x :: w) ::
        ((splits w).map fun p => ([], x :: p.1, p.2)) ++
          ((rightSplits3 w).map fun p => (x :: p.1, p.2.1, p.2.2))) := by
  simp only [rightSplits3, splits_cons, List.flatMap_cons]
  apply List.Perm.cons
  simp [List.map_flatMap, List.flatMap_map, Function.comp_def]

theorem leftSplits3_perm_rightSplits3 {α : Type u} :
    ∀ w : List α, (leftSplits3 w).Perm (rightSplits3 w)
  | [] => by
      simp [leftSplits3, rightSplits3]
  | x :: w => by
      have hmid :
          ((([], [], x :: w) ::
              ((splits w).map fun p : List α × List α => ([], x :: p.1, p.2)) ++
                ((leftSplits3 w).map fun p : TripleSplits α =>
                  (x :: p.1, p.2.1, p.2.2))).Perm
            (([], [], x :: w) ::
              ((splits w).map fun p : List α × List α => ([], x :: p.1, p.2)) ++
                ((rightSplits3 w).map fun p : TripleSplits α =>
                  (x :: p.1, p.2.1, p.2.2)))) := by
        apply List.Perm.cons
        apply List.Perm.append (List.Perm.refl _)
        exact (leftSplits3_perm_rightSplits3 w).map
          fun p => (x :: p.1, p.2.1, p.2.2)
      exact (leftSplits3_cons_perm_canonical x w).trans
        (hmid.trans (rightSplits3_cons_perm_canonical x w).symm)

end Word

end HopfAlgebras
