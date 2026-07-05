/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Words.Shuffle

/-!
# Shuffle–deconcatenation compatibility

The keystone bialgebra theorem of the word shuffle Hopf algebra: the
prefix–suffix splittings of all shuffles of `u` and `v` are, with
multiplicity, the pairs of shuffles of splittings of `u` and of `v`
(`Word.shuffle_splits_perm`). This drives both Chen's theorem for
piecewise-linear signatures and the bialgebra axiom of
`HopfAlgebras.wordHopf`.
-/

namespace HopfAlgebras

universe u v

variable {α : Type u}

namespace Word

/-- The shuffles of splittings of `u` and `v`, as prefix–suffix pairs. -/
def splitShufflePairs (u v : List α) : List (List α × List α) :=
  (splits u).flatMap fun p =>
    (splits v).flatMap fun q =>
      (shuffle p.1 q.1).flatMap fun x =>
        (shuffle p.2 q.2).map fun y => (x, y)

theorem splitShufflePairs_def (u v : List α) :
    splitShufflePairs u v =
      (splits u).flatMap fun p =>
        (splits v).flatMap fun q =>
          (shuffle p.1 q.1).flatMap fun x =>
            (shuffle p.2 q.2).map fun y => (x, y) :=
  rfl

/-- Prefix a letter to the first component of a splitting. -/
def consFst (a : α) : List α × List α → List α × List α :=
  fun p => (a :: p.1, p.2)

@[simp]
theorem consFst_apply (a : α) (p : List α × List α) :
    consFst a p = (a :: p.1, p.2) :=
  rfl

/-! ### Small loop lemmas -/

private theorem flatMap_singleton_pairs (l : List (List α × List α)) :
    (l.flatMap fun q => [(q.1, q.2)]) = l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
      rw [List.flatMap_cons, ih]
      rfl

/-- Expanding a `flatMap` over the splittings of a cons. -/
private theorem flatMap_splits_cons {β : Type v} (a : α) (w : List α)
    (F : List α × List α → List β) :
    (splits (a :: w)).flatMap F =
      F ([], a :: w) ++ (splits w).flatMap fun p => F (a :: p.1, p.2) := by
  rw [splits_cons, List.flatMap_cons]
  congr 1
  rw [List.flatMap_map]

/-- `flatMap` over a singleton shuffle with empty left factor. -/
private theorem flatMap_shuffle_nil_left {β : Type v} (z : List α)
    (f : List α → List β) :
    (shuffle ([] : List α) z).flatMap f = f z := by
  rw [shuffle_nil_left, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- `flatMap` over a singleton shuffle with empty right factor. -/
private theorem flatMap_shuffle_nil_right {β : Type v} (z : List α)
    (f : List α → List β) :
    (shuffle z ([] : List α)).flatMap f = f z := by
  rw [shuffle_nil_right, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Rearranging four appended blocks pairwise. -/
private theorem append_append_perm {β : Type v} (a b c d : List β) :
    ((a ++ b) ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
  rw [List.append_assoc, List.append_assoc]
  exact List.Perm.append_left a (List.perm_append_comm_assoc b c d)

/-! ### Degenerate cases -/

theorem splitShufflePairs_nil_left (v : List α) :
    splitShufflePairs [] v = splits v := by
  rw [splitShufflePairs_def, splits_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  have h1 : ((splits v).flatMap fun q =>
      (shuffle ([] : List α) q.1).flatMap fun x =>
        (shuffle ([] : List α) q.2).map fun y => (x, y)) =
      (splits v).flatMap fun q => [(q.1, q.2)] := by
    apply List.flatMap_congr
    intro q _
    rw [flatMap_shuffle_nil_left, shuffle_nil_left, List.map_cons,
      List.map_nil]
  rw [h1, flatMap_singleton_pairs]

theorem splitShufflePairs_nil_right (u : List α) :
    splitShufflePairs u [] = splits u := by
  rw [splitShufflePairs_def, splits_nil]
  have h1 : ((splits u).flatMap fun p =>
      ([(([] : List α), ([] : List α))].flatMap fun q =>
        (shuffle p.1 q.1).flatMap fun x =>
          (shuffle p.2 q.2).map fun y => (x, y))) =
      (splits u).flatMap fun p => [(p.1, p.2)] := by
    apply List.flatMap_congr
    intro p _
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [flatMap_shuffle_nil_right, shuffle_nil_right, List.map_cons,
      List.map_nil]
  rw [h1, flatMap_singleton_pairs]

/-! ### The cons–cons decompositions -/

section ConsCons

variable (x y : α) (u' v' : List α)

/-- The `A`-block: splittings of shuffles with empty prefix. -/
private def blockA : List (List α × List α) :=
  (shuffle (x :: u') (y :: v')).map fun w => (([] : List α), w)

/-- The `B₁₀`-block: prefix from `u` only. -/
private def blockB10 : List (List α × List α) :=
  (splits u').flatMap fun p =>
    (shuffle p.2 (y :: v')).map fun y' => (x :: p.1, y')

/-- The `B₀₁`-block: prefix from `v` only. -/
private def blockB01 : List (List α × List α) :=
  (splits v').flatMap fun q =>
    (shuffle (x :: u') q.2).map fun y' => (y :: q.1, y')

/-- The `C₁`-block: mixed prefixes starting with `x`. -/
private def blockC1 : List (List α × List α) :=
  (splits u').flatMap fun p =>
    (splits v').flatMap fun q =>
      (shuffle p.1 (y :: q.1)).flatMap fun x' =>
        (shuffle p.2 q.2).map fun y' => (x :: x', y')

/-- The `C₂`-block: mixed prefixes starting with `y`. -/
private def blockC2 : List (List α × List α) :=
  (splits u').flatMap fun p =>
    (splits v').flatMap fun q =>
      (shuffle (x :: p.1) q.1).flatMap fun x' =>
        (shuffle p.2 q.2).map fun y' => (y :: x', y')

/-- Mapped recursion, `x`-side: `consFst x` of the sub-pairs is `B₁₀ ++ C₁`
up to permutation. -/
private theorem map_consFst_x_perm :
    ((splitShufflePairs u' (y :: v')).map (consFst x)).Perm
      (blockB10 x y u' v' ++ blockC1 x y u' v') := by
  have hexp : (splitShufflePairs u' (y :: v')).map (consFst x) =
      (splits u').flatMap fun p =>
        ((shuffle p.2 (y :: v')).map fun y' => (x :: p.1, y')) ++
          ((splits v').flatMap fun q =>
            (shuffle p.1 (y :: q.1)).flatMap fun x' =>
              (shuffle p.2 q.2).map fun y' => (x :: x', y')) := by
    rw [splitShufflePairs_def, List.map_flatMap]
    apply List.flatMap_congr
    intro p _
    rw [List.map_flatMap, flatMap_splits_cons]
    congr 1
    · rw [flatMap_shuffle_nil_right, List.map_map]
      rfl
    · apply List.flatMap_congr
      intro q _
      rw [List.map_flatMap]
      apply List.flatMap_congr
      intro x' _
      rw [List.map_map]
      rfl
  rw [hexp, blockB10, blockC1]
  exact (List.flatMap_append_perm _ _ _).symm

/-- Mapped recursion, `y`-side: `consFst y` of the sub-pairs is `B₀₁ ++ C₂`
up to permutation. -/
private theorem map_consFst_y_perm :
    ((splitShufflePairs (x :: u') v').map (consFst y)).Perm
      (blockB01 x y u' v' ++ blockC2 x y u' v') := by
  have hexp : (splitShufflePairs (x :: u') v').map (consFst y) =
      ((splits v').flatMap fun q =>
        (shuffle (x :: u') q.2).map fun y' => (y :: q.1, y')) ++
        ((splits u').flatMap fun p =>
          (splits v').flatMap fun q =>
            (shuffle (x :: p.1) q.1).flatMap fun x' =>
              (shuffle p.2 q.2).map fun y' => (y :: x', y')) := by
    rw [splitShufflePairs_def, flatMap_splits_cons, List.map_append]
    congr 1
    · rw [List.map_flatMap]
      apply List.flatMap_congr
      intro q _
      rw [flatMap_shuffle_nil_left, List.map_map]
      rfl
    · rw [List.map_flatMap]
      apply List.flatMap_congr
      intro p _
      rw [List.map_flatMap]
      apply List.flatMap_congr
      intro q _
      rw [List.map_flatMap]
      apply List.flatMap_congr
      intro x' _
      rw [List.map_map]
      rfl
  rw [hexp, blockB01, blockC2]

/-- **K2**: the split–shuffle pairs at a double cons decompose into the
five blocks. -/
private theorem splitShufflePairs_cons_cons_perm :
    (splitShufflePairs (x :: u') (y :: v')).Perm
      (blockA x y u' v' ++
        (((splitShufflePairs u' (y :: v')).map (consFst x)) ++
          ((splitShufflePairs (x :: u') v').map (consFst y)))) := by
  -- expand the p-loop and the p₀ q-loop
  have hexp : splitShufflePairs (x :: u') (y :: v') =
      (blockA x y u' v' ++ blockB01 x y u' v') ++
        ((splits u').flatMap fun p =>
          ((shuffle p.2 (y :: v')).map fun y' => (x :: p.1, y')) ++
            ((splits v').flatMap fun q =>
              ((shuffle p.1 (y :: q.1)).flatMap fun x' =>
                (shuffle p.2 q.2).map fun y' => (x :: x', y')) ++
              ((shuffle (x :: p.1) q.1).flatMap fun x' =>
                (shuffle p.2 q.2).map fun y' => (y :: x', y')))) := by
    rw [splitShufflePairs_def, flatMap_splits_cons]
    congr 1
    · -- the p₀ = ([], x::u') block: A ++ B₀₁
      rw [flatMap_splits_cons]
      congr 1
      · -- q₀ = ([], y::v'): the A block
        rw [flatMap_shuffle_nil_left, blockA]
      · -- q' ∈ splits v': the B₀₁ block
        rw [blockB01]
        apply List.flatMap_congr
        intro q _
        rw [flatMap_shuffle_nil_left]
    · -- the p' ∈ splits u' blocks
      apply List.flatMap_congr
      intro p _
      rw [flatMap_splits_cons]
      congr 1
      · -- q₀: the B₁₀ summand
        rw [flatMap_shuffle_nil_right]
      · -- q' ∈ splits v': shuffle-cons-cons split into C₁ ++ C₂ summands
        apply List.flatMap_congr
        intro q _
        rw [shuffle_cons_cons, List.flatMap_append, List.flatMap_map,
          List.flatMap_map]
  rw [hexp]
  -- split the mixed p'-loop into B₁₀ ++ (C₁ ++ C₂)
  have hsplit : ((splits u').flatMap fun p =>
      ((shuffle p.2 (y :: v')).map fun y' => (x :: p.1, y')) ++
        ((splits v').flatMap fun q =>
          ((shuffle p.1 (y :: q.1)).flatMap fun x' =>
            (shuffle p.2 q.2).map fun y' => (x :: x', y')) ++
          ((shuffle (x :: p.1) q.1).flatMap fun x' =>
            (shuffle p.2 q.2).map fun y' => (y :: x', y')))).Perm
      (blockB10 x y u' v' ++ (blockC1 x y u' v' ++ blockC2 x y u' v')) := by
    refine ((List.flatMap_append_perm _ _ _).symm).trans ?_
    refine List.Perm.append (List.Perm.refl _) ?_
    refine (List.Perm.flatMap (List.Perm.refl _) fun p _ =>
      (List.flatMap_append_perm _ _ _).symm).trans ?_
    exact (List.flatMap_append_perm _ _ _).symm
  refine (List.Perm.append_left _ hsplit).trans ?_
  -- rearrange (A ++ B₀₁) ++ (B₁₀ ++ (C₁ ++ C₂))
  --        ~  A ++ ((B₁₀ ++ C₁) ++ (B₀₁ ++ C₂))
  refine List.Perm.trans ?_ (List.Perm.append_left _
    ((map_consFst_x_perm x y u' v').symm.append
      (map_consFst_y_perm x y u' v').symm))
  -- goal: (A ++ B₀₁) ++ (B₁₀ ++ (C₁ ++ C₂)) ~ A ++ ((B₁₀ ++ C₁) ++ (B₀₁ ++ C₂))
  rw [List.append_assoc, List.append_assoc]
  refine List.Perm.append_left _ ?_
  refine (List.perm_append_comm_assoc _ _ _).trans ?_
  exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)

end ConsCons

/-- **K1**: splitting all shuffles at a double cons decomposes into the
empty-prefix block plus the mapped sub-recursions. -/
private theorem flatMap_splits_shuffle_cons_cons_perm (x y : α) (u' v' : List α) :
    ((shuffle (x :: u') (y :: v')).flatMap splits).Perm
      (blockA x y u' v' ++
        ((((shuffle u' (y :: v')).flatMap splits).map (consFst x)) ++
          (((shuffle (x :: u') v').flatMap splits).map (consFst y)))) := by
  rw [shuffle_cons_cons, List.flatMap_append, List.flatMap_map,
    List.flatMap_map]
  have h1 : ((shuffle u' (y :: v')).flatMap fun w => splits (x :: w)).Perm
      (((shuffle u' (y :: v')).map fun w => (([] : List α), x :: w)) ++
        ((shuffle u' (y :: v')).flatMap splits).map (consFst x)) := by
    have he : ((shuffle u' (y :: v')).flatMap fun w => splits (x :: w)) =
        (shuffle u' (y :: v')).flatMap fun w =>
          (([] : List α), x :: w) :: (splits w).map (consFst x) := by
      apply List.flatMap_congr
      intro w _
      rw [splits_cons]
      rfl
    rw [he, List.map_flatMap]
    exact flatMap_cons_perm_map_flatMap _ _ _
  have h2 : ((shuffle (x :: u') v').flatMap fun w => splits (y :: w)).Perm
      (((shuffle (x :: u') v').map fun w => (([] : List α), y :: w)) ++
        ((shuffle (x :: u') v').flatMap splits).map (consFst y)) := by
    have he : ((shuffle (x :: u') v').flatMap fun w => splits (y :: w)) =
        (shuffle (x :: u') v').flatMap fun w =>
          (([] : List α), y :: w) :: (splits w).map (consFst y) := by
      apply List.flatMap_congr
      intro w _
      rw [splits_cons]
      rfl
    rw [he, List.map_flatMap]
    exact flatMap_cons_perm_map_flatMap _ _ _
  refine (h1.append h2).trans ?_
  refine (append_append_perm _ _ _ _).trans ?_
  refine List.Perm.append (List.Perm.of_eq ?_) (List.Perm.refl _)
  rw [blockA, shuffle_cons_cons, List.map_append, List.map_map, List.map_map]
  rfl

/-- **Shuffle–deconcatenation bialgebra compatibility.** -/
theorem shuffle_splits_perm :
    ∀ u v : List α,
      ((shuffle u v).flatMap splits).Perm (splitShufflePairs u v)
  | [], v => by
      rw [splitShufflePairs_nil_left, shuffle_nil_left, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
  | (x :: u'), [] => by
      rw [splitShufflePairs_nil_right, shuffle_nil_right, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
  | (x :: u'), (y :: v') => by
      refine (flatMap_splits_shuffle_cons_cons_perm x y u' v').trans ?_
      refine List.Perm.trans ?_ (splitShufflePairs_cons_cons_perm x y u' v').symm
      exact List.Perm.append_left _
        (((shuffle_splits_perm u' (y :: v')).map _).append
          ((shuffle_splits_perm (x :: u') v').map _))
  termination_by u v => u.length + v.length

end Word

end HopfAlgebras
