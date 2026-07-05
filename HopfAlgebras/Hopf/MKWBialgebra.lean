/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.MKWCoproduct

/-!
# Towards the MKW Bialgebra Law

This file defines the pairwise-shuffle product of MKW coproduct term lists
(the operation `⊔⊔` of arXiv:math/0603023) and the grafting tail of the
coproduct recursion, together with their unit laws. These are the operations
in which the MKW bialgebra compatibility
`Δ_N(ω₁ ⧢ ω₂) = Δ_N(ω₁) ⊔⊔ Δ_N(ω₂)` is stated.

## Main definitions

* `PlanarForest.pairShuffle` - shuffle both tensor factors of two term lists
* `PlanarForest.graftTail` - the tail operation of the coproduct recursion
-/

namespace HopfAlgebras

open HopfAlgebras

namespace PlanarForest

/-- The pairwise-shuffle product of two coproduct term lists: shuffle the
pruned factors and the remaining factors of every pair of terms
(the operation `⊔⊔` of arXiv:math/0603023). -/
def pairShuffle (xs ys : List (PlanarForest × PlanarForest)) :
    List (PlanarForest × PlanarForest) :=
  xs.flatMap fun t₁ => ys.flatMap fun t₂ =>
    (Word.shuffle t₁.1 t₂.1).flatMap fun p =>
      (Word.shuffle t₁.2 t₂.2).map fun r => (p, r)

/-- The tail operation of the MKW coproduct recursion:
`⊔·(I ⊗ B⁺)Δ_N(B⁻ τ)` applied to a term list. -/
def graftTail (xs : List (PlanarForest × PlanarForest)) (t : PTree) :
    List (PlanarForest × PlanarForest) :=
  xs.flatMap fun pr₁ => (mkwTerms t.children).flatMap fun pr₂ =>
    (Word.shuffle pr₁.1 pr₂.1).map fun s => (s, pr₁.2 ++ [PTree.node pr₂.2])

/-- The MKW coproduct recursion in terms of the grafting tail. -/
theorem mkwTerms_concat_graftTail (ω : PlanarForest) (t : PTree) :
    mkwTerms (ω ++ [t]) =
      (ω ++ [t], ([] : PlanarForest)) :: graftTail (mkwTerms ω) t :=
  mkwTerms_concat ω t

@[simp]
theorem pairShuffle_nil_left (ys : List (PlanarForest × PlanarForest)) :
    pairShuffle [] ys = [] :=
  rfl

@[simp]
theorem pairShuffle_nil_right (xs : List (PlanarForest × PlanarForest)) :
    pairShuffle xs [] = [] := by
  simp [pairShuffle]

/-- The empty-cut singleton is a left unit for the pairwise shuffle. -/
@[simp]
theorem pairShuffle_unit_left (ys : List (PlanarForest × PlanarForest)) :
    pairShuffle [(([] : PlanarForest), ([] : PlanarForest))] ys = ys := by
  simp [pairShuffle]

/-- The empty-cut singleton is a right unit for the pairwise shuffle. -/
@[simp]
theorem pairShuffle_unit_right (xs : List (PlanarForest × PlanarForest)) :
    pairShuffle xs [(([] : PlanarForest), ([] : PlanarForest))] = xs := by
  simp [pairShuffle]

@[simp]
theorem graftTail_nil (t : PTree) : graftTail [] t = [] :=
  rfl

theorem graftTail_append (xs ys : List (PlanarForest × PlanarForest))
    (t : PTree) :
    graftTail (xs ++ ys) t = graftTail xs t ++ graftTail ys t := by
  simp [graftTail]

theorem graftTail_perm {xs ys : List (PlanarForest × PlanarForest)}
    (h : xs.Perm ys) (t : PTree) :
    (graftTail xs t).Perm (graftTail ys t) :=
  List.Perm.flatMap_right _ h

theorem pairShuffle_cons_left (x : PlanarForest × PlanarForest)
    (xs ys : List (PlanarForest × PlanarForest)) :
    pairShuffle (x :: xs) ys =
      (ys.flatMap fun t₂ =>
        (Word.shuffle x.1 t₂.1).flatMap fun p =>
          (Word.shuffle x.2 t₂.2).map fun r => (p, r)) ++
        pairShuffle xs ys :=
  rfl

theorem pairShuffle_append_left (xs xs' ys : List (PlanarForest × PlanarForest)) :
    pairShuffle (xs ++ xs') ys = pairShuffle xs ys ++ pairShuffle xs' ys := by
  simp [pairShuffle]

/-- Splitting the second argument of the pairwise shuffle, up to
permutation. -/
theorem pairShuffle_cons_right_perm (xs : List (PlanarForest × PlanarForest))
    (y : PlanarForest × PlanarForest)
    (ys : List (PlanarForest × PlanarForest)) :
    (pairShuffle xs (y :: ys)).Perm
      ((xs.flatMap fun t₁ =>
        (Word.shuffle t₁.1 y.1).flatMap fun p =>
          (Word.shuffle t₁.2 y.2).map fun r => (p, r)) ++
        pairShuffle xs ys) := by
  refine List.Perm.trans ?_ (List.flatMap_append_perm xs _ _).symm
  refine List.Perm.flatMap_left _ fun t₁ _ => ?_
  rw [List.flatMap_cons]

private theorem perm_of_eq {α : Type*} {l₁ l₂ : List α} (h : l₁ = l₂) :
    l₁.Perm l₂ :=
  h ▸ List.Perm.refl l₁

private theorem map_eq_flatMap' {α β : Type*} (l : List α) (f : α → β) :
    l.map f = l.flatMap fun a => [f a] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem flatMap_map' {α β γ : Type*} (l : List α) (g : α → β)
    (f : β → List γ) :
    (l.map g).flatMap f = l.flatMap fun a => f (g a) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem map_flatMap' {α β γ : Type*} (l : List α) (f : α → List β)
    (g : β → γ) :
    (l.flatMap f).map g = l.flatMap fun a => (f a).map g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem flatMap_assoc' {α β γ : Type*} (l : List α) (f : α → List β)
    (g : β → List γ) :
    (l.flatMap f).flatMap g = l.flatMap fun a => (f a).flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.flatMap_append, ih]

private theorem flatMap_cons_perm {α β : Type*} (l : List α) (f : α → β)
    (g : α → List β) :
    (l.flatMap fun a => f a :: g a).Perm (l.map f ++ l.flatMap g) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [List.flatMap_cons, List.map_cons, List.cons_append]
      refine List.Perm.cons _ ?_
      refine (List.Perm.append_left _ ih).trans ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm

universe u

private theorem flatMap_map_comm_perm {α β γ : Type u} (l : List α)
    (m : List β) (f : α → β → γ) :
    (l.flatMap fun a => m.map fun b => f a b).Perm
      (m.flatMap fun b => l.map fun a => f a b) := by
  have h₁ : (l.flatMap fun a => m.map fun b => f a b) =
      l.flatMap fun a => m.flatMap fun b => [f a b] := by
    simp only [map_eq_flatMap']
  have h₂ : (m.flatMap fun b => l.map fun a => f a b) =
      m.flatMap fun b => l.flatMap fun a => [f a b] := by
    simp only [map_eq_flatMap']
  rw [h₁, h₂]
  exact Word.flatMap_comm_perm l m fun a b => [f a b]

/-- Reorder one term's grafted coproduct data: move the branch data outward
and exchange the pruned-factor shuffles. -/
private theorem inner_reorder_permA (u₁ u₂ v₁ v₂ : PlanarForest)
    (cs : List (PlanarForest × PlanarForest)) :
    ((Word.shuffle u₁ v₁).flatMap fun p' =>
        (Word.shuffle u₂ v₂).flatMap fun r =>
          cs.flatMap fun c =>
            (Word.shuffle p' c.1).map fun s =>
              (s, r ++ [PTree.node c.2])).Perm
      (cs.flatMap fun c =>
        (Word.shuffle u₁ c.1).flatMap fun s₁ =>
          (Word.shuffle s₁ v₁).flatMap fun p =>
            (Word.shuffle u₂ v₂).map fun r => (p, r ++ [PTree.node c.2])) := by
  refine (List.Perm.flatMap_left _ fun p' _ =>
    Word.flatMap_comm_perm (Word.shuffle u₂ v₂) cs fun r c =>
      (Word.shuffle p' c.1).map fun s => (s, r ++ [PTree.node c.2])).trans ?_
  refine (List.Perm.flatMap_left _ fun p' _ =>
    List.Perm.flatMap_left _ fun c _ =>
      flatMap_map_comm_perm (Word.shuffle u₂ v₂) (Word.shuffle p' c.1)
        fun r s => (s, r ++ [PTree.node c.2])).trans ?_
  refine (Word.flatMap_comm_perm (Word.shuffle u₁ v₁) cs fun p' c =>
    (Word.shuffle p' c.1).flatMap fun s =>
      (Word.shuffle u₂ v₂).map fun r => (s, r ++ [PTree.node c.2])).trans ?_
  refine List.Perm.flatMap_left _ fun c _ => ?_
  rw [← flatMap_assoc']
  refine (List.Perm.flatMap_right _
    (Word.shuffle_exchange_perm u₁ v₁ c.1)).trans ?_
  rw [flatMap_assoc']

/-- The variant of `inner_reorder_permA` in which the grafted branch attaches
via the second factor of the shuffle. -/
private theorem inner_reorder_permB (u₁ u₂ v₁ v₂ : PlanarForest)
    (cs : List (PlanarForest × PlanarForest)) :
    ((Word.shuffle u₁ v₁).flatMap fun p' =>
        (Word.shuffle u₂ v₂).flatMap fun r =>
          cs.flatMap fun c =>
            (Word.shuffle p' c.1).map fun s =>
              (s, r ++ [PTree.node c.2])).Perm
      (cs.flatMap fun c =>
        (Word.shuffle v₁ c.1).flatMap fun s₂ =>
          (Word.shuffle u₁ s₂).flatMap fun p =>
            (Word.shuffle u₂ v₂).map fun r => (p, r ++ [PTree.node c.2])) := by
  refine (List.Perm.flatMap_left _ fun p' _ =>
    Word.flatMap_comm_perm (Word.shuffle u₂ v₂) cs fun r c =>
      (Word.shuffle p' c.1).map fun s => (s, r ++ [PTree.node c.2])).trans ?_
  refine (List.Perm.flatMap_left _ fun p' _ =>
    List.Perm.flatMap_left _ fun c _ =>
      flatMap_map_comm_perm (Word.shuffle u₂ v₂) (Word.shuffle p' c.1)
        fun r s => (s, r ++ [PTree.node c.2])).trans ?_
  refine (Word.flatMap_comm_perm (Word.shuffle u₁ v₁) cs fun p' c =>
    (Word.shuffle p' c.1).flatMap fun s =>
      (Word.shuffle u₂ v₂).map fun r => (s, r ++ [PTree.node c.2])).trans ?_
  refine List.Perm.flatMap_left _ fun c _ => ?_
  rw [← flatMap_assoc']
  refine (List.Perm.flatMap_right _
    (Word.shuffle_flatMap_shuffle_perm u₁ v₁ c.1)).trans ?_
  rw [flatMap_assoc']

/--
First canonical form of grafting after a pairwise shuffle: the graft data is
enumerated together with the first factor
(arXiv:math/0603023, proof of Theorem 2). -/
private theorem graftTail_pairShuffle_canonicalA
    (xs ys : List (PlanarForest × PlanarForest)) (τ : PTree) :
    (graftTail (pairShuffle xs ys) τ).Perm
      (xs.flatMap fun t₁ =>
        (mkwTerms τ.children).flatMap fun c₁ =>
          (Word.shuffle t₁.1 c₁.1).flatMap fun s₁ =>
            ys.flatMap fun t₂ =>
              (Word.shuffle s₁ t₂.1).flatMap fun p =>
                (Word.shuffle t₁.2 t₂.2).map fun r =>
                  (p, r ++ [PTree.node c₁.2])) := by
  simp only [graftTail, pairShuffle, flatMap_assoc', flatMap_map']
  refine List.Perm.flatMap_left _ fun t₁ _ => ?_
  refine (List.Perm.flatMap_left _ fun t₂ _ =>
    inner_reorder_permA t₁.1 t₁.2 t₂.1 t₂.2 (mkwTerms τ.children)).trans ?_
  refine (Word.flatMap_comm_perm ys (mkwTerms τ.children) fun t₂ c =>
    (Word.shuffle t₁.1 c.1).flatMap fun s₁ =>
      (Word.shuffle s₁ t₂.1).flatMap fun p =>
        (Word.shuffle t₁.2 t₂.2).map fun r =>
          (p, r ++ [PTree.node c.2])).trans ?_
  refine List.Perm.flatMap_left _ fun c _ => ?_
  exact Word.flatMap_comm_perm ys (Word.shuffle t₁.1 c.1) fun t₂ s₁ =>
    (Word.shuffle s₁ t₂.1).flatMap fun p =>
      (Word.shuffle t₁.2 t₂.2).map fun r => (p, r ++ [PTree.node c.2])

/--
Second canonical form of grafting after a pairwise shuffle: the graft data is
enumerated together with the second factor. -/
private theorem graftTail_pairShuffle_canonicalB
    (xs ys : List (PlanarForest × PlanarForest)) (τ : PTree) :
    (graftTail (pairShuffle xs ys) τ).Perm
      (xs.flatMap fun t₁ =>
        ys.flatMap fun t₂ =>
          (mkwTerms τ.children).flatMap fun c₂ =>
            (Word.shuffle t₂.1 c₂.1).flatMap fun s₂ =>
              (Word.shuffle t₁.1 s₂).flatMap fun p =>
                (Word.shuffle t₁.2 t₂.2).map fun r =>
                  (p, r ++ [PTree.node c₂.2])) := by
  simp only [graftTail, pairShuffle, flatMap_assoc', flatMap_map']
  refine List.Perm.flatMap_left _ fun t₁ _ => ?_
  exact List.Perm.flatMap_left _ fun t₂ _ =>
    inner_reorder_permB t₁.1 t₁.2 t₂.1 t₂.2 (mkwTerms τ.children)

private theorem flatMap_split_perm {α β : Type*} (l : List α)
    (h f g : α → List β) (hfg : ∀ a ∈ l, (h a).Perm (f a ++ g a)) :
    (l.flatMap h).Perm (l.flatMap f ++ l.flatMap g) :=
  (List.Perm.flatMap_left l hfg).trans (List.flatMap_append_perm l f g).symm

private theorem swap_head_perm {α : Type*} (A B C : List α) :
    (A ++ (B ++ C)).Perm (B ++ (A ++ C)) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.Perm.append_right C List.perm_append_comm

private theorem shuffle_pair_concat_split_perm (s₁ s₂ u₁ u₂ : PlanarForest)
    (n₁ n₂ : PTree) :
    ((Word.shuffle s₁ s₂).flatMap fun p =>
        (Word.shuffle (u₁ ++ [n₁]) (u₂ ++ [n₂])).map fun r => (p, r)).Perm
      (((Word.shuffle s₁ s₂).flatMap fun p =>
          (Word.shuffle u₁ (u₂ ++ [n₂])).map fun r => (p, r ++ [n₁])) ++
        ((Word.shuffle s₁ s₂).flatMap fun p =>
          (Word.shuffle (u₁ ++ [n₁]) u₂).map fun r => (p, r ++ [n₂]))) := by
  refine flatMap_split_perm _ _ _ _ fun p _ => ?_
  refine ((Word.shuffle_concat_concat_perm n₁ n₂ u₁ u₂).map
    fun r => (p, r)).trans ?_
  exact perm_of_eq (by simp [Function.comp_def])

/-- Splitting the pairwise shuffle of two grafted term lists by which of the
two grafted branches ends up rightmost (arXiv:math/0603023, proof of
Theorem 2). -/
private theorem pairShuffle_graftTail_split_perm
    (xs ys : List (PlanarForest × PlanarForest)) (τ₁ τ₂ : PTree) :
    (pairShuffle (graftTail xs τ₁) (graftTail ys τ₂)).Perm
      ((xs.flatMap fun t₁ =>
          (mkwTerms τ₁.children).flatMap fun c₁ =>
            (Word.shuffle t₁.1 c₁.1).flatMap fun s₁ =>
              ys.flatMap fun t₂ =>
                (mkwTerms τ₂.children).flatMap fun c₂ =>
                  (Word.shuffle t₂.1 c₂.1).flatMap fun s₂ =>
                    (Word.shuffle s₁ s₂).flatMap fun p =>
                      (Word.shuffle t₁.2 (t₂.2 ++ [PTree.node c₂.2])).map
                        fun r => (p, r ++ [PTree.node c₁.2])) ++
        (xs.flatMap fun t₁ =>
          (mkwTerms τ₁.children).flatMap fun c₁ =>
            (Word.shuffle t₁.1 c₁.1).flatMap fun s₁ =>
              ys.flatMap fun t₂ =>
                (mkwTerms τ₂.children).flatMap fun c₂ =>
                  (Word.shuffle t₂.1 c₂.1).flatMap fun s₂ =>
                    (Word.shuffle s₁ s₂).flatMap fun p =>
                      (Word.shuffle (t₁.2 ++ [PTree.node c₁.2]) t₂.2).map
                        fun r => (p, r ++ [PTree.node c₂.2]))) := by
  simp only [pairShuffle, graftTail, flatMap_assoc', flatMap_map']
  refine flatMap_split_perm _ _ _ _ fun t₁ _ => ?_
  refine flatMap_split_perm _ _ _ _ fun c₁ _ => ?_
  refine flatMap_split_perm _ _ _ _ fun s₁ _ => ?_
  refine flatMap_split_perm _ _ _ _ fun t₂ _ => ?_
  refine flatMap_split_perm _ _ _ _ fun c₂ _ => ?_
  refine flatMap_split_perm _ _ _ _ fun s₂ _ => ?_
  exact shuffle_pair_concat_split_perm _ _ _ _ _ _

private theorem full_terms_perm (υ₁ υ₂ : PlanarForest) (τ₁ τ₂ : PTree) :
    (((Word.shuffle υ₁ (υ₂ ++ [τ₂])).map
        fun w => ((w ++ [τ₁] : PlanarForest), ([] : PlanarForest))) ++
      ((Word.shuffle (υ₁ ++ [τ₁]) υ₂).map
        fun w => ((w ++ [τ₂] : PlanarForest), ([] : PlanarForest)))).Perm
      ((Word.shuffle (υ₁ ++ [τ₁]) (υ₂ ++ [τ₂])).map
        fun w => (w, ([] : PlanarForest))) := by
  refine List.Perm.trans (perm_of_eq (by simp [Function.comp_def]))
    ((Word.shuffle_concat_concat_perm τ₁ τ₂ υ₁ υ₂).map
      fun w => (w, ([] : PlanarForest))).symm

private theorem shuffle_flatMap_mkwTerms_perm_aux (n : Nat) :
    ∀ ω₁ ω₂ : PlanarForest,
      PTree.orderList ω₁ + PTree.orderList ω₂ ≤ n →
      ((Word.shuffle ω₁ ω₂).flatMap mkwTerms).Perm
        (pairShuffle (mkwTerms ω₁) (mkwTerms ω₂)) := by
  induction n with
  | zero =>
      intro ω₁ ω₂ h
      have h₁ : ω₁ = [] := (PTree.orderList_eq_zero_iff ω₁).1 (by omega)
      subst h₁
      rw [Word.shuffle_nil_left, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, mkwTerms_nil, pairShuffle_unit_left]
  | succ n ih =>
      intro ω₁ ω₂ hle
      rcases List.eq_nil_or_concat ω₁ with rfl | ⟨υ₁, τ₁, hω₁⟩
      · rw [Word.shuffle_nil_left, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, mkwTerms_nil, pairShuffle_unit_left]
      rcases List.eq_nil_or_concat ω₂ with rfl | ⟨υ₂, τ₂, hω₂⟩
      · rw [Word.shuffle_nil_right, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, mkwTerms_nil, pairShuffle_unit_right]
      subst hω₁
      subst hω₂
      rw [List.concat_eq_append, List.concat_eq_append] at hle ⊢
      have hτ₁ := PTree.order_pos τ₁
      have hτ₂ := PTree.order_pos τ₂
      rw [PTree.orderList_append, PTree.orderList_append,
        PTree.orderList_cons, PTree.orderList_cons, PTree.orderList_nil]
        at hle
      -- the right-hand side, decomposed into its five sectors
      have hR :
          (pairShuffle (mkwTerms (υ₁ ++ [τ₁])) (mkwTerms (υ₂ ++ [τ₂]))).Perm
            (((((Word.shuffle υ₁ (υ₂ ++ [τ₂])).map
                fun w => ((w ++ [τ₁] : PlanarForest), ([] : PlanarForest))) ++
              ((Word.shuffle (υ₁ ++ [τ₁]) υ₂).map
                fun w => ((w ++ [τ₂] : PlanarForest), ([] : PlanarForest)))) ++
              ((mkwTerms υ₂).flatMap fun t₂ =>
                (mkwTerms τ₂.children).flatMap fun c₂ =>
                  (Word.shuffle t₂.1 c₂.1).flatMap fun s₂ =>
                    (Word.shuffle (υ₁ ++ [τ₁]) s₂).flatMap fun p =>
                      (Word.shuffle ([] : PlanarForest) t₂.2).map fun r =>
                        (p, r ++ [PTree.node c₂.2]))) ++
              (((mkwTerms υ₁).flatMap fun t₁ =>
                (mkwTerms τ₁.children).flatMap fun c₁ =>
                  (Word.shuffle t₁.1 c₁.1).flatMap fun s₁ =>
                    (Word.shuffle s₁ (υ₂ ++ [τ₂])).flatMap fun p =>
                      (Word.shuffle t₁.2 ([] : PlanarForest)).map fun r =>
                        (p, r ++ [PTree.node c₁.2])) ++
                (((mkwTerms υ₁).flatMap fun t₁ =>
                  (mkwTerms τ₁.children).flatMap fun c₁ =>
                    (Word.shuffle t₁.1 c₁.1).flatMap fun s₁ =>
                      (graftTail (mkwTerms υ₂) τ₂).flatMap fun t₂ =>
                        (Word.shuffle s₁ t₂.1).flatMap fun p =>
                          (Word.shuffle t₁.2 t₂.2).map fun r =>
                            (p, r ++ [PTree.node c₁.2])) ++
                  ((graftTail (mkwTerms υ₁) τ₁).flatMap fun d₁ =>
                    (mkwTerms υ₂).flatMap fun t₂ =>
                      (mkwTerms τ₂.children).flatMap fun c₂ =>
                        (Word.shuffle t₂.1 c₂.1).flatMap fun s₂ =>
                          (Word.shuffle d₁.1 s₂).flatMap fun p =>
                            (Word.shuffle d₁.2 t₂.2).map fun r =>
                              (p, r ++ [PTree.node c₂.2]))))) := by
        rw [mkwTerms_concat_graftTail υ₁ τ₁, mkwTerms_concat_graftTail υ₂ τ₂,
          pairShuffle_cons_left]
        refine List.Perm.append ?_ ?_
        · refine (perm_of_eq List.flatMap_cons).trans ?_
          refine List.Perm.append ?_ ?_
          · refine List.Perm.trans (perm_of_eq ?_)
              (full_terms_perm υ₁ υ₂ τ₁ τ₂).symm
            simp only [Word.shuffle_nil_left, List.map_cons, List.map_nil,
              ← map_eq_flatMap']
          · exact perm_of_eq (by
              simp only [graftTail, flatMap_assoc', flatMap_map',
                Word.shuffle_nil_left, List.map_cons, List.map_nil])
        · refine (pairShuffle_cons_right_perm _ _ _).trans ?_
          refine List.Perm.append ?_ ?_
          · exact perm_of_eq (by
              simp only [graftTail, flatMap_assoc', flatMap_map',
                Word.shuffle_nil_right, List.map_cons, List.map_nil])
          · refine (pairShuffle_graftTail_split_perm _ _ τ₁ τ₂).trans ?_
            refine List.Perm.append (perm_of_eq ?_) (perm_of_eq ?_)
            · exact (by
                simp only [graftTail, flatMap_assoc', flatMap_map'])
            · exact (by
                simp only [graftTail, flatMap_assoc', flatMap_map'])
      refine List.Perm.trans ?_ hR.symm
      -- the left-hand side: split the shuffles by their last letter
      refine (List.Perm.flatMap_right mkwTerms
        (Word.shuffle_concat_concat_perm τ₁ τ₂ υ₁ υ₂)).trans ?_
      rw [List.flatMap_append, flatMap_map', flatMap_map']
      simp only [mkwTerms_concat_graftTail]
      refine ((flatMap_cons_perm _ _ _).append (flatMap_cons_perm _ _ _)).trans
        ?_
      have hfold₁ :
          ((Word.shuffle υ₁ (υ₂ ++ [τ₂])).flatMap fun w =>
            graftTail (mkwTerms w) τ₁) =
          graftTail ((Word.shuffle υ₁ (υ₂ ++ [τ₂])).flatMap mkwTerms) τ₁ := by
        unfold graftTail
        rw [flatMap_assoc']
      have hfold₂ :
          ((Word.shuffle (υ₁ ++ [τ₁]) υ₂).flatMap fun w =>
            graftTail (mkwTerms w) τ₂) =
          graftTail ((Word.shuffle (υ₁ ++ [τ₁]) υ₂).flatMap mkwTerms) τ₂ := by
        unfold graftTail
        rw [flatMap_assoc']
      rw [hfold₁, hfold₂]
      have hIH₁ := graftTail_perm
        (ih υ₁ (υ₂ ++ [τ₂]) (by
          rw [PTree.orderList_append, PTree.orderList_cons,
            PTree.orderList_nil]
          omega)) τ₁
      have hIH₂ := graftTail_perm
        (ih (υ₁ ++ [τ₁]) υ₂ (by
          rw [PTree.orderList_append, PTree.orderList_cons,
            PTree.orderList_nil]
          omega)) τ₂
      refine (List.Perm.append (List.Perm.append_left _ hIH₁)
        (List.Perm.append_left _ hIH₂)).trans ?_
      refine (List.Perm.append
        (List.Perm.append_left _
          (graftTail_pairShuffle_canonicalA (mkwTerms υ₁)
            (mkwTerms (υ₂ ++ [τ₂])) τ₁))
        (List.Perm.append_left _
          (graftTail_pairShuffle_canonicalB (mkwTerms (υ₁ ++ [τ₁]))
            (mkwTerms υ₂) τ₂))).trans ?_
      -- split the canonical forms along the full cut of the other factor
      rw [mkwTerms_concat_graftTail υ₂ τ₂, mkwTerms_concat_graftTail υ₁ τ₁]
      refine (List.Perm.append
        (List.Perm.append_left _
          ((flatMap_split_perm _ _ _ _ fun t₁ _ =>
            flatMap_split_perm _ _ _ _ fun c₁ _ =>
              flatMap_split_perm _ _ _ _ fun s₁ _ =>
                perm_of_eq List.flatMap_cons)))
        (List.Perm.append_left _
          (perm_of_eq List.flatMap_cons))).trans ?_
      -- pure block rearrangement
      simp only [List.append_assoc]
      refine List.Perm.append_left _ ?_
      refine (List.Perm.append_left _ (swap_head_perm _ _ _)).trans ?_
      refine (swap_head_perm _ _ _).trans ?_
      refine List.Perm.append_left _ ?_
      refine (List.Perm.append_left _ (swap_head_perm _ _ _)).trans ?_
      exact swap_head_perm _ _ _

/--
The MKW bialgebra compatibility at the level of coproduct terms:
`Δ_N(ω₁ ⧢ ω₂) = Δ_N(ω₁) ⊔⊔ Δ_N(ω₂)` — the coproduct terms of all shuffles of
two ordered forests are, with multiplicity, the pairwise shuffles of the
coproduct terms of the factors (arXiv:math/0603023, Theorem 2).
-/
theorem shuffle_flatMap_mkwTerms_perm (ω₁ ω₂ : PlanarForest) :
    ((Word.shuffle ω₁ ω₂).flatMap mkwTerms).Perm
      (pairShuffle (mkwTerms ω₁) (mkwTerms ω₂)) :=
  shuffle_flatMap_mkwTerms_perm_aux
    (PTree.orderList ω₁ + PTree.orderList ω₂) ω₁ ω₂ le_rfl

/-! ### Coassociativity of the MKW coproduct -/

/-- The terms of the left iterated coproduct `(Δ_N ⊗ I)Δ_N`. -/
def mkwLeftTriples (ω : PlanarForest) :
    List (PlanarForest × PlanarForest × PlanarForest) :=
  (mkwTerms ω).flatMap fun pr =>
    (mkwTerms pr.1).map fun q => (q.1, q.2, pr.2)

/-- The terms of the right iterated coproduct `(I ⊗ Δ_N)Δ_N`. -/
def mkwRightTriples (ω : PlanarForest) :
    List (PlanarForest × PlanarForest × PlanarForest) :=
  (mkwTerms ω).flatMap fun pr =>
    (mkwTerms pr.2).map fun q => (pr.1, q.1, q.2)

/-- The triple analogue of the grafting product appearing in both iterated
coproducts of a forest `υ ++ [τ]`. -/
def tripleGraft (xs ys : List (PlanarForest × PlanarForest × PlanarForest)) :
    List (PlanarForest × PlanarForest × PlanarForest) :=
  xs.flatMap fun x => ys.flatMap fun y =>
    (Word.shuffle x.1 y.1).flatMap fun p =>
      (Word.shuffle x.2.1 y.2.1).map fun r =>
        (p, r, x.2.2 ++ [PTree.node y.2.2])

private theorem tripleGraft_perm
    {xs xs' ys ys' : List (PlanarForest × PlanarForest × PlanarForest)}
    (h1 : xs.Perm xs') (h2 : ys.Perm ys') :
    (tripleGraft xs ys).Perm (tripleGraft xs' ys') :=
  (List.Perm.flatMap_right _ h1).trans
    (List.Perm.flatMap_left _ fun _ _ => List.Perm.flatMap_right _ h2)

/-- Expansion of the left iterated coproduct tail via the bialgebra law. -/
private theorem tripleGraft_left_expand
    (xs ys : List (PlanarForest × PlanarForest)) :
    (xs.flatMap fun t => ys.flatMap fun c =>
        (Word.shuffle t.1 c.1).flatMap fun s =>
          (mkwTerms s).map fun q =>
            (q.1, q.2, t.2 ++ [PTree.node c.2])).Perm
      (tripleGraft
        (xs.flatMap fun t => (mkwTerms t.1).map fun q => (q.1, q.2, t.2))
        (ys.flatMap fun c => (mkwTerms c.1).map fun q => (q.1, q.2, c.2))) := by
  simp only [tripleGraft, flatMap_assoc', flatMap_map']
  refine List.Perm.flatMap_left _ fun t _ => ?_
  refine List.Perm.trans
    (l₂ := ys.flatMap fun c =>
      (mkwTerms t.1).flatMap fun a =>
        (mkwTerms c.1).flatMap fun b =>
          (Word.shuffle a.1 b.1).flatMap fun p =>
            (Word.shuffle a.2 b.2).map fun r =>
              (p, r, t.2 ++ [PTree.node c.2]))
    (List.Perm.flatMap_left _ fun c _ => ?_) ?_
  · rw [← map_flatMap']
    refine ((shuffle_flatMap_mkwTerms_perm t.1 c.1).map _).trans ?_
    exact perm_of_eq (by
      simp only [pairShuffle, List.map_map,
        map_flatMap', Function.comp_def])
  · exact Word.flatMap_comm_perm ys (mkwTerms t.1) fun c a =>
      (mkwTerms c.1).flatMap fun b =>
        (Word.shuffle a.1 b.1).flatMap fun p =>
          (Word.shuffle a.2 b.2).map fun r =>
            (p, r, t.2 ++ [PTree.node c.2])

/-- Reordering of the right iterated coproduct tail. -/
private theorem tripleGraft_right_expand
    (xs ys : List (PlanarForest × PlanarForest)) :
    (xs.flatMap fun t => ys.flatMap fun c =>
        (Word.shuffle t.1 c.1).flatMap fun s =>
          (mkwTerms t.2).flatMap fun u =>
            (mkwTerms c.2).flatMap fun v =>
              (Word.shuffle u.1 v.1).map fun w =>
                (s, w, u.2 ++ [PTree.node v.2])).Perm
      (tripleGraft
        (xs.flatMap fun t => (mkwTerms t.2).map fun q => (t.1, q.1, q.2))
        (ys.flatMap fun c => (mkwTerms c.2).map fun q => (c.1, q.1, q.2))) := by
  simp only [tripleGraft, flatMap_assoc', flatMap_map']
  refine List.Perm.flatMap_left _ fun t _ => ?_
  refine List.Perm.trans (List.Perm.flatMap_left _ fun c _ =>
    Word.flatMap_comm_perm (Word.shuffle t.1 c.1) (mkwTerms t.2) fun s u =>
      (mkwTerms c.2).flatMap fun v =>
        (Word.shuffle u.1 v.1).map fun w =>
          (s, w, u.2 ++ [PTree.node v.2])) ?_
  refine List.Perm.trans (List.Perm.flatMap_left _ fun c _ =>
    List.Perm.flatMap_left _ fun u _ =>
      Word.flatMap_comm_perm (Word.shuffle t.1 c.1) (mkwTerms c.2) fun s v =>
        (Word.shuffle u.1 v.1).map fun w =>
          (s, w, u.2 ++ [PTree.node v.2])) ?_
  exact Word.flatMap_comm_perm ys (mkwTerms t.2) fun c u =>
    (mkwTerms c.2).flatMap fun v =>
      (Word.shuffle t.1 c.1).flatMap fun s =>
        (Word.shuffle u.1 v.1).map fun w => (s, w, u.2 ++ [PTree.node v.2])

/--
Coassociativity of the MKW coproduct at the level of coproduct terms:
`(Δ_N ⊗ I)Δ_N` and `(I ⊗ Δ_N)Δ_N` produce the same triples of forests, with
multiplicity (arXiv:math/0603023, Theorem 2).
-/
theorem mkwLeftTriples_perm_mkwRightTriples (ω : PlanarForest) :
    (mkwLeftTriples ω).Perm (mkwRightTriples ω) := by
  induction ω using concatChildrenInduction with
  | nil =>
      exact perm_of_eq (by simp [mkwLeftTriples, mkwRightTriples])
  | concat υ τ ih₁ ih₂ =>
      simp only [mkwLeftTriples, mkwRightTriples] at *
      rw [mkwTerms_concat_graftTail υ τ]
      have hL : (((υ ++ [τ], ([] : PlanarForest)) ::
          graftTail (mkwTerms υ) τ).flatMap fun pr =>
            (mkwTerms pr.1).map fun q => (q.1, q.2, pr.2)) =
          ((mkwTerms (υ ++ [τ])).map fun q =>
            (q.1, q.2, ([] : PlanarForest))) ++
            ((graftTail (mkwTerms υ) τ).flatMap fun pr =>
              (mkwTerms pr.1).map fun q => (q.1, q.2, pr.2)) := by
        rw [List.flatMap_cons]
      have hR : (((υ ++ [τ], ([] : PlanarForest)) ::
          graftTail (mkwTerms υ) τ).flatMap fun pr =>
            (mkwTerms pr.2).map fun q => (pr.1, q.1, q.2)) =
          ((mkwTerms ([] : PlanarForest)).map fun q =>
            ((υ ++ [τ] : PlanarForest), q.1, q.2)) ++
            ((graftTail (mkwTerms υ) τ).flatMap fun pr =>
              (mkwTerms pr.2).map fun q => (pr.1, q.1, q.2)) := by
        rw [List.flatMap_cons]
      rw [hL, hR]
      -- decompose the right tail into the boundary terms and the double graft
      have hRtail : ((graftTail (mkwTerms υ) τ).flatMap fun pr =>
          (mkwTerms pr.2).map fun q => (pr.1, q.1, q.2)).Perm
          (((graftTail (mkwTerms υ) τ).map fun pr =>
            (pr.1, pr.2, ([] : PlanarForest))) ++
            ((mkwTerms υ).flatMap fun t =>
              (mkwTerms τ.children).flatMap fun c =>
                (Word.shuffle t.1 c.1).flatMap fun s =>
                  (mkwTerms t.2).flatMap fun u =>
                    (mkwTerms c.2).flatMap fun v =>
                      (Word.shuffle u.1 v.1).map fun w =>
                        (s, w, u.2 ++ [PTree.node v.2]))) := by
        have hexp : ((graftTail (mkwTerms υ) τ).flatMap fun pr =>
            (mkwTerms pr.2).map fun q => (pr.1, q.1, q.2)) =
            ((mkwTerms υ).flatMap fun t =>
              (mkwTerms τ.children).flatMap fun c =>
                (Word.shuffle t.1 c.1).flatMap fun s =>
                  ((s, t.2 ++ [PTree.node c.2], ([] : PlanarForest)) ::
                    ((mkwTerms t.2).flatMap fun pr₁ =>
                      (mkwTerms c.2).flatMap fun pr₂ =>
                        (Word.shuffle pr₁.1 pr₂.1).map fun w =>
                          (w, pr₁.2 ++ [PTree.node pr₂.2])).map fun q =>
                      (s, q.1, q.2))) := by
          simp only [graftTail, flatMap_assoc', flatMap_map',
            mkwTerms_concat_graftTail, List.map_cons, PTree.children_node]
        rw [hexp]
        have hsplit : ((mkwTerms υ).flatMap fun t =>
            (mkwTerms τ.children).flatMap fun c =>
              (Word.shuffle t.1 c.1).flatMap fun s =>
                ((s, t.2 ++ [PTree.node c.2], ([] : PlanarForest)) ::
                  ((mkwTerms t.2).flatMap fun pr₁ =>
                    (mkwTerms c.2).flatMap fun pr₂ =>
                      (Word.shuffle pr₁.1 pr₂.1).map fun w =>
                        (w, pr₁.2 ++ [PTree.node pr₂.2])).map fun q =>
                    (s, q.1, q.2))).Perm
            (((mkwTerms υ).flatMap fun t =>
              (mkwTerms τ.children).flatMap fun c =>
                (Word.shuffle t.1 c.1).flatMap fun s =>
                  [(s, t.2 ++ [PTree.node c.2], ([] : PlanarForest))]) ++
              ((mkwTerms υ).flatMap fun t =>
                (mkwTerms τ.children).flatMap fun c =>
                  (Word.shuffle t.1 c.1).flatMap fun s =>
                    ((mkwTerms t.2).flatMap fun pr₁ =>
                      (mkwTerms c.2).flatMap fun pr₂ =>
                        (Word.shuffle pr₁.1 pr₂.1).map fun w =>
                          (w, pr₁.2 ++ [PTree.node pr₂.2])).map fun q =>
                      (s, q.1, q.2))) :=
          flatMap_split_perm _ _ _ _ fun t _ =>
            flatMap_split_perm _ _ _ _ fun c _ =>
              flatMap_split_perm _ _ _ _ fun s _ => perm_of_eq rfl
        refine hsplit.trans (List.Perm.append (perm_of_eq ?_) (perm_of_eq ?_))
        · simp only [graftTail, flatMap_assoc',
            map_eq_flatMap', List.flatMap_cons, List.flatMap_nil,
            List.append_nil]
        · simp only [map_flatMap',
            List.map_map, Function.comp_def]
      refine List.Perm.trans ?_ (List.Perm.append_left _ hRtail).symm
      refine List.Perm.trans (List.Perm.append ?head ?tail)
        (perm_of_eq (List.append_assoc _ _ _))
      case head =>
        exact perm_of_eq (by
          simp only [mkwTerms_concat_graftTail, mkwTerms_nil, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append])
      case tail =>
        have hexpL : ((graftTail (mkwTerms υ) τ).flatMap fun pr =>
            (mkwTerms pr.1).map fun q => (q.1, q.2, pr.2)) =
            ((mkwTerms υ).flatMap fun t =>
              (mkwTerms τ.children).flatMap fun c =>
                (Word.shuffle t.1 c.1).flatMap fun s =>
                  (mkwTerms s).map fun q =>
                    (q.1, q.2, t.2 ++ [PTree.node c.2])) := by
          simp only [graftTail, flatMap_assoc', flatMap_map']
        rw [hexpL]
        refine (tripleGraft_left_expand (mkwTerms υ)
          (mkwTerms τ.children)).trans ?_
        refine (tripleGraft_perm ih₁ ih₂).trans ?_
        exact (tripleGraft_right_expand (mkwTerms υ)
          (mkwTerms τ.children)).symm

end PlanarForest

end HopfAlgebras
