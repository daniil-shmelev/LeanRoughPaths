/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Trees.Rooted

/-!
# Labelled Rooted Trees

This file defines rooted trees whose vertices carry labels. As with
`HopfAlgebras.Trees.Rooted`, the planar type is primary and the non-planar type is the
quotient by recursively permuting children.

## Main definitions

* `PLTree α` - non-empty planar rooted trees labelled by `α`
* `PLTree.Perm` - equivalence relation forgetting planar child order
* `LRootedTree α` - non-empty non-planar labelled rooted trees
* `LRootedTree.rootLabel` - the label at the root
* `PLTree.erase` and `LRootedTree.erase` - forget labels
* `PLTree.treeFactorial` and `LRootedTree.treeFactorial` - Butcher tree factorials
-/

namespace HopfAlgebras

universe u v w x

/-- Non-empty planar rooted trees with one label at each vertex. -/
inductive PLTree (α : Type u) : Type u where
  | node : α → List (PLTree α) → PLTree α
deriving Repr

namespace PLTree

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Forget labels from a planar labelled rooted tree. -/
def erase : PLTree α → PTree
  | .node _ ts => .node (ts.map erase)

/-- Label every vertex of a planar rooted tree by the same label. -/
def constLabel (a : α) : PTree → PLTree α
  | .node ts => .node a (ts.map (constLabel a))

/-- The label at the root of a planar labelled rooted tree. -/
def rootLabel : PLTree α → α
  | .node a _ => a

mutual

/-- The number of vertices of a planar labelled rooted tree. -/
def order : PLTree α → Nat
  | .node _ ts => 1 + orderList ts

/-- The sum of the orders of a list of planar labelled rooted trees. -/
def orderList : List (PLTree α) → Nat
  | [] => 0
  | t :: ts => order t + orderList ts

end

/-- Change all labels in a planar labelled rooted tree. -/
def map (f : α → β) : PLTree α → PLTree β
  | .node a ts => .node (f a) (ts.map (map f))

/-- Butcher's tree factorial, ignoring labels. -/
def treeFactorial (t : PLTree α) : Nat :=
  PTree.treeFactorial (erase t)

/-- Product of tree factorials over a list of labelled planar rooted trees. -/
def treeFactorialList (ts : List (PLTree α)) : Nat :=
  (ts.map treeFactorial).prod

/-- Two labelled planar trees are equivalent if labels agree and children are permuted recursively. -/
inductive Perm : PLTree α → PLTree α → Prop where
  | node {a : α} {ts us ts' : List (PLTree α)} :
      ts.Perm ts' →
      List.Forall₂ Perm ts' us →
      Perm (.node a ts) (.node a us)

@[simp]
theorem erase_node (a : α) (ts : List (PLTree α)) :
    erase (.node a ts) = .node (ts.map erase) := by
  simp [erase]

@[simp]
theorem constLabel_node (a : α) (ts : List PTree) :
    constLabel a (.node ts) = .node a (ts.map (constLabel a)) := by
  simp [constLabel]

mutual

@[simp]
theorem erase_constLabel (a : α) : ∀ t : PTree, erase (constLabel a t) = t
  | .node ts => by
      simp [eraseList_constLabel a ts]

@[simp]
theorem eraseList_constLabel (a : α) :
    ∀ ts : List PTree, (ts.map (constLabel a)).map erase = ts
  | [] => rfl
  | t :: ts => by
      simp [erase_constLabel a t, eraseList_constLabel a ts]

end

@[simp]
theorem rootLabel_node (a : α) (ts : List (PLTree α)) :
    rootLabel (.node a ts) = a :=
  rfl

@[simp]
theorem rootLabel_constLabel (a : α) : ∀ t : PTree, rootLabel (constLabel a t) = a
  | .node ts => by simp [rootLabel]

@[simp]
theorem order_node (a : α) (ts : List (PLTree α)) :
    order (.node a ts) = 1 + orderList ts :=
  rfl

@[simp]
theorem orderList_nil : orderList ([] : List (PLTree α)) = 0 :=
  rfl

@[simp]
theorem orderList_cons (t : PLTree α) (ts : List (PLTree α)) :
    orderList (t :: ts) = order t + orderList ts :=
  rfl

@[simp]
theorem map_node (f : α → β) (a : α) (ts : List (PLTree α)) :
    map f (.node a ts) = .node (f a) (ts.map (map f)) := by
  simp [map]

@[simp]
theorem rootLabel_map (f : α → β) (t : PLTree α) :
    rootLabel (map f t) = f (rootLabel t) := by
  cases t
  simp [rootLabel]

mutual

@[simp]
theorem map_constLabel (f : α → β) (a : α) :
    ∀ t : PTree, map f (constLabel a t) = constLabel (f a) t
  | .node ts => by
      simp [mapList_constLabel f a ts]

@[simp]
theorem mapList_constLabel (f : α → β) (a : α) :
    ∀ ts : List PTree, (ts.map (constLabel a)).map (map f) =
      ts.map (constLabel (f a))
  | [] => rfl
  | t :: ts => by
      simp [map_constLabel f a t, mapList_constLabel f a ts]

end

@[simp]
theorem treeFactorialList_nil : treeFactorialList ([] : List (PLTree α)) = 1 :=
  rfl

@[simp]
theorem treeFactorialList_cons (t : PLTree α) (ts : List (PLTree α)) :
    treeFactorialList (t :: ts) = treeFactorial t * treeFactorialList ts :=
  rfl

theorem treeFactorialList_erase :
    ∀ ts : List (PLTree α), PTree.treeFactorialList (ts.map erase) = treeFactorialList ts
  | [] => rfl
  | t :: ts => by
      simp [treeFactorial, treeFactorialList_erase ts]

theorem treeFactorial_pos (t : PLTree α) : 0 < treeFactorial t := by
  simp [treeFactorial, PTree.treeFactorial_pos]

theorem treeFactorial_ne_zero (t : PLTree α) : treeFactorial t ≠ 0 :=
  Nat.ne_of_gt (treeFactorial_pos t)

theorem treeFactorialList_pos : ∀ ts : List (PLTree α), 0 < treeFactorialList ts
  | [] => by simp [treeFactorialList]
  | t :: ts => by
      rw [treeFactorialList_cons]
      exact Nat.mul_pos (treeFactorial_pos t) (treeFactorialList_pos ts)

theorem treeFactorialList_ne_zero (ts : List (PLTree α)) : treeFactorialList ts ≠ 0 :=
  Nat.ne_of_gt (treeFactorialList_pos ts)

@[simp]
theorem treeFactorialList_append (ts us : List (PLTree α)) :
    treeFactorialList (ts ++ us) = treeFactorialList ts * treeFactorialList us := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp [ih, Nat.mul_assoc]

@[simp]
theorem orderList_append (ts us : List (PLTree α)) :
    orderList (ts ++ us) = orderList ts + orderList us := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp [ih, Nat.add_assoc]

theorem order_pos : ∀ t : PLTree α, 0 < order t
  | .node _ _ => by
      simp only [order]
      omega

mutual

@[simp]
theorem order_erase : ∀ t : PLTree α, PTree.order (erase t) = order t
  | .node _ ts => by
      simp [order, orderList_erase ts]

@[simp]
theorem orderList_erase :
    ∀ ts : List (PLTree α), PTree.orderList (ts.map erase) = orderList ts
  | [] => rfl
  | t :: ts => by
      simp [order_erase t, orderList_erase ts]

end

@[simp]
theorem treeFactorial_node (a : α) (ts : List (PLTree α)) :
    treeFactorial (.node a ts) = order (.node a ts) * treeFactorialList ts := by
  simp [treeFactorial, treeFactorialList_erase ts, orderList_erase ts]

mutual

@[simp]
theorem order_map (f : α → β) :
    ∀ t : PLTree α, order (map f t) = order t
  | .node _ ts => by
      simp [order, orderList_map f ts]

@[simp]
theorem orderList_map (f : α → β) :
    ∀ ts : List (PLTree α), orderList (ts.map (map f)) = orderList ts
  | [] => rfl
  | t :: ts => by
      simp [order_map f t, orderList_map f ts]

end

mutual

@[simp]
theorem erase_map (f : α → β) :
    ∀ t : PLTree α, erase (map f t) = erase t
  | .node _ ts => by
      simp [eraseList_map f ts]

@[simp]
theorem eraseList_map (f : α → β) :
    ∀ ts : List (PLTree α), (ts.map (map f)).map erase = ts.map erase
  | [] => rfl
  | t :: ts => by
      simp [erase_map f t, eraseList_map f ts]

end

/-- Attach an ordered labelled forest as the first children of the root. -/
def butcherProduct (ts : List (PLTree α)) : PLTree α → PLTree α
  | .node a us => .node a (ts ++ us)

@[simp]
theorem butcherProduct_node (ts us : List (PLTree α)) (a : α) :
    butcherProduct ts (.node a us) = .node a (ts ++ us) :=
  rfl

@[simp]
theorem rootLabel_butcherProduct (ts : List (PLTree α)) (t : PLTree α) :
    rootLabel (butcherProduct ts t) = rootLabel t := by
  cases t
  rfl

@[simp]
theorem butcherProduct_nil (t : PLTree α) : butcherProduct [] t = t := by
  cases t
  simp [butcherProduct]

@[simp]
theorem butcherProduct_assoc (ts us : List (PLTree α)) (t : PLTree α) :
    butcherProduct ts (butcherProduct us t) = butcherProduct (ts ++ us) t := by
  cases t
  simp [butcherProduct, List.append_assoc]

@[simp]
theorem order_butcherProduct (ts : List (PLTree α)) (t : PLTree α) :
    order (butcherProduct ts t) = orderList ts + order t := by
  cases t with
  | node _ us =>
      simp [butcherProduct, order]
      omega

@[simp]
theorem erase_butcherProduct (ts : List (PLTree α)) (t : PLTree α) :
    erase (butcherProduct ts t) = PTree.butcherProduct (ts.map erase) (erase t) := by
  cases t with
  | node _ us =>
      simp [butcherProduct, PTree.butcherProduct, List.map_append]

@[simp]
theorem map_butcherProduct (f : α → β) (ts : List (PLTree α)) (t : PLTree α) :
    map f (butcherProduct ts t) = butcherProduct (ts.map (map f)) (map f t) := by
  cases t with
  | node _ us =>
      simp [butcherProduct, List.map_append]

@[simp]
theorem butcherProduct_constLabel (a : α) (ts : List PTree) (t : PTree) :
    butcherProduct (ts.map (constLabel a)) (constLabel a t) =
      constLabel a (PTree.butcherProduct ts t) := by
  cases t with
  | node us =>
      simp [butcherProduct, PTree.butcherProduct, List.map_append]

theorem treeFactorial_butcherProduct (ts us : List (PLTree α)) (a : α) :
    treeFactorial (butcherProduct ts (.node a us)) =
      (orderList ts + order (.node a us)) *
        (treeFactorialList ts * treeFactorialList us) := by
  rw [butcherProduct_node]
  simp only [treeFactorial, erase_node, List.map_append, PTree.treeFactorial_node,
    PTree.order_node, order_node]
  rw [PTree.orderList_append, PTree.treeFactorialList_append, orderList_erase ts,
    orderList_erase us, treeFactorialList_erase ts, treeFactorialList_erase us]
  have horder : 1 + (orderList ts + orderList us) = orderList ts + (1 + orderList us) := by
    omega
  rw [horder]

mutual

@[simp]
theorem map_id : ∀ t : PLTree α, map id t = t
  | .node a ts => by
      simp [mapList_id ts]

@[simp]
theorem mapList_id : ∀ ts : List (PLTree α), ts.map (map id) = ts
  | [] => rfl
  | t :: ts => by
      simp [map_id t, mapList_id ts]

end

mutual

@[simp]
theorem map_comp (g : β → γ) (f : α → β) :
    ∀ t : PLTree α, map g (map f t) = map (g ∘ f) t
  | .node a ts => by
      simp [mapList_comp g f ts]

@[simp]
theorem mapList_comp (g : β → γ) (f : α → β) :
    ∀ ts : List (PLTree α), (ts.map (map f)).map (map g) = ts.map (map (g ∘ f))
  | [] => rfl
  | t :: ts => by
      simp [map_comp g f t, mapList_comp g f ts]

end

theorem map_injective (f : α → β) (hf : Function.Injective f) :
    Function.Injective (map f : PLTree α → PLTree β) := by
  intro t u h
  cases t with
  | node a ts =>
      letI : Nonempty α := ⟨a⟩
      have hleft : Function.LeftInverse (Function.invFun f) f :=
        Function.leftInverse_invFun hf
      have hcomp : Function.invFun f ∘ f = id := by
        funext x
        exact hleft x
      calc
        PLTree.node a ts = map id (PLTree.node a ts) := (map_id _).symm
        _ = map (Function.invFun f ∘ f) (PLTree.node a ts) := by rw [hcomp]
        _ = map (Function.invFun f) (map f (PLTree.node a ts)) :=
          (map_comp (Function.invFun f) f _).symm
        _ = map (Function.invFun f) (map f u) :=
          congrArg (map (Function.invFun f)) h
        _ = map (Function.invFun f ∘ f) u := map_comp (Function.invFun f) f u
        _ = map id u := by rw [hcomp]
        _ = u := map_id u

theorem map_eq_map_iff_of_injective (f : α → β) (hf : Function.Injective f)
    {t u : PLTree α} :
    map f t = map f u ↔ t = u := by
  constructor
  · intro h
    exact map_injective f hf h
  · intro h
    rw [h]

@[simp]
theorem treeFactorial_map (f : α → β) (t : PLTree α) :
    treeFactorial (map f t) = treeFactorial t := by
  simp [treeFactorial]

theorem erase_order_eq_order (t : PLTree α) : PTree.order (erase t) = order t :=
  order_erase t

theorem orderList_perm {ts us : List (PLTree α)} (h : ts.Perm us) :
    orderList ts = orderList us := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [Nat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem eraseList_perm {ts us : List (PLTree α)} (h : ts.Perm us) :
    (ts.map erase).Perm (us.map erase) :=
  h.map erase

private lemma forall₂_perm_right {γ : Type w} {δ : Type x} {R : γ → δ → Prop}
    {l₂ l₃ : List δ} (hp : l₂.Perm l₃) :
    ∀ {l₁ : List γ}, List.Forall₂ R l₁ l₂ →
      ∃ l₁', l₁.Perm l₁' ∧ List.Forall₂ R l₁' l₃ := by
  induction hp with
  | nil =>
      intro l₁ hf
      cases hf
      exact ⟨[], .nil, .nil⟩
  | cons _ _ ih =>
      intro l₁ hf
      cases hf with
      | cons ha hf =>
          obtain ⟨l₁', hp', hf'⟩ := ih hf
          exact ⟨_ :: l₁', .cons _ hp', .cons ha hf'⟩
  | swap _ _ _ =>
      intro l₁ hf
      cases hf with
      | cons ha hf =>
          cases hf with
          | cons hb hf =>
              exact ⟨_ :: _ :: _, .swap _ _ _, .cons hb (.cons ha hf)⟩
  | trans _ _ ih₁ ih₂ =>
      intro l₁ hf
      obtain ⟨l₁', hp', hf'⟩ := ih₁ hf
      obtain ⟨l₁'', hp'', hf''⟩ := ih₂ hf'
      exact ⟨l₁'', hp'.trans hp'', hf''⟩

mutual

/-- `PLTree.Perm` is reflexive. -/
theorem Perm.refl : ∀ t : PLTree α, Perm t t
  | .node _ ts => .node (List.Perm.refl ts) (permForall₂_refl ts)

/-- Elementwise reflexivity for `PLTree.Perm`. -/
theorem permForall₂_refl :
    ∀ ts : List (PLTree α), List.Forall₂ Perm ts ts
  | [] => .nil
  | t :: ts => .cons (Perm.refl t) (permForall₂_refl ts)

end

mutual

/-- Elementwise symmetry for `PLTree.Perm`. -/
theorem permForall₂_symm :
    ∀ {ts us : List (PLTree α)},
      List.Forall₂ Perm ts us → List.Forall₂ Perm us ts
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (Perm.symm h) (permForall₂_symm hs)

/-- `PLTree.Perm` is symmetric. -/
theorem Perm.symm : ∀ {t u : PLTree α}, Perm t u → Perm u t
  | _, _, .node hp hf => by
      obtain ⟨us', hp', hf'⟩ :=
        forall₂_perm_right (R := Perm) hp.symm (permForall₂_symm hf)
      exact .node hp' hf'

end

mutual

/-- Elementwise transitivity for `PLTree.Perm`. -/
theorem permForall₂_trans :
    ∀ {ts us vs : List (PLTree α)},
      List.Forall₂ Perm ts us →
      List.Forall₂ Perm us vs →
      List.Forall₂ Perm ts vs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons htu hts, .cons huv hus =>
      .cons (Perm.trans htu huv) (permForall₂_trans hts hus)

/-- `PLTree.Perm` is transitive. -/
theorem Perm.trans : ∀ {t u v : PLTree α}, Perm t u → Perm u v → Perm t v
  | _, _, _, .node hp₁ hf₁, .node hp₂ hf₂ => by
      obtain ⟨ts, hp, hf⟩ := forall₂_perm_right (R := Perm) hp₂ hf₁
      exact .node (hp₁.trans hp) (permForall₂_trans hf hf₂)

end

mutual

theorem Perm.order_eq : ∀ {t u : PLTree α}, Perm t u → order t = order u
  | _, _, .node hp hf => by
      simp [orderList_perm hp, orderList_eq_of_forall₂ hf]

theorem orderList_eq_of_forall₂ :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ Perm ts us → orderList ts = orderList us
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [Perm.order_eq h, orderList_eq_of_forall₂ hs]

end

theorem Perm.rootLabel_eq : ∀ {t u : PLTree α}, Perm t u → rootLabel t = rootLabel u
  | _, _, .node _ _ => rfl

mutual

theorem Perm.erase_perm : ∀ {t u : PLTree α}, Perm t u → PTree.Perm (erase t) (erase u)
  | _, _, .node hp hf => by
      simpa [erase] using PTree.Perm.node (eraseList_perm hp) (erase_forall₂_perm hf)

theorem erase_forall₂_perm :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ Perm ts us →
      List.Forall₂ PTree.Perm (ts.map erase) (us.map erase)
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (Perm.erase_perm h) (erase_forall₂_perm hs)

end

theorem Perm.treeFactorial_eq {t u : PLTree α} (h : Perm t u) :
    treeFactorial t = treeFactorial u := by
  simp [treeFactorial, PTree.Perm.treeFactorial_eq (Perm.erase_perm h)]

mutual

theorem Perm.map (f : α → β) : ∀ {t u : PLTree α}, Perm t u → Perm (map f t) (map f u)
  | _, _, .node hp hf => by
      simpa [map] using .node (hp.map (map f)) (map_forall₂ f hf)

theorem map_forall₂ (f : α → β) :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ Perm ts us →
      List.Forall₂ Perm (ts.map (map f)) (us.map (map f))
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (Perm.map f h) (map_forall₂ f hs)

end

mutual

theorem constLabel_perm (a : α) :
    ∀ {t u : PTree}, PTree.Perm t u → Perm (constLabel a t) (constLabel a u)
  | _, _, .node hp hf => by
      simpa [constLabel] using .node (hp.map (constLabel a)) (constLabel_forall₂ a hf)

theorem constLabel_forall₂ (a : α) :
    ∀ {ts us : List PTree}, List.Forall₂ PTree.Perm ts us →
      List.Forall₂ Perm (ts.map (constLabel a)) (us.map (constLabel a))
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (constLabel_perm a h) (constLabel_forall₂ a hs)

end

instance : Setoid (PLTree α) where
  r := Perm
  iseqv := ⟨Perm.refl, Perm.symm, Perm.trans⟩

end PLTree

/-- Non-empty non-planar labelled rooted trees. -/
abbrev LRootedTree (α : Type u) : Type u :=
  Quotient (inferInstance : Setoid (PLTree α))

namespace LRootedTree

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The quotient map from planar labelled trees to non-planar labelled trees. -/
def ofPLTree (t : PLTree α) : LRootedTree α :=
  Quotient.mk _ t

theorem ofPLTree_eq_iff {t u : PLTree α} :
    ofPLTree t = ofPLTree u ↔ PLTree.Perm t u := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- The number of vertices of a non-planar labelled rooted tree. -/
def order : LRootedTree α → Nat :=
  Quotient.lift PLTree.order (fun _ _ h => PLTree.Perm.order_eq h)

/-- The label at the root of a non-planar labelled rooted tree. -/
def rootLabel : LRootedTree α → α :=
  Quotient.lift PLTree.rootLabel (fun _ _ h => PLTree.Perm.rootLabel_eq h)

/-- Forget labels from a non-planar labelled rooted tree. -/
def erase : LRootedTree α → RootedTree :=
  Quotient.lift
    (fun t : PLTree α => RootedTree.ofPTree (PLTree.erase t))
    (fun _ _ h => RootedTree.ofPTree_eq_iff.2 (PLTree.Perm.erase_perm h))

/-- Label every vertex of a rooted tree by the same label. -/
def constLabel (a : α) : RootedTree → LRootedTree α :=
  Quotient.lift
    (fun t : PTree => ofPLTree (PLTree.constLabel a t))
    (fun _ _ h => ofPLTree_eq_iff.2 (PLTree.constLabel_perm a h))

/-- Change all labels in a non-planar labelled rooted tree. -/
def map (f : α → β) : LRootedTree α → LRootedTree β :=
  Quotient.lift
    (fun t : PLTree α => ofPLTree (PLTree.map f t))
    (fun _ _ h => ofPLTree_eq_iff.2 (PLTree.Perm.map f h))

/-- Butcher's tree factorial for non-planar labelled rooted trees. -/
def treeFactorial : LRootedTree α → Nat :=
  Quotient.lift PLTree.treeFactorial (fun _ _ h => PLTree.Perm.treeFactorial_eq h)

@[simp]
theorem order_ofPLTree (t : PLTree α) : order (ofPLTree t) = PLTree.order t :=
  rfl

@[simp]
theorem rootLabel_ofPLTree (t : PLTree α) :
    rootLabel (ofPLTree t) = PLTree.rootLabel t :=
  rfl

@[simp]
theorem erase_ofPLTree (t : PLTree α) :
    erase (ofPLTree t) = RootedTree.ofPTree (PLTree.erase t) :=
  rfl

theorem erase_out_perm (τ : LRootedTree α) :
    PTree.Perm (PLTree.erase (Quotient.out τ)) (Quotient.out (erase τ)) := by
  exact Quotient.exact <| by
    calc
      RootedTree.ofPTree (PLTree.erase (Quotient.out τ))
          = erase (ofPLTree (Quotient.out τ)) := rfl
      _ = erase τ := congrArg erase (Quotient.out_eq τ)
      _ = RootedTree.ofPTree (Quotient.out (erase τ)) := (Quotient.out_eq (erase τ)).symm

@[simp]
theorem constLabel_ofPTree (a : α) (t : PTree) :
    constLabel a (RootedTree.ofPTree t) = ofPLTree (PLTree.constLabel a t) :=
  rfl

@[simp]
theorem rootLabel_constLabel (a : α) (t : RootedTree) :
    rootLabel (constLabel a t) = a := by
  refine Quotient.inductionOn t ?_
  intro t
  exact PLTree.rootLabel_constLabel a t

@[simp]
theorem map_ofPLTree (f : α → β) (t : PLTree α) :
    map f (ofPLTree t) = ofPLTree (PLTree.map f t) :=
  rfl

@[simp]
theorem treeFactorial_ofPLTree (t : PLTree α) :
    treeFactorial (ofPLTree t) = PLTree.treeFactorial t :=
  rfl

@[simp]
theorem ofPLTree_out (τ : LRootedTree α) : ofPLTree (Quotient.out τ) = τ :=
  Quotient.out_eq τ

theorem out_perm_ofPLTree (t : PLTree α) :
    PLTree.Perm (Quotient.out (ofPLTree t)) t :=
  Quotient.exact (ofPLTree_out (ofPLTree t))

theorem map_out_perm (f : α → β) (τ : LRootedTree α) :
    PLTree.Perm (PLTree.map f (Quotient.out τ)) (Quotient.out (map f τ)) := by
  exact Quotient.exact <| by
    calc
      LRootedTree.ofPLTree (PLTree.map f (Quotient.out τ))
          = map f (ofPLTree (Quotient.out τ)) := rfl
      _ = map f τ := congrArg (map f) (Quotient.out_eq τ)
      _ = ofPLTree (Quotient.out (map f τ)) := (Quotient.out_eq (map f τ)).symm

theorem constLabel_out_perm (a : α) (τ : RootedTree) :
    PLTree.Perm (PLTree.constLabel a (Quotient.out τ)) (Quotient.out (constLabel a τ)) := by
  exact Quotient.exact <| by
    calc
      LRootedTree.ofPLTree (PLTree.constLabel a (Quotient.out τ))
          = constLabel a (RootedTree.ofPTree (Quotient.out τ)) := rfl
      _ = constLabel a τ := congrArg (constLabel a) (Quotient.out_eq τ)
      _ = ofPLTree (Quotient.out (constLabel a τ)) :=
          (Quotient.out_eq (constLabel a τ)).symm

theorem map_ofPLTree_eq_of_forall₂_perm :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ PLTree.Perm ts us →
      ts.map ofPLTree = us.map ofPLTree
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [
        show ofPLTree _ = ofPLTree _ from ofPLTree_eq_iff.2 h,
        map_ofPLTree_eq_of_forall₂_perm hs
      ]

@[simp]
theorem rootLabel_map (f : α → β) (t : LRootedTree α) :
    rootLabel (map f t) = f (rootLabel t) := by
  refine Quotient.inductionOn t ?_
  intro t
  exact PLTree.rootLabel_map f t

@[simp]
theorem map_constLabel (f : α → β) (a : α) (t : RootedTree) :
    map f (constLabel a t) = constLabel (f a) t := by
  refine Quotient.inductionOn t ?_
  intro t
  exact congrArg ofPLTree (PLTree.map_constLabel f a t)

@[simp]
theorem erase_constLabel (a : α) (t : RootedTree) :
    erase (constLabel a t) = t := by
  refine Quotient.inductionOn t ?_
  intro t
  exact congrArg RootedTree.ofPTree (PLTree.erase_constLabel a t)

theorem constLabel_injective (a : α) : Function.Injective (constLabel a) := by
  intro s t h
  have hErase := congrArg erase h
  simpa using hErase

@[simp]
theorem constLabel_eq_constLabel_iff (a : α) {s t : RootedTree} :
    constLabel a s = constLabel a t ↔ s = t := by
  constructor
  · intro h
    exact constLabel_injective a h
  · intro h
    rw [h]

@[simp]
theorem order_erase (t : LRootedTree α) :
    RootedTree.order (erase t) = order t := by
  refine Quotient.inductionOn t ?_
  intro t
  simp [erase, order, PLTree.order_erase]

@[simp]
theorem order_map (f : α → β) (t : LRootedTree α) :
    order (map f t) = order t := by
  refine Quotient.inductionOn t ?_
  intro t
  change PLTree.order (PLTree.map f t) = PLTree.order t
  exact PLTree.order_map f t

@[simp]
theorem erase_map (f : α → β) (t : LRootedTree α) :
    erase (map f t) = erase t := by
  refine Quotient.inductionOn t ?_
  intro t
  exact congrArg RootedTree.ofPTree (PLTree.erase_map f t)

@[simp]
theorem treeFactorial_erase (t : LRootedTree α) :
    RootedTree.treeFactorial (erase t) = treeFactorial t := by
  refine Quotient.inductionOn t ?_
  intro t
  rfl

@[simp]
theorem order_constLabel (a : α) (t : RootedTree) :
    order (constLabel a t) = RootedTree.order t := by
  have h := order_erase (constLabel a t)
  rw [erase_constLabel] at h
  exact h.symm

@[simp]
theorem treeFactorial_constLabel (a : α) (t : RootedTree) :
    treeFactorial (constLabel a t) = RootedTree.treeFactorial t := by
  have h := treeFactorial_erase (constLabel a t)
  rw [erase_constLabel] at h
  exact h.symm

@[simp]
theorem treeFactorial_map (f : α → β) (t : LRootedTree α) :
    treeFactorial (map f t) = treeFactorial t := by
  refine Quotient.inductionOn t ?_
  intro t
  exact PLTree.treeFactorial_map f t

theorem treeFactorial_pos (t : LRootedTree α) : 0 < treeFactorial t := by
  have h := RootedTree.treeFactorial_pos (erase t)
  rwa [treeFactorial_erase] at h

theorem treeFactorial_ne_zero (t : LRootedTree α) : treeFactorial t ≠ 0 :=
  Nat.ne_of_gt (treeFactorial_pos t)

@[simp]
theorem map_id (t : LRootedTree α) : map id t = t := by
  refine Quotient.inductionOn t ?_
  intro t
  exact congrArg ofPLTree (PLTree.map_id t)

@[simp]
theorem map_comp (g : β → γ) (f : α → β) (t : LRootedTree α) :
    map g (map f t) = map (g ∘ f) t := by
  refine Quotient.inductionOn t ?_
  intro t
  exact congrArg ofPLTree (PLTree.map_comp g f t)

theorem map_injective (f : α → β) (hf : Function.Injective f) :
    Function.Injective (map f : LRootedTree α → LRootedTree β) := by
  intro s t h
  refine Quotient.inductionOn₂ s t ?_ h
  intro s t hst
  cases s with
  | node a ts =>
      letI : Nonempty α := ⟨a⟩
      have hleft : Function.LeftInverse (Function.invFun f) f :=
        Function.leftInverse_invFun hf
      have hcomp : Function.invFun f ∘ f = id := by
        funext x
        exact hleft x
      calc
        ofPLTree (PLTree.node a ts) = map id (ofPLTree (PLTree.node a ts)) :=
          (map_id _).symm
        _ = map (Function.invFun f ∘ f) (ofPLTree (PLTree.node a ts)) := by rw [hcomp]
        _ = map (Function.invFun f) (map f (ofPLTree (PLTree.node a ts))) :=
          (map_comp (Function.invFun f) f _).symm
        _ = map (Function.invFun f) (map f (ofPLTree t)) :=
          congrArg (map (Function.invFun f)) hst
        _ = map (Function.invFun f ∘ f) (ofPLTree t) := map_comp (Function.invFun f) f _
        _ = map id (ofPLTree t) := by rw [hcomp]
        _ = ofPLTree t := map_id _

theorem map_eq_map_iff_of_injective (f : α → β) (hf : Function.Injective f)
    {s t : LRootedTree α} :
    map f s = map f t ↔ s = t := by
  constructor
  · intro h
    exact map_injective f hf h
  · intro h
    rw [h]

theorem order_pos (t : LRootedTree α) : 0 < order t := by
  refine Quotient.inductionOn t ?_
  intro t
  change 0 < PLTree.order t
  exact PLTree.order_pos t

end LRootedTree

end HopfAlgebras
