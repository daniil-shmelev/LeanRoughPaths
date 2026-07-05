/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Forests.Labelled

/-!
# Planar Rooted Trees and Forests

This file gives explicit names and basic APIs for planar rooted trees and
ordered forests. The underlying tree types are the existing `PTree` and
`PLTree`; the forest types are lists, so sibling order is retained.

## Main definitions

* `PlanarTree` and `PlanarForest`
* `LPlanarTree` and `LPlanarForest`
* conversion maps to the non-planar quotients
-/

namespace HopfAlgebras

universe u v w

/-- Non-empty planar rooted trees. -/
abbrev PlanarTree : Type :=
  PTree

/-- Ordered forests of non-empty planar rooted trees. -/
abbrev PlanarForest : Type :=
  List PlanarTree

/-- Non-empty labelled planar rooted trees. -/
abbrev LPlanarTree (α : Type u) : Type u :=
  PLTree α

/-- Ordered forests of labelled planar rooted trees. -/
abbrev LPlanarForest (α : Type u) : Type u :=
  List (LPlanarTree α)

namespace PlanarTree

/-- Build a planar tree from its ordered list of children. -/
def node (ts : PlanarForest) : PlanarTree :=
  PTree.node ts

/-- The one-vertex planar rooted tree. -/
def bullet : PlanarTree :=
  PTree.bullet

/-- A two-vertex planar rooted tree. -/
def chain2 : PlanarTree :=
  PTree.chain2

/-- A three-vertex planar chain. -/
def chain3 : PlanarTree :=
  PTree.chain3

/-- A root with two bullet children. -/
def cherry : PlanarTree :=
  PTree.cherry

/-- The number of vertices of a planar rooted tree. -/
def order (t : PlanarTree) : Nat :=
  PTree.order t

/-- Butcher's tree factorial. -/
def treeFactorial (t : PlanarTree) : Nat :=
  PTree.treeFactorial t

/-- Attach an ordered forest as the first children of the root. -/
def butcherProduct (ts : PlanarForest) (t : PlanarTree) : PlanarTree :=
  PTree.butcherProduct ts t

/-- Forget the planar embedding by quotienting sibling order. -/
def toRootedTree (t : PlanarTree) : RootedTree :=
  RootedTree.ofPTree t

@[simp]
theorem node_eq (ts : PlanarForest) : node ts = PTree.node ts :=
  rfl

@[simp]
theorem order_node (ts : PlanarForest) :
    order (node ts) = 1 + PTree.orderList ts :=
  rfl

@[simp]
theorem order_bullet : order bullet = 1 :=
  rfl

@[simp]
theorem order_chain2 : order chain2 = 2 :=
  rfl

@[simp]
theorem order_chain3 : order chain3 = 3 :=
  rfl

@[simp]
theorem order_cherry : order cherry = 3 :=
  rfl

theorem order_pos (t : PlanarTree) : 0 < order t :=
  PTree.order_pos t

@[simp]
theorem treeFactorial_node (ts : PlanarForest) :
    treeFactorial (node ts) = order (node ts) * PTree.treeFactorialList ts :=
  rfl

@[simp]
theorem treeFactorial_bullet : treeFactorial bullet = 1 :=
  rfl

@[simp]
theorem treeFactorial_chain2 : treeFactorial chain2 = 2 :=
  rfl

@[simp]
theorem treeFactorial_chain3 : treeFactorial chain3 = 6 :=
  rfl

@[simp]
theorem treeFactorial_cherry : treeFactorial cherry = 3 :=
  rfl

theorem treeFactorial_pos (t : PlanarTree) : 0 < treeFactorial t :=
  PTree.treeFactorial_pos t

theorem treeFactorial_ne_zero (t : PlanarTree) : treeFactorial t ≠ 0 :=
  PTree.treeFactorial_ne_zero t

@[simp]
theorem butcherProduct_nil (t : PlanarTree) :
    butcherProduct [] t = t :=
  PTree.butcherProduct_nil t

@[simp]
theorem order_butcherProduct (ts : PlanarForest) (t : PlanarTree) :
    order (butcherProduct ts t) = PTree.orderList ts + order t :=
  PTree.order_butcherProduct ts t

@[simp]
theorem butcherProduct_assoc (ts us : PlanarForest) (t : PlanarTree) :
    butcherProduct ts (butcherProduct us t) = butcherProduct (ts ++ us) t :=
  PTree.butcherProduct_assoc ts us t

@[simp]
theorem order_toRootedTree (t : PlanarTree) :
    RootedTree.order (toRootedTree t) = order t :=
  rfl

@[simp]
theorem treeFactorial_toRootedTree (t : PlanarTree) :
    RootedTree.treeFactorial (toRootedTree t) = treeFactorial t :=
  rfl

theorem toRootedTree_eq_iff {t u : PlanarTree} :
    toRootedTree t = toRootedTree u ↔ PTree.Perm t u :=
  RootedTree.ofPTree_eq_iff

end PlanarTree

namespace PlanarForest

/-- The empty ordered planar forest. -/
def empty : PlanarForest :=
  []

/-- The ordered forest with one tree. -/
def singleton (t : PlanarTree) : PlanarForest :=
  [t]

/-- Concatenate ordered forests. -/
def append (ts us : PlanarForest) : PlanarForest :=
  ts ++ us

/-- The sum of the orders of all trees in an ordered forest. -/
def order (ts : PlanarForest) : Nat :=
  PTree.orderList ts

/-- Product of tree factorials over an ordered forest. -/
def treeFactorial (ts : PlanarForest) : Nat :=
  PTree.treeFactorialList ts

/-- Graft an ordered forest onto one new root. -/
def graft (ts : PlanarForest) : PlanarTree :=
  PlanarTree.node ts

/-- Forget order by mapping each planar tree to its non-planar quotient. -/
def toRootedForest (ts : PlanarForest) : RootedForest :=
  ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest)

@[simp]
theorem empty_eq : empty = ([] : PlanarForest) :=
  rfl

@[simp]
theorem singleton_eq (t : PlanarTree) : singleton t = [t] :=
  rfl

@[simp]
theorem append_eq (ts us : PlanarForest) : append ts us = ts ++ us :=
  rfl

@[simp]
theorem order_empty : order empty = 0 :=
  rfl

@[simp]
theorem order_nil : order ([] : PlanarForest) = 0 :=
  rfl

@[simp]
theorem order_cons (t : PlanarTree) (ts : PlanarForest) :
    order (t :: ts) = PlanarTree.order t + order ts :=
  rfl

@[simp]
theorem order_singleton (t : PlanarTree) :
    order (singleton t) = PlanarTree.order t := by
  simp [singleton, order, PlanarTree.order]

@[simp]
theorem order_append (ts us : PlanarForest) :
    order (append ts us) = order ts + order us := by
  exact PTree.orderList_append ts us

theorem order_eq_zero_iff (ts : PlanarForest) :
    order ts = 0 ↔ ts = [] :=
  PTree.orderList_eq_zero_iff ts

@[simp]
theorem treeFactorial_empty : treeFactorial empty = 1 :=
  rfl

@[simp]
theorem treeFactorial_nil : treeFactorial ([] : PlanarForest) = 1 :=
  rfl

@[simp]
theorem treeFactorial_cons (t : PlanarTree) (ts : PlanarForest) :
    treeFactorial (t :: ts) = PlanarTree.treeFactorial t * treeFactorial ts :=
  rfl

@[simp]
theorem treeFactorial_singleton (t : PlanarTree) :
    treeFactorial (singleton t) = PlanarTree.treeFactorial t := by
  simp [singleton, treeFactorial, PlanarTree.treeFactorial]

@[simp]
theorem treeFactorial_append (ts us : PlanarForest) :
    treeFactorial (append ts us) = treeFactorial ts * treeFactorial us := by
  exact PTree.treeFactorialList_append ts us

theorem treeFactorial_pos (ts : PlanarForest) : 0 < treeFactorial ts :=
  PTree.treeFactorialList_pos ts

theorem treeFactorial_ne_zero (ts : PlanarForest) : treeFactorial ts ≠ 0 :=
  PTree.treeFactorialList_ne_zero ts

@[simp]
theorem order_graft (ts : PlanarForest) :
    PlanarTree.order (graft ts) = 1 + order ts :=
  rfl

@[simp]
theorem treeFactorial_graft (ts : PlanarForest) :
    PlanarTree.treeFactorial (graft ts) = (1 + order ts) * treeFactorial ts :=
  rfl

@[simp]
theorem order_toRootedForest (ts : PlanarForest) :
    RootedForest.order (toRootedForest ts) = order ts :=
  RootedForest.order_ofPTree_list ts

@[simp]
theorem treeFactorial_toRootedForest (ts : PlanarForest) :
    RootedForest.treeFactorial (toRootedForest ts) = treeFactorial ts :=
  RootedForest.treeFactorial_ofPTree_list ts

theorem graft_toRootedForest (ts : PlanarForest) :
    RootedForest.graft (toRootedForest ts) = PlanarTree.toRootedTree (graft ts) :=
  RootedForest.graft_ofPTree_list ts

end PlanarForest

namespace LPlanarTree

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Build a labelled planar tree from a root label and ordered children. -/
def node (a : α) (ts : LPlanarForest α) : LPlanarTree α :=
  PLTree.node a ts

/-- Forget labels from a labelled planar tree. -/
def erase (t : LPlanarTree α) : PlanarTree :=
  PLTree.erase t

/-- Label every vertex of a planar tree by the same label. -/
def constLabel (a : α) (t : PlanarTree) : LPlanarTree α :=
  PLTree.constLabel a t

/-- The label at the root. -/
def rootLabel (t : LPlanarTree α) : α :=
  PLTree.rootLabel t

/-- Change every label in a labelled planar tree. -/
def map (f : α → β) (t : LPlanarTree α) : LPlanarTree β :=
  PLTree.map f t

/-- The number of vertices. -/
def order (t : LPlanarTree α) : Nat :=
  PLTree.order t

/-- Butcher's tree factorial, ignoring labels. -/
def treeFactorial (t : LPlanarTree α) : Nat :=
  PLTree.treeFactorial t

/-- Attach an ordered labelled forest as the first children of the root. -/
def butcherProduct (ts : LPlanarForest α) (t : LPlanarTree α) : LPlanarTree α :=
  PLTree.butcherProduct ts t

/-- Forget planar order by quotienting recursively by sibling permutations. -/
def toRootedTree (t : LPlanarTree α) : LRootedTree α :=
  LRootedTree.ofPLTree t

@[simp]
theorem node_eq (a : α) (ts : LPlanarForest α) : node a ts = PLTree.node a ts :=
  rfl

@[simp]
theorem erase_node (a : α) (ts : LPlanarForest α) :
    erase (node a ts) = PlanarTree.node (List.map erase ts) := by
  simp [erase, node, PlanarTree.node]

@[simp]
theorem rootLabel_node (a : α) (ts : LPlanarForest α) :
    rootLabel (node a ts) = a :=
  rfl

@[simp]
theorem order_node (a : α) (ts : LPlanarForest α) :
    order (node a ts) = 1 + PLTree.orderList ts :=
  rfl

@[simp]
theorem map_node (f : α → β) (a : α) (ts : LPlanarForest α) :
    map f (node a ts) = node (f a) (List.map (map f) ts) := by
  simp [map, node]

@[simp]
theorem map_id (t : LPlanarTree α) : map (fun a : α => a) t = t := by
  change PLTree.map (fun a : α => a) t = t
  exact PLTree.map_id t

@[simp]
theorem map_comp (g : β → γ) (f : α → β) (t : LPlanarTree α) :
    map g (map f t) = map (g ∘ f) t := by
  change PLTree.map g (PLTree.map f t) = PLTree.map (g ∘ f) t
  exact PLTree.map_comp g f t

@[simp]
theorem map_constLabel (f : α → β) (a : α) (t : PlanarTree) :
    map f (constLabel a t) = constLabel (f a) t := by
  change PLTree.map f (PLTree.constLabel a t) = PLTree.constLabel (f a) t
  exact PLTree.map_constLabel f a t

@[simp]
theorem erase_constLabel (a : α) (t : PlanarTree) :
    erase (constLabel a t) = t :=
  PLTree.erase_constLabel a t

@[simp]
theorem rootLabel_constLabel (a : α) (t : PlanarTree) :
    rootLabel (constLabel a t) = a :=
  PLTree.rootLabel_constLabel a t

@[simp]
theorem order_erase (t : LPlanarTree α) :
    PlanarTree.order (erase t) = order t :=
  PLTree.order_erase t

@[simp]
theorem order_map (f : α → β) (t : LPlanarTree α) :
    order (map f t) = order t :=
  PLTree.order_map f t

@[simp]
theorem erase_map (f : α → β) (t : LPlanarTree α) :
    erase (map f t) = erase t :=
  PLTree.erase_map f t

@[simp]
theorem treeFactorial_erase (t : LPlanarTree α) :
    PlanarTree.treeFactorial (erase t) = treeFactorial t :=
  rfl

@[simp]
theorem order_toRootedTree (t : LPlanarTree α) :
    LRootedTree.order (toRootedTree t) = order t :=
  rfl

@[simp]
theorem treeFactorial_toRootedTree (t : LPlanarTree α) :
    LRootedTree.treeFactorial (toRootedTree t) = treeFactorial t :=
  rfl

@[simp]
theorem erase_toRootedTree (t : LPlanarTree α) :
    LRootedTree.erase (toRootedTree t) = PlanarTree.toRootedTree (erase t) :=
  rfl

theorem toRootedTree_eq_iff {t u : LPlanarTree α} :
    toRootedTree t = toRootedTree u ↔ PLTree.Perm t u :=
  LRootedTree.ofPLTree_eq_iff

end LPlanarTree

namespace LPlanarForest

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The empty ordered labelled planar forest. -/
def empty : LPlanarForest α :=
  []

/-- The ordered labelled forest with one tree. -/
def singleton (t : LPlanarTree α) : LPlanarForest α :=
  [t]

/-- Concatenate ordered labelled forests. -/
def append (ts us : LPlanarForest α) : LPlanarForest α :=
  ts ++ us

/-- Forget all labels. -/
def erase (ts : LPlanarForest α) : PlanarForest :=
  List.map LPlanarTree.erase ts

/-- Label every vertex of every tree by the same label. -/
def constLabel (a : α) (ts : PlanarForest) : LPlanarForest α :=
  List.map (LPlanarTree.constLabel a) ts

/-- Change every label in an ordered forest. -/
def map (f : α → β) (ts : LPlanarForest α) : LPlanarForest β :=
  List.map (LPlanarTree.map f) ts

@[simp]
theorem map_nil (f : α → β) : map f ([] : LPlanarForest α) = [] :=
  rfl

@[simp]
theorem map_append (f : α → β) (ts us : LPlanarForest α) :
    map f (ts ++ us) = map f ts ++ map f us := by
  simp [map, List.map_append]

@[simp]
theorem map_id (ts : LPlanarForest α) : map (fun a : α => a) ts = ts := by
  induction ts with
  | nil =>
      rfl
  | cons t ts ih =>
      change LPlanarTree.map (fun a : α => a) t :: map (fun a : α => a) ts = t :: ts
      rw [LPlanarTree.map_id, ih]

@[simp]
theorem map_comp (g : β → γ) (f : α → β) (ts : LPlanarForest α) :
    map g (map f ts) = map (g ∘ f) ts := by
  simp [map, List.map_map, Function.comp_def]

@[simp]
theorem map_constLabel (f : α → β) (a : α) (ts : PlanarForest) :
    map f (constLabel a ts) = constLabel (f a) ts := by
  simp [map, constLabel, List.map_map, Function.comp_def]

/-- The sum of the orders of all trees in an ordered labelled forest. -/
def order (ts : LPlanarForest α) : Nat :=
  PLTree.orderList ts

/-- Product of tree factorials over an ordered labelled forest. -/
def treeFactorial (ts : LPlanarForest α) : Nat :=
  PLTree.treeFactorialList ts

/-- Graft an ordered labelled forest onto one new labelled root. -/
def graft (a : α) (ts : LPlanarForest α) : LPlanarTree α :=
  LPlanarTree.node a ts

/-- Forget planar order by quotienting all trees recursively. -/
def toRootedForest (ts : LPlanarForest α) : LRootedForest α :=
  ((List.map LRootedTree.ofPLTree ts : List (LRootedTree α)) : LRootedForest α)

@[simp]
theorem erase_empty : erase (empty : LPlanarForest α) = PlanarForest.empty :=
  rfl

@[simp]
theorem erase_cons (t : LPlanarTree α) (ts : LPlanarForest α) :
    erase (t :: ts) = LPlanarTree.erase t :: erase ts :=
  rfl

@[simp]
theorem erase_append (ts us : LPlanarForest α) :
    erase (append ts us) = PlanarForest.append (erase ts) (erase us) := by
  simp [erase, append, PlanarForest.append, List.map_append]

@[simp]
theorem erase_constLabel (a : α) (ts : PlanarForest) :
    erase (constLabel a ts) = ts :=
  PLTree.eraseList_constLabel a ts

@[simp]
theorem erase_map (f : α → β) (ts : LPlanarForest α) :
    erase (map f ts) = erase ts :=
  PLTree.eraseList_map f ts

@[simp]
theorem order_empty : order (empty : LPlanarForest α) = 0 :=
  rfl

@[simp]
theorem order_nil : order ([] : LPlanarForest α) = 0 :=
  rfl

@[simp]
theorem order_cons (t : LPlanarTree α) (ts : LPlanarForest α) :
    order (t :: ts) = LPlanarTree.order t + order ts :=
  rfl

@[simp]
theorem order_append (ts us : LPlanarForest α) :
    order (append ts us) = order ts + order us := by
  exact PLTree.orderList_append ts us

@[simp]
theorem order_erase (ts : LPlanarForest α) :
    PlanarForest.order (erase ts) = order ts :=
  PLTree.orderList_erase ts

@[simp]
theorem order_map (f : α → β) (ts : LPlanarForest α) :
    order (map f ts) = order ts :=
  PLTree.orderList_map f ts

@[simp]
theorem order_constLabel (a : α) (ts : PlanarForest) :
    order (constLabel a ts) = PlanarForest.order ts := by
  rw [← order_erase (constLabel a ts), erase_constLabel]

@[simp]
theorem treeFactorial_empty : treeFactorial (empty : LPlanarForest α) = 1 :=
  rfl

@[simp]
theorem treeFactorial_nil : treeFactorial ([] : LPlanarForest α) = 1 :=
  rfl

@[simp]
theorem treeFactorial_cons (t : LPlanarTree α) (ts : LPlanarForest α) :
    treeFactorial (t :: ts) = LPlanarTree.treeFactorial t * treeFactorial ts :=
  rfl

@[simp]
theorem treeFactorial_append (ts us : LPlanarForest α) :
    treeFactorial (append ts us) = treeFactorial ts * treeFactorial us := by
  exact PLTree.treeFactorialList_append ts us

@[simp]
theorem treeFactorial_erase (ts : LPlanarForest α) :
    PlanarForest.treeFactorial (erase ts) = treeFactorial ts :=
  PLTree.treeFactorialList_erase ts

@[simp]
theorem treeFactorial_constLabel (a : α) (ts : PlanarForest) :
    treeFactorial (constLabel a ts) = PlanarForest.treeFactorial ts := by
  rw [← treeFactorial_erase (constLabel a ts), erase_constLabel]

@[simp]
theorem order_graft (a : α) (ts : LPlanarForest α) :
    LPlanarTree.order (graft a ts) = 1 + order ts :=
  rfl

@[simp]
theorem erase_graft (a : α) (ts : LPlanarForest α) :
    LPlanarTree.erase (graft a ts) = PlanarForest.graft (erase ts) :=
  LPlanarTree.erase_node a ts

@[simp]
theorem rootLabel_graft (a : α) (ts : LPlanarForest α) :
    LPlanarTree.rootLabel (graft a ts) = a :=
  rfl

@[simp]
theorem order_toRootedForest (ts : LPlanarForest α) :
    LRootedForest.order (toRootedForest ts) = order ts :=
  LRootedForest.order_ofPLTree_list ts

@[simp]
theorem treeFactorial_toRootedForest (ts : LPlanarForest α) :
    LRootedForest.treeFactorial (toRootedForest ts) = treeFactorial ts :=
  LRootedForest.treeFactorial_ofPLTree_list ts

@[simp]
theorem erase_toRootedForest (ts : LPlanarForest α) :
    LRootedForest.erase (toRootedForest ts) =
      PlanarForest.toRootedForest (erase ts) := by
  have h :
      List.map LRootedTree.erase (List.map LRootedTree.ofPLTree ts) =
        List.map RootedTree.ofPTree (List.map LPlanarTree.erase ts) := by
    simp [List.map_map, Function.comp_def, LPlanarTree.erase]
  simpa [toRootedForest, erase, PlanarForest.toRootedForest, LRootedForest.erase]
    using congrArg (fun xs : List RootedTree => (xs : RootedForest)) h

end LPlanarForest

end HopfAlgebras
