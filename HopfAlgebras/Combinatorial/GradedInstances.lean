/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Combinatorial.Graded
import HopfAlgebras.Combinatorial.Shuffle
import HopfAlgebras.Combinatorial.BCK
import HopfAlgebras.Combinatorial.LBCK
import HopfAlgebras.Combinatorial.MKW

/-!
# Gradings of the concrete combinatorial bialgebras

The word shuffle Hopf algebra is graded by word length, and the BCK,
labelled BCK and MKW forest bialgebras by forest order. Via
`CombBialg.Grading.characterGroup` the characters of all four form
groups under convolution — in particular the tree bialgebras, which
have no terms-level antipode, acquire their character groups here.

The only new combinatorial input is `mkwTermsAux_order`: MKW coproduct
terms split the forest order, proved by the same well-founded recursion
as `mkwTermsAux` itself.
-/

namespace HopfAlgebras

universe u v

/-! ### The word shuffle Hopf algebra, graded by word length -/

/-- Word length grades the word shuffle Hopf algebra. -/
def wordGrading (α : Type u) : (wordHopf α).toCombBialg.Grading where
  deg := List.length
  deg_eq_zero_iff x := by
    show x.length = 0 ↔ x = ([] : List α)
    exact List.length_eq_zero_iff
  deg_coprod x p hp := by
    have h := Word.mem_splits_append hp
    calc p.1.length + p.2.length = (p.1 ++ p.2).length :=
          (List.length_append).symm
      _ = x.length := by rw [h]
  deg_mul x y z hz := Word.length_of_mem_shuffle hz

/-! ### The BCK bialgebras, graded by forest order -/

/-- Forest order grades the BCK bialgebra. -/
def bckGrading : bckBialg.Grading where
  deg := RootedForest.order
  deg_eq_zero_iff := RootedForest.order_eq_zero_iff
  deg_coprod _ _ hp := RootedForest.coproductTerms_order hp
  deg_mul x y z hz := by
    have h : z = x + y := List.mem_singleton.mp hz
    rw [h]
    exact RootedForest.order_add x y

/-- Forest order grades the labelled BCK bialgebra. -/
def lbckGrading (α : Type u) : (lbckBialg α).Grading where
  deg := LRootedForest.order
  deg_eq_zero_iff := LRootedForest.order_eq_zero_iff
  deg_coprod _ _ hp := LRootedForest.coproductTerms_order hp
  deg_mul x y z hz := by
    have h : z = x + y := List.mem_singleton.mp hz
    rw [h]
    exact LRootedForest.order_add x y

/-! ### The MKW bialgebra, graded by planar forest order -/

/-- MKW coproduct terms split the planar forest order — by the same
well-founded recursion as `mkwTermsAux`. -/
theorem mkwTermsAux_order :
    ∀ l : List PTree, ∀ pr ∈ PlanarForest.mkwTermsAux l,
      PlanarForest.order pr.1 + PlanarForest.order pr.2 =
        PTree.orderList l
  | [], pr, hpr => by
      simp only [PlanarForest.mkwTermsAux, List.mem_singleton] at hpr
      rw [hpr]
      rfl
  | t :: rev, pr, hpr => by
      simp only [PlanarForest.mkwTermsAux, List.mem_cons] at hpr
      rcases hpr with h | h
      · rw [h]
        show PTree.orderList (t :: rev).reverse + PTree.orderList [] =
          PTree.orderList (t :: rev)
        rw [PTree.orderList_reverse]
        rfl
      · obtain ⟨pr₁, h1, h⟩ := List.mem_flatMap.mp h
        obtain ⟨pr₂, h2, h⟩ := List.mem_flatMap.mp h
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
        have ih1 : PTree.orderList pr₁.1 + PTree.orderList pr₁.2 =
            PTree.orderList rev := mkwTermsAux_order rev pr₁ h1
        have ih2' : PTree.orderList pr₂.1 + PTree.orderList pr₂.2 =
            PTree.orderList t.children.reverse :=
          mkwTermsAux_order t.children.reverse pr₂ h2
        rw [PTree.orderList_reverse] at ih2'
        have hsord : PTree.orderList s =
            PTree.orderList pr₁.1 + PTree.orderList pr₂.1 := by
          rw [PTree.orderList_perm (Word.perm_append_of_mem_shuffle hs)]
          exact PTree.orderList_append _ _
        have htail : PTree.orderList (pr₁.2 ++ [PTree.node pr₂.2]) =
            PTree.orderList pr₁.2 + (1 + PTree.orderList pr₂.2) := by
          rw [PTree.orderList_append,
            show PTree.orderList [PTree.node pr₂.2] =
              PTree.order (PTree.node pr₂.2) + 0 from rfl,
            PTree.order_eq_one_add_orderList_children (PTree.node pr₂.2),
            show (PTree.node pr₂.2).children = pr₂.2 from rfl]
          omega
        have ht := PTree.order_eq_one_add_orderList_children t
        show PTree.orderList s +
          PTree.orderList (pr₁.2 ++ [PTree.node pr₂.2]) =
          PTree.orderList (t :: rev)
        rw [hsord, htail, PTree.orderList_cons]
        omega
  termination_by l => PTree.orderList l
  decreasing_by
    all_goals
      have hpos := PTree.order_pos t
      have ht := PTree.order_eq_one_add_orderList_children t
      simp only [PTree.orderList_reverse, PTree.orderList_cons]
      omega

/-- MKW coproduct terms split the forest order. -/
theorem mkwTerms_order {ω : PlanarForest}
    {pr : PlanarForest × PlanarForest}
    (hpr : pr ∈ PlanarForest.mkwTerms ω) :
    PlanarForest.order pr.1 + PlanarForest.order pr.2 =
      PlanarForest.order ω := by
  have h := mkwTermsAux_order ω.reverse pr hpr
  rwa [PTree.orderList_reverse] at h

/-- Planar forest order grades the MKW bialgebra. -/
def mkwGrading : mkwBialg.Grading where
  deg := PlanarForest.order
  deg_eq_zero_iff := PlanarForest.order_eq_zero_iff
  deg_coprod _ _ hp := mkwTerms_order hp
  deg_mul x y z hz := by
    show PTree.orderList z = _
    rw [PTree.orderList_perm (Word.perm_append_of_mem_shuffle hz)]
    exact PTree.orderList_append x y

/-! ### Character groups of the tree bialgebras

The word shuffle Hopf algebra already carries the antipode group
(`CombBialg.Character.instGroup`); the graded construction now supplies
groups for the tree bialgebras, which have no terms-level antipode. -/

variable (R : Type v) [CommRing R]

/-- **The BCK character group**: branched rough path increments are
invertible under character convolution. -/
@[reducible] noncomputable def bckCharacterGroup : Group (bckBialg.Character R) :=
  bckGrading.characterGroup

/-- **The labelled BCK character group.** -/
@[reducible] noncomputable def lbckCharacterGroup (α : Type u) :
    Group ((lbckBialg α).Character R) :=
  (lbckGrading α).characterGroup

/-- **The MKW character group**: planarly branched rough path
increments are invertible under Grossman–Larson convolution. -/
@[reducible] noncomputable def mkwCharacterGroup : Group (mkwBialg.Character R) :=
  mkwGrading.characterGroup

end HopfAlgebras
