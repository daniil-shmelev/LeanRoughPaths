/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Algebra.PlanarForest
import HopfAlgebras.Words.Shuffle

/-!
# The Munthe-Kaas-Wright Coproduct

This file defines the coproduct of the Munthe-Kaas-Wright Hopf algebra of
ordered forests of planar rooted trees, following the recursion of
Munthe-Kaas & Wright, *On the Hopf algebraic structure of Lie group
integrators* (Found. Comput. Math. 8, 2008; arXiv:math/0603023), Definition 3:

  `Δ_N(𝟙) = 𝟙 ⊗ 𝟙`,
  `Δ_N(ω τ) = ω τ ⊗ 𝟙 + Δ_N(ω) ⊔·(I ⊗ B⁺)Δ_N(B⁻(τ))`,

where `τ` is the last tree of the forest and `⊔·` shuffles the left tensor
factors and concatenates the right tensor factors. The terms of the coproduct
enumerate the full admissible left cuts of the ordered forest.

## Main definitions

* `PlanarForest.mkwTerms` - the list of coproduct terms, with multiplicity
* `PlanarTensorAlgebra` - tensor-coded ordered forest algebra
* `PlanarForest.mkwCoproduct` - the MKW coproduct
* `PlanarForest.counitLeft_mkwCoproduct` and
  `PlanarForest.counitRight_mkwCoproduct` - the counit laws
* `PlanarForest.orderList_fst_add_snd_of_mem_mkwTerms` - the order grading

The small-order values are verified against the coproduct table of the paper;
in particular `Δ_N(•χ)` reproduces the illustrative example of Section 2 with
its multiplicity `2` term, and the cherry shows the left-admissibility
constraint (the right branch alone is never pruned, unlike in the
Butcher-Connes-Kreimer coproduct).
-/

namespace HopfAlgebras

open HopfAlgebras

universe u v

namespace PlanarForest

private theorem map_flatMap' {α β γ : Type*} (l : List α) (f : α → List β)
    (g : β → γ) :
    (l.flatMap f).map g = l.flatMap fun a => (f a).map g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem sum_flatMap' {α : Type u} {M : Type v} [AddCommMonoid M]
    (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem smul_sum' {R : Type u} {M : Type v} [Semiring R]
    [AddCommMonoid M] [Module R M] (r : R) (l : List M) :
    r • l.sum = (l.map fun x => r • x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [smul_add, ih]

/--
MKW coproduct terms of the ordered forest whose reversed tree list is the
input. The recursion peels the last tree `τ = B⁺(τ.children)` of the forest,
following arXiv:math/0603023, Definition 3.
-/
def mkwTermsAux : List PTree → List (PlanarForest × PlanarForest)
  | [] => [([], [])]
  | t :: rev =>
      ((t :: rev).reverse, []) ::
        (mkwTermsAux rev).flatMap fun pr₁ =>
          (mkwTermsAux t.children.reverse).flatMap fun pr₂ =>
            (Word.shuffle pr₁.1 pr₂.1).map fun s =>
              (s, pr₁.2 ++ [PTree.node pr₂.2])
termination_by ts => PTree.orderList ts
decreasing_by
  all_goals
    have hpos := PTree.order_pos t
    have ht := PTree.order_eq_one_add_orderList_children t
    simp only [PTree.orderList_reverse, PTree.orderList_cons]
    omega

/--
The list of MKW coproduct terms of an ordered forest, with multiplicity. Each
term is a pair `(pruned, remaining)` corresponding to one full admissible left
cut of the forest.
-/
def mkwTerms (ω : PlanarForest) : List (PlanarForest × PlanarForest) :=
  mkwTermsAux ω.reverse

@[simp]
theorem mkwTerms_nil : mkwTerms ([] : PlanarForest) = [([], [])] := by
  simp [mkwTerms, mkwTermsAux]

/-- The defining recursion of the MKW coproduct terms, peeling the last tree. -/
theorem mkwTerms_concat (ω : PlanarForest) (t : PTree) :
    mkwTerms (ω ++ [t]) =
      (ω ++ [t], ([] : PlanarForest)) ::
        (mkwTerms ω).flatMap fun pr₁ =>
          (mkwTerms t.children).flatMap fun pr₂ =>
            (Word.shuffle pr₁.1 pr₂.1).map fun s =>
              (s, pr₁.2 ++ [PTree.node pr₂.2]) := by
  have h : (ω ++ [t]).reverse = t :: ω.reverse := by simp
  rw [mkwTerms, h]
  rw [show mkwTerms ω = mkwTermsAux ω.reverse from rfl,
    show mkwTerms t.children = mkwTermsAux t.children.reverse from rfl]
  simp only [mkwTermsAux]
  congr 1
  simp

/--
Induction along the MKW recursion: the empty forest, and appending one tree
whose children forest satisfies the motive.
-/
@[elab_as_elim]
theorem concatChildrenInduction {motive : PlanarForest → Prop} (ω : PlanarForest)
    (nil : motive [])
    (concat : ∀ (ω : PlanarForest) (t : PTree),
      motive ω → motive t.children → motive (ω ++ [t])) :
    motive ω := by
  have key : ∀ (n : Nat) (υ : PlanarForest), PTree.orderList υ ≤ n → motive υ := by
    intro n
    induction n with
    | zero =>
        intro υ h
        have hυ : υ = [] := (PTree.orderList_eq_zero_iff υ).1 (Nat.le_zero.1 h)
        exact hυ ▸ nil
    | succ n ih =>
        intro υ h
        rcases List.eq_nil_or_concat υ with rfl | ⟨υ', t, hυ⟩
        · exact nil
        · subst hυ
          rw [List.concat_eq_append] at h ⊢
          rw [PTree.orderList_append, PTree.orderList_cons, PTree.orderList_nil] at h
          have ht := PTree.order_eq_one_add_orderList_children t
          have hpos := PTree.order_pos t
          exact concat υ' t (ih υ' (by omega)) (ih t.children (by omega))
  exact key (PTree.orderList ω) ω le_rfl

/-- The full cut, pruning the whole forest, is always a coproduct term. -/
theorem self_nil_mem_mkwTerms (ω : PlanarForest) :
    (ω, ([] : PlanarForest)) ∈ mkwTerms ω := by
  rcases List.eq_nil_or_concat ω with rfl | ⟨ω', t, hω⟩
  · simp
  · subst hω
    rw [List.concat_eq_append, mkwTerms_concat]
    exact List.mem_cons_self

/-- The empty cut, pruning nothing, is always a coproduct term. -/
theorem nil_self_mem_mkwTerms (ω : PlanarForest) :
    (([] : PlanarForest), ω) ∈ mkwTerms ω := by
  induction ω using concatChildrenInduction with
  | nil => simp
  | concat ω t ih₁ ih₂ =>
      rw [mkwTerms_concat]
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_flatMap.2 ⟨([], ω), ih₁, ?_⟩
      refine List.mem_flatMap.2 ⟨([], t.children), ih₂, ?_⟩
      refine List.mem_map.2 ⟨[], ?_, ?_⟩
      · simp
      · simp

/-- The first MKW coproduct term is always the full cut `ω ⊗ 𝟙`. -/
theorem mkwTerms_eq_self_nil_cons (ω : PlanarForest) :
    mkwTerms ω = (ω, ([] : PlanarForest)) :: (mkwTerms ω).tail := by
  rcases List.eq_nil_or_concat ω with rfl | ⟨ω', t, hω⟩
  · simp
  · subst hω
    rw [List.concat_eq_append, mkwTerms_concat, List.tail_cons]

/-- Every MKW coproduct term other than the full cut has a nonempty
remaining part. -/
theorem snd_ne_nil_of_mem_tail_mkwTerms {ω : PlanarForest}
    {pr : PlanarForest × PlanarForest} (hω : ω ≠ [])
    (hpr : pr ∈ (mkwTerms ω).tail) : pr.2 ≠ [] := by
  rcases List.eq_nil_or_concat ω with rfl | ⟨ω', t, hω'⟩
  · exact absurd rfl hω
  · subst hω'
    rw [List.concat_eq_append, mkwTerms_concat, List.tail_cons] at hpr
    rcases List.mem_flatMap.1 hpr with ⟨pr₁, _, hpr'⟩
    rcases List.mem_flatMap.1 hpr' with ⟨pr₂, _, hpr''⟩
    rcases List.mem_map.1 hpr'' with ⟨s, _, rfl⟩
    simp

/-- The MKW coproduct respects the grading by total order of forests. -/
theorem orderList_fst_add_snd_of_mem_mkwTerms (ω : PlanarForest) :
    ∀ pr ∈ mkwTerms ω,
      PTree.orderList pr.1 + PTree.orderList pr.2 = PTree.orderList ω := by
  induction ω using concatChildrenInduction with
  | nil =>
      intro pr hpr
      simp only [mkwTerms_nil, List.mem_singleton] at hpr
      simp [hpr]
  | concat ω t ih₁ ih₂ =>
      intro pr hpr
      rw [mkwTerms_concat] at hpr
      rcases List.mem_cons.1 hpr with rfl | hpr
      · simp
      · rcases List.mem_flatMap.1 hpr with ⟨pr₁, hpr₁, hpr'⟩
        rcases List.mem_flatMap.1 hpr' with ⟨pr₂, hpr₂, hpr''⟩
        rcases List.mem_map.1 hpr'' with ⟨s, hs, rfl⟩
        have h₁ := ih₁ pr₁ hpr₁
        have h₂ := ih₂ pr₂ hpr₂
        have hs' : PTree.orderList s =
            PTree.orderList pr₁.1 + PTree.orderList pr₂.1 := by
          rw [PTree.orderList_perm (Word.perm_append_of_mem_shuffle hs)]
          exact PTree.orderList_append pr₁.1 pr₂.1
        have ht := PTree.order_eq_one_add_orderList_children t
        simp only [PTree.orderList_append, PTree.orderList_cons,
          PTree.orderList_nil, PTree.order_node] at h₁ h₂ ⊢
        omega

/-- Every MKW coproduct term other than the full cut prunes strictly fewer
vertices than the whole forest. This justifies the recursive definition of
the antipode. -/
theorem orderList_fst_lt_of_mem_tail_mkwTerms {ω : PlanarForest}
    {pr : PlanarForest × PlanarForest} (hω : ω ≠ [])
    (hpr : pr ∈ (mkwTerms ω).tail) :
    PTree.orderList pr.1 < PTree.orderList ω := by
  have hmem : pr ∈ mkwTerms ω := by
    rw [mkwTerms_eq_self_nil_cons ω]
    exact List.mem_cons_of_mem _ hpr
  have hgrade := orderList_fst_add_snd_of_mem_mkwTerms ω pr hmem
  have hsnd : PTree.orderList pr.2 ≠ 0 := fun h0 =>
    snd_ne_nil_of_mem_tail_mkwTerms hω hpr
      ((PTree.orderList_eq_zero_iff pr.2).1 h0)
  have hω' : PTree.orderList ω ≠ 0 := fun h0 =>
    hω ((PTree.orderList_eq_zero_iff ω).1 h0)
  omega

private theorem sum_map_counitCoeff_smul_shuffle {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] (u v : List PTree) (x : M) :
    ((Word.shuffle u v).map fun s =>
        PlanarForestAlgebra.counitCoeff (R := R) (s : PlanarForest) • x).sum =
      PlanarForestAlgebra.counitCoeff (R := R) (u : PlanarForest) •
        PlanarForestAlgebra.counitCoeff (R := R) (v : PlanarForest) • x := by
  cases u with
  | nil =>
      cases v with
      | nil => simp
      | cons b v =>
          have h0 : PlanarForestAlgebra.counitCoeff (R := R)
              ((b :: v : List PTree) : PlanarForest) = 0 :=
            PlanarForestAlgebra.counitCoeff_ne_nil (by simp)
          simp [h0]
  | cons a u =>
      have h0 : PlanarForestAlgebra.counitCoeff (R := R)
          ((a :: u : List PTree) : PlanarForest) = 0 :=
        PlanarForestAlgebra.counitCoeff_ne_nil (by simp)
      rw [h0, zero_smul]
      apply List.sum_eq_zero
      intro y hy
      rcases List.mem_map.1 hy with ⟨s, hs, rfl⟩
      have hs0 : PlanarForestAlgebra.counitCoeff (R := R) (s : PlanarForest) = 0 :=
        PlanarForestAlgebra.counitCoeff_ne_nil
          (Word.ne_nil_of_mem_shuffle_left hs (by simp))
      rw [hs0, zero_smul]

/--
Applying the counit to the pruned factor of every MKW coproduct term recovers
the forest: the only term with empty pruned part is the empty cut `𝟙 ⊗ ω`.
The statement is generalized over an arbitrary module-valued weight `g` of the
remaining factor so that it can serve as its own induction hypothesis.
-/
theorem sum_map_counitCoeff_fst_smul_mkwTerms {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] (ω : PlanarForest) :
    ∀ g : PlanarForest → M,
      ((mkwTerms ω).map fun pr =>
          PlanarForestAlgebra.counitCoeff (R := R) pr.1 • g pr.2).sum = g ω := by
  induction ω using concatChildrenInduction with
  | nil =>
      intro g
      simp
  | concat ω t ih₁ ih₂ =>
      intro g
      rw [mkwTerms_concat, List.map_cons, List.sum_cons]
      have hhead :
          PlanarForestAlgebra.counitCoeff (R := R) (ω ++ [t] : PlanarForest) = 0 :=
        PlanarForestAlgebra.counitCoeff_ne_nil (by simp)
      rw [hhead, zero_smul, zero_add, map_flatMap', sum_flatMap']
      have hinner : ∀ pr₁ : PlanarForest × PlanarForest,
          ((((mkwTerms t.children).flatMap fun pr₂ =>
              (Word.shuffle pr₁.1 pr₂.1).map fun s =>
                (s, pr₁.2 ++ [PTree.node pr₂.2])).map fun pr =>
                  PlanarForestAlgebra.counitCoeff (R := R) pr.1 • g pr.2).sum) =
            PlanarForestAlgebra.counitCoeff (R := R) pr₁.1 • g (pr₁.2 ++ [t]) := by
        intro pr₁
        rw [map_flatMap', sum_flatMap']
        have h₂ : ∀ pr₂ : PlanarForest × PlanarForest,
            ((((Word.shuffle pr₁.1 pr₂.1).map fun s =>
                (s, pr₁.2 ++ [PTree.node pr₂.2])).map fun pr =>
                  PlanarForestAlgebra.counitCoeff (R := R) pr.1 • g pr.2).sum) =
              PlanarForestAlgebra.counitCoeff (R := R) pr₁.1 •
                (PlanarForestAlgebra.counitCoeff (R := R) pr₂.1 •
                  g (pr₁.2 ++ [PTree.node pr₂.2])) := by
          intro pr₂
          rw [List.map_map]
          simpa [Function.comp_def] using
            sum_map_counitCoeff_smul_shuffle (R := R) pr₁.1 pr₂.1
              (g (pr₁.2 ++ [PTree.node pr₂.2]))
        rw [List.map_congr_left fun pr₂ _ => h₂ pr₂]
        have hpull :
            ((mkwTerms t.children).map fun pr₂ =>
                PlanarForestAlgebra.counitCoeff (R := R) pr₁.1 •
                  (PlanarForestAlgebra.counitCoeff (R := R) pr₂.1 •
                    g (pr₁.2 ++ [PTree.node pr₂.2]))).sum =
              PlanarForestAlgebra.counitCoeff (R := R) pr₁.1 •
                ((mkwTerms t.children).map fun pr₂ =>
                  PlanarForestAlgebra.counitCoeff (R := R) pr₂.1 •
                    g (pr₁.2 ++ [PTree.node pr₂.2])).sum := by
          rw [smul_sum', List.map_map]
          simp [Function.comp_def]
        rw [hpull, ih₂ fun r₂ => g (pr₁.2 ++ [PTree.node r₂]), PTree.node_children]
      rw [List.map_congr_left fun pr₁ _ => hinner pr₁]
      exact ih₁ fun r => g (r ++ [t])

/--
Applying the counit to the remaining factor of every MKW coproduct term
recovers the forest: the only term with empty remaining part is the full cut
`ω ⊗ 𝟙`.
-/
theorem sum_map_counitCoeff_snd_smul_mkwTerms {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] (ω : PlanarForest)
    (g : PlanarForest → M) :
    ((mkwTerms ω).map fun pr =>
        PlanarForestAlgebra.counitCoeff (R := R) pr.2 • g pr.1).sum = g ω := by
  rcases List.eq_nil_or_concat ω with rfl | ⟨ω', t, hω⟩
  · simp
  · subst hω
    rw [List.concat_eq_append, mkwTerms_concat, List.map_cons, List.sum_cons]
    have htail :
        (((mkwTerms ω').flatMap fun pr₁ =>
            (mkwTerms t.children).flatMap fun pr₂ =>
              (Word.shuffle pr₁.1 pr₂.1).map fun s =>
                (s, pr₁.2 ++ [PTree.node pr₂.2])).map fun pr =>
                  PlanarForestAlgebra.counitCoeff (R := R) pr.2 • g pr.1).sum = 0 := by
      apply List.sum_eq_zero
      intro y hy
      rcases List.mem_map.1 hy with ⟨pr, hpr, rfl⟩
      rcases List.mem_flatMap.1 hpr with ⟨pr₁, hpr₁, hpr'⟩
      rcases List.mem_flatMap.1 hpr' with ⟨pr₂, hpr₂, hpr''⟩
      rcases List.mem_map.1 hpr'' with ⟨s, hs, rfl⟩
      have h0 : PlanarForestAlgebra.counitCoeff (R := R)
          (pr₁.2 ++ [PTree.node pr₂.2] : PlanarForest) = 0 :=
        PlanarForestAlgebra.counitCoeff_ne_nil (by simp)
      rw [h0, zero_smul]
    rw [htail, add_zero, PlanarForestAlgebra.counitCoeff_nil, one_smul]

end PlanarForest

/-- Tensor-coded ordered forest algebra: `(φ, ψ)` represents `φ ⊗ ψ`. -/
abbrev PlanarTensorAlgebra (R : Type u) [Semiring R] : Type u :=
  MonoidAlgebra R (PlanarForest × PlanarForest)

namespace PlanarTensorAlgebra

noncomputable section

variable {R : Type u}

/-- The basis tensor `φ ⊗ ψ` represented by a pair of ordered forests. -/
def ofPair [Semiring R] (term : PlanarForest × PlanarForest) :
    PlanarTensorAlgebra R :=
  MonoidAlgebra.single term 1

@[simp]
theorem ofPair_nil_nil [Semiring R] :
    ofPair (R := R) (([] : PlanarForest), ([] : PlanarForest)) = 1 := by
  change MonoidAlgebra.single (([], []) : PlanarForest × PlanarForest) (1 : R) =
    MonoidAlgebra.single (1 : PlanarForest × PlanarForest) 1
  rfl

@[simp]
theorem ofPair_mul [Semiring R] (x y : PlanarForest × PlanarForest) :
    ofPair (R := R) (x.1 ++ y.1, x.2 ++ y.2) = ofPair x * ofPair y := by
  rw [ofPair, ofPair, ofPair, MonoidAlgebra.single_mul_single, one_mul]
  rfl

/-- Sum a finite list of basis tensors. Duplicates contribute multiplicity. -/
def sumTerms [Semiring R] (terms : List (PlanarForest × PlanarForest)) :
    PlanarTensorAlgebra R :=
  (terms.map fun term => ofPair (R := R) term).sum

@[simp]
theorem sumTerms_nil [Semiring R] : sumTerms (R := R) [] = 0 :=
  rfl

@[simp]
theorem sumTerms_cons [Semiring R] (term : PlanarForest × PlanarForest)
    (terms : List (PlanarForest × PlanarForest)) :
    sumTerms (R := R) (term :: terms) = ofPair term + sumTerms terms := by
  simp [sumTerms]

@[simp]
theorem sumTerms_singleton [Semiring R] (term : PlanarForest × PlanarForest) :
    sumTerms (R := R) [term] = ofPair term := by
  simp

theorem sumTerms_append [Semiring R]
    (xs ys : List (PlanarForest × PlanarForest)) :
    sumTerms (R := R) (xs ++ ys) = sumTerms xs + sumTerms ys := by
  simp [sumTerms]

private def counitLeftMonoidHom (R : Type u) [CommSemiring R] :
    (PlanarForest × PlanarForest) →* PlanarForestAlgebra R where
  toFun term :=
    PlanarForestAlgebra.counitCoeff (R := R) term.1 •
      PlanarForestAlgebra.ofForest (R := R) term.2
  map_one' := by
    change PlanarForestAlgebra.counitCoeff (R := R) ([] : PlanarForest) •
      PlanarForestAlgebra.ofForest (R := R) ([] : PlanarForest) = 1
    simp
  map_mul' x y := by
    change
      PlanarForestAlgebra.counitCoeff (R := R) (x.1 ++ y.1) •
          PlanarForestAlgebra.ofForest (R := R) (x.2 ++ y.2) = _
    rw [PlanarForestAlgebra.counitCoeff_append, PlanarForestAlgebra.ofForest_append,
      ← smul_mul_smul_comm]

/-- Apply the counit to the left tensor factor. -/
def counitLeft [CommSemiring R] :
    PlanarTensorAlgebra R →ₐ[R] PlanarForestAlgebra R :=
  (MonoidAlgebra.lift R (PlanarForestAlgebra R) (PlanarForest × PlanarForest))
    (counitLeftMonoidHom R)

@[simp]
theorem counitLeft_ofPair [CommSemiring R] (term : PlanarForest × PlanarForest) :
    counitLeft (R := R) (ofPair term) =
      PlanarForestAlgebra.counitCoeff (R := R) term.1 •
        PlanarForestAlgebra.ofForest (R := R) term.2 := by
  simp [counitLeft, ofPair, counitLeftMonoidHom]

theorem counitLeft_sumTerms [CommSemiring R]
    (terms : List (PlanarForest × PlanarForest)) :
    counitLeft (R := R) (sumTerms terms) =
      (terms.map fun term =>
        PlanarForestAlgebra.counitCoeff (R := R) term.1 •
          PlanarForestAlgebra.ofForest (R := R) term.2).sum := by
  rw [sumTerms, map_list_sum, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun term _ => counitLeft_ofPair term)

private def counitRightMonoidHom (R : Type u) [CommSemiring R] :
    (PlanarForest × PlanarForest) →* PlanarForestAlgebra R where
  toFun term :=
    PlanarForestAlgebra.counitCoeff (R := R) term.2 •
      PlanarForestAlgebra.ofForest (R := R) term.1
  map_one' := by
    change PlanarForestAlgebra.counitCoeff (R := R) ([] : PlanarForest) •
      PlanarForestAlgebra.ofForest (R := R) ([] : PlanarForest) = 1
    simp
  map_mul' x y := by
    change
      PlanarForestAlgebra.counitCoeff (R := R) (x.2 ++ y.2) •
          PlanarForestAlgebra.ofForest (R := R) (x.1 ++ y.1) = _
    rw [PlanarForestAlgebra.counitCoeff_append, PlanarForestAlgebra.ofForest_append,
      ← smul_mul_smul_comm]

/-- Apply the counit to the right tensor factor. -/
def counitRight [CommSemiring R] :
    PlanarTensorAlgebra R →ₐ[R] PlanarForestAlgebra R :=
  (MonoidAlgebra.lift R (PlanarForestAlgebra R) (PlanarForest × PlanarForest))
    (counitRightMonoidHom R)

@[simp]
theorem counitRight_ofPair [CommSemiring R] (term : PlanarForest × PlanarForest) :
    counitRight (R := R) (ofPair term) =
      PlanarForestAlgebra.counitCoeff (R := R) term.2 •
        PlanarForestAlgebra.ofForest (R := R) term.1 := by
  simp [counitRight, ofPair, counitRightMonoidHom]

theorem counitRight_sumTerms [CommSemiring R]
    (terms : List (PlanarForest × PlanarForest)) :
    counitRight (R := R) (sumTerms terms) =
      (terms.map fun term =>
        PlanarForestAlgebra.counitCoeff (R := R) term.2 •
          PlanarForestAlgebra.ofForest (R := R) term.1).sum := by
  rw [sumTerms, map_list_sum, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun term _ => counitRight_ofPair term)

end

end PlanarTensorAlgebra

namespace PlanarForest

noncomputable section

variable {R : Type u}

/--
The MKW coproduct of an ordered forest, in the tensor-coded algebra.
Munthe-Kaas & Wright, arXiv:math/0603023, Definition 3.
-/
def mkwCoproduct [Semiring R] (ω : PlanarForest) : PlanarTensorAlgebra R :=
  PlanarTensorAlgebra.sumTerms (R := R) (mkwTerms ω)

@[simp]
theorem mkwCoproduct_nil [Semiring R] :
    mkwCoproduct (R := R) ([] : PlanarForest) = 1 := by
  simp [mkwCoproduct]

/-- The left counit law of the MKW coproduct: `(e ⊗ I)Δ_N = I`. -/
theorem counitLeft_mkwCoproduct [CommSemiring R] (ω : PlanarForest) :
    PlanarTensorAlgebra.counitLeft (R := R) (mkwCoproduct ω) =
      PlanarForestAlgebra.ofForest ω := by
  rw [mkwCoproduct, PlanarTensorAlgebra.counitLeft_sumTerms]
  exact sum_map_counitCoeff_fst_smul_mkwTerms ω _

/-- The right counit law of the MKW coproduct: `(I ⊗ e)Δ_N = I`. -/
theorem counitRight_mkwCoproduct [CommSemiring R] (ω : PlanarForest) :
    PlanarTensorAlgebra.counitRight (R := R) (mkwCoproduct ω) =
      PlanarForestAlgebra.ofForest ω := by
  rw [mkwCoproduct, PlanarTensorAlgebra.counitRight_sumTerms]
  exact sum_map_counitCoeff_snd_smul_mkwTerms ω _

/-! ### Small-order verification against arXiv:math/0603023

The coproduct terms for all ordered forests of order at most three, and the
paper's illustrative example `Δ_N(•χ)` with its multiplicity `2` term. The
cherry demonstrates left-admissibility: only the left branch may be pruned on
its own, so `• ⊗ χ` appears with coefficient `1` rather than `2` as it would
in the Butcher-Connes-Kreimer coproduct.
-/

theorem mkwTerms_bullet_forest :
    mkwTerms [PTree.bullet] = [([PTree.bullet], []), ([], [PTree.bullet])] := by
  have h : ([PTree.bullet] : PlanarForest) = [] ++ [PTree.bullet] := rfl
  rw [h, mkwTerms_concat]
  simp [PTree.bullet]

theorem mkwTerms_chain2_forest :
    mkwTerms [PTree.chain2] =
      [([PTree.chain2], []), ([PTree.bullet], [PTree.bullet]),
        ([], [PTree.chain2])] := by
  have h : ([PTree.chain2] : PlanarForest) = [] ++ [PTree.chain2] := rfl
  have hc : PTree.children PTree.chain2 = [PTree.bullet] := rfl
  rw [h, mkwTerms_concat, hc, mkwTerms_bullet_forest]
  simp [PTree.bullet, PTree.chain2]

theorem mkwTerms_bullet_bullet_forest :
    mkwTerms [PTree.bullet, PTree.bullet] =
      [([PTree.bullet, PTree.bullet], []), ([PTree.bullet], [PTree.bullet]),
        ([], [PTree.bullet, PTree.bullet])] := by
  have h : ([PTree.bullet, PTree.bullet] : PlanarForest) =
      [PTree.bullet] ++ [PTree.bullet] := rfl
  rw [h, mkwTerms_concat, mkwTerms_bullet_forest]
  simp [PTree.bullet]

theorem mkwTerms_chain3_forest :
    mkwTerms [PTree.chain3] =
      [([PTree.chain3], []), ([PTree.chain2], [PTree.bullet]),
        ([PTree.bullet], [PTree.chain2]), ([], [PTree.chain3])] := by
  have h : ([PTree.chain3] : PlanarForest) = [] ++ [PTree.chain3] := rfl
  have hc : PTree.children PTree.chain3 = [PTree.chain2] := rfl
  rw [h, mkwTerms_concat, hc, mkwTerms_chain2_forest]
  simp [PTree.bullet, PTree.chain2, PTree.chain3]

/-- Only the left branch of the cherry may be pruned on its own. -/
theorem mkwTerms_cherry_forest :
    mkwTerms [PTree.cherry] =
      [([PTree.cherry], []),
        ([PTree.bullet, PTree.bullet], [PTree.bullet]),
        ([PTree.bullet], [PTree.chain2]),
        ([], [PTree.cherry])] := by
  have h : ([PTree.cherry] : PlanarForest) = [] ++ [PTree.cherry] := rfl
  have hc : PTree.children PTree.cherry = [PTree.bullet, PTree.bullet] := rfl
  rw [h, mkwTerms_concat, hc, mkwTerms_bullet_bullet_forest]
  simp [PTree.bullet, PTree.chain2, PTree.cherry]

/--
The illustrative example of arXiv:math/0603023, Section 2:
`Δ_N(•χ) = •χ ⊗ 𝟙 + 2 (•• ⊗ •) + • ⊗ χ + • ⊗ •• + 𝟙 ⊗ •χ`,
where `χ` is the two-vertex chain.
-/
theorem mkwTerms_bullet_chain2_forest :
    mkwTerms [PTree.bullet, PTree.chain2] =
      [([PTree.bullet, PTree.chain2], []),
        ([PTree.bullet, PTree.bullet], [PTree.bullet]),
        ([PTree.bullet, PTree.bullet], [PTree.bullet]),
        ([PTree.bullet], [PTree.chain2]),
        ([PTree.bullet], [PTree.bullet, PTree.bullet]),
        ([], [PTree.bullet, PTree.chain2])] := by
  have h : ([PTree.bullet, PTree.chain2] : PlanarForest) =
      [PTree.bullet] ++ [PTree.chain2] := rfl
  have hc : PTree.children PTree.chain2 = [PTree.bullet] := rfl
  rw [h, mkwTerms_concat, hc, mkwTerms_bullet_forest]
  simp [PTree.bullet, PTree.chain2]

/-- The one-vertex forest is primitive for the MKW coproduct. -/
theorem mkwCoproduct_bullet_forest [Semiring R] :
    mkwCoproduct (R := R) [PTree.bullet] =
      PlanarTensorAlgebra.ofPair ([PTree.bullet], []) +
        PlanarTensorAlgebra.ofPair ([], [PTree.bullet]) := by
  rw [mkwCoproduct, mkwTerms_bullet_forest]
  simp

end

end PlanarForest

end HopfAlgebras
