/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.HopfRoughPath.Basic
import HopfAlgebras.Combinatorial.MKW
import HopfAlgebras.Combinatorial.BCK
import RoughPaths.Word.Algebraic

/-!
# The three instances of Hopf rough paths

The abstract `HopfRoughPath` (Rahm, Definition 2.2) specialises to the
three signature notions of the library, with inverse translations:

* **classical**: weakly geometric word rough paths over the shuffle
  Hopf algebra — `AlgebraicRoughPath.toHopf` /
  `HopfRoughPath.toWord`;
* **branched**: `AlgebraicBranchedRoughPath` is *defined* as
  `HopfRoughPath bckBialg` (`RoughPaths.Branched`) — no bridge needed;
* **planar branched**: `PlanarBranchedRoughPath` is *defined* as
  `HopfRoughPath mkwBialg` (`RoughPaths.PlanarBranched`) — no bridge
  needed.

The γ-regularity of Definition 2.2.3 specialises with the natural
gradings: word length, forest order, and planar forest order.
-/

namespace RoughPaths

open HopfAlgebras

universe u v w

/-! ### Classical rough paths: the word shuffle Hopf algebra -/

section Word

variable {T : Type u} {α : Type v} {R : Type w} [CommSemiring R]

/-- A weakly geometric word rough path is a Hopf rough path over the
word shuffle Hopf algebra. -/
def AlgebraicRoughPath.toHopf (X : AlgebraicRoughPath T α R)
    (hX : X.IsWeaklyGeometric) :
    HopfRoughPath (wordHopf α).toCombBialg T R where
  increment s t := ⟨X.increment s t, hX s t⟩
  identity t := Subtype.ext ((X.identity t).trans Signature.one_val.symm)
  chen s t u := Subtype.ext (X.chen s t u)

/-- A Hopf rough path over the word shuffle Hopf algebra is a
(weakly geometric) word rough path. -/
def HopfRoughPath.toWord
    (X : HopfRoughPath (wordHopf α).toCombBialg T R) :
    AlgebraicRoughPath T α R where
  increment s t := (X.increment s t : (List α → R))
  identity t :=
    (congrArg Subtype.val (X.identity t)).trans Signature.one_val
  chen s t u := congrArg Subtype.val (X.chen s t u)
  unitEmpty s t := (X.increment s t).2.1

theorem HopfRoughPath.toWord_isWeaklyGeometric
    (X : HopfRoughPath (wordHopf α).toCombBialg T R) :
    X.toWord.IsWeaklyGeometric :=
  fun s t => (X.increment s t).2

@[simp]
theorem AlgebraicRoughPath.toHopf_toWord (X : AlgebraicRoughPath T α R)
    (hX : X.IsWeaklyGeometric) : (X.toHopf hX).toWord = X :=
  rfl

@[simp]
theorem HopfRoughPath.toWord_toHopf
    (X : HopfRoughPath (wordHopf α).toCombBialg T R) :
    X.toWord.toHopf X.toWord_isWeaklyGeometric = X :=
  rfl

end Word

/-! ### γ-regularity with the natural gradings (Definition 2.2.3) -/

section Regularity

variable {α : Type} {R : Type} [CommSemiring R]

/-- A **γ-regular classical rough path**: Definition 2.2 over the word
shuffle Hopf algebra, graded by word length. -/
abbrev HopfRoughPath.IsGeometricHolder
    (X : HopfRoughPath (wordHopf α).toCombBialg ℝ ℝ) (γ : ℝ) : Prop :=
  X.IsHolderRegular List.length γ

/-- A **γ-regular branched rough path**: Definition 2.2 over the BCK
bialgebra, graded by forest order. -/
abbrev HopfRoughPath.IsBranchedHolder
    (X : HopfRoughPath bckBialg ℝ ℝ) (γ : ℝ) : Prop :=
  X.IsHolderRegular RootedForest.order γ

/-- A **γ-regular planarly branched rough path**: Definition 2.2 over
the MKW bialgebra, graded by planar forest order. -/
abbrev HopfRoughPath.IsPlanarBranchedHolder
    (X : HopfRoughPath mkwBialg ℝ ℝ) (γ : ℝ) : Prop :=
  X.IsHolderRegular PlanarForest.order γ

end Regularity

end RoughPaths
