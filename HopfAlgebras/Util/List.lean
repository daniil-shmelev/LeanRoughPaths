/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# List lemmas

Small general-purpose `List` lemmas used across the library.
-/

namespace List

/-- Summing over `l.attach` equals summing over `l`; removes the `attach`
plumbing that recursive definitions introduce for termination. -/
theorem sum_attach_map {α : Type*} {M : Type*} [AddMonoid M]
    (l : List α) (f : α → M) :
    (l.attach.map fun i => f i.1).sum = (l.map f).sum :=
  congrArg List.sum (attach_map_val (l := l) (f := f))

end List
