import Lake
open Lake DSL

package «lean-rough-paths» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "2899f1514b0e12bd6c2dfa77f6f6bb0031cf7f21"

@[default_target]
lean_lib «HopfAlgebras» where
  srcDir := "."

@[default_target]
lean_lib «RoughPaths» where
  srcDir := "."
