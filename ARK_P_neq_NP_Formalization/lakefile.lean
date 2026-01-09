import Lake
open Lake DSL

package «ARK-P-neq-NP» {
  version := v!"1.0.0-final"
  description := "Formal Verification of P ≠ NP via Spectral Geometry"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ARK_Core» {
  srcDir := "src"
}
