import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.28.0"

package «coherence-tactics» where
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib CoherenceTactics

@[default_target]
lean_exe «coherence-tactics-docs» where
  root := `CoherenceTacticsDocsMain
  supportInterpreter := true
