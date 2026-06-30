import Lake
open Lake DSL

package «pm4lean» where
  version := v!"0.1.0"

@[default_target]
lean_lib Pm4Lean where
  roots := #[`Pm4Lean]
