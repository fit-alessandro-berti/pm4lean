import Pm4Lean.Models.Petri.Basic.Net

namespace Pm4Lean
namespace Petri

/-- Nodes in the directed bipartite graph underlying a Petri net. -/
inductive Node (N : Net) where
  | place : N.Place → Node N
  | transition : N.Transition → Node N
deriving DecidableEq

end Petri
end Pm4Lean
