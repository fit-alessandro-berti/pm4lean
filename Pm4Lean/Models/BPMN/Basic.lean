namespace Pm4Lean
namespace ProcessModel

/-- A small gateway vocabulary for BPMN control-flow models. -/
inductive BPMNGatewayKind where
  | exclusive
  | parallel
  | inclusive
deriving DecidableEq, Repr

/-- BPMN flow nodes relevant to control-flow semantics. -/
inductive BPMNNode (Activity : Type u) where
  | startEvent
  | endEvent
  | task : Activity → BPMNNode Activity
  | gateway : BPMNGatewayKind → BPMNNode Activity
deriving Repr

/-- A lightweight BPMN process graph with explicit finite node and flow lists. -/
structure BPMN (Activity : Type u) where
  Node : Type v
  nodeDecEq : DecidableEq Node
  nodes : List Node
  nodes_complete : ∀ n : Node, n ∈ nodes
  kind : Node → BPMNNode Activity
  flows : List (Node × Node)

attribute [instance] BPMN.nodeDecEq

namespace BPMN

/-- A node has no incoming sequence-flow edge. -/
def IsSource (B : BPMN Activity) (n : B.Node) : Prop :=
  ∀ e ∈ B.flows, e.2 ≠ n

/-- A node has no outgoing sequence-flow edge. -/
def IsSink (B : BPMN Activity) (n : B.Node) : Prop :=
  ∀ e ∈ B.flows, e.1 ≠ n

/-- A directed sequence-flow edge in a BPMN graph. -/
def Edge (B : BPMN Activity) (src dst : B.Node) : Prop :=
  (src, dst) ∈ B.flows

end BPMN
end ProcessModel
end Pm4Lean
