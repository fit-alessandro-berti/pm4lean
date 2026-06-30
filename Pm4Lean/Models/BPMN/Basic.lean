import Pm4Lean.Models.Language

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

/-- The visible trace contributed by entering a BPMN node. -/
def nodeLabel {Activity : Type u} : BPMNNode Activity → Trace Activity
  | BPMNNode.startEvent => []
  | BPMNNode.endEvent => []
  | BPMNNode.task a => [a]
  | BPMNNode.gateway _ => []

/-- A node has no incoming sequence-flow edge. -/
def IsSource (B : BPMN Activity) (n : B.Node) : Prop :=
  ∀ e ∈ B.flows, e.2 ≠ n

/-- A node has no outgoing sequence-flow edge. -/
def IsSink (B : BPMN Activity) (n : B.Node) : Prop :=
  ∀ e ∈ B.flows, e.1 ≠ n

/-- A directed sequence-flow edge in a BPMN graph. -/
def Edge (B : BPMN Activity) (src dst : B.Node) : Prop :=
  (src, dst) ∈ B.flows

/--
A walk through a BPMN graph.  The trace records visible task labels when the
walk enters a node; events and gateways contribute the empty trace.
-/
inductive Walk (B : BPMN Activity) :
    B.Node → B.Node → Trace Activity → Prop where
  | nil (n : B.Node) : Walk B n n []
  | cons {src mid dst : B.Node} {σ : Trace Activity} :
      Edge B src mid →
      Walk B mid dst σ →
      Walk B src dst (nodeLabel (B.kind mid) ++ σ)

/-- A BPMN trace starts at a start event and ends at an end event. -/
def language (B : BPMN Activity) : Language Activity :=
  fun σ => ∃ start finish : B.Node,
    B.kind start = BPMNNode.startEvent ∧
    B.kind finish = BPMNNode.endEvent ∧
    Walk B start finish σ

theorem nodeLabel_startEvent :
    nodeLabel (Activity := Activity) BPMNNode.startEvent = [] :=
  rfl

theorem nodeLabel_endEvent :
    nodeLabel (Activity := Activity) BPMNNode.endEvent = [] :=
  rfl

theorem nodeLabel_task (a : Activity) :
    nodeLabel (BPMNNode.task a) = [a] :=
  rfl

theorem walk_refl (B : BPMN Activity) (n : B.Node) :
    Walk B n n [] :=
  Walk.nil n

theorem walk_of_edge {B : BPMN Activity} {src dst : B.Node}
    (hEdge : Edge B src dst) :
    Walk B src dst (nodeLabel (B.kind dst)) := by
  simpa using Walk.cons hEdge (Walk.nil dst)

theorem language_of_start_end_walk {B : BPMN Activity}
    {start finish : B.Node} {σ : Trace Activity}
    (hStart : B.kind start = BPMNNode.startEvent)
    (hEnd : B.kind finish = BPMNNode.endEvent)
    (hWalk : Walk B start finish σ) :
    language B σ :=
  ⟨start, finish, hStart, hEnd, hWalk⟩

/-- The node set of the BPMN model containing exactly one task. -/
inductive SingleTaskNode where
  | start
  | task
  | finish
deriving DecidableEq, Repr

/-- A BPMN model consisting of start -> task(a) -> end. -/
def singleTask (a : Activity) : BPMN Activity where
  Node := SingleTaskNode
  nodeDecEq := inferInstance
  nodes := [SingleTaskNode.start, SingleTaskNode.task, SingleTaskNode.finish]
  nodes_complete := by
    intro n
    cases n <;> simp
  kind := fun
    | SingleTaskNode.start => BPMNNode.startEvent
    | SingleTaskNode.task => BPMNNode.task a
    | SingleTaskNode.finish => BPMNNode.endEvent
  flows := [
    (SingleTaskNode.start, SingleTaskNode.task),
    (SingleTaskNode.task, SingleTaskNode.finish)
  ]

namespace SingleTask

theorem start_to_task (a : Activity) :
    Edge (singleTask a) SingleTaskNode.start SingleTaskNode.task := by
  exact List.Mem.head _

theorem task_to_finish (a : Activity) :
    Edge (singleTask a) SingleTaskNode.task SingleTaskNode.finish := by
  exact List.Mem.tail _ (List.Mem.head _)

theorem walk_start_finish (a : Activity) :
    Walk (singleTask a) SingleTaskNode.start SingleTaskNode.finish [a] := by
  simpa [singleTask, nodeLabel] using
    Walk.cons (start_to_task a)
      (Walk.cons (task_to_finish a)
        (Walk.nil (B := singleTask a) SingleTaskNode.finish))

theorem language_contains_task (a : Activity) :
    language (singleTask a) [a] :=
  language_of_start_end_walk rfl rfl (walk_start_finish a)

end SingleTask

end BPMN
end ProcessModel
end Pm4Lean
