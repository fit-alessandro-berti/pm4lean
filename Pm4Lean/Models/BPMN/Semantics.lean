import Pm4Lean.Models.Language
import Pm4Lean.Models.BPMN.Basic

namespace Pm4Lean
namespace ProcessModel
namespace BPMN

/-- The visible trace contributed by entering a BPMN node. -/
def nodeLabel {Activity : Type u} : BPMNNode Activity → Trace Activity
  | BPMNNode.startEvent => []
  | BPMNNode.endEvent => []
  | BPMNNode.task a => [a]
  | BPMNNode.gateway _ => []

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

end BPMN
end ProcessModel
end Pm4Lean
