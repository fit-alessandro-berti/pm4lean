import Pm4Lean.Models.BPMN.Semantics

namespace Pm4Lean
namespace ProcessModel
namespace BPMN

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
