import Pm4Lean.Conversion.ProcessTree
import Pm4Lean.Models.BPMN.Semantics

namespace Pm4Lean
namespace ProcessModel

/-- A behavior-preserving conversion from process trees to BPMN models. -/
def PreservesProcessTreeToBPMN
    {Activity : Type u}
    (bpmnLanguage : BPMN Activity → Language Activity)
    (C : Conversion (ProcessTree Activity) (BPMN Activity)) : Prop :=
  PreservesProcessTreeLanguage bpmnLanguage C

/-- A process-tree-to-BPMN conversion preserving the concrete BPMN walk language. -/
abbrev PreservesProcessTreeToConcreteBPMN
    {Activity : Type u}
    (C : Conversion (ProcessTree Activity) (BPMN Activity)) : Prop :=
  PreservesProcessTreeToBPMN BPMN.language C

end ProcessModel
end Pm4Lean
