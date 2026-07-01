import Pm4Lean.Models.POWL.Semantics
import Pm4Lean.Models.POWL2.Basic

namespace Pm4Lean
namespace ProcessModel
namespace POWL2

variable {Activity : Type u}

/-- POWL2 trace semantics is the semantics of its POWL desugaring. -/
noncomputable def language (p : POWL2 Activity) : Language Activity :=
  POWL.language (toPOWL p)

theorem ofPOWL_language (p : POWL Activity) :
    language (ofPOWL p) = POWL.language p :=
  by simp [language, toPOWL]

theorem sequence_language (children : List (POWL2 Activity)) :
    language (sequence children) =
      POWL.language
        (POWL.partialOrder (children.map toPOWL)
          (sequenceOrder children.length)) :=
  by simp [language, toPOWL]

theorem parallel_language (children : List (POWL2 Activity)) :
    language (parallel children) =
      POWL.language
        (POWL.partialOrder (children.map toPOWL) parallelOrder) :=
  by simp [language, toPOWL]

end POWL2
end ProcessModel
end Pm4Lean
