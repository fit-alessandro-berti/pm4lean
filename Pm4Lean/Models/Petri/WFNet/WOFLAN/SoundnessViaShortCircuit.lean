import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness

namespace Pm4Lean
namespace Petri

/--
The standard WOFLAN target theorem will relate WF-net soundness to liveness
and boundedness of the short-circuited marked net.  This predicate records the
statement shape while the full proof is developed.
-/
def SoundnessViaShortCircuitStatement (W : WFNet) : Prop :=
  Sound W ↔ Live (shortCircuit W) W.initial ∧ Bounded (shortCircuit W) W.initial

end Petri
end Pm4Lean
