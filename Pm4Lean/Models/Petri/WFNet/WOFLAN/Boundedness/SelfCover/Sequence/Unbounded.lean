import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Sequence.Conversions

namespace Pm4Lean
namespace Petri

theorem unboundedOriginalProducesSelfCover_of_firingSequence
    {W : WFNet}
    (hExtract : UnboundedOriginalProducesFiringSequenceSelfCover W) :
    UnboundedOriginalProducesSelfCover W := by
  intro hNotBounded
  exact reachableSelfCover_of_firingSequenceSelfCover
    (hExtract hNotBounded)

end Petri
end Pm4Lean
