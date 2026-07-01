import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Sequence.Conversions

namespace Pm4Lean
namespace Petri

theorem largeSequencesProduceFiringSequenceSelfCover_of_cut
    {W : WFNet}
    (hExtract : LargeSequencesProduceCutSelfCover W) :
    LargeSequencesProduceFiringSequenceSelfCover W := by
  intro hLarge
  exact firingSequenceSelfCover_of_cutSelfCover (hExtract hLarge)

theorem largeSequencesProduceCutSelfCover_of_factoredRun
    {W : WFNet}
    (hExtract : LargeSequencesProduceFactoredRunCutSelfCover W) :
    LargeSequencesProduceCutSelfCover W := by
  intro hLarge
  exact cutSelfCover_of_factoredRunCutSelfCover (hExtract hLarge)

theorem largeSequencesProduceFactoredRunCutSelfCover_of_local
    {W : WFNet}
    (hExtract : LargeSequencesProduceLocalFactoredRunCutSelfCover W) :
    LargeSequencesProduceFactoredRunCutSelfCover W := by
  intro hLarge
  exact factoredRunCutSelfCover_of_local (hExtract hLarge)

end Petri
end Pm4Lean
