import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.SoundExclusion.Reachable

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_self_cover_extraction
    {W : WFNet}
    (hExtract : UnboundedOriginalProducesSelfCover W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W := by
  classical
  exact Classical.byContradiction (fun hNotBounded =>
    sound_excludes_reachable_self_cover hSound (hExtract hNotBounded))

theorem original_bounded_of_sound_and_firingSequence_self_cover_extraction
    {W : WFNet}
    (hExtract : UnboundedOriginalProducesFiringSequenceSelfCover W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_self_cover_extraction
    (unboundedOriginalProducesSelfCover_of_firingSequence hExtract)
    hSound

end Petri
end Pm4Lean
