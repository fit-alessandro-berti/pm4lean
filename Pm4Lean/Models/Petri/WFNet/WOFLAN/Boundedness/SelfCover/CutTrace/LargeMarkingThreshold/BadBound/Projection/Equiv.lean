import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Bound
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Box

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorBound_iff_markingDominatingCover
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorBound W ↔
      HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover_of_bound,
    hasLargeCoveredPrefixCutNoPredecessorBound_of_markingsDominated⟩

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_markingDominatingCover_iff
    {W : WFNet} (hCovered :
      HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_iff_markingDominatingCover.mpr
    hCovered

theorem hasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover_of_bound_iff
    {W : WFNet} (hBound : HasLargeCoveredPrefixCutNoPredecessorBound W) :
    HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_iff_markingDominatingCover.mp
    hBound

end Petri
end Pm4Lean
