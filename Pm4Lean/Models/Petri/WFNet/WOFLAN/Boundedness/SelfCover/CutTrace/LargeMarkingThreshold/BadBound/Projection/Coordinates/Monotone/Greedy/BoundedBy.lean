import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions
import Pm4Lean.Util.NatListMax

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_mono
    {W : WFNet} {k k' : Nat}
    (hLe : k ≤ k')
    (hBounded :
      LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k' := by
  intro ts Mend hSeq samples hSamplesCovered coords hCoordsMem x hXMem
  exact Nat.le_trans
    (hBounded ts Mend hSeq samples hSamplesCovered coords hCoordsMem
      x hXMem)
    hLe

theorem largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_max_left
    {W : WFNet} {k k' : Nat}
    (hBounded :
      LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W (Nat.max k k') :=
  largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_mono
    (Nat.le_max_left k k') hBounded

theorem largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_max_right
    {W : WFNet} {k k' : Nat}
    (hBounded :
      LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k') :
    LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W (Nat.max k k') :=
  largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_mono
    (Nat.le_max_right k k') hBounded

theorem largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_natListMax
    {W : WFNet} {bounds : List Nat} {k : Nat}
    (hMem : k ∈ bounds)
    (hBounded :
      LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W
      (NatListMax bounds) :=
  largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_mono
    (le_natListMax_of_mem hMem) hBounded

end Petri
end Pm4Lean
