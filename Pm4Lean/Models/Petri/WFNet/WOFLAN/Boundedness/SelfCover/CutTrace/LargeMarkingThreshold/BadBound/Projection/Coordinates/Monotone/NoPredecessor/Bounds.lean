import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions
import Pm4Lean.Util.NatListMax

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_mono
    {W : WFNet} {k k' : Nat}
    (hLe : k ≤ k')
    (hBounded :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
      W k' := by
  intro ts Mend hSeq samples hSamplesCovered coords hCoordsMem x hXMem
  exact Nat.le_trans
    (hBounded ts Mend hSeq samples hSamplesCovered coords hCoordsMem
      x hXMem)
    hLe

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_max_left
    {W : WFNet} {k k' : Nat}
    (hBounded :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
      W (Nat.max k k') :=
  largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_mono
    (Nat.le_max_left k k') hBounded

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_max_right
    {W : WFNet} {k k' : Nat}
    (hBounded :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy W k') :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
      W (Nat.max k k') :=
  largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_mono
    (Nat.le_max_right k k') hBounded

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_natListMax
    {W : WFNet} {bounds : List Nat} {k : Nat}
    (hMem : k ∈ bounds)
    (hBounded :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
      W (NatListMax bounds) :=
  largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_mono
    (le_natListMax_of_mem hMem) hBounded

end Petri
end Pm4Lean
