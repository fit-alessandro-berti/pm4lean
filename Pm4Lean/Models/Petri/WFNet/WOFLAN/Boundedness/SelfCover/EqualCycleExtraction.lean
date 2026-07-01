import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Duplicate.Prefix.Cycle
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.EqualCycle

namespace Pm4Lean
namespace Petri

theorem equalCutCycle_of_noPredecessor_length_gt
    {W : WFNet} {ts : List W.net.Transition} {Mend : W.Marking}
    {samples :
      List (FiringSequence.PrefixCutSample W.net W.initial ts Mend)}
    {k : Nat}
    (hLength :
      (NatListsUpTo W.net.places.length k).length < samples.length)
    (hNoPredecessor :
      ∀ sample : FiringSequence.PrefixCutSample W.net W.initial ts Mend,
        sample ∈ samples →
          ¬ FiringSequence.HasComparablePrefixCutPredecessor sample)
    (hBounded :
      FiringSequence.NoComparablePrefixCutPredecessorsBounded samples k) :
    EqualCutCycle W :=
  equalCutCycle_of_equalPrefixCutCycleInRun
    (FiringSequence.equalPrefixCutCycleInRun_of_noPredecessor_length_gt
      hLength hNoPredecessor hBounded)

end Petri
end Pm4Lean
