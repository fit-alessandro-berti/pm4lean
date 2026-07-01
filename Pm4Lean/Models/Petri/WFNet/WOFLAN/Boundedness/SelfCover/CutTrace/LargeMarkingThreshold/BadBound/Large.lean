import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Definitions

namespace Pm4Lean
namespace Petri

theorem arbitrarilyLargeFiringSequenceMarking_of_arbitrarilyLargeCoveredPrefixCutNoPredecessorSample
    {W : WFNet}
    (hLarge : ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample W) :
    ArbitrarilyLargeFiringSequenceMarking W := by
  intro k
  obtain ⟨_ts, _Mend, _hSeq, _samples, _hCovered,
    sample, _hSampleMem, _hNoPredecessor, p, hLt⟩ := hLarge k
  obtain ⟨_suffix, _hTsEq, _hRun, hPrefRun⟩ := sample.isCut
  exact ⟨sample.pref, sample.marking, hPrefRun, p, hLt⟩

end Petri
end Pm4Lean
