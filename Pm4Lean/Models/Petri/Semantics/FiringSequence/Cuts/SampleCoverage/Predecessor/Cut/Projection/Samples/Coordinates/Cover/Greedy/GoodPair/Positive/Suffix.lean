import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Antichain.GoodPair
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.Membership

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem containsPrefixCoordinateGoodPair_of_greedyPrefixCutSampleCoordinateBasis_before_suffix_le
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before))
    (hSuffixLe :
      ∀ second : PrefixCutSample N M₀ ts Mend,
        second ∈ before →
          coords = Marking.placeValues N second.marking →
            ∃ loop : List N.Transition,
              second.pref = sample.pref ++ loop ∧
                NatListLe (Marking.placeValues N sample.marking)
                  coords) :
    ContainsPrefixCoordinateGoodPair (before ++ sample :: after) := by
  obtain ⟨second, hSecondMem, hCoordsEq⟩ :=
    exists_sample_of_mem_greedyPrefixCutSampleCoordinateBasis
      (samples := before) hCoordsMem
  obtain ⟨loop, hPrefix, hLe⟩ := hSuffixLe second hSecondMem hCoordsEq
  exact containsPrefixCoordinateGoodPair_of_split_second_prefix_coordinateLe
    (before := before)
    (after := after)
    (first := sample)
    (second := second)
    (loop := loop)
    hSecondMem
    hPrefix
    (by simpa [hCoordsEq] using hLe)

end FiringSequence
end Petri
end Pm4Lean
