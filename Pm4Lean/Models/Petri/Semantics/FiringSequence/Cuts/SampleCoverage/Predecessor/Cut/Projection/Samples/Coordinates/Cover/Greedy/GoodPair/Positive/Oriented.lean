import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.GoodPair.Positive.Prefix
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.GoodPair.Positive.Suffix

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem containsPrefixCoordinateGoodPair_of_greedyPrefixCutSampleCoordinateBasis_before_oriented_le
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before))
    (hOrientedLe :
      ∀ earlier : PrefixCutSample N M₀ ts Mend,
        earlier ∈ before →
          coords = Marking.placeValues N earlier.marking →
            (∃ loop : List N.Transition,
              sample.pref = earlier.pref ++ loop ∧
                NatListLe coords
                  (Marking.placeValues N sample.marking)) ∨
            (∃ loop : List N.Transition,
              earlier.pref = sample.pref ++ loop ∧
                NatListLe (Marking.placeValues N sample.marking)
                  coords)) :
    ContainsPrefixCoordinateGoodPair (before ++ sample :: after) := by
  obtain ⟨earlier, hEarlierMem, hCoordsEq⟩ :=
    exists_sample_of_mem_greedyPrefixCutSampleCoordinateBasis
      (samples := before) hCoordsMem
  obtain hPrefixLe | hSuffixLe :=
    hOrientedLe earlier hEarlierMem hCoordsEq
  · obtain ⟨loop, hPrefix, hLe⟩ := hPrefixLe
    exact containsPrefixCoordinateGoodPair_of_split_prefix_coordinateLe
      (before := before)
      (after := after)
      (first := earlier)
      (second := sample)
      (loop := loop)
      hEarlierMem
      hPrefix
      (by simpa [hCoordsEq] using hLe)
  · obtain ⟨loop, hPrefix, hLe⟩ := hSuffixLe
    exact containsPrefixCoordinateGoodPair_of_split_second_prefix_coordinateLe
      (before := before)
      (after := after)
      (first := sample)
      (second := earlier)
      (loop := loop)
      hEarlierMem
      hPrefix
      (by simpa [hCoordsEq] using hLe)

end FiringSequence
end Petri
end Pm4Lean
