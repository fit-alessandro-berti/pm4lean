import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Antichain.GoodPair
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.Membership

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem containsPrefixCoordinateGoodPair_of_greedyPrefixCutSampleCoordinateBasis_before_prefix_le
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before))
    (hPrefixLe :
      ∀ first : PrefixCutSample N M₀ ts Mend,
        first ∈ before →
          coords = Marking.placeValues N first.marking →
            ∃ loop : List N.Transition,
              sample.pref = first.pref ++ loop ∧
                NatListLe coords
                  (Marking.placeValues N sample.marking)) :
    ContainsPrefixCoordinateGoodPair (before ++ sample :: after) := by
  obtain ⟨first, hFirstMem, hCoordsEq⟩ :=
    exists_sample_of_mem_greedyPrefixCutSampleCoordinateBasis
      (samples := before) hCoordsMem
  obtain ⟨loop, hPrefix, hLe⟩ := hPrefixLe first hFirstMem hCoordsEq
  exact containsPrefixCoordinateGoodPair_of_split_prefix_coordinateLe
    (before := before)
    (after := after)
    (first := first)
    (second := sample)
    (loop := loop)
    hFirstMem
    hPrefix
    (by simpa [hCoordsEq] using hLe)

end FiringSequence
end Petri
end Pm4Lean
