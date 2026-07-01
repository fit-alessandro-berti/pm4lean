import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Antichain.GoodPair.Negative
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.Membership

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem not_coordinateLe_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_before_prefix
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    {loop : List N.Transition}
    (hNoPair :
      ¬ ContainsPrefixCoordinateGoodPair (before ++ sample :: after))
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before))
    (hPrefix :
      ∀ first : PrefixCutSample N M₀ ts Mend,
        first ∈ before →
          coords = Marking.placeValues N first.marking →
            sample.pref = first.pref ++ loop) :
    ¬ NatListLe coords (Marking.placeValues N sample.marking) := by
  obtain ⟨first, hFirstMem, hCoordsEq⟩ :=
    exists_sample_of_mem_greedyPrefixCutSampleCoordinateBasis
      (samples := before) hCoordsMem
  intro hLe
  exact
    not_coordinateLe_of_no_split_prefixCoordinateGoodPair
      (before := before)
      (after := after)
      (first := first)
      (second := sample)
      (loop := loop)
      hNoPair
      hFirstMem
      (hPrefix first hFirstMem hCoordsEq)
      (by simpa [hCoordsEq] using hLe)

theorem not_coordinateLe_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_before_suffix
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    {loop : List N.Transition}
    (hNoPair :
      ¬ ContainsPrefixCoordinateGoodPair (before ++ sample :: after))
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before))
    (hPrefix :
      ∀ second : PrefixCutSample N M₀ ts Mend,
        second ∈ before →
          coords = Marking.placeValues N second.marking →
            second.pref = sample.pref ++ loop) :
    ¬ NatListLe (Marking.placeValues N sample.marking) coords := by
  obtain ⟨second, hSecondMem, hCoordsEq⟩ :=
    exists_sample_of_mem_greedyPrefixCutSampleCoordinateBasis
      (samples := before) hCoordsMem
  intro hLe
  exact
    not_coordinateLe_of_no_split_second_prefixCoordinateGoodPair
      (before := before)
      (after := after)
      (first := sample)
      (second := second)
      (loop := loop)
      hNoPair
      hSecondMem
      (hPrefix second hSecondMem hCoordsEq)
      (by simpa [hCoordsEq] using hLe)

end FiringSequence
end Petri
end Pm4Lean
