import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.GoodPair.Negative.Order.Impossible

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem hasGreaterCoordinate_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_before_prefix
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
    NatListHasGreaterCoordinate coords
      (Marking.placeValues N sample.marking) :=
  natListHasGreaterCoordinate_of_not_natListLe
    (by
      rw [greedyPrefixCutSampleCoordinateBasis_length_of_mem hCoordsMem,
        sample_placeValues_length sample])
    (not_coordinateLe_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_before_prefix
      hNoPair hCoordsMem hPrefix)

theorem hasGreaterCoordinate_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_before_suffix
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
    NatListHasGreaterCoordinate
      (Marking.placeValues N sample.marking) coords :=
  natListHasGreaterCoordinate_of_not_natListLe
    (by
      rw [sample_placeValues_length sample,
        greedyPrefixCutSampleCoordinateBasis_length_of_mem hCoordsMem])
    (not_coordinateLe_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_before_suffix
      hNoPair hCoordsMem hPrefix)

end FiringSequence
end Petri
end Pm4Lean
