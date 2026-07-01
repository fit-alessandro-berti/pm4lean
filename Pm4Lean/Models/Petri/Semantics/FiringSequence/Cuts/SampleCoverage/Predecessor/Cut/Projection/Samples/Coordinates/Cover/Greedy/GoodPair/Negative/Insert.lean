import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.GoodPair.Negative.Order

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem mem_and_hasGreaterCoordinate_and_or_hasGreaterCoordinate_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_split_not_dominated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hNoPair :
      ¬ ContainsPrefixCoordinateGoodPair (before ++ sample :: after))
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before))
    (hNotDominated :
      ¬ NatListDominatedBy
        (Marking.placeValues N sample.marking)
        (natListGreedyBasis (prefixCutSampleCoordinateLists before))) :
    Marking.placeValues N sample.marking ∈
        natListGreedyBasis
          (prefixCutSampleCoordinateLists (before ++ sample :: after)) ∧
      NatListHasGreaterCoordinate
        (Marking.placeValues N sample.marking) coords ∧
      (NatListHasGreaterCoordinate coords
          (Marking.placeValues N sample.marking) ∨
        NatListHasGreaterCoordinate
          (Marking.placeValues N sample.marking) coords) := by
  obtain ⟨hMem, hSampleGt⟩ :=
    mem_and_hasGreaterCoordinate_of_greedyPrefixCutSampleCoordinateBasis_split_not_dominated
      (before := before)
      (after := after)
      hCoordsMem
      hNotDominated
  exact
    ⟨hMem, hSampleGt,
      hasGreaterCoordinate_or_hasGreaterCoordinate_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_before
        hNoPair
        hCoordsMem⟩

end FiringSequence
end Petri
end Pm4Lean
