import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Prefix.Cycle
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Antichain.GoodPair.Negative.Order

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem hasGreaterCoordinate_or_hasGreaterCoordinate_of_no_split_prefixCoordinateGoodPair
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {first second : PrefixCutSample N M₀ ts Mend}
    (hNoPair :
      ¬ ContainsPrefixCoordinateGoodPair (before ++ second :: after))
    (hFirstMem : first ∈ before) :
    NatListHasGreaterCoordinate
        (Marking.placeValues N first.marking)
        (Marking.placeValues N second.marking) ∨
      NatListHasGreaterCoordinate
        (Marking.placeValues N second.marking)
        (Marking.placeValues N first.marking) := by
  obtain ⟨loop, hPrefix⟩ | ⟨loop, hPrefix⟩ :=
    prefixCutSamples_prefix_comparable first second
  · exact Or.inl
      (natListHasGreaterCoordinate_of_not_natListLe
        (by
          rw [Marking.placeValues_length,
            Marking.placeValues_length])
        (not_coordinateLe_of_no_split_prefixCoordinateGoodPair
          (before := before)
          (after := after)
          (first := first)
          (second := second)
          (loop := loop)
          hNoPair
          hFirstMem
          hPrefix))
  · exact Or.inr
      (natListHasGreaterCoordinate_of_not_natListLe
        (by
          rw [Marking.placeValues_length,
            Marking.placeValues_length])
        (not_coordinateLe_of_no_split_second_prefixCoordinateGoodPair
          (before := before)
          (after := after)
          (first := second)
          (second := first)
          (loop := loop)
          hNoPair
          hFirstMem
          hPrefix))

end FiringSequence
end Petri
end Pm4Lean
