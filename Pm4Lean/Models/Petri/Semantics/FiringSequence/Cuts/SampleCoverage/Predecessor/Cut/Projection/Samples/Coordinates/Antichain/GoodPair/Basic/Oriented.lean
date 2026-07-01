import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Antichain.GoodPair.Basic.Definition

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem containsPrefixCoordinateGoodPair_of_oriented_comparable_coordinateLe
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {first second : PrefixCutSample N M₀ ts Mend}
    (hFirstMem : first ∈ samples)
    (hSecondMem : second ∈ samples)
    (hComparableLe :
      (∃ loop : List N.Transition,
        second.pref = first.pref ++ loop ∧
          NatListLe (Marking.placeValues N first.marking)
            (Marking.placeValues N second.marking)) ∨
      (∃ loop : List N.Transition,
        first.pref = second.pref ++ loop ∧
          NatListLe (Marking.placeValues N second.marking)
            (Marking.placeValues N first.marking))) :
    ContainsPrefixCoordinateGoodPair samples := by
  obtain ⟨loop, hPrefix, hLe⟩ | ⟨loop, hPrefix, hLe⟩ := hComparableLe
  · exact containsPrefixCoordinateGoodPair_of_prefix_coordinateLe
      hFirstMem hSecondMem hPrefix hLe
  · exact containsPrefixCoordinateGoodPair_of_prefix_coordinateLe
      hSecondMem hFirstMem hPrefix hLe

end FiringSequence
end Petri
end Pm4Lean
