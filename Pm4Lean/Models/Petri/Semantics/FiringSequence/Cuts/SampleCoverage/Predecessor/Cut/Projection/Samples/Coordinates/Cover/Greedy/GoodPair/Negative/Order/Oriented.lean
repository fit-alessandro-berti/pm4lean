import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.GoodPair.Negative.Order.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem not_oriented_coordinateLe_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_before
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hNoPair :
      ¬ ContainsPrefixCoordinateGoodPair (before ++ sample :: after))
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before)) :
    ∀ earlier : PrefixCutSample N M₀ ts Mend,
      earlier ∈ before →
        coords = Marking.placeValues N earlier.marking →
          ¬ ((∃ loop : List N.Transition,
                sample.pref = earlier.pref ++ loop ∧
                  NatListLe coords
                    (Marking.placeValues N sample.marking)) ∨
              (∃ loop : List N.Transition,
                earlier.pref = sample.pref ++ loop ∧
                  NatListLe (Marking.placeValues N sample.marking)
                    coords)) := by
  have _hRecovered :
      ∃ earlier : PrefixCutSample N M₀ ts Mend,
        earlier ∈ before ∧
          coords = Marking.placeValues N earlier.marking :=
    exists_sample_of_mem_greedyPrefixCutSampleCoordinateBasis
      (samples := before) hCoordsMem
  intro earlier hEarlierMem hCoordsEq hOriented
  apply
    not_oriented_coordinateLe_of_no_split_prefixCoordinateGoodPair
      (before := before)
      (after := after)
      (first := earlier)
      (second := sample)
      hNoPair
      hEarlierMem
  obtain ⟨loop, hPrefix, hLe⟩ | ⟨loop, hPrefix, hLe⟩ := hOriented
  · exact Or.inl ⟨loop, hPrefix, by simpa [hCoordsEq] using hLe⟩
  · exact Or.inr ⟨loop, hPrefix, by simpa [hCoordsEq] using hLe⟩

theorem hasGreaterCoordinate_or_hasGreaterCoordinate_of_no_prefixCoordinateGoodPair_greedyPrefixCutSampleCoordinateBasis_before
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hNoPair :
      ¬ ContainsPrefixCoordinateGoodPair (before ++ sample :: after))
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before)) :
    NatListHasGreaterCoordinate coords
        (Marking.placeValues N sample.marking) ∨
      NatListHasGreaterCoordinate
        (Marking.placeValues N sample.marking) coords := by
  obtain ⟨earlier, hEarlierMem, hCoordsEq⟩ :=
    exists_sample_of_mem_greedyPrefixCutSampleCoordinateBasis
      (samples := before) hCoordsMem
  obtain hGt | hGt :=
    hasGreaterCoordinate_or_hasGreaterCoordinate_of_no_split_prefixCoordinateGoodPair
      (before := before)
      (after := after)
      (first := earlier)
      (second := sample)
      hNoPair
      hEarlierMem
  · exact Or.inl (by simpa [hCoordsEq] using hGt)
  · exact Or.inr (by simpa [hCoordsEq] using hGt)

end FiringSequence
end Petri
end Pm4Lean
