import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Antichain.GoodPair.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem not_coordinateLe_of_no_split_prefixCoordinateGoodPair
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hNoPair :
      ¬ ContainsPrefixCoordinateGoodPair (before ++ second :: after))
    (hFirstMem : first ∈ before)
    (hPrefix : second.pref = first.pref ++ loop) :
    ¬ NatListLe (Marking.placeValues N first.marking)
      (Marking.placeValues N second.marking) := by
  intro hLe
  exact hNoPair
    (containsPrefixCoordinateGoodPair_of_split_prefix_coordinateLe
      (before := before)
      (after := after)
      (first := first)
      (second := second)
      (loop := loop)
      hFirstMem
      hPrefix
      hLe)

theorem not_coordinateLe_of_no_split_second_prefixCoordinateGoodPair
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hNoPair :
      ¬ ContainsPrefixCoordinateGoodPair (before ++ first :: after))
    (hSecondMem : second ∈ before)
    (hPrefix : second.pref = first.pref ++ loop) :
    ¬ NatListLe (Marking.placeValues N first.marking)
      (Marking.placeValues N second.marking) := by
  intro hLe
  exact hNoPair
    (containsPrefixCoordinateGoodPair_of_split_second_prefix_coordinateLe
      (before := before)
      (after := after)
      (first := first)
      (second := second)
      (loop := loop)
      hSecondMem
      hPrefix
      hLe)

theorem not_oriented_coordinateLe_of_no_split_prefixCoordinateGoodPair
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {first second : PrefixCutSample N M₀ ts Mend}
    (hNoPair :
      ¬ ContainsPrefixCoordinateGoodPair (before ++ second :: after))
    (hFirstMem : first ∈ before) :
    ¬ ((∃ loop : List N.Transition,
          second.pref = first.pref ++ loop ∧
            NatListLe (Marking.placeValues N first.marking)
              (Marking.placeValues N second.marking)) ∨
        (∃ loop : List N.Transition,
          first.pref = second.pref ++ loop ∧
            NatListLe (Marking.placeValues N second.marking)
              (Marking.placeValues N first.marking))) := by
  intro hOriented
  obtain ⟨loop, hPrefix, hLe⟩ | ⟨loop, hPrefix, hLe⟩ := hOriented
  · exact
      not_coordinateLe_of_no_split_prefixCoordinateGoodPair
        (before := before)
        (after := after)
        (first := first)
        (second := second)
        (loop := loop)
        hNoPair
        hFirstMem
        hPrefix
        hLe
  · exact
      not_coordinateLe_of_no_split_second_prefixCoordinateGoodPair
        (before := before)
        (after := after)
        (first := second)
        (second := first)
        (loop := loop)
        hNoPair
        hFirstMem
        hPrefix
        hLe

end FiringSequence
end Petri
end Pm4Lean
