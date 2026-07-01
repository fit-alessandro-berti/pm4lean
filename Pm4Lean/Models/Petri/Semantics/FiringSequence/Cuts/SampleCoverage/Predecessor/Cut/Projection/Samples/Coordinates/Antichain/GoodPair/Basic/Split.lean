import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Antichain.GoodPair.Basic.Definition

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem containsPrefixCoordinateGoodPair_of_split_prefix_coordinateLe
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hFirstMem : first ∈ before)
    (hPrefix : second.pref = first.pref ++ loop)
    (hLe :
      NatListLe (Marking.placeValues N first.marking)
        (Marking.placeValues N second.marking)) :
    ContainsPrefixCoordinateGoodPair (before ++ second :: after) :=
  containsPrefixCoordinateGoodPair_of_prefix_coordinateLe
    (samples := before ++ second :: after)
    (first := first)
    (second := second)
    (loop := loop)
    (List.mem_append_left (second :: after) hFirstMem)
    (by simp)
    hPrefix
    hLe

theorem containsPrefixCoordinateGoodPair_of_split_second_prefix_coordinateLe
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hSecondMem : second ∈ before)
    (hPrefix : second.pref = first.pref ++ loop)
    (hLe :
      NatListLe (Marking.placeValues N first.marking)
        (Marking.placeValues N second.marking)) :
    ContainsPrefixCoordinateGoodPair (before ++ first :: after) :=
  containsPrefixCoordinateGoodPair_of_prefix_coordinateLe
    (samples := before ++ first :: after)
    (first := first)
    (second := second)
    (loop := loop)
    (by simp)
    (List.mem_append_left (first :: after) hSecondMem)
    hPrefix
    hLe

end FiringSequence
end Petri
end Pm4Lean
