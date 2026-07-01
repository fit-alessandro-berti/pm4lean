import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Antichain.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def ContainsPrefixCoordinateGoodPair
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) : Prop :=
  ∃ first second : PrefixCutSample N M₀ ts Mend,
    ∃ loop : List N.Transition,
      first ∈ samples ∧
        second ∈ samples ∧
          second.pref = first.pref ++ loop ∧
            NatListLe (Marking.placeValues N first.marking)
              (Marking.placeValues N second.marking)

theorem containsPrefixCoordinateGoodPair_of_prefix_coordinateLe
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hFirstMem : first ∈ samples)
    (hSecondMem : second ∈ samples)
    (hPrefix : second.pref = first.pref ++ loop)
    (hLe :
      NatListLe (Marking.placeValues N first.marking)
        (Marking.placeValues N second.marking)) :
    ContainsPrefixCoordinateGoodPair samples :=
  ⟨first, second, loop, hFirstMem, hSecondMem, hPrefix, hLe⟩

end FiringSequence
end Petri
end Pm4Lean
