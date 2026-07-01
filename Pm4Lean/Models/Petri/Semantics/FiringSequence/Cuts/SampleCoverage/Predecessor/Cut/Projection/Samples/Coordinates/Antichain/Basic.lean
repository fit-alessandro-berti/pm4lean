import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Antichain
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem marking_eq_of_no_comparablePrefixCutPredecessor_of_coordinateLe
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hNoPredecessor : ¬ HasComparablePrefixCutPredecessor second)
    (hPrefix : second.pref = first.pref ++ loop)
    (hLe :
      NatListLe (Marking.placeValues N first.marking)
        (Marking.placeValues N second.marking)) :
    first.marking = second.marking :=
  marking_eq_of_no_comparablePrefixCutPredecessor
    hNoPredecessor hPrefix
    (Marking.le_of_placeValues_le hLe)

theorem not_strictPrefix_coordinateLe_of_no_comparablePrefixCutPredecessor
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hNoPredecessor : ¬ HasComparablePrefixCutPredecessor second)
    (hPrefix : second.pref = first.pref ++ loop)
    (hLe :
      NatListLe (Marking.placeValues N first.marking)
        (Marking.placeValues N second.marking))
    (hNe : first.marking ≠ second.marking) :
    False :=
  hNe
    (marking_eq_of_no_comparablePrefixCutPredecessor_of_coordinateLe
      hNoPredecessor hPrefix hLe)

end FiringSequence
end Petri
end Pm4Lean
