import Pm4Lean.Models.Petri.Basic.Marking.Coordinates.Box
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_boundedBox
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
      (NatListsUpTo N.places.length k) := by
  intro sample hSampleMem hNoPredecessor
  exact ⟨Marking.placeValues N sample.marking,
    Marking.placeValues_mem_natListsUpTo_of_forall_le
      (hBounded sample hSampleMem hNoPredecessor),
    natListLe_refl (Marking.placeValues N sample.marking)⟩

end FiringSequence
end Petri
end Pm4Lean
