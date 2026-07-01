import Pm4Lean.Models.Petri.Basic.Marking.Coordinates.Reconstruction
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples
import Pm4Lean.Util.NatListBasis

namespace Pm4Lean
namespace Petri

namespace FiringSequence

/-- Prefix-cut sample markings read as finite coordinate vectors over `N.places`. -/
def prefixCutSampleCoordinateLists
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) : List (List Nat) :=
  samples.map (fun sample => Marking.placeValues N sample.marking)

def NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend))
    (coordinates : List (List Nat)) : Prop :=
  ∀ sample : PrefixCutSample N M₀ ts Mend,
    sample ∈ samples →
      ¬ HasComparablePrefixCutPredecessor sample →
        ∃ coords : List Nat,
          coords ∈ coordinates ∧
            NatListLe (Marking.placeValues N sample.marking) coords

theorem mem_prefixCutSampleCoordinateLists_of_mem
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {sample : PrefixCutSample N M₀ ts Mend}
    (hMem : sample ∈ samples) :
    Marking.placeValues N sample.marking ∈
      prefixCutSampleCoordinateLists samples := by
  simp [prefixCutSampleCoordinateLists]
  exact ⟨sample, hMem, rfl⟩

theorem exists_sample_of_mem_prefixCutSampleCoordinateLists
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hMem : coords ∈ prefixCutSampleCoordinateLists samples) :
    ∃ sample : PrefixCutSample N M₀ ts Mend,
      sample ∈ samples ∧ coords = Marking.placeValues N sample.marking := by
  rw [prefixCutSampleCoordinateLists, List.mem_map] at hMem
  obtain ⟨sample, hSampleMem, hEq⟩ := hMem
  exact ⟨sample, hSampleMem, hEq.symm⟩

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_sampleCoordinates
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
      (prefixCutSampleCoordinateLists samples) := by
  intro sample hSampleMem _hNoPredecessor
  exact ⟨Marking.placeValues N sample.marking,
    mem_prefixCutSampleCoordinateLists_of_mem hSampleMem,
    natListLe_refl (Marking.placeValues N sample.marking)⟩

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_iff_dominatedBy
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coordinates : List (List Nat)} :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
      samples coordinates ↔
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples →
          ¬ HasComparablePrefixCutPredecessor sample →
            NatListDominatedBy
              (Marking.placeValues N sample.marking) coordinates := by
  constructor
  · intro hCovered sample hSampleMem hNoPredecessor
    obtain ⟨coords, hMem, hLe⟩ :=
      hCovered sample hSampleMem hNoPredecessor
    exact natListDominatedBy_of_mem_le hMem hLe
  · intro hCovered sample hSampleMem hNoPredecessor
    exact hCovered sample hSampleMem hNoPredecessor

end FiringSequence
end Petri
end Pm4Lean
