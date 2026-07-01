import Pm4Lean.Models.Petri.Basic.Marking.Coordinates.Box.Finiteness
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem sampleMarkings_forall_le_of_samples_forall_le
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hBound :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ∀ p : N.Place, sample.marking p ≤ k) :
    ∀ M : N.Marking,
      M ∈ prefixCutSampleMarkings samples → ∀ p : N.Place, M p ≤ k := by
  intro M hMem p
  rw [prefixCutSampleMarkings, List.mem_map] at hMem
  obtain ⟨sample, hSampleMem, hEq⟩ := hMem
  subst M
  exact hBound sample hSampleMem p

theorem length_le_natListsUpTo_length_of_nodup_sampleMarkings_forall_le
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hNodup : (prefixCutSampleMarkings samples).Nodup)
    (hBound :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ∀ p : N.Place, sample.marking p ≤ k) :
    samples.length ≤ (NatListsUpTo N.places.length k).length := by
  have hMarkings :=
    Marking.length_le_natListsUpTo_length_of_nodup_markings_forall_le
      (N := N)
      (markings := prefixCutSampleMarkings samples)
      hNodup
      (sampleMarkings_forall_le_of_samples_forall_le hBound)
  simpa [prefixCutSampleMarkings, List.length_map] using hMarkings

theorem not_nodup_sampleMarkings_of_length_gt_natListsUpTo_length
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < samples.length)
    (hBound :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ∀ p : N.Place, sample.marking p ≤ k) :
    ¬ (prefixCutSampleMarkings samples).Nodup := by
  intro hNodup
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_nodup_sampleMarkings_forall_le
      hNodup hBound)
    hLength

theorem length_le_natListsUpTo_length_of_nodup_noPredecessorSamples
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hNodup : (prefixCutSampleMarkings samples).Nodup)
    (hNoPredecessor :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ¬ HasComparablePrefixCutPredecessor sample)
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    samples.length ≤ (NatListsUpTo N.places.length k).length :=
  length_le_natListsUpTo_length_of_nodup_sampleMarkings_forall_le
    hNodup
    (fun sample hSampleMem =>
      hBounded sample hSampleMem
        (hNoPredecessor sample hSampleMem))

theorem not_nodup_noPredecessorSampleMarkings_of_length_gt_natListsUpTo_length
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < samples.length)
    (hNoPredecessor :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ¬ HasComparablePrefixCutPredecessor sample)
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    ¬ (prefixCutSampleMarkings samples).Nodup := by
  intro hNodup
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_nodup_noPredecessorSamples
      hNodup hNoPredecessor hBounded)
    hLength

theorem hasDuplicate_noPredecessorSampleMarkings_of_length_gt_natListsUpTo_length
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < samples.length)
    (hNoPredecessor :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ¬ HasComparablePrefixCutPredecessor sample)
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    List.HasDuplicate (prefixCutSampleMarkings samples) :=
  Pm4Lean.List.hasDuplicate_of_not_nodup
    (not_nodup_noPredecessorSampleMarkings_of_length_gt_natListsUpTo_length
      hLength hNoPredecessor hBounded)

end FiringSequence
end Petri
end Pm4Lean
