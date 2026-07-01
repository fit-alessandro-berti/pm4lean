import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Finiteness

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def HasRepeatedPrefixCutSampleMarking
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking} :
    List (PrefixCutSample N M₀ ts Mend) → Prop
  | [] => False
  | sample :: samples =>
      sample.marking ∈ prefixCutSampleMarkings samples ∨
        HasRepeatedPrefixCutSampleMarking samples

def ContainsRepeatedPrefixCutSampleMarkingPair
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) : Prop :=
  ∃ first second : PrefixCutSample N M₀ ts Mend,
    ∃ before between after :
      List (PrefixCutSample N M₀ ts Mend),
      samples = before ++ first :: between ++ second :: after ∧
        first.marking = second.marking

theorem hasRepeatedPrefixCutSampleMarking_of_duplicate_markings
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hDuplicate : List.HasDuplicate (prefixCutSampleMarkings samples)) :
    HasRepeatedPrefixCutSampleMarking samples := by
  induction samples with
  | nil =>
      exact hDuplicate
  | cons sample samples ih =>
      unfold prefixCutSampleMarkings at hDuplicate
      change List.HasDuplicate
        (sample.marking :: prefixCutSampleMarkings samples) at hDuplicate
      unfold HasRepeatedPrefixCutSampleMarking
      exact hDuplicate.elim
        (fun hMem => Or.inl hMem)
        (fun hTail => Or.inr (ih hTail))

theorem hasRepeatedPrefixCutSampleMarking_of_noPredecessor_length_gt
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < samples.length)
    (hNoPredecessor :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ¬ HasComparablePrefixCutPredecessor sample)
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    HasRepeatedPrefixCutSampleMarking samples :=
  hasRepeatedPrefixCutSampleMarking_of_duplicate_markings
    (hasDuplicate_noPredecessorSampleMarkings_of_length_gt_natListsUpTo_length
      hLength hNoPredecessor hBounded)

theorem containsRepeatedPrefixCutSampleMarkingPair_of_repeated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hRepeated : HasRepeatedPrefixCutSampleMarking samples) :
    ContainsRepeatedPrefixCutSampleMarkingPair samples := by
  induction samples with
  | nil =>
      exact False.elim hRepeated
  | cons sample samples ih =>
      unfold HasRepeatedPrefixCutSampleMarking at hRepeated
      cases hRepeated with
      | inl hMem =>
          rw [prefixCutSampleMarkings, List.mem_map] at hMem
          obtain ⟨second, hSecondMem, hEq⟩ := hMem
          obtain ⟨between, after, hSplit⟩ :=
            Pm4Lean.List.exists_split_of_mem hSecondMem
          refine ⟨sample, second, [], between, after, ?_, hEq.symm⟩
          simp [hSplit]
      | inr hTail =>
          obtain ⟨first, second, before, between, after,
            hSplit, hEq⟩ := ih hTail
          refine ⟨first, second, sample :: before, between, after, ?_, hEq⟩
          simp [hSplit]

theorem containsRepeatedPrefixCutSampleMarkingPair_of_noPredecessor_length_gt
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < samples.length)
    (hNoPredecessor :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ¬ HasComparablePrefixCutPredecessor sample)
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    ContainsRepeatedPrefixCutSampleMarkingPair samples :=
  containsRepeatedPrefixCutSampleMarkingPair_of_repeated
    (hasRepeatedPrefixCutSampleMarking_of_noPredecessor_length_gt
      hLength hNoPredecessor hBounded)

end FiringSequence
end Petri
end Pm4Lean
