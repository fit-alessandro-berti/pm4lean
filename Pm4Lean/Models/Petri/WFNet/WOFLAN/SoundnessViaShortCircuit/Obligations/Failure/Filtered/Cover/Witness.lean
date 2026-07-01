import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.Negation

namespace Pm4Lean
namespace Petri

theorem exists_retained_noPredecessorGreedyCoordinate_not_dominated_of_not_woflanNoPredecessorGreedyCoordinateProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateProofObligations W)
    (coordinates : List (List Nat)) :
    ∃ ts : List W.net.Transition,
      ∃ Mend : W.Marking,
        ∃ _hSeq : FiringSequence W.net W.initial ts Mend,
          ∃ samples :
            List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
            FiringSequence.PrefixCutsCoveredBySamples samples ∧
              ∃ coords : List Nat,
                coords ∈ natListGreedyBasis
                  (FiringSequence.prefixCutNoPredecessorSampleCoordinateLists
                    samples) ∧
                ¬ NatListDominatedBy coords coordinates := by
  exact
    exists_retained_noPredecessorGreedyCoordinate_not_dominated_of_not_cover
      (fun hCover => hNotObligations ⟨hCover⟩)
      coordinates

theorem exists_retained_noPredecessorGreedyCoordinate_greaterWitness_of_not_woflanNoPredecessorGreedyCoordinateProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateProofObligations W)
    (coordinates : List (List Nat))
    (hCoordinatesLength :
      ∀ upper : List Nat, upper ∈ coordinates →
        upper.length = W.net.places.length) :
    ∃ ts : List W.net.Transition,
      ∃ Mend : W.Marking,
        ∃ _hSeq : FiringSequence W.net W.initial ts Mend,
          ∃ samples :
            List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
            FiringSequence.PrefixCutsCoveredBySamples samples ∧
              ∃ coords : List Nat,
                coords ∈ natListGreedyBasis
                  (FiringSequence.prefixCutNoPredecessorSampleCoordinateLists
                    samples) ∧
                NatListBasisHasGreaterCoordinateWitness
                  coords coordinates := by
  exact
    exists_retained_noPredecessorGreedyCoordinate_greaterWitness_of_not_cover
      (fun hCover => hNotObligations ⟨hCover⟩)
      coordinates
      hCoordinatesLength

end Petri
end Pm4Lean
