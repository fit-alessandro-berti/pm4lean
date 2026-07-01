import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.Basis

namespace Pm4Lean
namespace Petri

theorem not_hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_iff
    {W : WFNet} :
    ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W ↔
      ∀ coordinates : List (List Nat),
        (∀ upper : List Nat, upper ∈ coordinates →
          upper.length = W.net.places.length) →
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
  constructor
  · intro hNotCover coordinates hCoordinatesLength
    exact
      exists_retained_noPredecessorGreedyCoordinate_not_dominated_of_not_dominatedBy
        (fun hDominated =>
          hNotCover ⟨coordinates, hCoordinatesLength, hDominated⟩)
  · intro hCounter hCover
    obtain ⟨coordinates, hCoordinatesLength, hDominated⟩ := hCover
    obtain ⟨ts, Mend, hSeq, samples, hCovered,
        coords, hCoordsMem, hNotDominated⟩ :=
      hCounter coordinates hCoordinatesLength
    exact hNotDominated
      (hDominated ts Mend hSeq samples hCovered coords hCoordsMem)

end Petri
end Pm4Lean
