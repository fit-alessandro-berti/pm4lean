import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.DominatedBy.NotDominated

namespace Pm4Lean
namespace Petri

theorem exists_retained_noPredecessorGreedyCoordinate_greaterWitness_of_not_dominatedBy
    {W : WFNet} {coordinates : List (List Nat)}
    (hCoordinatesLength :
      ∀ upper : List Nat, upper ∈ coordinates →
        upper.length = W.net.places.length)
    (hNotDominated :
      ¬ LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
        W coordinates) :
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
  obtain ⟨ts, Mend, hSeq, samples, hCovered,
      coords, hCoordsMem, hNotDominatedCoords⟩ :=
    exists_retained_noPredecessorGreedyCoordinate_not_dominated_of_not_dominatedBy
      hNotDominated
  exact ⟨ts, Mend, hSeq, samples, hCovered,
    coords, hCoordsMem,
    natListBasisHasGreaterCoordinateWitness_of_not_dominated_length_eq
      (FiringSequence.greedyPrefixCutNoPredecessorSampleCoordinateBasis_length_of_mem
        hCoordsMem)
      hCoordinatesLength
      hNotDominatedCoords⟩

end Petri
end Pm4Lean
