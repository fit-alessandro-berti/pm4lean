import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_subset
    {W : WFNet} {coordinates coordinates' : List (List Nat)}
    (hSubset : ∀ coords : List Nat, coords ∈ coordinates → coords ∈ coordinates')
    (hCovered :
      LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
        W coordinates) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
      W coordinates' := by
  intro ts Mend hSeq samples hSamplesCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_subset
      hSubset
      (hCovered ts Mend hSeq samples hSamplesCovered)

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_subset
    {W : WFNet} {coordinates coordinates' : List (List Nat)}
    (hSubset : ∀ coords : List Nat, coords ∈ coordinates → coords ∈ coordinates')
    (hCovered :
      LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
        W coordinates) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W :=
  ⟨coordinates',
    largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_subset
      hSubset hCovered⟩

theorem largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_cons
    {W : WFNet} (coords : List Nat) {coordinates : List (List Nat)}
    (hCovered :
      LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
        W coordinates) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
      W (coords :: coordinates) :=
  largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_subset
    (fun _ hMem => by simp [hMem])
    hCovered

theorem largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_append_left
    {W : WFNet} {coordinates extra : List (List Nat)}
    (hCovered :
      LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
        W coordinates) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
      W (coordinates ++ extra) :=
  largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_subset
    (fun _ hMem => List.mem_append_left extra hMem)
    hCovered

theorem largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_append_right
    {W : WFNet} {coordinates extra : List (List Nat)}
    (hCovered :
      LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
        W extra) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
      W (coordinates ++ extra) :=
  largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_subset
    (fun _ hMem => List.mem_append_right coordinates hMem)
    hCovered

end Petri
end Pm4Lean
