import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.Membership.Insert

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem mem_greedyPrefixCutSampleCoordinateBasis_of_mem
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists samples)) :
    coords ∈ prefixCutSampleCoordinateLists samples :=
  mem_natListGreedyBasis hMem

theorem exists_sample_of_mem_greedyPrefixCutSampleCoordinateBasis
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists samples)) :
    ∃ sample : PrefixCutSample N M₀ ts Mend,
      sample ∈ samples ∧ coords = Marking.placeValues N sample.marking :=
  exists_sample_of_mem_prefixCutSampleCoordinateLists
    (mem_greedyPrefixCutSampleCoordinateBasis_of_mem hMem)

theorem greedyPrefixCutSampleCoordinateBasis_length_of_mem
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists samples)) :
    coords.length = N.places.length :=
  prefixCutSampleCoordinateLists_length_of_mem
    (mem_greedyPrefixCutSampleCoordinateBasis_of_mem hMem)

theorem natListHasGreaterCoordinate_of_mem_greedyPrefixCutSampleCoordinateBasis_before_of_not_dominated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before))
    (hNotDominated :
      ¬ NatListDominatedBy
        (Marking.placeValues N sample.marking)
        (natListGreedyBasis (prefixCutSampleCoordinateLists before))) :
    NatListHasGreaterCoordinate
      (Marking.placeValues N sample.marking) coords :=
  natListHasGreaterCoordinate_of_mem_greedyBasisFrom_of_not_dominated
    (pre := prefixCutSampleCoordinateLists before)
    (basis := [])
    hCoordsMem
    (by
      rw [sample_placeValues_length sample,
        greedyPrefixCutSampleCoordinateBasis_length_of_mem hCoordsMem])
    hNotDominated

theorem mem_and_hasGreaterCoordinate_of_greedyPrefixCutSampleCoordinateBasis_split_not_dominated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists before))
    (hNotDominated :
      ¬ NatListDominatedBy
        (Marking.placeValues N sample.marking)
        (natListGreedyBasis (prefixCutSampleCoordinateLists before))) :
    Marking.placeValues N sample.marking ∈
        natListGreedyBasis
          (prefixCutSampleCoordinateLists (before ++ sample :: after)) ∧
      NatListHasGreaterCoordinate
        (Marking.placeValues N sample.marking) coords :=
  ⟨mem_greedyBasisFrom_prefixCutSampleCoordinateLists_append_cons_self_of_not_dominated
      (before := before) (after := after) (coordinates := [])
      hNotDominated,
    natListHasGreaterCoordinate_of_mem_greedyPrefixCutSampleCoordinateBasis_before_of_not_dominated
      hCoordsMem hNotDominated⟩

end FiringSequence
end Petri
end Pm4Lean
