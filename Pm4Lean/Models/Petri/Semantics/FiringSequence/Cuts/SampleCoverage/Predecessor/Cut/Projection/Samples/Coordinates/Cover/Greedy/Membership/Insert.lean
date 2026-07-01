import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Length
import Pm4Lean.Util.NatListBasis

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem mem_greedyBasisFrom_prefixCutSampleCoordinateLists_cons_self_of_not_dominated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coordinates : List (List Nat)}
    (hNotDominated :
      ¬ NatListDominatedBy
        (Marking.placeValues N sample.marking) coordinates) :
    Marking.placeValues N sample.marking ∈
      natListGreedyBasisFrom
        (prefixCutSampleCoordinateLists (sample :: samples))
        coordinates := by
  simpa [prefixCutSampleCoordinateLists] using
    mem_natListGreedyBasisFrom_cons_self_of_not_dominated
      (x := Marking.placeValues N sample.marking)
      (xs := prefixCutSampleCoordinateLists samples)
      (basis := coordinates)
      hNotDominated

theorem mem_greedyBasisFrom_prefixCutSampleCoordinateLists_append_cons_self_of_not_dominated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {sample : PrefixCutSample N M₀ ts Mend}
    {before after : List (PrefixCutSample N M₀ ts Mend)}
    {coordinates : List (List Nat)}
    (hNotDominated :
      ¬ NatListDominatedBy
        (Marking.placeValues N sample.marking)
        (natListGreedyBasisFrom
          (prefixCutSampleCoordinateLists before)
          coordinates)) :
    Marking.placeValues N sample.marking ∈
      natListGreedyBasisFrom
        (prefixCutSampleCoordinateLists (before ++ sample :: after))
        coordinates := by
  simpa [prefixCutSampleCoordinateLists, List.map_append] using
    mem_natListGreedyBasisFrom_append_cons_self_of_not_dominated
      (pre := prefixCutSampleCoordinateLists before)
      (suffix := prefixCutSampleCoordinateLists after)
      (basis := coordinates)
      (x := Marking.placeValues N sample.marking)
      hNotDominated

end FiringSequence
end Petri
end Pm4Lean
