import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.LargeTokenSum

namespace Pm4Lean
namespace Petri

/--
There are concrete original-net firing sequences longer than every numeric
bound.  This is the run-length form needed before extracting repeated or
comparable cuts from one long run.
-/
def ArbitrarilyLongFiringSequences (W : WFNet) : Prop :=
  ∀ n : Nat, ∃ ts : List W.net.Transition,
    ∃ M : W.Marking,
      FiringSequence W.net W.initial ts M ∧ n < ts.length

theorem arbitrarilyLongFiringSequences_of_tokenSum
    {W : WFNet}
    (hLarge : ArbitrarilyLargeFiringSequenceTokenSum W) :
    ArbitrarilyLongFiringSequences W := by
  intro n
  let c := TransitionPostTokenBound W.net
  let initialSum := Marking.TokenSumOn W.net.places W.initial
  obtain ⟨ts, M, hSeq, hLargeSum⟩ :=
    hLarge (initialSum + n * c)
  exact ⟨ts, M, hSeq,
    length_gt_of_tokenSum_gt_initial_add_post_bound
      (N := W.net) (M := W.initial) (M' := M)
      (ts := ts) (n := n) (c := c)
      (post_tokenSum_le_transitionPostTokenBound W.net)
      hSeq
      (by simpa [initialSum] using hLargeSum)⟩

theorem arbitrarilyLongFiringSequences_of_large_marking
    {W : WFNet}
    (hLarge : ArbitrarilyLargeFiringSequenceMarking W) :
    ArbitrarilyLongFiringSequences W :=
  arbitrarilyLongFiringSequences_of_tokenSum
    (arbitrarilyLargeFiringSequenceTokenSum_of_marking hLarge)

/--
The remaining finite/Dickson extraction boundary after the checked
large-marking-to-long-run bridge: arbitrarily long concrete runs contain two
comparable cuts in one factored run.
-/
def LongRunsProduceComparableCutsInRun (W : WFNet) : Prop :=
  ArbitrarilyLongFiringSequences W → ComparableCutsInRun W

def LongRunsProduceComparableCutTrace (W : WFNet) : Prop :=
  ArbitrarilyLongFiringSequences W → ComparableCutTrace W

theorem largeSequencesProduceComparableCutsInRun_of_longRuns
    {W : WFNet}
    (hExtract : LongRunsProduceComparableCutsInRun W) :
    LargeSequencesProduceComparableCutsInRun W := by
  intro hLarge
  exact hExtract (arbitrarilyLongFiringSequences_of_large_marking hLarge)

end Petri
end Pm4Lean
