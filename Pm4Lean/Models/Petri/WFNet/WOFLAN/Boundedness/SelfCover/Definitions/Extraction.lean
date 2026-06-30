import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Definitions.Covers

namespace Pm4Lean
namespace Petri

def UnboundedOriginalProducesSelfCover (W : WFNet) : Prop :=
  ¬ TokenBoundedReachableOriginal W → ReachableSelfCover W

def UnboundedOriginalProducesFiringSequenceSelfCover (W : WFNet) : Prop :=
  ¬ TokenBoundedReachableOriginal W → FiringSequenceSelfCover W

/--
Unboundedness expressed with concrete firing-sequence witnesses: every numeric
bound is exceeded at some place by a marking reached by a concrete sequence.
-/
def ArbitrarilyLargeFiringSequenceMarking (W : WFNet) : Prop :=
  ∀ k : Nat, ∃ ts : List W.net.Transition,
    ∃ M : W.Marking,
      FiringSequence W.net W.initial ts M ∧
        ∃ p : W.net.Place, k < M p

def LargeSequencesProduceFiringSequenceSelfCover (W : WFNet) : Prop :=
  ArbitrarilyLargeFiringSequenceMarking W → FiringSequenceSelfCover W

def LargeSequencesProduceCutSelfCover (W : WFNet) : Prop :=
  ArbitrarilyLargeFiringSequenceMarking W → CutSelfCover W

def LargeSequencesProduceFactoredRunCutSelfCover (W : WFNet) : Prop :=
  ArbitrarilyLargeFiringSequenceMarking W → FactoredRunCutSelfCover W

def LargeSequencesProduceLocalFactoredRunCutSelfCover (W : WFNet) : Prop :=
  ArbitrarilyLargeFiringSequenceMarking W → LocalFactoredRunCutSelfCover W

def LargeSequencesProduceComparableCutsInRun (W : WFNet) : Prop :=
  ArbitrarilyLargeFiringSequenceMarking W → ComparableCutsInRun W

/--
The constructive witness expected from enumerating cuts of one concrete run.
It is the local factored-run self-cover shape, named here for the final
finite/Dickson extraction layer.
-/
abbrev ComparableCutTrace (W : WFNet) : Prop :=
  LocalFactoredRunCutSelfCover W

end Petri
end Pm4Lean
