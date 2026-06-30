import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.ExtraFinalCover

namespace Pm4Lean
namespace Petri

/--
An extra final-cover marking can be pumped linearly at a fixed place.  This is
the concrete repeated-growth obligation needed for the full WOFLAN
boundedness contradiction.
-/
def ExtraFinalCoverLinearPumpAt
    (W : WFNet) (M : W.Marking) (p : W.net.Place) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat, ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧ n ≤ M' p

/--
The repeated-return accumulation obligation for an extra final-cover marking:
after `n` cycles, the selected place carries at least its initial tokens plus
`n` copies of the extra remainder left by the return transition.
-/
def ExtraFinalCoverAccumulatedGrowthAt
    (W : WFNet) (M : W.Marking) (p : W.net.Place) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat, ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧
        W.initial p + n * (M p - W.final p) ≤ M' p

/--
Closed-form version of the repeated-return target: the short-circuited net can
reach the initial marking plus `n` copies of the extra remainder.
-/
def ExtraFinalCoverClosedFormGrowth (W : WFNet) (M : W.Marking) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat,
      Reachable (shortCircuit W) W.initial
        (W.initial + Marking.scale n (M - W.final))

/--
Stepwise version of closed-form growth: each accumulated marking can reach the
next accumulated marking.
-/
def ExtraFinalCoverClosedFormStep (W : WFNet) (M : W.Marking) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat,
      Reachable (shortCircuit W)
        (W.initial + Marking.scale n (M - W.final))
        (W.initial + Marking.scale (n + 1) (M - W.final))

/--
An operational plan for proving accumulated growth: provide a Nat-indexed
chain of short-circuit reachable cycles, starting at the initial marking, whose
token count at `p` grows by the extra remainder.
-/
def ExtraFinalCoverAccumulationPlanAt
    (W : WFNet) (M : W.Marking) (p : W.net.Place) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∃ F : Nat → W.Marking,
      F 0 = W.initial ∧
        (∀ n : Nat,
          Reachable (shortCircuit W) (F n) (F (n + 1))) ∧
        ∀ n : Nat,
          W.initial p + n * (M p - W.final p) ≤ F n p

end Petri
end Pm4Lean
