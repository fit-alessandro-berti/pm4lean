import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Growth

namespace Pm4Lean
namespace Petri

/--
An extra final-cover marking can be pumped in the short-circuited net past
every proposed global token bound.
-/
def ExtraFinalCoverPumpsAboveEveryBound (W : WFNet) (M : W.Marking) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ k : Nat, ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧
        ∃ p : W.net.Place, k < M' p

end Petri
end Pm4Lean
