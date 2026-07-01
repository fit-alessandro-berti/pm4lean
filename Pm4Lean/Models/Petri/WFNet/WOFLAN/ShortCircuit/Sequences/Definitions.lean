import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Basic

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

def ShortCircuitTransition.ofOriginalList :
    List W.net.Transition → List (ShortCircuitTransition W)
  | [] => []
  | t :: ts =>
      ShortCircuitTransition.original t ::
        ShortCircuitTransition.ofOriginalList ts

def ContainsReturn (ts : List (ShortCircuitTransition W)) : Prop :=
  ShortCircuitTransition.returnTransition ∈ ts

def NoReturn (ts : List (ShortCircuitTransition W)) : Prop :=
  ¬ ContainsReturn W ts

def ShortCircuitTransition.toOriginal? :
    ShortCircuitTransition W → Option W.net.Transition
  | Sum.inl t => some t
  | Sum.inr () => none

def ShortCircuitTransition.originalOfNoReturnSequence
    (ts : List (ShortCircuitTransition W)) : List W.net.Transition :=
  ts.filterMap (ShortCircuitTransition.toOriginal? W)

theorem ofOriginalList_noReturn (ts : List W.net.Transition) :
    NoReturn W (ShortCircuitTransition.ofOriginalList W ts) := by
  induction ts with
  | nil =>
      simp [NoReturn, ContainsReturn, ShortCircuitTransition.ofOriginalList]
  | cons t ts ih =>
      simpa [NoReturn, ContainsReturn, ShortCircuitTransition.ofOriginalList,
        ShortCircuitTransition.original, ShortCircuitTransition.returnTransition] using ih

end shortCircuit

end Petri
end Pm4Lean
