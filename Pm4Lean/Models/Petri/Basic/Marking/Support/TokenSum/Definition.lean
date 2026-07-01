import Pm4Lean.Models.Petri.Basic.Marking

namespace Pm4Lean
namespace Petri

namespace Marking

variable {Place : Type u}

/-- Sum the tokens of a marking over a finite list of places. -/
def TokenSumOn (places : List Place) (M : Marking Place) : Nat :=
  places.foldl (fun acc p => acc + M p) 0

theorem tokenSumOn_nil (M : Marking Place) :
    TokenSumOn [] M = 0 :=
  rfl

theorem tokenSumOn_singleton (p : Place) (M : Marking Place) :
    TokenSumOn [p] M = M p := by
  simp [TokenSumOn]

end Marking
end Petri
end Pm4Lean
