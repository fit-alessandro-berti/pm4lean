import Pm4Lean.Models.Petri.Basic.Net

namespace Pm4Lean
namespace Petri

/-- A transition is enabled when the current marking covers its precondition. -/
def Enabled (N : Net) (M : N.Marking) (t : N.Transition) : Prop :=
  N.pre t ≤ M

theorem enabled_iff_pre_le {N : Net} {M : N.Marking} {t : N.Transition} :
    Enabled N M t ↔ N.pre t ≤ M := Iff.rfl

end Petri
end Pm4Lean
