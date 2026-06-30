import Pm4Lean.Models.Petri.Semantics.Fire

namespace Pm4Lean
namespace Petri

/-- One operational Petri-net step, labeled by the transition that fires. -/
inductive Step (N : Net) : N.Marking → N.Marking → Prop where
  | fire {M : N.Marking} {t : N.Transition} :
      Enabled N M t → Step N M (fire N M t)

theorem reachable_of_enabled_step {N : Net} {M : N.Marking} {t : N.Transition}
    (h : Enabled N M t) :
    Step N M (fire N M t) :=
  Step.fire h

end Petri
end Pm4Lean
