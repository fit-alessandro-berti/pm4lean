import Pm4Lean.Models.Petri.Structure.Node

namespace Pm4Lean
namespace Petri

/-- Directed adjacency induced by nonzero pre/post arc weights. -/
inductive Adjacent (N : Net) : Node N → Node N → Prop where
  | placeToTransition (p : N.Place) (t : N.Transition) :
      0 < N.pre t p → Adjacent N (.place p) (.transition t)
  | transitionToPlace (t : N.Transition) (p : N.Place) :
      0 < N.post t p → Adjacent N (.transition t) (.place p)

/-- Directed paths through the Petri-net graph. -/
inductive Path (N : Net) : Node N → Node N → Prop where
  | refl (x : Node N) : Path N x x
  | step {x y z : Node N} :
      Adjacent N x y → Path N y z → Path N x z

namespace Path

theorem trans {N : Net} {x y z : Node N}
    (hxy : Path N x y) (hyz : Path N y z) :
    Path N x z := by
  induction hxy with
  | refl x =>
      exact hyz
  | step hAdj hTail ih =>
      exact Path.step hAdj (ih hyz)

end Path
end Petri
end Pm4Lean
