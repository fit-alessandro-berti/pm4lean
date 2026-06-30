import Pm4Lean.Models.Petri.Structure.SourceSink
import Pm4Lean.Models.Petri.Semantics.Reachability

namespace Pm4Lean
namespace Petri

theorem sink_place_token_monotone_step
    {N : Net} {M M' : N.Marking} {p : N.Place}
    (hSink : SinkPlace N p) (hStep : Step N M M') :
    M p ≤ M' p := by
  cases hStep with
  | fire hEnabled =>
      exact fire_token_monotone_of_no_pre (hSink _)

theorem sink_place_token_monotone_reachable
    {N : Net} {M M' : N.Marking} {p : N.Place}
    (hSink : SinkPlace N p) (hReach : Reachable N M M') :
    M p ≤ M' p := by
  induction hReach with
  | refl M =>
      exact Nat.le_refl (M p)
  | step hStep hTail ih =>
      exact Nat.le_trans (sink_place_token_monotone_step hSink hStep) ih

theorem reachable_from_marking_with_final_token_preserves_final_token
    {N : Net} {M M' : N.Marking} {p : N.Place}
    (hSink : SinkPlace N p) (hToken : 0 < M p)
    (hReach : Reachable N M M') :
    0 < M' p :=
  Nat.lt_of_lt_of_le hToken (sink_place_token_monotone_reachable hSink hReach)

end Petri
end Pm4Lean
