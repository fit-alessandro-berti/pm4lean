import Pm4Lean.Models.Petri.Behavior.Boundedness.Unbounded

namespace Pm4Lean
namespace Petri

/-- A marked net has reachable markings with arbitrarily many tokens at one
fixed place. -/
def LinearTokenGrowthAt (N : Net) (M₀ : N.Marking) (p : N.Place) : Prop :=
  ∀ n : Nat, ∃ M : N.Marking, Reachable N M₀ M ∧ n ≤ M p

theorem linearTokenGrowthAt_not_boundedBy
    {N : Net} {M₀ : N.Marking} {p : N.Place}
    (hGrow : LinearTokenGrowthAt N M₀ p) (k : Nat) :
    ¬ BoundedBy N M₀ k := by
  obtain ⟨M, hReach, hLe⟩ := hGrow (k + 1)
  exact not_boundedBy_of_reachable_gt hReach (Nat.lt_of_succ_le hLe)

theorem linearTokenGrowthAt_not_bounded
    {N : Net} {M₀ : N.Marking} {p : N.Place}
    (hGrow : LinearTokenGrowthAt N M₀ p) :
    ¬ Bounded N M₀ := by
  intro hBounded
  obtain ⟨k, hBoundedBy⟩ := hBounded
  exact linearTokenGrowthAt_not_boundedBy hGrow k hBoundedBy

end Petri
end Pm4Lean
