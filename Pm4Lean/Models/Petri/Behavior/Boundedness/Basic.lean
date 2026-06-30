import Pm4Lean.Models.Petri.Basic.Marking.Support
import Pm4Lean.Models.Petri.Semantics.Reachability

namespace Pm4Lean
namespace Petri

def BoundedBy (N : Net) (M₀ : N.Marking) (k : Nat) : Prop :=
  ∀ M : N.Marking, Reachable N M₀ M → ∀ p : N.Place, M p ≤ k

/-- A marked net has some finite global token bound. -/
def Bounded (N : Net) (M₀ : N.Marking) : Prop :=
  ∃ k : Nat, BoundedBy N M₀ k

/-- A marked net is safe when each place always has at most one token. -/
def Safe (N : Net) (M₀ : N.Marking) : Prop :=
  BoundedBy N M₀ 1

/-- A marked net has a global bound on the total tokens over its place list. -/
def TokenSumBoundedReachable (N : Net) (M₀ : N.Marking) : Prop :=
  ∃ k : Nat, ∀ M : N.Marking, Reachable N M₀ M →
    Marking.TokenSumOn N.places M ≤ k

theorem bounded_of_tokenSumBoundedReachable
    {N : Net} {M₀ : N.Marking}
    (hTokenSumBounded : TokenSumBoundedReachable N M₀) :
    Bounded N M₀ := by
  obtain ⟨k, hBoundSum⟩ := hTokenSumBounded
  exact ⟨k, fun M hReach p =>
    Nat.le_trans
      (Marking.le_tokenSumOn_of_complete
        N.places N.places_complete M p)
      (hBoundSum M hReach)⟩

theorem tokenSumBoundedReachable_of_bounded
    {N : Net} {M₀ : N.Marking}
    (hBounded : Bounded N M₀) :
    TokenSumBoundedReachable N M₀ := by
  obtain ⟨k, hBoundedBy⟩ := hBounded
  exact ⟨N.places.length * k, fun M hReach =>
    Marking.tokenSumOn_le_length_mul_of_forall_le
      N.places M k (fun p => hBoundedBy M hReach p)⟩

theorem bounded_iff_tokenSumBoundedReachable
    {N : Net} {M₀ : N.Marking} :
    Bounded N M₀ ↔ TokenSumBoundedReachable N M₀ :=
  ⟨tokenSumBoundedReachable_of_bounded,
    bounded_of_tokenSumBoundedReachable⟩

end Petri
end Pm4Lean
