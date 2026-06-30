import Pm4Lean.Models.Petri.Behavior.Boundedness.Basic

namespace Pm4Lean
namespace Petri

/-- Every reachable marking is represented by one marking in a finite list. -/
def ReachableCoveredBySamples
    (N : Net) (M₀ : N.Marking) (samples : List N.Marking) : Prop :=
  ∀ M : N.Marking, Reachable N M₀ M →
    ∃ S : N.Marking, S ∈ samples ∧ M = S

/-- A finite list of sample markings has a uniform place-token bound. -/
def SamplesBounded (N : Net) (samples : List N.Marking) : Prop :=
  ∃ k : Nat, ∀ S : N.Marking, S ∈ samples → ∀ p : N.Place, S p ≤ k

theorem samplesBounded_nil {N : Net} :
    SamplesBounded N [] :=
  ⟨0, by
    intro S hMem _p
    cases hMem⟩

theorem samplesBounded_cons {N : Net}
    (S : N.Marking) (samples : List N.Marking)
    (hTail : SamplesBounded N samples) :
    SamplesBounded N (S :: samples) := by
  obtain ⟨k, hBoundTail⟩ := hTail
  exact ⟨Nat.max (Marking.TokenSumOn N.places S) k,
    by
      intro T hMem p
      cases hMem with
      | head =>
          exact Nat.le_trans
            (Marking.le_tokenSumOn_of_complete
              N.places N.places_complete S p)
            (Nat.le_max_left _ _)
      | tail _ hTailMem =>
          exact Nat.le_trans
            (hBoundTail T hTailMem p)
            (Nat.le_max_right _ _)⟩

theorem samplesBounded (N : Net) (samples : List N.Marking) :
    SamplesBounded N samples := by
  induction samples with
  | nil =>
      exact samplesBounded_nil
  | cons S samples ih =>
      exact samplesBounded_cons S samples ih

theorem bounded_of_reachableCoveredBySamples
    {N : Net} {M₀ : N.Marking} {samples : List N.Marking}
    (hCovered : ReachableCoveredBySamples N M₀ samples) :
    Bounded N M₀ := by
  obtain ⟨k, hSamplesBounded⟩ := samplesBounded N samples
  exact ⟨k, fun M hReach p =>
    by
      obtain ⟨S, hMem, hEq⟩ := hCovered M hReach
      rw [hEq]
      exact hSamplesBounded S hMem p⟩

end Petri
end Pm4Lean
