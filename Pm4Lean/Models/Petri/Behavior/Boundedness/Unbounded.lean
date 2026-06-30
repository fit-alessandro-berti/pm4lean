import Pm4Lean.Models.Petri.Behavior.Boundedness.Samples

namespace Pm4Lean
namespace Petri

theorem not_reachableCoveredBySamples_of_not_bounded
    {N : Net} {M₀ : N.Marking}
    (hNotBounded : ¬ Bounded N M₀) (samples : List N.Marking) :
    ¬ ReachableCoveredBySamples N M₀ samples := by
  intro hCovered
  exact hNotBounded (bounded_of_reachableCoveredBySamples hCovered)

theorem not_bounded_implies_no_finite_reachable_cover
    {N : Net} {M₀ : N.Marking}
    (hNotBounded : ¬ Bounded N M₀) :
    ∀ samples : List N.Marking,
      ¬ ReachableCoveredBySamples N M₀ samples := by
  intro samples
  exact not_reachableCoveredBySamples_of_not_bounded
    hNotBounded samples

theorem not_boundedBy_of_reachable_gt
    {N : Net} {M₀ M : N.Marking} {k : Nat} {p : N.Place}
    (hReach : Reachable N M₀ M) (hGt : k < M p) :
    ¬ BoundedBy N M₀ k := by
  intro hBoundedBy
  exact Nat.not_lt_of_ge (hBoundedBy M hReach p) hGt

theorem not_boundedBy_iff_exists_reachable_gt
    {N : Net} {M₀ : N.Marking} {k : Nat} :
    ¬ BoundedBy N M₀ k ↔
      ∃ M : N.Marking, Reachable N M₀ M ∧
        ∃ p : N.Place, k < M p := by
  constructor
  · intro hNotBoundedBy
    classical
    exact Classical.byContradiction (fun hNoWitness =>
      hNotBoundedBy (fun M hReach p =>
        Nat.le_of_not_gt (by
          intro hGt
          exact hNoWitness ⟨M, hReach, p, hGt⟩)))
  · intro hWitness hBoundedBy
    obtain ⟨M, hReach, p, hGt⟩ := hWitness
    exact Nat.not_lt_of_ge (hBoundedBy M hReach p) hGt

theorem not_bounded_of_forall_bound_reachable_gt
    {N : Net} {M₀ : N.Marking}
    (hUnbounded :
      ∀ k : Nat, ∃ M : N.Marking, Reachable N M₀ M ∧
        ∃ p : N.Place, k < M p) :
    ¬ Bounded N M₀ := by
  intro hBounded
  obtain ⟨k, hBoundedBy⟩ := hBounded
  obtain ⟨M, hReach, p, hGt⟩ := hUnbounded k
  exact Nat.not_lt_of_ge (hBoundedBy M hReach p) hGt

theorem not_bounded_iff_forall_bound_reachable_gt
    {N : Net} {M₀ : N.Marking} :
    ¬ Bounded N M₀ ↔
      ∀ k : Nat, ∃ M : N.Marking, Reachable N M₀ M ∧
        ∃ p : N.Place, k < M p := by
  constructor
  · intro hNotBounded k
    exact not_boundedBy_iff_exists_reachable_gt.1
      (fun hBoundedBy => hNotBounded ⟨k, hBoundedBy⟩)
  · intro hUnbounded
    exact not_bounded_of_forall_bound_reachable_gt hUnbounded

end Petri
end Pm4Lean
