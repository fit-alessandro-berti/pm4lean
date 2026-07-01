import Pm4Lean.Models.Petri.Behavior.Boundedness.Samples
import Pm4Lean.Util.NatListMax

namespace Pm4Lean
namespace Petri

def sampleMarkingTokenSums (N : Net)
    (samples : List N.Marking) : List Nat :=
  samples.map (fun M => Marking.TokenSumOn N.places M)

theorem sampleMarking_le_natListMax_tokenSums
    {N : Net} {samples : List N.Marking}
    {M : N.Marking} (hMem : M ∈ samples) :
    ∀ p : N.Place,
      M p ≤ NatListMax (sampleMarkingTokenSums N samples) := by
  intro p
  exact Nat.le_trans
    (Marking.le_tokenSumOn_of_complete N.places N.places_complete M p)
    (le_natListMax_of_mem (by
      simp [sampleMarkingTokenSums]
      exact ⟨M, hMem, rfl⟩))

theorem samplesBounded_explicit (N : Net)
    (samples : List N.Marking) :
    SamplesBounded N samples :=
  ⟨NatListMax (sampleMarkingTokenSums N samples),
    fun _ hMem => sampleMarking_le_natListMax_tokenSums hMem⟩

end Petri
end Pm4Lean
