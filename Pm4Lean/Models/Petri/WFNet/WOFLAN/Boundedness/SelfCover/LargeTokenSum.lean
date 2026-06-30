import Pm4Lean.Models.Petri.Semantics.TokenSum
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Definitions

namespace Pm4Lean
namespace Petri

/--
Unboundedness expressed by concrete firing sequences whose total token count
over the net's finite place enumeration exceeds every bound.
-/
def ArbitrarilyLargeFiringSequenceTokenSum (W : WFNet) : Prop :=
  ∀ k : Nat, ∃ ts : List W.net.Transition,
    ∃ M : W.Marking,
      FiringSequence W.net W.initial ts M ∧
        k < Marking.TokenSumOn W.net.places M

theorem arbitrarilyLargeFiringSequenceTokenSum_of_marking
    {W : WFNet}
    (hLarge : ArbitrarilyLargeFiringSequenceMarking W) :
    ArbitrarilyLargeFiringSequenceTokenSum W := by
  intro k
  obtain ⟨ts, M, hSeq, p, hLt⟩ := hLarge k
  exact ⟨ts, M, hSeq,
    Nat.lt_of_lt_of_le hLt
      (Marking.le_tokenSumOn_of_complete
        W.net.places W.net.places_complete M p)⟩

theorem arbitrarilyLargeFiringSequenceMarking_of_tokenSum
    {W : WFNet}
    (hLarge : ArbitrarilyLargeFiringSequenceTokenSum W) :
    ArbitrarilyLargeFiringSequenceMarking W := by
  intro k
  obtain ⟨ts, M, hSeq, hSumGt⟩ :=
    hLarge (W.net.places.length * k)
  by_cases hExists : ∃ p : W.net.Place, k < M p
  · obtain ⟨p, hLt⟩ := hExists
    exact ⟨ts, M, hSeq, p, hLt⟩
  · have hAllLe : ∀ p : W.net.Place, M p ≤ k := by
      intro p
      exact Nat.le_of_not_gt (by
        intro hLt
        exact hExists ⟨p, hLt⟩)
    have hSumLe :
        Marking.TokenSumOn W.net.places M ≤ W.net.places.length * k :=
      Marking.tokenSumOn_le_length_mul_of_forall_le
        W.net.places M k hAllLe
    exact False.elim ((Nat.not_lt_of_ge hSumLe) hSumGt)

theorem arbitrarilyLargeFiringSequenceMarking_iff_tokenSum
    {W : WFNet} :
    ArbitrarilyLargeFiringSequenceMarking W ↔
      ArbitrarilyLargeFiringSequenceTokenSum W :=
  ⟨arbitrarilyLargeFiringSequenceTokenSum_of_marking,
    arbitrarilyLargeFiringSequenceMarking_of_tokenSum⟩

end Petri
end Pm4Lean
