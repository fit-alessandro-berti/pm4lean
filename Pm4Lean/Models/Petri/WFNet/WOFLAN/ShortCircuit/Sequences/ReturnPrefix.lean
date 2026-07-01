import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Sequences.Projection

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

theorem firingSequence_to_return_enabled_has_noReturn_prefix
    {M M' : W.Marking} {ts : List (ShortCircuitTransition W)}
    (hSeq : FiringSequence (shortCircuit W) M ts M')
    (hReturnEnabled :
      Enabled (shortCircuit W) M'
        ShortCircuitTransition.returnTransition) :
    ∃ Mcover : W.Marking,
      ∃ pref : List (ShortCircuitTransition W),
        FiringSequence (shortCircuit W) M pref Mcover ∧
          NoReturn W pref ∧
          Enabled (shortCircuit W) Mcover
            ShortCircuitTransition.returnTransition := by
  exact
    FiringSequence.rec (N := shortCircuit W)
      (motive := fun M _ts M' hSeq =>
        Enabled (shortCircuit W) M'
          ShortCircuitTransition.returnTransition →
          ∃ Mcover : W.Marking,
            ∃ pref : List (ShortCircuitTransition W),
              FiringSequence (shortCircuit W) M pref Mcover ∧
                NoReturn W pref ∧
                Enabled (shortCircuit W) Mcover
                  ShortCircuitTransition.returnTransition)
      (fun M hReturnEnabled =>
        ⟨M, [],
          FiringSequence.nil (N := shortCircuit W) M,
          by
            simp [NoReturn, ContainsReturn],
          hReturnEnabled⟩)
      (fun {M M'' t ts} hEnabled hTail ih hReturnEnabled =>
        match t with
        | Sum.inl t =>
            let ⟨Mcover, pref, hPrefixSeq, hPrefixNoReturn,
              hPrefixReturnEnabled⟩ := ih hReturnEnabled
            have hConsNoReturn :
                NoReturn W (ShortCircuitTransition.original t :: pref) := by
              simpa [NoReturn, ContainsReturn, ShortCircuitTransition.original,
                ShortCircuitTransition.returnTransition] using hPrefixNoReturn
            ⟨Mcover, ShortCircuitTransition.original t :: pref,
              FiringSequence.cons hEnabled hPrefixSeq,
              hConsNoReturn,
              hPrefixReturnEnabled⟩
        | Sum.inr u =>
            match u with
            | () =>
                ⟨M, [],
                  FiringSequence.nil (N := shortCircuit W) M,
                  by
                    simp [NoReturn, ContainsReturn],
                  hEnabled⟩)
      hSeq
      hReturnEnabled

end shortCircuit

end Petri
end Pm4Lean
