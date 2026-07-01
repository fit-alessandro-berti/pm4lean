import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Sequences.Original

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

theorem noReturn_firingSequence_projects_to_original
    {M M' : W.Marking} {ts : List (ShortCircuitTransition W)}
    (hNoReturn : NoReturn W ts)
    (hSeq : FiringSequence (shortCircuit W) M ts M') :
    ∃ ots : List W.net.Transition, FiringSequence W.net M ots M' := by
  exact
    FiringSequence.rec (N := shortCircuit W)
      (motive := fun M ts M' _ =>
        NoReturn W ts →
          ∃ ots : List W.net.Transition, FiringSequence W.net M ots M')
      (fun M _hNoReturn =>
        ⟨[], FiringSequence.nil (N := W.net) M⟩)
      (fun {M M'' t ts} hEnabled _hTail ih hNoReturn =>
        match t with
        | Sum.inl t =>
            have hTailNoReturn : NoReturn W ts := by
              intro hContains
              exact hNoReturn (by
                unfold ContainsReturn at hContains ⊢
                exact List.mem_cons_of_mem _ hContains)
            let ⟨ots, hOriginalTail⟩ := ih hTailNoReturn
            ⟨t :: ots,
              FiringSequence.cons
                ((original_enabled_iff W M t).1 hEnabled)
                (by simpa [fire_original] using hOriginalTail)⟩
        | Sum.inr u =>
            match u with
            | () =>
                False.elim (hNoReturn (by
                  unfold ContainsReturn
                  exact List.Mem.head _)))
      hSeq
      hNoReturn

theorem noReturn_firingSequence_reachable_projects_to_original
    {M M' : W.Marking} {ts : List (ShortCircuitTransition W)}
    (hNoReturn : NoReturn W ts)
    (hSeq : FiringSequence (shortCircuit W) M ts M') :
    Reachable W.net M M' :=
  let ⟨_, hOriginalSeq⟩ :=
    noReturn_firingSequence_projects_to_original W hNoReturn hSeq
  Reachable.of_firingSequence hOriginalSeq

end shortCircuit

end Petri
end Pm4Lean
