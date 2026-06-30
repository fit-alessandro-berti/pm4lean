import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Basic

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

def ShortCircuitTransition.ofOriginalList :
    List W.net.Transition → List (ShortCircuitTransition W)
  | [] => []
  | t :: ts =>
      ShortCircuitTransition.original t ::
        ShortCircuitTransition.ofOriginalList ts

def ContainsReturn (ts : List (ShortCircuitTransition W)) : Prop :=
  ShortCircuitTransition.returnTransition ∈ ts

def NoReturn (ts : List (ShortCircuitTransition W)) : Prop :=
  ¬ ContainsReturn W ts

def ShortCircuitTransition.toOriginal? :
    ShortCircuitTransition W → Option W.net.Transition
  | Sum.inl t => some t
  | Sum.inr () => none

def ShortCircuitTransition.originalOfNoReturnSequence
    (ts : List (ShortCircuitTransition W)) : List W.net.Transition :=
  ts.filterMap (ShortCircuitTransition.toOriginal? W)

theorem ofOriginalList_noReturn (ts : List W.net.Transition) :
    NoReturn W (ShortCircuitTransition.ofOriginalList W ts) := by
  induction ts with
  | nil =>
      simp [NoReturn, ContainsReturn, ShortCircuitTransition.ofOriginalList]
  | cons t ts ih =>
      simpa [NoReturn, ContainsReturn, ShortCircuitTransition.ofOriginalList,
        ShortCircuitTransition.original, ShortCircuitTransition.returnTransition] using ih

theorem firingSequence_original_to_shortCircuit
    {M M' : W.Marking} {ts : List W.net.Transition}
    (hSeq : FiringSequence W.net M ts M') :
    FiringSequence (shortCircuit W) M
      (ShortCircuitTransition.ofOriginalList W ts) M' := by
  induction hSeq with
  | nil M =>
      exact FiringSequence.nil (N := shortCircuit W) M
  | cons hEnabled hTail ih =>
      exact FiringSequence.cons
        ((original_enabled_iff W _ _).2 hEnabled)
        (by simpa [fire_original] using ih)

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
