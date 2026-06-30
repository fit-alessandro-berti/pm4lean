import Pm4Lean.Models.Petri.WFNet.Soundness.Soundness

namespace Pm4Lean
namespace Petri

/-- Transitions of the short-circuited WF-net. -/
abbrev ShortCircuitTransition (W : WFNet) :=
  Sum W.net.Transition Unit

namespace ShortCircuitTransition

variable {W : WFNet}

/-- An original transition embedded into the short-circuited net. -/
def original (t : W.net.Transition) : ShortCircuitTransition W :=
  Sum.inl t

/-- The fresh return transition from the final place to the initial place. -/
def returnTransition : ShortCircuitTransition W :=
  Sum.inr ()

end ShortCircuitTransition

/--
The short-circuited net used by WOFLAN: it preserves the original places and
transitions, and adds one transition consuming from the final place and
producing at the initial place.
-/
def shortCircuit (W : WFNet) : Net where
  Place := W.net.Place
  Transition := ShortCircuitTransition W
  placeDecEq := W.net.placeDecEq
  transitionDecEq := inferInstance
  places := W.net.places
  transitions :=
    W.net.transitions.map ShortCircuitTransition.original ++
      [ShortCircuitTransition.returnTransition]
  places_complete := W.net.places_complete
  transitions_complete := by
    intro t
    cases t with
    | inl t =>
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨t, W.net.transitions_complete t, rfl⟩
    | inr u =>
        cases u
        apply List.mem_append_right
        simp [ShortCircuitTransition.returnTransition]
  pre := fun t =>
    match t with
    | Sum.inl t => W.net.pre t
    | Sum.inr () => Marking.singleton W.o
  post := fun t =>
    match t with
    | Sum.inl t => W.net.post t
    | Sum.inr () => Marking.singleton W.i

namespace shortCircuit

variable (W : WFNet)

theorem places_eq :
    (shortCircuit W).places = W.net.places :=
  rfl

theorem pre_original (t : W.net.Transition) :
    (shortCircuit W).pre (ShortCircuitTransition.original t) = W.net.pre t :=
  rfl

theorem post_original (t : W.net.Transition) :
    (shortCircuit W).post (ShortCircuitTransition.original t) = W.net.post t :=
  rfl

theorem pre_return :
    (shortCircuit W).pre ShortCircuitTransition.returnTransition = W.final :=
  rfl

theorem post_return :
    (shortCircuit W).post ShortCircuitTransition.returnTransition = W.initial :=
  rfl

theorem return_enabled_at_final :
    Enabled (shortCircuit W) W.final ShortCircuitTransition.returnTransition := by
  intro p
  exact Nat.le_refl (W.final p)

theorem return_enabled_iff_final_covered (M : W.Marking) :
    Enabled (shortCircuit W) M ShortCircuitTransition.returnTransition ↔
      W.final ≤ M :=
  Iff.rfl

theorem original_enabled_iff (M : W.Marking) (t : W.net.Transition) :
    Enabled (shortCircuit W) M (ShortCircuitTransition.original t) ↔
      Enabled W.net M t :=
  Iff.rfl

theorem fire_original (M : W.Marking) (t : W.net.Transition) :
    fire (shortCircuit W) M (ShortCircuitTransition.original t) =
      fire W.net M t :=
  rfl

theorem fire_return (M : W.Marking) :
    fire (shortCircuit W) M ShortCircuitTransition.returnTransition =
      M - W.final + W.initial :=
  rfl

theorem fire_return_apply (M : W.Marking) (p : W.net.Place) :
    fire (shortCircuit W) M ShortCircuitTransition.returnTransition p =
      M p - W.final p + W.initial p :=
  rfl

theorem remainder_le_fire_return (M : W.Marking) (p : W.net.Place) :
    M p - W.final p ≤
      fire (shortCircuit W) M ShortCircuitTransition.returnTransition p := by
  rw [fire_return_apply]
  exact Nat.le_add_right _ _

theorem fire_return_positive_of_positive_remainder
    {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p) :
    0 < fire (shortCircuit W) M ShortCircuitTransition.returnTransition p :=
  Nat.lt_of_lt_of_le hPositive (remainder_le_fire_return W M p)

theorem initial_lt_fire_return_of_positive_remainder
    {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p) :
    W.initial p <
      fire (shortCircuit W) M ShortCircuitTransition.returnTransition p := by
  rw [fire_return_apply]
  exact Nat.lt_add_of_pos_left hPositive

theorem reachable_fire_return_of_final_covered
    {M : W.Marking}
    (hFinalCovered : W.final ≤ M) :
    Reachable (shortCircuit W) M (M - W.final + W.initial) := by
  simpa [fire_return] using
    (Reachable.of_enabled
      ((return_enabled_iff_final_covered W M).2 hFinalCovered))

theorem step_original_of_enabled {M : W.Marking} {t : W.net.Transition}
    (hEnabled : Enabled W.net M t) :
    Step (shortCircuit W) M (fire W.net M t) :=
  Step.fire ((original_enabled_iff W M t).2 hEnabled)

theorem step_original_to_shortCircuit {M M' : W.Marking}
    (hStep : Step W.net M M') :
    Step (shortCircuit W) M M' := by
  cases hStep with
  | fire hEnabled =>
      simpa [fire_original] using step_original_of_enabled W hEnabled

theorem reachable_original_of_enabled {M : W.Marking} {t : W.net.Transition}
    (hEnabled : Enabled W.net M t) :
    Reachable (shortCircuit W) M (fire W.net M t) :=
  Reachable.of_step (step_original_of_enabled W hEnabled)

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

def ReachableNoReturn (M M' : W.Marking) : Prop :=
  ∃ ts : List (ShortCircuitTransition W),
    FiringSequence (shortCircuit W) M ts M' ∧ NoReturn W ts

theorem firingSequence_original_to_reachableNoReturn
    {M M' : W.Marking} {ts : List W.net.Transition}
    (hSeq : FiringSequence W.net M ts M') :
    ReachableNoReturn W M M' :=
  ⟨ShortCircuitTransition.ofOriginalList W ts,
    firingSequence_original_to_shortCircuit W hSeq,
    ofOriginalList_noReturn W ts⟩

theorem reachableNoReturn_projects_to_original
    {M M' : W.Marking}
    (hReach : ReachableNoReturn W M M') :
    Reachable W.net M M' := by
  obtain ⟨ts, hSeq, hNoReturn⟩ := hReach
  exact noReturn_firingSequence_reachable_projects_to_original W hNoReturn hSeq

theorem reachable_original_to_shortCircuit {M M' : W.Marking}
    (hReach : Reachable W.net M M') :
    Reachable (shortCircuit W) M M' := by
  induction hReach with
  | refl M =>
      exact Reachable.refl (N := shortCircuit W) M
  | step hStep hReach ih =>
      exact Reachable.step (step_original_to_shortCircuit W hStep) ih

theorem reachable_original_to_reachableNoReturn {M M' : W.Marking}
    (hReach : Reachable W.net M M') :
    ReachableNoReturn W M M' := by
  obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReach
  exact firingSequence_original_to_reachableNoReturn W hSeq

theorem reachableNoReturn_iff_original {M M' : W.Marking} :
    ReachableNoReturn W M M' ↔ Reachable W.net M M' :=
  ⟨reachableNoReturn_projects_to_original W,
    reachable_original_to_reachableNoReturn W⟩

theorem reachableNoReturn_to_return_enabled_gives_original_reach_to_cover
    {M M' : W.Marking}
    (hReach : ReachableNoReturn W M M')
    (hReturnEnabled :
      Enabled (shortCircuit W) M'
        ShortCircuitTransition.returnTransition) :
    ∃ Mcover : W.Marking,
      Reachable W.net M Mcover ∧ W.final ≤ Mcover :=
  ⟨M',
    reachableNoReturn_projects_to_original W hReach,
    (return_enabled_iff_final_covered W M').1 hReturnEnabled⟩

theorem reachable_to_return_enabled_gives_original_reach_to_cover
    {M M' : W.Marking}
    (hReachSC : Reachable (shortCircuit W) M M')
    (hReturnEnabled :
      Enabled (shortCircuit W) M'
        ShortCircuitTransition.returnTransition) :
    ∃ Mcover : W.Marking,
      Reachable W.net M Mcover ∧ W.final ≤ Mcover := by
  obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReachSC
  obtain ⟨Mcover, pref, hPrefixSeq, hNoReturn, hPrefixReturnEnabled⟩ :=
    firingSequence_to_return_enabled_has_noReturn_prefix W hSeq hReturnEnabled
  exact ⟨Mcover,
    noReturn_firingSequence_reachable_projects_to_original
      W hNoReturn hPrefixSeq,
    (return_enabled_iff_final_covered W Mcover).1 hPrefixReturnEnabled⟩

theorem fire_return_at_final :
    fire (shortCircuit W) W.final ShortCircuitTransition.returnTransition =
      W.initial := by
  apply Marking.ext
  intro p
  calc
    fire (shortCircuit W) W.final ShortCircuitTransition.returnTransition p
        = W.final p - W.final p + W.initial p := rfl
    _ = W.initial p := by rw [Nat.sub_self, Nat.zero_add]

theorem step_preserves_original_reachable_of_proper
    (hProper : ProperCompletion W)
    {M M' : W.Marking}
    (hReachOriginal : Reachable W.net W.initial M)
    (hStep : Step (shortCircuit W) M M') :
    Reachable W.net W.initial M' := by
  exact
    @Step.rec (shortCircuit W) M
      (fun M' _ => Reachable W.net W.initial M')
      (fun {t} hEnabled =>
        match t with
        | Sum.inl t =>
            Reachable.trans hReachOriginal
              (Reachable.of_enabled (N := W.net)
                ((original_enabled_iff W M t).1 hEnabled))
        | Sum.inr u =>
            match u with
            | () =>
                have hFinalCovered : W.final ≤ M :=
                  (return_enabled_iff_final_covered W M).1 hEnabled
                have hMFinal : M = W.final :=
                  hProper M hReachOriginal hFinalCovered
                have hFireInitial :
                    fire (shortCircuit W) M
                      ShortCircuitTransition.returnTransition = W.initial := by
                  rw [hMFinal]
                  exact fire_return_at_final W
                by
                  show Reachable W.net W.initial
                    (fire (shortCircuit W) M
                      ShortCircuitTransition.returnTransition)
                  exact hFireInitial.symm ▸
                    (Reachable.refl (N := W.net) W.initial))
      M'
      hStep

theorem firingSequence_preserves_original_reachable_of_proper
    (hProper : ProperCompletion W)
    {M M' : W.Marking} {ts : List (ShortCircuitTransition W)}
    (hReachOriginal : Reachable W.net W.initial M)
    (hSeq : FiringSequence (shortCircuit W) M ts M') :
    Reachable W.net W.initial M' := by
  exact
    FiringSequence.rec (N := shortCircuit W)
      (motive := fun M _ts M' _ =>
        Reachable W.net W.initial M → Reachable W.net W.initial M')
      (fun M hReachOriginal => hReachOriginal)
      (fun hEnabled _hTail ih hReachOriginal =>
        ih
          (step_preserves_original_reachable_of_proper
            W hProper hReachOriginal (Step.fire hEnabled)))
      hSeq
      hReachOriginal

theorem reachable_shortCircuit_to_original_of_proper
    (hProper : ProperCompletion W)
    {M : W.Marking}
    (hReachSC : Reachable (shortCircuit W) W.initial M) :
    Reachable W.net W.initial M := by
  obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReachSC
  exact firingSequence_preserves_original_reachable_of_proper
    W hProper (Reachable.refl W.initial) hSeq

theorem reachable_final_to_initial_in_shortCircuit :
    Reachable (shortCircuit W) W.final W.initial := by
  simpa [fire_return_at_final] using
    (Reachable.of_enabled (return_enabled_at_final W))

end shortCircuit

end Petri
end Pm4Lean
