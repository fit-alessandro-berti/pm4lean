import Pm4Lean.Models.Petri.Basic.Marking.Support
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Liveness

namespace Pm4Lean
namespace Petri

/-- A marked net is bounded by a global token bound. -/
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

theorem not_boundedBy_of_reachable_gt
    {N : Net} {M₀ M : N.Marking} {k : Nat} {p : N.Place}
    (hReach : Reachable N M₀ M) (hGt : k < M p) :
    ¬ BoundedBy N M₀ k := by
  intro hBoundedBy
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

/-- The original WF-net has a global token bound on markings reachable from
its initial marking. -/
def TokenBoundedReachableOriginal (W : WFNet) : Prop :=
  ∃ k : Nat, ∀ M : W.Marking, Reachable W.net W.initial M →
    ∀ p : W.net.Place, M p ≤ k

/-- The original WF-net has a global bound on the total tokens over its place
enumeration. -/
def TokenSumBoundedReachableOriginal (W : WFNet) : Prop :=
  TokenSumBoundedReachable W.net W.initial

theorem original_bounded_of_tokenSumBoundedReachableOriginal
    {W : WFNet}
    (hTokenSumBounded : TokenSumBoundedReachableOriginal W) :
    TokenBoundedReachableOriginal W := by
  obtain ⟨k, hBoundSum⟩ := hTokenSumBounded
  exact ⟨k, fun M hReach p =>
    Nat.le_trans
      (Marking.le_tokenSumOn_of_complete
        W.net.places W.net.places_complete M p)
      (hBoundSum M hReach)⟩

theorem tokenSumBoundedReachableOriginal_of_original_bounded
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W) :
    TokenSumBoundedReachableOriginal W := by
  obtain ⟨k, hBoundOriginalBy⟩ := hBoundOriginal
  exact ⟨W.net.places.length * k, fun M hReach =>
    Marking.tokenSumOn_le_length_mul_of_forall_le
      W.net.places M k (fun p => hBoundOriginalBy M hReach p)⟩

theorem original_bounded_iff_tokenSumBoundedReachableOriginal
    {W : WFNet} :
    TokenBoundedReachableOriginal W ↔
      TokenSumBoundedReachableOriginal W :=
  ⟨tokenSumBoundedReachableOriginal_of_original_bounded,
    original_bounded_of_tokenSumBoundedReachableOriginal⟩

theorem original_bounded_of_shortCircuit_bounded
    {W : WFNet}
    (hBounded : Bounded (shortCircuit W) W.initial) :
    TokenBoundedReachableOriginal W := by
  obtain ⟨k, hBoundedBy⟩ := hBounded
  exact ⟨k, fun M hReach p =>
    hBoundedBy M
      (shortCircuit.reachable_original_to_shortCircuit W hReach)
      p⟩

theorem original_tokenSum_bounded_of_shortCircuit_bounded
    {W : WFNet}
    (hBounded : Bounded (shortCircuit W) W.initial) :
    TokenSumBoundedReachableOriginal W :=
  tokenSumBoundedReachableOriginal_of_original_bounded
    (original_bounded_of_shortCircuit_bounded hBounded)

theorem shortCircuit_bounded_of_original_bounded_and_proper
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hProper : ProperCompletion W) :
    Bounded (shortCircuit W) W.initial := by
  obtain ⟨k, hBoundOriginalBy⟩ := hBoundOriginal
  exact ⟨k, fun M hReachSC p =>
    hBoundOriginalBy M
      (shortCircuit.reachable_shortCircuit_to_original_of_proper
        W hProper hReachSC)
      p⟩

theorem shortCircuit_bounded_of_original_tokenSum_bounded_and_proper
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hProper : ProperCompletion W) :
    Bounded (shortCircuit W) W.initial :=
  shortCircuit_bounded_of_original_bounded_and_proper
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hProper

theorem shortCircuit_bounded_of_original_bounded_and_sound
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hSound : Sound W) :
    Bounded (shortCircuit W) W.initial :=
  shortCircuit_bounded_of_original_bounded_and_proper
    hBoundOriginal hSound.2.1

theorem shortCircuit_bounded_of_original_tokenSum_bounded_and_sound
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hSound : Sound W) :
    Bounded (shortCircuit W) W.initial :=
  shortCircuit_bounded_of_original_tokenSum_bounded_and_proper
    hBoundOriginal hSound.2.1

/-- A reachable final-cover marking that is not exactly the final marking. -/
def HasExtraTokensAtFinalCover (W : WFNet) (M : W.Marking) : Prop :=
  Reachable W.net W.initial M ∧ W.final ≤ M ∧ M ≠ W.final

theorem hasExtraTokensAtFinalCover_exists_strict_extra
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place, W.final p < M p :=
  Marking.exists_lt_of_le_ne hExtra.2.1 hExtra.2.2.symm

theorem hasExtraTokensAtFinalCover_exists_positive_remainder
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place, 0 < M p - W.final p := by
  obtain ⟨p, hStrict⟩ :=
    hasExtraTokensAtFinalCover_exists_strict_extra hExtra
  exact ⟨p, Nat.sub_pos_of_lt hStrict⟩

theorem hasExtraTokensAtFinalCover_reachable_after_return
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    Reachable (shortCircuit W) W.initial
      (M - W.final + W.initial) := by
  exact Reachable.trans
    (shortCircuit.reachable_original_to_shortCircuit W hExtra.1)
    (shortCircuit.reachable_fire_return_of_final_covered W hExtra.2.1)

theorem hasExtraTokensAtFinalCover_return_has_positive_token
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place,
      0 <
        fire (shortCircuit W) M
          ShortCircuitTransition.returnTransition p := by
  obtain ⟨p, hPositive⟩ :=
    hasExtraTokensAtFinalCover_exists_positive_remainder hExtra
  exact ⟨p,
    shortCircuit.fire_return_positive_of_positive_remainder
      W hPositive⟩

theorem hasExtraTokensAtFinalCover_return_exceeds_initial
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place,
      W.initial p <
        fire (shortCircuit W) M
          ShortCircuitTransition.returnTransition p := by
  obtain ⟨p, hPositive⟩ :=
    hasExtraTokensAtFinalCover_exists_positive_remainder hExtra
  exact ⟨p,
    shortCircuit.initial_lt_fire_return_of_positive_remainder
      W hPositive⟩

theorem hasExtraTokensAtFinalCover_reachable_after_return_exceeds_initial
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧
        ∃ p : W.net.Place, W.initial p < M' p := by
  exact ⟨M - W.final + W.initial,
    hasExtraTokensAtFinalCover_reachable_after_return hExtra,
    by
      simpa [shortCircuit.fire_return] using
        hasExtraTokensAtFinalCover_return_exceeds_initial hExtra⟩

theorem hasExtraTokensAtFinalCover_not_boundedBy_initial_token
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place,
      ¬ BoundedBy (shortCircuit W) W.initial (W.initial p) := by
  obtain ⟨M', hReach, p, hGt⟩ :=
    hasExtraTokensAtFinalCover_reachable_after_return_exceeds_initial
      hExtra
  exact ⟨p, not_boundedBy_of_reachable_gt hReach hGt⟩

/--
An extra final-cover marking can be pumped linearly at a fixed place.  This is
the concrete repeated-growth obligation needed for the full WOFLAN
boundedness contradiction.
-/
def ExtraFinalCoverLinearPumpAt
    (W : WFNet) (M : W.Marking) (p : W.net.Place) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat, ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧ n ≤ M' p

/--
The repeated-return accumulation obligation for an extra final-cover marking:
after `n` cycles, the selected place carries at least its initial tokens plus
`n` copies of the extra remainder left by the return transition.
-/
def ExtraFinalCoverAccumulatedGrowthAt
    (W : WFNet) (M : W.Marking) (p : W.net.Place) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat, ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧
        W.initial p + n * (M p - W.final p) ≤ M' p

/--
Closed-form version of the repeated-return target: the short-circuited net can
reach the initial marking plus `n` copies of the extra remainder.
-/
def ExtraFinalCoverClosedFormGrowth (W : WFNet) (M : W.Marking) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat,
      Reachable (shortCircuit W) W.initial
        (W.initial + Marking.scale n (M - W.final))

/--
Stepwise version of closed-form growth: each accumulated marking can reach the
next accumulated marking.
-/
def ExtraFinalCoverClosedFormStep (W : WFNet) (M : W.Marking) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat,
      Reachable (shortCircuit W)
        (W.initial + Marking.scale n (M - W.final))
        (W.initial + Marking.scale (n + 1) (M - W.final))

theorem extra_final_cover_closedFormStep_implies_closedFormGrowth
    {W : WFNet} {M : W.Marking}
    (hStep : ExtraFinalCoverClosedFormStep W M) :
    ExtraFinalCoverClosedFormGrowth W M := by
  intro hExtra n
  let F : Nat → W.Marking :=
    fun k => W.initial + Marking.scale k (M - W.final)
  have hReachFromF0 :
      Reachable (shortCircuit W) (F 0) (F n) :=
    Reachable.of_nat_chain (N := shortCircuit W) F (hStep hExtra) n
  have hF0 : F 0 = W.initial := by
    simp [F, Marking.scale_zero, Marking.add_zero]
  simpa [F, hF0] using hReachFromF0

theorem extra_final_cover_closedFormGrowth_implies_accumulated_growth_at
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hClosed : ExtraFinalCoverClosedFormGrowth W M) :
    ExtraFinalCoverAccumulatedGrowthAt W M p := by
  intro hExtra n
  exact ⟨W.initial + Marking.scale n (M - W.final),
    hClosed hExtra n,
    Nat.le_refl _⟩

theorem extra_final_cover_closedFormGrowth_implies_accumulated_growth
    {W : WFNet} {M : W.Marking}
    (hClosed : ExtraFinalCoverClosedFormGrowth W M) :
    ∀ p : W.net.Place,
      0 < M p - W.final p →
        ExtraFinalCoverAccumulatedGrowthAt W M p := by
  intro p _hPositive
  exact extra_final_cover_closedFormGrowth_implies_accumulated_growth_at
    hClosed

/--
An operational plan for proving accumulated growth: provide a Nat-indexed
chain of short-circuit reachable cycles, starting at the initial marking, whose
token count at `p` grows by the extra remainder.
-/
def ExtraFinalCoverAccumulationPlanAt
    (W : WFNet) (M : W.Marking) (p : W.net.Place) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∃ F : Nat → W.Marking,
      F 0 = W.initial ∧
        (∀ n : Nat,
          Reachable (shortCircuit W) (F n) (F (n + 1))) ∧
        ∀ n : Nat,
          W.initial p + n * (M p - W.final p) ≤ F n p

theorem extra_final_cover_accumulation_plan_at_implies_accumulated_growth_at
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hPlan : ExtraFinalCoverAccumulationPlanAt W M p) :
    ExtraFinalCoverAccumulatedGrowthAt W M p := by
  intro hExtra n
  obtain ⟨F, hStart, hStep, hGrowth⟩ := hPlan hExtra
  have hReachFromStart :
      Reachable (shortCircuit W) (F 0) (F n) :=
    Reachable.of_nat_chain (N := shortCircuit W) F hStep n
  have hReach :
      Reachable (shortCircuit W) W.initial (F n) := by
    simpa [hStart] using hReachFromStart
  exact ⟨F n, hReach, hGrowth n⟩

theorem extra_final_cover_accumulation_plan_implies_accumulated_growth
    {W : WFNet} {M : W.Marking}
    (hPlan :
      ∀ p : W.net.Place,
        0 < M p - W.final p →
          ExtraFinalCoverAccumulationPlanAt W M p) :
    ∀ p : W.net.Place,
      0 < M p - W.final p →
        ExtraFinalCoverAccumulatedGrowthAt W M p := by
  intro p hPositive
  exact extra_final_cover_accumulation_plan_at_implies_accumulated_growth_at
    (hPlan p hPositive)

theorem extra_final_cover_accumulated_growth_at_implies_linear_pump_at
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p)
    (hAccum : ExtraFinalCoverAccumulatedGrowthAt W M p) :
    ExtraFinalCoverLinearPumpAt W M p := by
  intro hExtra n
  obtain ⟨M', hReach, hAccumLe⟩ := hAccum hExtra n
  have hNLeAccum : n ≤ W.initial p + n * (M p - W.final p) :=
    Nat.le_trans
      (Nat.le_mul_of_pos_right (m := M p - W.final p) n hPositive)
      (Nat.le_add_left _ _)
  exact ⟨M', hReach, Nat.le_trans hNLeAccum hAccumLe⟩

theorem extra_final_cover_accumulated_growth_implies_linear_pump
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hAccum :
      ∀ p : W.net.Place,
        0 < M p - W.final p →
          ExtraFinalCoverAccumulatedGrowthAt W M p) :
    ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p := by
  obtain ⟨p, hPositive⟩ :=
    hasExtraTokensAtFinalCover_exists_positive_remainder hExtra
  exact ⟨p,
    extra_final_cover_accumulated_growth_at_implies_linear_pump_at
      hPositive (hAccum p hPositive)⟩

theorem extra_final_cover_closedFormGrowth_implies_linear_pump
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hClosed : ExtraFinalCoverClosedFormGrowth W M) :
    ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p :=
  extra_final_cover_accumulated_growth_implies_linear_pump
    hExtra
    (extra_final_cover_closedFormGrowth_implies_accumulated_growth
      hClosed)

theorem extra_final_cover_accumulation_plan_at_implies_linear_pump_at
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p)
    (hPlan : ExtraFinalCoverAccumulationPlanAt W M p) :
    ExtraFinalCoverLinearPumpAt W M p :=
  extra_final_cover_accumulated_growth_at_implies_linear_pump_at
    hPositive
    (extra_final_cover_accumulation_plan_at_implies_accumulated_growth_at
      hPlan)

theorem extra_final_cover_accumulation_plan_implies_linear_pump
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hPlan :
      ∀ p : W.net.Place,
        0 < M p - W.final p →
          ExtraFinalCoverAccumulationPlanAt W M p) :
    ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p := by
  obtain ⟨p, hPositive⟩ :=
    hasExtraTokensAtFinalCover_exists_positive_remainder hExtra
  exact ⟨p,
    extra_final_cover_accumulation_plan_at_implies_linear_pump_at
      hPositive (hPlan p hPositive)⟩

/--
An extra final-cover marking can be pumped in the short-circuited net past
every proposed global token bound.
-/
def ExtraFinalCoverPumpsAboveEveryBound (W : WFNet) (M : W.Marking) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ k : Nat, ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧
        ∃ p : W.net.Place, k < M' p

theorem extra_final_cover_linear_pump_at_implies_pumps_above_every_bound
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hLinear : ExtraFinalCoverLinearPumpAt W M p) :
    ExtraFinalCoverPumpsAboveEveryBound W M := by
  intro hExtra k
  obtain ⟨M', hReach, hLe⟩ := hLinear hExtra (k + 1)
  exact ⟨M', hReach, p, Nat.lt_of_succ_le hLe⟩

theorem extra_final_cover_linear_pump_implies_pumps_above_every_bound
    {W : WFNet} {M : W.Marking}
    (hLinear : ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    ExtraFinalCoverPumpsAboveEveryBound W M := by
  obtain ⟨p, hPumpAt⟩ := hLinear
  exact extra_final_cover_linear_pump_at_implies_pumps_above_every_bound
    hPumpAt

theorem extra_final_cover_linear_pump_at_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hLinear : ExtraFinalCoverLinearPumpAt W M p)
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  linearTokenGrowthAt_not_bounded (N := shortCircuit W)
    (M₀ := W.initial) (p := p) (hLinear hExtra)

theorem extra_final_cover_linear_pump_at_not_boundedBy
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hLinear : ExtraFinalCoverLinearPumpAt W M p)
    (hExtra : HasExtraTokensAtFinalCover W M)
    (k : Nat) :
    ¬ BoundedBy (shortCircuit W) W.initial k :=
  linearTokenGrowthAt_not_boundedBy (N := shortCircuit W)
    (M₀ := W.initial) (p := p) (hLinear hExtra) k

theorem extra_final_cover_pumping_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hPump : ExtraFinalCoverPumpsAboveEveryBound W M)
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  not_bounded_of_forall_bound_reachable_gt (hPump hExtra)

theorem extra_final_cover_linear_pump_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hLinear : ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p)
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  extra_final_cover_pumping_implies_shortCircuit_unbounded
    (extra_final_cover_linear_pump_implies_pumps_above_every_bound hLinear)
    hExtra

theorem extra_final_cover_closedFormGrowth_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hClosed : ExtraFinalCoverClosedFormGrowth W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  extra_final_cover_linear_pump_implies_shortCircuit_unbounded
    (extra_final_cover_closedFormGrowth_implies_linear_pump
      hExtra hClosed)
    hExtra

theorem extra_final_cover_closedFormStep_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hStep : ExtraFinalCoverClosedFormStep W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  extra_final_cover_closedFormGrowth_implies_shortCircuit_unbounded
    hExtra
    (extra_final_cover_closedFormStep_implies_closedFormGrowth hStep)

theorem extra_final_cover_accumulation_plan_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hPlan :
      ∀ p : W.net.Place,
        0 < M p - W.final p →
          ExtraFinalCoverAccumulationPlanAt W M p) :
    ¬ Bounded (shortCircuit W) W.initial :=
  extra_final_cover_linear_pump_implies_shortCircuit_unbounded
    (extra_final_cover_accumulation_plan_implies_linear_pump
      hExtra hPlan)
    hExtra

/--
The remaining WOFLAN boundedness obligation: in a live and bounded
short-circuited net, no reachable marking may cover the final marking while
carrying extra tokens.
-/
def ShortCircuitBoundedExcludesExtraFinalCover (W : WFNet) : Prop :=
  Live (shortCircuit W) W.initial →
    Bounded (shortCircuit W) W.initial →
      ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M

theorem shortCircuit_bounded_excludes_extra_final_cover_of_pumping
    {W : WFNet}
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M) :
    ShortCircuitBoundedExcludesExtraFinalCover W := by
  intro _hLive hBounded M hExtra
  exact extra_final_cover_pumping_implies_shortCircuit_unbounded
    (hPump M) hExtra hBounded

theorem shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
    {W : WFNet}
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_pumping
    (fun M =>
      extra_final_cover_linear_pump_implies_pumps_above_every_bound
        (hLinear M))

theorem shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
    {W : WFNet}
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
    (fun M =>
      by
        by_cases hExtra : HasExtraTokensAtFinalCover W M
        · exact extra_final_cover_accumulated_growth_implies_linear_pump
            hExtra (hAccum M hExtra)
        · exact ⟨W.i, fun hFalse => False.elim (hExtra hFalse)⟩)

theorem shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
    {W : WFNet}
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
    (fun M _hExtra =>
      extra_final_cover_closedFormGrowth_implies_accumulated_growth
        (hClosed M))

theorem shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
    {W : WFNet}
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
    (fun M =>
      extra_final_cover_closedFormStep_implies_closedFormGrowth
        (hStep M))

theorem shortCircuit_bounded_excludes_extra_final_cover_of_accumulation_plan
    {W : WFNet}
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
    (fun M hExtra =>
      extra_final_cover_accumulation_plan_implies_accumulated_growth
        (hPlan M hExtra))

theorem proper_completion_iff_no_extra_tokens_at_final_cover
    (W : WFNet) :
    ProperCompletion W ↔
      ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M := by
  constructor
  · intro hProper M hExtra
    exact hExtra.2.2 (hProper M hExtra.1 hExtra.2.1)
  · intro hNoExtra M hReach hFinalCovered
    classical
    by_cases hEq : M = W.final
    · exact hEq
    · exact False.elim (hNoExtra M ⟨hReach, hFinalCovered, hEq⟩)

theorem not_proper_completion_iff_exists_extra_tokens_at_final_cover
    (W : WFNet) :
    ¬ ProperCompletion W ↔
      ∃ M : W.Marking, HasExtraTokensAtFinalCover W M := by
  classical
  rw [proper_completion_iff_no_extra_tokens_at_final_cover W]
  constructor
  · intro hNotAllNoExtra
    by_cases hExists : ∃ M : W.Marking, HasExtraTokensAtFinalCover W M
    · exact hExists
    · exact False.elim (hNotAllNoExtra (by
        intro M hExtra
        exact hExists ⟨M, hExtra⟩))
  · intro hExists hAllNoExtra
    obtain ⟨M, hExtra⟩ := hExists
    exact hAllNoExtra M hExtra

theorem not_proper_completion_implies_shortCircuit_unbounded_of_pumping
    {W : WFNet}
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial := by
  obtain ⟨M, hExtra⟩ :=
    (not_proper_completion_iff_exists_extra_tokens_at_final_cover W).1
      hNotProper
  exact extra_final_cover_pumping_implies_shortCircuit_unbounded
    (hPump M) hExtra

theorem not_proper_completion_implies_shortCircuit_unbounded_of_linear_pumping
    {W : WFNet}
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial :=
  not_proper_completion_implies_shortCircuit_unbounded_of_pumping
    (fun M =>
      extra_final_cover_linear_pump_implies_pumps_above_every_bound
        (hLinear M))
    hNotProper

theorem not_proper_completion_implies_shortCircuit_unbounded_of_closedFormGrowth
    {W : WFNet}
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial := by
  obtain ⟨M, hExtra⟩ :=
    (not_proper_completion_iff_exists_extra_tokens_at_final_cover W).1
      hNotProper
  exact extra_final_cover_closedFormGrowth_implies_shortCircuit_unbounded
    hExtra (hClosed M)

theorem not_proper_completion_implies_shortCircuit_unbounded_of_closedFormStep
    {W : WFNet}
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial := by
  obtain ⟨M, hExtra⟩ :=
    (not_proper_completion_iff_exists_extra_tokens_at_final_cover W).1
      hNotProper
  exact extra_final_cover_closedFormStep_implies_shortCircuit_unbounded
    hExtra (hStep M)

theorem not_proper_completion_implies_shortCircuit_unbounded_of_accumulation_plan
    {W : WFNet}
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial := by
  obtain ⟨M, hExtra⟩ :=
    (not_proper_completion_iff_exists_extra_tokens_at_final_cover W).1
      hNotProper
  exact extra_final_cover_accumulation_plan_implies_shortCircuit_unbounded
    hExtra (hPlan M hExtra)

theorem no_extra_tokens_at_final_cover_implies_proper_completion
    {W : WFNet}
    (hNoExtra : ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M) :
    ProperCompletion W :=
  (proper_completion_iff_no_extra_tokens_at_final_cover W).2 hNoExtra

theorem bounded_shortCircuit_implies_proper_completion_of_no_extra
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W) :
    ProperCompletion W :=
  no_extra_tokens_at_final_cover_implies_proper_completion
    (hNoExtra hLive hBounded)

theorem bounded_shortCircuit_implies_proper_completion_of_pumping
    {W : WFNet}
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_pumping hPump)

theorem bounded_shortCircuit_implies_proper_completion_of_linear_pumping
    {W : WFNet}
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
      hLinear)

theorem bounded_shortCircuit_implies_proper_completion_of_accumulated_growth
    {W : WFNet}
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
      hAccum)

theorem bounded_shortCircuit_implies_proper_completion_of_closedFormGrowth
    {W : WFNet}
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
      hClosed)

theorem bounded_shortCircuit_implies_proper_completion_of_closedFormStep
    {W : WFNet}
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
      hStep)

theorem bounded_shortCircuit_implies_proper_completion_of_accumulation_plan
    {W : WFNet}
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulation_plan
      hPlan)

end Petri
end Pm4Lean
