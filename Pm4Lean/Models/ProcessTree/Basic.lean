import Pm4Lean.Models.Language

namespace Pm4Lean
namespace ProcessModel

/-- Basic process-tree syntax. -/
inductive ProcessTree (Activity : Type u) where
  | tau : ProcessTree Activity
  | activity : Activity → ProcessTree Activity
  | sequence : ProcessTree Activity → ProcessTree Activity → ProcessTree Activity
  | exclusiveChoice : ProcessTree Activity → ProcessTree Activity → ProcessTree Activity
  | parallel : ProcessTree Activity → ProcessTree Activity → ProcessTree Activity
  | loop : ProcessTree Activity → ProcessTree Activity → ProcessTree Activity
deriving Repr

namespace ProcessTree

variable {Activity : Type u}

/-- Number of visible activity leaves. -/
def activityCount : ProcessTree Activity → Nat
  | tau => 0
  | activity _ => 1
  | sequence l r => activityCount l + activityCount r
  | exclusiveChoice l r => activityCount l + activityCount r
  | parallel l r => activityCount l + activityCount r
  | loop body redo => activityCount body + activityCount redo

theorem activityCount_nonnegative (T : ProcessTree Activity) :
    0 ≤ activityCount T :=
  Nat.zero_le _

/--
Concrete finite-trace semantics for process trees.

The loop node follows the standard process-tree intuition: execute the body
once, then repeat zero or more `redo; body` rounds.
-/
def language : ProcessTree Activity → Language Activity
  | tau => Language.epsilon
  | activity a => Language.singleton a
  | sequence l r => Language.seq (language l) (language r)
  | exclusiveChoice l r => Language.union (language l) (language r)
  | parallel l r => Language.parallel (language l) (language r)
  | loop body redo =>
      Language.seq (language body)
        (Language.Star (Language.seq (language redo) (language body)))

theorem tau_language :
    language (Activity := Activity) tau = Language.epsilon :=
  rfl

theorem activity_language (a : Activity) :
    language (activity a) = Language.singleton a :=
  rfl

theorem sequence_language (l r : ProcessTree Activity) :
    language (sequence l r) = Language.seq (language l) (language r) :=
  rfl

theorem exclusiveChoice_language (l r : ProcessTree Activity) :
    language (exclusiveChoice l r) =
      Language.union (language l) (language r) :=
  rfl

theorem parallel_language (l r : ProcessTree Activity) :
    language (parallel l r) =
      Language.parallel (language l) (language r) :=
  rfl

theorem loop_body_once {body redo : ProcessTree Activity} {σ : Trace Activity}
    (hBody : language body σ) :
    language (loop body redo) σ := by
  exact ⟨σ, [], hBody, Language.Star.nil, by simp⟩

theorem tau_seq_left_equiv (T : ProcessTree Activity) :
    Language.Equivalent (language (sequence tau T)) (language T) := by
  exact Language.seq_epsilon_left (language T)

theorem tau_seq_right_equiv (T : ProcessTree Activity) :
    Language.Equivalent (language (sequence T tau)) (language T) := by
  exact Language.seq_epsilon_right (language T)

end ProcessTree
end ProcessModel
end Pm4Lean
