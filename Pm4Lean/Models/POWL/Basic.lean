import Pm4Lean.Models.Language

namespace Pm4Lean
namespace ProcessModel

/-- Atomic and composite POWL terms. -/
inductive POWL (Activity : Type u) where
  | tau : POWL Activity
  | activity : Activity → POWL Activity
  | xor : POWL Activity → POWL Activity → POWL Activity
  | loop : POWL Activity → POWL Activity → POWL Activity
  | partialOrder : List (POWL Activity) → (Nat → Nat → Prop) → POWL Activity

namespace POWL

variable {Activity : Type u}

/-- A binary relation is irreflexive on a finite index range. -/
def IrreflexiveOnRange (n : Nat) (r : Nat → Nat → Prop) : Prop :=
  ∀ i, i < n → ¬ r i i

/-- A binary relation is transitive on a finite index range. -/
def TransitiveOnRange (n : Nat) (r : Nat → Nat → Prop) : Prop :=
  ∀ i j k, i < n → j < n → k < n → r i j → r j k → r i k

/-- Well-formedness for POWL partial-order nodes. -/
def WellFormed : POWL Activity → Prop
  | tau => True
  | activity _ => True
  | xor l r => WellFormed l ∧ WellFormed r
  | loop body redo => WellFormed body ∧ WellFormed redo
  | partialOrder children order =>
      (∀ child ∈ children, WellFormed child) ∧
      IrreflexiveOnRange children.length order ∧
      TransitiveOnRange children.length order

/--
Concrete finite-trace semantics for POWL terms.

The current partial-order node semantics interleaves all child languages.  The
order relation is captured by `WellFormed`; order-constrained interleavings can
refine this definition once event-origin tracking is introduced.
-/
noncomputable def language : POWL Activity → Language Activity
  | tau => Language.epsilon
  | activity a => Language.singleton a
  | xor l r => Language.union (language l) (language r)
  | loop body redo =>
      Language.seq (language body)
        (Language.Star (Language.seq (language redo) (language body)))
  | partialOrder [l, r] order =>
      by
        classical
        exact
          if order 0 1 then
            Language.seq (language l) (language r)
          else if order 1 0 then
            Language.seq (language r) (language l)
          else
            Language.parallel (language l) (language r)
  | partialOrder children _ =>
      Language.interleaving (children.map language)

theorem tau_language :
    language (Activity := Activity) tau = Language.epsilon :=
  by simp [language]

theorem activity_language (a : Activity) :
    language (activity a) = Language.singleton a :=
  by simp [language]

theorem xor_language (l r : POWL Activity) :
    language (xor l r) = Language.union (language l) (language r) :=
  by simp [language]

theorem loop_body_once {body redo : POWL Activity} {σ : Trace Activity}
    (hBody : language body σ) :
    language (loop body redo) σ := by
  simp [language]
  exact ⟨σ, [], hBody, Language.Star.nil, by simp⟩

theorem partialOrder_nil_language (order : Nat → Nat → Prop) :
    language (partialOrder ([] : List (POWL Activity)) order) [] := by
  simpa [language] using
    (Language.interleaving_nil (Activity := Activity))

theorem partialOrder_singleton_equiv
    (child : POWL Activity) (order : Nat → Nat → Prop) :
    Language.Equivalent
      (language (partialOrder [child] order))
      (language child) := by
  simpa [language] using
    (Language.interleaving_singleton (language child))

theorem partialOrder_pair_sequence_language
    (l r : POWL Activity) :
    language (partialOrder [l, r] (fun i j => i = 0 ∧ j = 1)) =
      Language.seq (language l) (language r) := by
  classical
  simp [language]

theorem partialOrder_pair_parallel_language
    (l r : POWL Activity) :
    language (partialOrder [l, r] (fun _ _ => False)) =
      Language.parallel (language l) (language r) := by
  classical
  simp [language]

end POWL
end ProcessModel
end Pm4Lean
