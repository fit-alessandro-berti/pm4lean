import Pm4Lean.Models.Language
import Pm4Lean.Models.POWL2.Basic

namespace Pm4Lean
namespace ProcessModel
namespace POWL2

variable {Activity : Type u}

/-- Minimal natural-number list indexing, avoiding extra library dependencies. -/
def listGet? {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- A valid choice-graph path starting from the distinguished graph source. -/
inductive ChoicePathFrom (g : POWL2ChoiceGraph) :
    Nat → List Nat → Prop where
  | finish {i : Nat} :
      g.finish i → ChoicePathFrom g i [i]
  | step {i j : Nat} {rest : List Nat} :
      g.edge i j → ChoicePathFrom g j rest →
        ChoicePathFrom g i (i :: rest)

/-- A valid source-to-sink choice-graph path, represented by child indices. -/
inductive ChoicePath (g : POWL2ChoiceGraph) :
    List Nat → Prop where
  | empty :
      g.empty → ChoicePath g []
  | start {i : Nat} {rest : List Nat} :
      g.start i → ChoicePathFrom g i rest → ChoicePath g rest

/-- The language at `index`, or empty if the graph references no child there. -/
def childLanguage
    (children : List (Language Activity)) (index : Nat) : Language Activity :=
  match listGet? children index with
  | some child => child
  | none => Language.empty

/-- Sequential composition of the languages named by a choice-graph path. -/
def pathLanguage
    (children : List (Language Activity)) : List Nat → Language Activity
  | [] => Language.epsilon
  | i :: rest => Language.seq (childLanguage children i) (pathLanguage children rest)

/-- Semantics of a POWL2 choice graph: concatenate child traces along a path. -/
def choiceGraphLanguage
    (children : List (Language Activity)) (graph : POWL2ChoiceGraph) :
    Language Activity :=
  fun σ => ∃ path : List Nat,
    ChoicePath graph path ∧ pathLanguage children path σ

/-- POWL2 trace semantics, with choice graphs as first-class constructs. -/
noncomputable def language : POWL2 Activity → Language Activity
  | tau => Language.epsilon
  | activity a => Language.singleton a
  | loop body redo =>
      Language.seq (language body)
        (Language.Star (Language.seq (language redo) (language body)))
  | choiceGraph children graph => choiceGraphLanguage (children.map language) graph
  | partialOrder children order =>
      Language.partialOrder (children.map language) order

theorem tau_language :
    language (Activity := Activity) tau = Language.epsilon :=
  by simp [language]

theorem activity_language (a : Activity) :
    language (activity a) = Language.singleton a :=
  by simp [language]

theorem loop_language (body redo : POWL2 Activity) :
    language (loop body redo) =
      Language.seq (language body)
        (Language.Star (Language.seq (language redo) (language body))) :=
  by simp [language]

theorem choiceGraph_language
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph) :
    language (choiceGraph children graph) =
      choiceGraphLanguage (children.map language) graph :=
  by simp [language]

theorem partialOrder_language
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop) :
    language (partialOrder children order) =
      Language.partialOrder (children.map language) order :=
  by simp [language]

end POWL2
end ProcessModel
end Pm4Lean
