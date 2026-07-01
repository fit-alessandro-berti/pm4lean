import Pm4Lean.Models.POWL.Verification
import Pm4Lean.Models.POWL2.Semantics

namespace Pm4Lean
namespace ProcessModel
namespace POWL2

variable {Activity : Type u}

theorem sequenceOrder_irreflexive (n : Nat) :
    POWL.IrreflexiveOnRange n (sequenceOrder n) := by
  intro i _ h
  exact Nat.lt_irrefl i h.1

theorem sequenceOrder_transitive (n : Nat) :
    POWL.TransitiveOnRange n (sequenceOrder n) := by
  intro i j k _ _ _ hij hjk
  exact ⟨Nat.lt_trans hij.1 hjk.1, hjk.2⟩

theorem parallelOrder_irreflexive (n : Nat) :
    POWL.IrreflexiveOnRange n parallelOrder := by
  intro _ _ h
  exact h

theorem parallelOrder_transitive (n : Nat) :
    POWL.TransitiveOnRange n parallelOrder := by
  intro _ _ _ _ _ _ h _
  exact False.elim h

theorem ofPOWL_wellFormed {p : POWL Activity}
    (h : POWL.WellFormed p) :
    WellFormed (ofPOWL p) :=
  by simpa [WellFormed] using h

theorem sequence_child_wellFormed
    {children : List (POWL2 Activity)}
    (h : WellFormed (sequence children))
    {child : POWL2 Activity} (hChild : child ∈ children) :
    WellFormed child := by
  have h' : ∀ child ∈ children, WellFormed child := by
    simpa [WellFormed] using h
  exact h' child hChild

theorem parallel_child_wellFormed
    {children : List (POWL2 Activity)}
    (h : WellFormed (parallel children))
    {child : POWL2 Activity} (hChild : child ∈ children) :
    WellFormed child := by
  have h' : ∀ child ∈ children, WellFormed child := by
    simpa [WellFormed] using h
  exact h' child hChild

theorem choiceGraph_child_wellFormed
    {children : List (POWL2 Activity)} {graph : POWL2ChoiceGraph}
    (h : WellFormed (choiceGraph children graph))
    {child : POWL2 Activity} (hChild : child ∈ children) :
    WellFormed child := by
  have h' :
      (∀ child ∈ children, WellFormed child) ∧
        POWL2ChoiceGraph.WellFormed children.length graph := by
    simpa [WellFormed] using h
  exact h'.1 child hChild

theorem choicePathFrom_index_in_range
    {graph : POWL2ChoiceGraph} {n i : Nat} {path : List Nat}
    (hGraph : POWL2ChoiceGraph.WellFormed n graph)
    (hPath : ChoicePathFrom graph i path) :
    i < n := by
  induction hPath with
  | finish hFinish =>
      exact hGraph.2.1 _ hFinish
  | step hEdge _ _ =>
      exact (hGraph.2.2 _ _ hEdge).1

theorem choicePathFrom_indices_in_range
    {graph : POWL2ChoiceGraph} {n i : Nat} {path : List Nat}
    (hGraph : POWL2ChoiceGraph.WellFormed n graph)
    (hPath : ChoicePathFrom graph i path) :
    ∀ j, j ∈ path → j < n := by
  induction hPath with
  | finish hFinish =>
      intro j hMem
      simp at hMem
      subst hMem
      exact hGraph.2.1 _ hFinish
  | step hEdge hRest ih =>
      intro j hMem
      simp at hMem
      cases hMem with
      | inl hEq =>
          subst hEq
          exact (hGraph.2.2 _ _ hEdge).1
      | inr hTail =>
          exact ih j hTail

theorem choicePath_indices_in_range
    {graph : POWL2ChoiceGraph} {n : Nat} {path : List Nat}
    (hGraph : POWL2ChoiceGraph.WellFormed n graph)
    (hPath : ChoicePath graph path) :
    ∀ j, j ∈ path → j < n := by
  intro j hMem
  cases hPath with
  | empty => cases hMem
  | start hStart hRest =>
      exact choicePathFrom_indices_in_range hGraph hRest j hMem

theorem partialOrder_child_wellFormed
    {children : List (POWL2 Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order))
    {child : POWL2 Activity} (hChild : child ∈ children) :
    WellFormed child := by
  have h' :
      (∀ child ∈ children, WellFormed child) ∧
        POWL.IrreflexiveOnRange children.length order ∧
          POWL.TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.1 child hChild

theorem partialOrder_irreflexive
    {children : List (POWL2 Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order)) :
    POWL.IrreflexiveOnRange children.length order := by
  have h' :
      (∀ child ∈ children, WellFormed child) ∧
        POWL.IrreflexiveOnRange children.length order ∧
          POWL.TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.2.1

theorem partialOrder_transitive
    {children : List (POWL2 Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order)) :
    POWL.TransitiveOnRange children.length order := by
  have h' :
      (∀ child ∈ children, WellFormed child) ∧
        POWL.IrreflexiveOnRange children.length order ∧
          POWL.TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.2.2

end POWL2
end ProcessModel
end Pm4Lean
