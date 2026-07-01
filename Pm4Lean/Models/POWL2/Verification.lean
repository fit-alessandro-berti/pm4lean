import Pm4Lean.Models.POWL.Verification
import Pm4Lean.Models.POWL2.Semantics

namespace Pm4Lean
namespace ProcessModel
namespace POWL2

variable {Activity : Type u}

theorem listGet?_mem {α : Type u} {xs : List α} {i : Nat} {x : α}
    (h : listGet? xs i = some x) :
    x ∈ xs := by
  induction xs generalizing i with
  | nil =>
      cases i <;> simp [listGet?] at h
  | cons head tail ih =>
      cases i with
      | zero =>
          simp [listGet?] at h
          subst h
          simp
      | succ i =>
          simp
          exact Or.inr (ih h)

theorem exists_listGet?_of_lt {α : Type u} :
    ∀ {xs : List α} {i : Nat}, i < xs.length → ∃ x, listGet? xs i = some x
  | [], i, h => False.elim (Nat.not_lt_zero i h)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, Nat.succ i, h =>
      exists_listGet?_of_lt (xs := xs) (i := i)
        (Nat.succ_lt_succ_iff.mp h)

theorem listGet?_map {α β : Type u} (f : α → β) :
    ∀ {xs : List α} {i : Nat} {x : α},
      listGet? xs i = some x →
        listGet? (xs.map f) i = some (f x)
  | [], i, _, h => by
      cases i <;> simp [listGet?] at h
  | _ :: _, 0, _, h => by
      simp [listGet?] at h ⊢
      exact congrArg f h
  | _ :: xs, Nat.succ i, x, h => by
      simp [listGet?] at h ⊢
      exact listGet?_map f h

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

theorem choiceGraph_wellFormed_graph
    {children : List (POWL2 Activity)} {graph : POWL2ChoiceGraph}
    (h : WellFormed (choiceGraph children graph)) :
    POWL2ChoiceGraph.WellFormed children.length graph := by
  have h' :
      (∀ child ∈ children, WellFormed child) ∧
        POWL2ChoiceGraph.WellFormed children.length graph := by
    simpa [WellFormed] using h
  exact h'.2

theorem choiceGraph_min_arity
    {children : List (POWL2 Activity)} {graph : POWL2ChoiceGraph}
    (h : WellFormed (choiceGraph children graph)) :
    2 ≤ children.length :=
  (choiceGraph_wellFormed_graph h).1

theorem choicePathFrom_index_in_range
    {graph : POWL2ChoiceGraph} {n i : Nat} {path : List Nat}
    (hGraph : POWL2ChoiceGraph.WellFormed n graph)
    (hPath : ChoicePathFrom graph i path) :
    i < n := by
  induction hPath with
  | finish hFinish =>
      exact hGraph.2.2.1 _ hFinish
  | step hEdge _ _ =>
      exact (hGraph.2.2.2.1 _ _ hEdge).1

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
      exact hGraph.2.2.1 _ hFinish
  | step hEdge hRest ih =>
      intro j hMem
      simp at hMem
      cases hMem with
      | inl hEq =>
          subst hEq
          exact (hGraph.2.2.2.1 _ _ hEdge).1
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

theorem choicePath_index_has_child
    {children : List (POWL2 Activity)} {graph : POWL2ChoiceGraph}
    {path : List Nat}
    (hGraph : POWL2ChoiceGraph.WellFormed children.length graph)
    (hPath : ChoicePath graph path)
    {i : Nat} (hMem : i ∈ path) :
    ∃ child, listGet? children i = some child := by
  exact exists_listGet?_of_lt
    (choicePath_indices_in_range hGraph hPath i hMem)

theorem choicePathFrom_of_canReachFinish
    {graph : POWL2ChoiceGraph} :
    ∀ {i : Nat},
      POWL2ChoiceGraph.CanReachFinish graph i →
        ∃ path : List Nat,
          ChoicePathFrom graph i path ∧ i ∈ path
  | i, POWL2ChoiceGraph.CanReachFinish.finish hFinish =>
      ⟨[i], ChoicePathFrom.finish hFinish, by simp⟩
  | i, POWL2ChoiceGraph.CanReachFinish.step hEdge hReach =>
      by
        obtain ⟨path, hPath, _hMem⟩ :=
          choicePathFrom_of_canReachFinish hReach
        exact ⟨i :: path, ChoicePathFrom.step hEdge hPath, by simp⟩

theorem choicePath_of_reachable_with_suffix
    {graph : POWL2ChoiceGraph} :
    ∀ {i : Nat} {suffix : List Nat},
      POWL2ChoiceGraph.ReachableFromStart graph i →
      ChoicePathFrom graph i suffix →
        ∃ path : List Nat,
          ChoicePath graph path ∧ ∀ j, j ∈ suffix → j ∈ path
  | i, suffix, POWL2ChoiceGraph.ReachableFromStart.start hStart, hSuffix =>
      ⟨suffix, ChoicePath.start hStart hSuffix, fun _ hMem => hMem⟩
  | i, suffix,
      POWL2ChoiceGraph.ReachableFromStart.step hReach hEdge, hSuffix =>
      by
        obtain ⟨path, hPath, hContains⟩ :=
          choicePath_of_reachable_with_suffix hReach
            (ChoicePathFrom.step hEdge hSuffix)
        refine ⟨path, hPath, ?_⟩
        intro j hMem
        exact hContains j (by simp [hMem])

theorem choiceGraph_wellFormed_index_on_choicePath
    {graph : POWL2ChoiceGraph} {n i : Nat}
    (hGraph : POWL2ChoiceGraph.WellFormed n graph)
    (hRange : i < n) :
    ∃ path : List Nat, ChoicePath graph path ∧ i ∈ path := by
  obtain ⟨hReach, hCanReach⟩ := hGraph.2.2.2.2 i hRange
  obtain ⟨suffix, hSuffix, hMemSuffix⟩ :=
    choicePathFrom_of_canReachFinish hCanReach
  obtain ⟨path, hPath, hContains⟩ :=
    choicePath_of_reachable_with_suffix hReach hSuffix
  exact ⟨path, hPath, hContains i hMemSuffix⟩

theorem choiceGraph_path_child_wellFormed
    {children : List (POWL2 Activity)} {graph : POWL2ChoiceGraph}
    (h : WellFormed (choiceGraph children graph))
    {path : List Nat} (_hPath : ChoicePath graph path)
    {i : Nat} (_hMem : i ∈ path)
    {child : POWL2 Activity} (hGet : listGet? children i = some child) :
    WellFormed child :=
  choiceGraph_child_wellFormed h (listGet?_mem hGet)

theorem partialOrder_child_wellFormed
    {children : List (POWL2 Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order))
    {child : POWL2 Activity} (hChild : child ∈ children) :
    WellFormed child := by
  have h' :
      2 ≤ children.length ∧
      (∀ child ∈ children, WellFormed child) ∧
        POWL.IrreflexiveOnRange children.length order ∧
          POWL.TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.2.1 child hChild

theorem partialOrder_min_arity
    {children : List (POWL2 Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order)) :
    2 ≤ children.length := by
  have h' :
      2 ≤ children.length ∧
      (∀ child ∈ children, WellFormed child) ∧
        POWL.IrreflexiveOnRange children.length order ∧
          POWL.TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.1

theorem partialOrder_irreflexive
    {children : List (POWL2 Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order)) :
    POWL.IrreflexiveOnRange children.length order := by
  have h' :
      2 ≤ children.length ∧
      (∀ child ∈ children, WellFormed child) ∧
        POWL.IrreflexiveOnRange children.length order ∧
          POWL.TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.2.2.1

theorem partialOrder_transitive
    {children : List (POWL2 Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order)) :
    POWL.TransitiveOnRange children.length order := by
  have h' :
      2 ≤ children.length ∧
      (∀ child ∈ children, WellFormed child) ∧
        POWL.IrreflexiveOnRange children.length order ∧
          POWL.TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.2.2.2

end POWL2
end ProcessModel
end Pm4Lean
