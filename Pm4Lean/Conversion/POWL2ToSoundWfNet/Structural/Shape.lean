import Pm4Lean.Conversion.POWL2ToSoundWfNet.Structural.Arcs

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace Structural

theorem mem_filterProp_of_mem {α : Type u} (p : α → Prop)
    {x : α} {xs : List α} (hMem : x ∈ xs) (hPred : p x) :
    x ∈ filterProp xs p := by
  classical
  simp [filterProp, hMem, hPred]

theorem entry_mem (p : POWL2 Activity) (addr : Address) :
    entry addr ∈ rawPlaces p addr := by
  cases p <;> simp [rawPlaces, entry, placesForPartialOrder]

theorem exit_mem (p : POWL2 Activity) (addr : Address) :
    exit addr ∈ rawPlaces p addr := by
  cases p <;> simp [rawPlaces, exit, placesForPartialOrder]

theorem rawPlacesChildren_entry_mem :
    ∀ (children : List (POWL2 Activity)) (addr : Address) (start i : Nat),
      i < children.length →
      entry (childAddr addr (start + i)) ∈
        rawPlacesChildren children addr start
  | [], _, _, i, h => False.elim (Nat.not_lt_zero i h)
  | child :: rest, addr, start, 0, _ => by
      have hEntry : entry (childAddr addr start) ∈
          rawPlaces child (childAddr addr start) :=
        entry_mem child (childAddr addr start)
      simpa [rawPlacesChildren] using Or.inl hEntry
  | child :: rest, addr, start, Nat.succ i, h => by
      have hRest : i < rest.length := Nat.succ_lt_succ_iff.mp h
      have hRec :
          entry (childAddr addr ((start + 1) + i)) ∈
            rawPlacesChildren rest addr (start + 1) :=
        rawPlacesChildren_entry_mem rest addr (start + 1) i hRest
      simpa [rawPlacesChildren, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using Or.inr hRec

theorem rawPlacesChildren_exit_mem :
    ∀ (children : List (POWL2 Activity)) (addr : Address) (start i : Nat),
      i < children.length →
      exit (childAddr addr (start + i)) ∈
        rawPlacesChildren children addr start
  | [], _, _, i, h => False.elim (Nat.not_lt_zero i h)
  | child :: rest, addr, start, 0, _ => by
      have hExit : exit (childAddr addr start) ∈
          rawPlaces child (childAddr addr start) :=
        exit_mem child (childAddr addr start)
      simpa [rawPlacesChildren] using Or.inl hExit
  | child :: rest, addr, start, Nat.succ i, h => by
      have hRest : i < rest.length := Nat.succ_lt_succ_iff.mp h
      have hRec :
          exit (childAddr addr ((start + 1) + i)) ∈
            rawPlacesChildren rest addr (start + 1) :=
        rawPlacesChildren_exit_mem rest addr (start + 1) i hRest
      simpa [rawPlacesChildren, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using Or.inr hRec

theorem rawChildEntry_mem
    (children : List (POWL2 Activity)) (addr : Address)
    {i : Nat} (hRange : i < children.length) :
    childEntry addr i ∈ rawPlacesChildren children addr 0 := by
  simpa [childEntry] using
    rawPlacesChildren_entry_mem children addr 0 i hRange

theorem rawChildExit_mem
    (children : List (POWL2 Activity)) (addr : Address)
    {i : Nat} (hRange : i < children.length) :
    childExit addr i ∈ rawPlacesChildren children addr 0 := by
  simpa [childExit] using
    rawPlacesChildren_exit_mem children addr 0 i hRange

theorem loop_body_entry_mem
    (body redo : POWL2 Activity) (addr : Address) :
    childEntry addr 0 ∈ rawPlaces (POWL2.loop body redo) addr := by
  have hEntry : entry (childAddr addr 0) ∈ rawPlaces body (childAddr addr 0) :=
    entry_mem body (childAddr addr 0)
  simpa [rawPlaces, childEntry] using Or.inr (Or.inr (Or.inl hEntry))

theorem loop_body_exit_mem
    (body redo : POWL2 Activity) (addr : Address) :
    childExit addr 0 ∈ rawPlaces (POWL2.loop body redo) addr := by
  have hExit : exit (childAddr addr 0) ∈ rawPlaces body (childAddr addr 0) :=
    exit_mem body (childAddr addr 0)
  simpa [rawPlaces, childExit] using Or.inr (Or.inr (Or.inl hExit))

theorem loop_redo_entry_mem
    (body redo : POWL2 Activity) (addr : Address) :
    childEntry addr 1 ∈ rawPlaces (POWL2.loop body redo) addr := by
  have hEntry : entry (childAddr addr 1) ∈ rawPlaces redo (childAddr addr 1) :=
    entry_mem redo (childAddr addr 1)
  simpa [rawPlaces, childEntry] using Or.inr (Or.inr (Or.inr hEntry))

theorem loop_redo_exit_mem
    (body redo : POWL2 Activity) (addr : Address) :
    childExit addr 1 ∈ rawPlaces (POWL2.loop body redo) addr := by
  have hExit : exit (childAddr addr 1) ∈ rawPlaces redo (childAddr addr 1) :=
    exit_mem redo (childAddr addr 1)
  simpa [rawPlaces, childExit] using Or.inr (Or.inr (Or.inr hExit))

theorem loop_start_transition_mem
    (body redo : POWL2 Activity) (addr : Address) :
    transition addr TransitionKind.loopStart ∈
      rawTransitions (POWL2.loop body redo) addr := by
  simp [rawTransitions]

theorem loop_exit_transition_mem
    (body redo : POWL2 Activity) (addr : Address) :
    transition addr TransitionKind.loopExit ∈
      rawTransitions (POWL2.loop body redo) addr := by
  simp [rawTransitions]

theorem loop_redo_transition_mem
    (body redo : POWL2 Activity) (addr : Address) :
    transition addr TransitionKind.loopRedo ∈
      rawTransitions (POWL2.loop body redo) addr := by
  simp [rawTransitions]

theorem loop_back_transition_mem
    (body redo : POWL2 Activity) (addr : Address) :
    transition addr TransitionKind.loopBack ∈
      rawTransitions (POWL2.loop body redo) addr := by
  simp [rawTransitions]

theorem loop_start_consumes_entry
    (body redo : POWL2 Activity) (addr : Address) :
    rawPre (POWL2.loop body redo)
      (transition addr TransitionKind.loopStart) (entry addr) = 1 := by
  simp [rawPre, rawMark, entry, transition]

theorem loop_start_produces_body_entry
    (body redo : POWL2 Activity) (addr : Address) :
    rawPost (POWL2.loop body redo)
      (transition addr TransitionKind.loopStart) (childEntry addr 0) = 1 := by
  simp [rawPost, rawMark, childEntry, childAddr, entry, transition]

theorem loop_redo_produces_redo_entry
    (body redo : POWL2 Activity) (addr : Address) :
    rawPost (POWL2.loop body redo)
      (transition addr TransitionKind.loopRedo) (childEntry addr 1) = 1 := by
  simp [rawPost, rawMark, childEntry, childAddr, entry, transition]

theorem loop_exit_consumes_body_exit
    (body redo : POWL2 Activity) (addr : Address) :
    rawPre (POWL2.loop body redo)
      (transition addr TransitionKind.loopExit) (childExit addr 0) = 1 := by
  simp [rawPre, rawMark, childExit, childAddr, exit, transition]

theorem loop_exit_produces_exit
    (body redo : POWL2 Activity) (addr : Address) :
    rawPost (POWL2.loop body redo)
      (transition addr TransitionKind.loopExit) (exit addr) = 1 := by
  simp [rawPost, rawMark, exit, transition]

theorem loop_redo_consumes_body_exit
    (body redo : POWL2 Activity) (addr : Address) :
    rawPre (POWL2.loop body redo)
      (transition addr TransitionKind.loopRedo) (childExit addr 0) = 1 := by
  simp [rawPre, rawMark, childExit, childAddr, exit, transition]

theorem loop_back_consumes_redo_exit
    (body redo : POWL2 Activity) (addr : Address) :
    rawPre (POWL2.loop body redo)
      (transition addr TransitionKind.loopBack) (childExit addr 1) = 1 := by
  simp [rawPre, rawMark, childExit, childAddr, exit, transition]

theorem loop_back_produces_body_entry
    (body redo : POWL2 Activity) (addr : Address) :
    rawPost (POWL2.loop body redo)
      (transition addr TransitionKind.loopBack) (childEntry addr 0) = 1 := by
  simp [rawPost, rawMark, childEntry, childAddr, entry, transition]

theorem partialOrder_fork_transition_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) :
    transition addr TransitionKind.poFork ∈
      rawTransitions (POWL2.partialOrder children order) addr := by
  by_cases h : children.length = 0
  · simp [rawTransitions, transitionsForPartialOrder, h]
  · simp [rawTransitions, transitionsForPartialOrder, h]

theorem partialOrder_fork_consumes_entry
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) :
    rawPre (POWL2.partialOrder children order)
      (transition addr TransitionKind.poFork) (entry addr) = 1 := by
  simp [rawPre, rawMark, entry, transition]

theorem partialOrder_fork_empty_produces_exit
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) (hEmpty : children.length = 0) :
    rawPost (POWL2.partialOrder children order)
      (transition addr TransitionKind.poFork) (exit addr) = 1 := by
  simp [rawPost, rawMark, exit, transition, hEmpty]

theorem partialOrder_join_transition_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) (h : children.length ≠ 0) :
    transition addr TransitionKind.poJoin ∈
      rawTransitions (POWL2.partialOrder children order) addr := by
  simp [rawTransitions, transitionsForPartialOrder, h]

theorem partialOrder_begin_transition_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) {i : Nat} (hRange : i < children.length) :
    transition addr (TransitionKind.poBegin i) ∈
      rawTransitions (POWL2.partialOrder children order) addr := by
  have hNonempty : children.length ≠ 0 := by
    intro hZero
    rw [hZero] at hRange
    exact Nat.not_lt_zero i hRange
  simp [rawTransitions, transitionsForPartialOrder, hNonempty]
  exact Or.inr (Or.inl ⟨i, hRange, rfl⟩)

theorem partialOrder_complete_transition_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) {i : Nat} (hRange : i < children.length) :
    transition addr (TransitionKind.poComplete i) ∈
      rawTransitions (POWL2.partialOrder children order) addr := by
  have hNonempty : children.length ≠ 0 := by
    intro hZero
    rw [hZero] at hRange
    exact Nat.not_lt_zero i hRange
  simp [rawTransitions, transitionsForPartialOrder, hNonempty]
  exact Or.inr (Or.inr (Or.inl ⟨i, hRange, rfl⟩))

theorem partialOrder_begin_produces_child_entry
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) (i : Nat) :
    rawPost (POWL2.partialOrder children order)
      (transition addr (TransitionKind.poBegin i)) (childEntry addr i) = 1 := by
  simp [rawPost, rawMark, childEntry, childAddr, entry, transition]

theorem partialOrder_complete_consumes_child_exit
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) (i : Nat) :
    rawPre (POWL2.partialOrder children order)
      (transition addr (TransitionKind.poComplete i)) (childExit addr i) = 1 := by
  simp [rawPre, rawMark, childExit, childAddr, exit, transition]

theorem partialOrder_join_produces_exit
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) :
    rawPost (POWL2.partialOrder children order)
      (transition addr TransitionKind.poJoin) (exit addr) = 1 := by
  simp [rawPost, rawMark, exit, transition]

theorem choiceGraph_empty_transition_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) (h : graph.empty) :
    transition addr TransitionKind.choiceEmpty ∈
      rawTransitions (POWL2.choiceGraph children graph) addr := by
  classical
  simp [rawTransitions, h]

theorem choiceGraph_empty_consumes_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) :
    rawPre (POWL2.choiceGraph children graph)
      (transition addr TransitionKind.choiceEmpty) (entry addr) = 1 := by
  simp [rawPre, rawMark, entry, transition]

theorem choiceGraph_empty_produces_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) :
    rawPost (POWL2.choiceGraph children graph)
      (transition addr TransitionKind.choiceEmpty) (exit addr) = 1 := by
  simp [rawPost, rawMark, exit, transition]

theorem choiceGraph_start_transition_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) {i : Nat} (hStart : graph.start i)
    (hRange : i < children.length) :
    transition addr (TransitionKind.choiceStart i) ∈
      rawTransitions (POWL2.choiceGraph children graph) addr := by
  classical
  have hInFilter :
      i ∈ indicesWhere children.length graph.start :=
    mem_filterProp_of_mem graph.start (List.mem_range.mpr hRange) hStart
  simp [rawTransitions]
  exact Or.inr (Or.inl ⟨i, hInFilter, rfl⟩)

theorem choiceGraph_start_consumes_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) (i : Nat) :
    rawPre (POWL2.choiceGraph children graph)
      (transition addr (TransitionKind.choiceStart i)) (entry addr) = 1 := by
  simp [rawPre, rawMark, entry, transition]

theorem choiceGraph_start_produces_child_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) (i : Nat) :
    rawPost (POWL2.choiceGraph children graph)
      (transition addr (TransitionKind.choiceStart i)) (childEntry addr i) = 1 := by
  simp [rawPost, rawMark, childEntry, childAddr, entry, transition]

theorem choiceGraph_edge_transition_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) {i j : Nat} (hEdge : graph.edge i j)
    (hI : i < children.length) (hJ : j < children.length) :
    transition addr (TransitionKind.choiceEdge i j) ∈
      rawTransitions (POWL2.choiceGraph children graph) addr := by
  classical
  have hInFilter :
      (i, j) ∈ edgesWhere children.length graph.edge :=
    mem_filterProp_of_mem (fun edge : Nat × Nat => graph.edge edge.1 edge.2)
      (by
        unfold pairsUpTo
        apply List.mem_flatten.mpr
        exact ⟨(List.range children.length).map (fun j => (i, j)),
          List.mem_map.mpr ⟨i, List.mem_range.mpr hI, rfl⟩,
          List.mem_map.mpr ⟨j, List.mem_range.mpr hJ, rfl⟩⟩)
      hEdge
  simp [rawTransitions]
  exact Or.inr (Or.inr (Or.inl ⟨i, j, hInFilter, rfl⟩))

theorem choiceGraph_edge_consumes_source_child_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) (i j : Nat) :
    rawPre (POWL2.choiceGraph children graph)
      (transition addr (TransitionKind.choiceEdge i j)) (childExit addr i) = 1 := by
  simp [rawPre, rawMark, childExit, childAddr, exit, transition]

theorem choiceGraph_edge_produces_target_child_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) (i j : Nat) :
    rawPost (POWL2.choiceGraph children graph)
      (transition addr (TransitionKind.choiceEdge i j)) (childEntry addr j) = 1 := by
  simp [rawPost, rawMark, childEntry, childAddr, entry, transition]

theorem choiceGraph_end_transition_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) {i : Nat} (hFinish : graph.finish i)
    (hRange : i < children.length) :
    transition addr (TransitionKind.choiceEnd i) ∈
      rawTransitions (POWL2.choiceGraph children graph) addr := by
  classical
  have hInFilter :
      i ∈ indicesWhere children.length graph.finish :=
    mem_filterProp_of_mem graph.finish (List.mem_range.mpr hRange) hFinish
  simp [rawTransitions]
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hInFilter, rfl⟩)))

theorem choiceGraph_end_consumes_child_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) (i : Nat) :
    rawPre (POWL2.choiceGraph children graph)
      (transition addr (TransitionKind.choiceEnd i)) (childExit addr i) = 1 := by
  simp [rawPre, rawMark, childExit, childAddr, exit, transition]

theorem choiceGraph_end_produces_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) (i : Nat) :
    rawPost (POWL2.choiceGraph children graph)
      (transition addr (TransitionKind.choiceEnd i)) (exit addr) = 1 := by
  simp [rawPost, rawMark, exit, transition]

end Structural

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
