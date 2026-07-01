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

theorem prefixTransition_nil (t : RawTransition) :
    prefixTransition [] t = t := by
  cases t
  rfl

theorem prefixTransition_append (left right : Address) (t : RawTransition) :
    prefixTransition left (prefixTransition right t) =
      prefixTransition (left ++ right) t := by
  cases t
  simp [prefixTransition, List.append_assoc]

theorem prefixPlace_nil (q : RawPlace) :
    prefixPlace [] q = q := by
  cases q
  rfl

theorem prefixPlace_append (left right : Address) (q : RawPlace) :
    prefixPlace left (prefixPlace right q) =
      prefixPlace (left ++ right) q := by
  cases q
  simp [prefixPlace, List.append_assoc]

theorem placesForPartialOrder_prefix_mem
    (pref addr : Address) (n : Nat) {q : RawPlace}
    (hMem : q ∈ placesForPartialOrder addr n) :
    prefixPlace pref q ∈ placesForPartialOrder (pref ++ addr) n := by
  simp [placesForPartialOrder] at hMem ⊢
  rcases hMem with hEntry | hExit | hReady | hDone | hPred
  · subst hEntry
    simp [prefixPlace, entry]
  · subst hExit
    simp [prefixPlace, exit]
  · rcases hReady with ⟨i, hRange, rfl⟩
    exact Or.inr (Or.inr (Or.inl ⟨i, hRange, by
      simp [prefixPlace, poReady]⟩))
  · rcases hDone with ⟨i, hRange, rfl⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hRange, by
      simp [prefixPlace, poDone]⟩)))
  · rcases hPred with ⟨i, j, hPair, rfl⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, hPair, by
      simp [prefixPlace, poPredDone]⟩)))

theorem placesForPartialOrder_addr_suffix
    (addr : Address) (n : Nat) {q : RawPlace}
    (hMem : q ∈ placesForPartialOrder addr n) :
    ∃ suffix : Address, q.addr = addr ++ suffix := by
  simp [placesForPartialOrder] at hMem
  rcases hMem with hEntry | hExit | hReady | hDone | hPred
  · subst hEntry
    exact ⟨[], by simp [entry]⟩
  · subst hExit
    exact ⟨[], by simp [exit]⟩
  · rcases hReady with ⟨i, _hRange, rfl⟩
    exact ⟨[], by simp [poReady]⟩
  · rcases hDone with ⟨i, _hRange, rfl⟩
    exact ⟨[], by simp [poDone]⟩
  · rcases hPred with ⟨i, j, _hPair, rfl⟩
    exact ⟨[], by simp [poPredDone]⟩

mutual
  theorem rawPlaces_prefix_mem :
      ∀ (p : POWL2 Activity) (pref addr : Address) {q : RawPlace},
        q ∈ rawPlaces p addr →
          prefixPlace pref q ∈ rawPlaces p (pref ++ addr)
    | POWL2.tau, pref, addr, q, hMem => by
        simp [rawPlaces] at hMem ⊢
        rcases hMem with hEntry | hExit
        · subst hEntry
          simp [prefixPlace, entry]
        · subst hExit
          simp [prefixPlace, exit]
    | POWL2.activity _, pref, addr, q, hMem => by
        simp [rawPlaces] at hMem ⊢
        rcases hMem with hEntry | hExit
        · subst hEntry
          simp [prefixPlace, entry]
        · subst hExit
          simp [prefixPlace, exit]
    | POWL2.loop body redo, pref, addr, q, hMem => by
        simp [rawPlaces] at hMem ⊢
        rcases hMem with hEntry | hExit | hBody | hRedo
        · subst hEntry
          simp [prefixPlace, entry]
        · subst hExit
          simp [prefixPlace, exit]
        · exact Or.inr (Or.inr (Or.inl (by
            simpa [childAddr, List.append_assoc] using
              rawPlaces_prefix_mem body pref (childAddr addr 0) hBody)))
        · exact Or.inr (Or.inr (Or.inr (by
            simpa [childAddr, List.append_assoc] using
              rawPlaces_prefix_mem redo pref (childAddr addr 1) hRedo)))
    | POWL2.choiceGraph children graph, pref, addr, q, hMem => by
        simp [rawPlaces] at hMem ⊢
        rcases hMem with hEntry | hExit | hChildren
        · subst hEntry
          simp [prefixPlace, entry]
        · subst hExit
          simp [prefixPlace, exit]
        · exact Or.inr (Or.inr
            (rawPlacesChildren_prefix_mem children pref addr 0 hChildren))
    | POWL2.partialOrder children order, pref, addr, q, hMem => by
        have hSplit :
            q ∈ placesForPartialOrder addr children.length ∨
              q ∈ rawPlacesChildren children addr 0 := by
          simpa [rawPlaces] using List.mem_append.mp hMem
        apply List.mem_append.mpr
        cases hSplit with
        | inl hConn =>
            exact Or.inl
              (placesForPartialOrder_prefix_mem pref addr
                children.length hConn)
        | inr hChildren =>
            exact Or.inr
              (rawPlacesChildren_prefix_mem children pref addr 0 hChildren)

  theorem rawPlacesChildren_prefix_mem :
      ∀ (children : List (POWL2 Activity)) (pref addr : Address) (start : Nat)
        {q : RawPlace},
        q ∈ rawPlacesChildren children addr start →
          prefixPlace pref q ∈
            rawPlacesChildren children (pref ++ addr) start
    | [], _, _, _, q, hMem => by
        simp [rawPlacesChildren] at hMem
    | child :: rest, pref, addr, start, q, hMem => by
        simp [rawPlacesChildren] at hMem ⊢
        rcases hMem with hHead | hRest
        · exact Or.inl (by
            simpa [childAddr, List.append_assoc] using
              rawPlaces_prefix_mem child pref
                (childAddr addr start) hHead)
        · exact Or.inr
              (rawPlacesChildren_prefix_mem rest pref addr
              (start + 1) hRest)
end

mutual
  theorem rawPlaces_addr_suffix :
      ∀ (p : POWL2 Activity) (addr : Address) {q : RawPlace},
        q ∈ rawPlaces p addr →
          ∃ suffix : Address, q.addr = addr ++ suffix
    | POWL2.tau, addr, q, hMem => by
        simp [rawPlaces] at hMem
        rcases hMem with hEntry | hExit
        · subst hEntry
          exact ⟨[], by simp [entry]⟩
        · subst hExit
          exact ⟨[], by simp [exit]⟩
    | POWL2.activity _, addr, q, hMem => by
        simp [rawPlaces] at hMem
        rcases hMem with hEntry | hExit
        · subst hEntry
          exact ⟨[], by simp [entry]⟩
        · subst hExit
          exact ⟨[], by simp [exit]⟩
    | POWL2.loop body redo, addr, q, hMem => by
        simp [rawPlaces] at hMem
        rcases hMem with hEntry | hExit | hBody | hRedo
        · subst hEntry
          exact ⟨[], by simp [entry]⟩
        · subst hExit
          exact ⟨[], by simp [exit]⟩
        · rcases rawPlaces_addr_suffix body (childAddr addr 0) hBody
            with ⟨suffix, hAddr⟩
          exact ⟨[0] ++ suffix, by simpa [childAddr, List.append_assoc] using hAddr⟩
        · rcases rawPlaces_addr_suffix redo (childAddr addr 1) hRedo
            with ⟨suffix, hAddr⟩
          exact ⟨[1] ++ suffix, by simpa [childAddr, List.append_assoc] using hAddr⟩
    | POWL2.choiceGraph children graph, addr, q, hMem => by
        simp [rawPlaces] at hMem
        rcases hMem with hEntry | hExit | hChildren
        · subst hEntry
          exact ⟨[], by simp [entry]⟩
        · subst hExit
          exact ⟨[], by simp [exit]⟩
        · exact rawPlacesChildren_addr_suffix children addr 0 hChildren
    | POWL2.partialOrder children order, addr, q, hMem => by
        have hSplit :
            q ∈ placesForPartialOrder addr children.length ∨
              q ∈ rawPlacesChildren children addr 0 := by
          simpa [rawPlaces] using List.mem_append.mp hMem
        cases hSplit with
        | inl hConn => exact placesForPartialOrder_addr_suffix addr children.length hConn
        | inr hChildren => exact rawPlacesChildren_addr_suffix children addr 0 hChildren

  theorem rawPlacesChildren_addr_suffix :
      ∀ (children : List (POWL2 Activity)) (addr : Address) (start : Nat)
        {q : RawPlace},
        q ∈ rawPlacesChildren children addr start →
          ∃ suffix : Address, q.addr = addr ++ suffix
    | [], addr, start, q, hMem => by
        simp [rawPlacesChildren] at hMem
    | child :: rest, addr, start, q, hMem => by
        simp [rawPlacesChildren] at hMem
        rcases hMem with hHead | hRest
        · rcases rawPlaces_addr_suffix child (childAddr addr start) hHead
            with ⟨suffix, hAddr⟩
          exact ⟨[start] ++ suffix, by simpa [childAddr, List.append_assoc] using hAddr⟩
        · exact rawPlacesChildren_addr_suffix rest addr (start + 1) hRest
end

mutual
  theorem rawPlaces_unprefix_mem :
      ∀ (p : POWL2 Activity) (pref addr : Address) {q : RawPlace},
        prefixPlace pref q ∈ rawPlaces p (pref ++ addr) →
          q ∈ rawPlaces p addr
    | POWL2.tau, pref, addr, q, hMem => by
        simp [rawPlaces] at hMem ⊢
        rcases hMem with hEntry | hExit
        · left
          cases q
          simp [prefixPlace, entry] at hEntry ⊢
          exact hEntry
        · right
          cases q
          simp [prefixPlace, exit] at hExit ⊢
          exact hExit
    | POWL2.activity _, pref, addr, q, hMem => by
        simp [rawPlaces] at hMem ⊢
        rcases hMem with hEntry | hExit
        · left
          cases q
          simp [prefixPlace, entry] at hEntry ⊢
          exact hEntry
        · right
          cases q
          simp [prefixPlace, exit] at hExit ⊢
          exact hExit
    | POWL2.loop body redo, pref, addr, q, hMem => by
        simp [rawPlaces] at hMem ⊢
        rcases hMem with hEntry | hExit | hBody | hRedo
        · left
          cases q
          simp [prefixPlace, entry] at hEntry ⊢
          exact hEntry
        · right; left
          cases q
          simp [prefixPlace, exit] at hExit ⊢
          exact hExit
        · exact Or.inr (Or.inr (Or.inl (by
            have hBody' :
                prefixPlace pref q ∈
                  rawPlaces body (pref ++ childAddr addr 0) := by
              simpa [childAddr, List.append_assoc] using hBody
            simpa [childAddr, List.append_assoc] using
              rawPlaces_unprefix_mem body pref (childAddr addr 0) hBody')))
        · exact Or.inr (Or.inr (Or.inr (by
            have hRedo' :
                prefixPlace pref q ∈
                  rawPlaces redo (pref ++ childAddr addr 1) := by
              simpa [childAddr, List.append_assoc] using hRedo
            simpa [childAddr, List.append_assoc] using
              rawPlaces_unprefix_mem redo pref (childAddr addr 1) hRedo')))
    | POWL2.choiceGraph children graph, pref, addr, q, hMem => by
        simp [rawPlaces] at hMem ⊢
        rcases hMem with hEntry | hExit | hChildren
        · left
          cases q
          simp [prefixPlace, entry] at hEntry ⊢
          exact hEntry
        · right; left
          cases q
          simp [prefixPlace, exit] at hExit ⊢
          exact hExit
        · exact Or.inr (Or.inr
            (rawPlacesChildren_unprefix_mem children pref addr 0 hChildren))
    | POWL2.partialOrder children order, pref, addr, q, hMem => by
        have hSplit :
            prefixPlace pref q ∈ placesForPartialOrder (pref ++ addr) children.length ∨
              prefixPlace pref q ∈ rawPlacesChildren children (pref ++ addr) 0 := by
          simpa [rawPlaces] using List.mem_append.mp hMem
        apply List.mem_append.mpr
        cases hSplit with
        | inl hConn =>
            left
            simp [placesForPartialOrder] at hConn ⊢
            rcases hConn with hEntry | hExit | hReady | hDone | hPred
            · left
              cases q
              simp [prefixPlace, entry] at hEntry ⊢
              exact hEntry
            · right; left
              cases q
              simp [prefixPlace, exit] at hExit ⊢
              exact hExit
            · rcases hReady with ⟨i, hRange, hEq⟩
              right; right; left
              cases q
              simp [prefixPlace, poReady] at hEq ⊢
              exact ⟨i, hRange, hEq⟩
            · rcases hDone with ⟨i, hRange, hEq⟩
              right; right; right; left
              cases q
              simp [prefixPlace, poDone] at hEq ⊢
              exact ⟨i, hRange, hEq⟩
            · rcases hPred with ⟨i, j, hPair, hEq⟩
              right; right; right; right
              cases q
              simp [prefixPlace, poPredDone] at hEq ⊢
              exact ⟨i, j, hPair, hEq⟩
        | inr hChildren =>
            right
            exact rawPlacesChildren_unprefix_mem children pref addr 0 hChildren

  theorem rawPlacesChildren_unprefix_mem :
      ∀ (children : List (POWL2 Activity)) (pref addr : Address) (start : Nat)
        {q : RawPlace},
        prefixPlace pref q ∈ rawPlacesChildren children (pref ++ addr) start →
          q ∈ rawPlacesChildren children addr start
    | [], pref, addr, start, q, hMem => by
        simp [rawPlacesChildren] at hMem
    | child :: rest, pref, addr, start, q, hMem => by
        simp [rawPlacesChildren] at hMem ⊢
        rcases hMem with hHead | hRest
        · exact Or.inl (by
            have hHead' :
                prefixPlace pref q ∈
                  rawPlaces child (pref ++ childAddr addr start) := by
              simpa [childAddr, List.append_assoc] using hHead
            simpa [childAddr, List.append_assoc] using
              rawPlaces_unprefix_mem child pref
                (childAddr addr start) hHead')
        · exact Or.inr
            (rawPlacesChildren_unprefix_mem rest pref addr
              (start + 1) hRest)
end

theorem prefixPlace_ne_mem_rawPlaces_of_child_index_ne
    (p : POWL2 Activity) {i j : Nat} (hNe : i ≠ j)
    (base : RawPlace)
    (hMem : prefixPlace [i] base ∈ rawPlaces p (childAddr [] j)) :
    False := by
  rcases rawPlaces_addr_suffix p (childAddr [] j) hMem with ⟨suffix, hAddr⟩
  have hHead : some i = some j := by
    simpa [prefixPlace, childAddr] using congrArg List.head? hAddr
  exact hNe (Option.some.inj hHead)

theorem transitionsForPartialOrder_prefix_mem
    (pref addr : Address) (n : Nat) {t : RawTransition}
    (hMem : t ∈ transitionsForPartialOrder addr n) :
    prefixTransition pref t ∈ transitionsForPartialOrder (pref ++ addr) n := by
  by_cases h : n = 0
  · simp [transitionsForPartialOrder, h] at hMem ⊢
    subst hMem
    simp [prefixTransition, transition]
  · simp [transitionsForPartialOrder, h] at hMem ⊢
    rcases hMem with hFork | hBegin | hComplete | hJoin
    · subst hFork
      simp [prefixTransition, transition]
    · rcases hBegin with ⟨i, hRange, rfl⟩
      exact Or.inr (Or.inl ⟨i, hRange, by
        simp [prefixTransition, transition]⟩)
    · rcases hComplete with ⟨i, hRange, rfl⟩
      exact Or.inr (Or.inr (Or.inl ⟨i, hRange, by
        simp [prefixTransition, transition]⟩))
    · subst hJoin
      simp [prefixTransition, transition]

theorem choiceGraphConnectors_prefix_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    [Decidable graph.empty]
    (pref addr : Address) {t : RawTransition}
    (hMem : t ∈
      (if graph.empty then [transition addr TransitionKind.choiceEmpty] else []) ++
        (indicesWhere children.length graph.start).map
          (fun i => transition addr (TransitionKind.choiceStart i)) ++
        (edgesWhere children.length graph.edge).map
          (fun edge => transition addr (TransitionKind.choiceEdge edge.1 edge.2)) ++
        (indicesWhere children.length graph.finish).map
          (fun i => transition addr (TransitionKind.choiceEnd i))) :
    prefixTransition pref t ∈
      (if graph.empty then [transition (pref ++ addr) TransitionKind.choiceEmpty] else []) ++
        (indicesWhere children.length graph.start).map
          (fun i => transition (pref ++ addr) (TransitionKind.choiceStart i)) ++
        (edgesWhere children.length graph.edge).map
          (fun edge => transition (pref ++ addr) (TransitionKind.choiceEdge edge.1 edge.2)) ++
        (indicesWhere children.length graph.finish).map
          (fun i => transition (pref ++ addr) (TransitionKind.choiceEnd i)) := by
  simp at hMem ⊢
  rcases hMem with hEmpty | hStart | hEdge | hFinish
  · rcases hEmpty with ⟨hEmpty, rfl⟩
    exact Or.inl ⟨hEmpty, by simp [prefixTransition, transition]⟩
  · rcases hStart with ⟨i, hIndex, rfl⟩
    exact Or.inr (Or.inl ⟨i, hIndex, by
      simp [prefixTransition, transition]⟩)
  · rcases hEdge with ⟨i, j, hIndex, rfl⟩
    exact Or.inr (Or.inr (Or.inl ⟨i, j, hIndex, by
      simp [prefixTransition, transition]⟩))
  · rcases hFinish with ⟨i, hIndex, rfl⟩
    exact Or.inr (Or.inr (Or.inr ⟨i, hIndex, by
      simp [prefixTransition, transition]⟩))

mutual
  theorem rawTransitions_prefix_mem :
      ∀ (p : POWL2 Activity) (pref addr : Address) {t : RawTransition},
        t ∈ rawTransitions p addr →
          prefixTransition pref t ∈ rawTransitions p (pref ++ addr)
    | POWL2.tau, pref, addr, t, hMem => by
        simp [rawTransitions] at hMem ⊢
        subst hMem
        simp [prefixTransition, transition]
    | POWL2.activity _, pref, addr, t, hMem => by
        simp [rawTransitions] at hMem ⊢
        subst hMem
        simp [prefixTransition, transition]
    | POWL2.loop body redo, pref, addr, t, hMem => by
        simp [rawTransitions] at hMem ⊢
        rcases hMem with hStart | hExit | hRedoT | hBack | hBody | hRedo
        · subst hStart
          simp [prefixTransition, transition]
        · subst hExit
          simp [prefixTransition, transition]
        · subst hRedoT
          simp [prefixTransition, transition]
        · subst hBack
          simp [prefixTransition, transition]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
            simpa [childAddr, List.append_assoc] using
              rawTransitions_prefix_mem body pref (childAddr addr 0) hBody)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
            simpa [childAddr, List.append_assoc] using
              rawTransitions_prefix_mem redo pref (childAddr addr 1) hRedo)))))
    | POWL2.choiceGraph children graph, pref, addr, t, hMem => by
        classical
        let front : List RawTransition :=
          (if graph.empty then [transition addr TransitionKind.choiceEmpty] else []) ++
            (indicesWhere children.length graph.start).map
              (fun i => transition addr (TransitionKind.choiceStart i)) ++
            (edgesWhere children.length graph.edge).map
              (fun edge => transition addr (TransitionKind.choiceEdge edge.1 edge.2)) ++
            (indicesWhere children.length graph.finish).map
              (fun i => transition addr (TransitionKind.choiceEnd i))
        have hSplit : t ∈ front ∨
            t ∈ rawTransitionsChildren children addr 0 := by
          simpa [rawTransitions, front] using List.mem_append.mp hMem
        apply List.mem_append.mpr
        cases hSplit with
        | inl hFront =>
            exact Or.inl (by
              simpa [front] using
                choiceGraphConnectors_prefix_mem children graph pref addr hFront)
        | inr hChildren =>
            exact Or.inr
              (rawTransitionsChildren_prefix_mem children pref addr 0 hChildren)
    | POWL2.partialOrder children order, pref, addr, t, hMem => by
        have hSplit :
            t ∈ transitionsForPartialOrder addr children.length ∨
              t ∈ rawTransitionsChildren children addr 0 := by
          simpa [rawTransitions] using List.mem_append.mp hMem
        apply List.mem_append.mpr
        cases hSplit with
        | inl hConn =>
            exact Or.inl
              (transitionsForPartialOrder_prefix_mem pref addr
                children.length hConn)
        | inr hChildren =>
            exact Or.inr
              (rawTransitionsChildren_prefix_mem children pref addr 0 hChildren)

  theorem rawTransitionsChildren_prefix_mem :
      ∀ (children : List (POWL2 Activity)) (pref addr : Address) (start : Nat)
        {t : RawTransition},
        t ∈ rawTransitionsChildren children addr start →
          prefixTransition pref t ∈
            rawTransitionsChildren children (pref ++ addr) start
    | [], _, _, _, t, hMem => by
        simp [rawTransitionsChildren] at hMem
    | child :: rest, pref, addr, start, t, hMem => by
        simp [rawTransitionsChildren] at hMem ⊢
        rcases hMem with hHead | hRest
        · exact Or.inl (by
            simpa [childAddr, List.append_assoc] using
              rawTransitions_prefix_mem child pref
                (childAddr addr start) hHead)
        · exact Or.inr
            (rawTransitionsChildren_prefix_mem rest pref addr
              (start + 1) hRest)
end

theorem rawPlacesChildren_mem :
    ∀ (children : List (POWL2 Activity)) (addr : Address) (start i : Nat)
      (child : POWL2 Activity) (q : RawPlace),
      POWL2.listGet? children i = some child →
      q ∈ rawPlaces child (childAddr addr (start + i)) →
      q ∈ rawPlacesChildren children addr start
  | [], _, _, i, _, _, hGet, _ => by
      cases i <;> simp [POWL2.listGet?] at hGet
  | head :: rest, addr, start, 0, child, q, hGet, hMem => by
      simp [POWL2.listGet?] at hGet
      subst hGet
      simpa [rawPlacesChildren] using Or.inl hMem
  | head :: rest, addr, start, Nat.succ i, child, q, hGet, hMem => by
      have hMem' :
          q ∈ rawPlaces child (childAddr addr ((start + 1) + i)) := by
        simpa [childAddr, Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hMem
      have hRec :
          q ∈ rawPlacesChildren rest addr (start + 1) :=
        rawPlacesChildren_mem rest addr (start + 1) i child q hGet hMem'
      simpa [rawPlacesChildren] using Or.inr hRec

theorem rawTransitionsChildren_mem :
    ∀ (children : List (POWL2 Activity)) (addr : Address) (start i : Nat)
      (child : POWL2 Activity) (t : RawTransition),
      POWL2.listGet? children i = some child →
      t ∈ rawTransitions child (childAddr addr (start + i)) →
      t ∈ rawTransitionsChildren children addr start
  | [], _, _, i, _, _, hGet, _ => by
      cases i <;> simp [POWL2.listGet?] at hGet
  | head :: rest, addr, start, 0, child, t, hGet, hMem => by
      simp [POWL2.listGet?] at hGet
      subst hGet
      simpa [rawTransitionsChildren] using Or.inl hMem
  | head :: rest, addr, start, Nat.succ i, child, t, hGet, hMem => by
      have hMem' :
          t ∈ rawTransitions child (childAddr addr ((start + 1) + i)) := by
        simpa [childAddr, Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hMem
      have hRec :
          t ∈ rawTransitionsChildren rest addr (start + 1) :=
        rawTransitionsChildren_mem rest addr (start + 1) i child t hGet hMem'
      simpa [rawTransitionsChildren] using Or.inr hRec

theorem loop_body_transition_mem
    (body redo : POWL2 Activity) (addr : Address) {t : RawTransition}
    (hMem : t ∈ rawTransitions body (childAddr addr 0)) :
    t ∈ rawTransitions (POWL2.loop body redo) addr := by
  simpa [rawTransitions] using
    (List.mem_append_right
      [ transition addr TransitionKind.loopStart,
        transition addr TransitionKind.loopExit,
        transition addr TransitionKind.loopRedo,
        transition addr TransitionKind.loopBack ]
      (List.mem_append_left (rawTransitions redo (childAddr addr 1)) hMem))

theorem loop_redo_transition_child_mem
    (body redo : POWL2 Activity) (addr : Address) {t : RawTransition}
    (hMem : t ∈ rawTransitions redo (childAddr addr 1)) :
    t ∈ rawTransitions (POWL2.loop body redo) addr := by
  simpa [rawTransitions] using
    (List.mem_append_right
      [ transition addr TransitionKind.loopStart,
        transition addr TransitionKind.loopExit,
        transition addr TransitionKind.loopRedo,
        transition addr TransitionKind.loopBack ]
      (List.mem_append_right (rawTransitions body (childAddr addr 0)) hMem))

theorem loop_body_place_mem
    (body redo : POWL2 Activity) (addr : Address) {q : RawPlace}
    (hMem : q ∈ rawPlaces body (childAddr addr 0)) :
    q ∈ rawPlaces (POWL2.loop body redo) addr := by
  simp [rawPlaces]
  exact Or.inr (Or.inr (Or.inl hMem))

theorem loop_redo_place_mem
    (body redo : POWL2 Activity) (addr : Address) {q : RawPlace}
    (hMem : q ∈ rawPlaces redo (childAddr addr 1)) :
    q ∈ rawPlaces (POWL2.loop body redo) addr := by
  simp [rawPlaces]
  exact Or.inr (Or.inr (Or.inr hMem))

theorem partialOrder_child_place_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) {i : Nat} {child : POWL2 Activity}
    {q : RawPlace}
    (hGet : POWL2.listGet? children i = some child)
    (hMem : q ∈ rawPlaces child (childAddr addr i)) :
    q ∈ rawPlaces (POWL2.partialOrder children order) addr := by
  have hChild :
      q ∈ rawPlacesChildren children addr 0 :=
    rawPlacesChildren_mem children addr 0 i child q hGet (by
      simpa using hMem)
  simp [rawPlaces]
  exact Or.inr hChild

theorem choiceGraph_child_place_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) {i : Nat} {child : POWL2 Activity}
    {q : RawPlace}
    (hGet : POWL2.listGet? children i = some child)
    (hMem : q ∈ rawPlaces child (childAddr addr i)) :
    q ∈ rawPlaces (POWL2.choiceGraph children graph) addr := by
  have hChild :
      q ∈ rawPlacesChildren children addr 0 :=
    rawPlacesChildren_mem children addr 0 i child q hGet (by
      simpa using hMem)
  simp [rawPlaces]
  exact Or.inr (Or.inr hChild)

theorem partialOrder_child_transition_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (addr : Address) {i : Nat} {child : POWL2 Activity}
    {t : RawTransition}
    (hGet : POWL2.listGet? children i = some child)
    (hMem : t ∈ rawTransitions child (childAddr addr i)) :
    t ∈ rawTransitions (POWL2.partialOrder children order) addr := by
  have hChild :
      t ∈ rawTransitionsChildren children addr 0 :=
    rawTransitionsChildren_mem children addr 0 i child t hGet (by
      simpa using hMem)
  simpa [rawTransitions] using
    (List.mem_append_right
      (transitionsForPartialOrder addr children.length) hChild)

theorem choiceGraph_child_transition_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) {i : Nat} {child : POWL2 Activity}
    {t : RawTransition}
    (hGet : POWL2.listGet? children i = some child)
    (hMem : t ∈ rawTransitions child (childAddr addr i)) :
    t ∈ rawTransitions (POWL2.choiceGraph children graph) addr := by
  have hChild :
      t ∈ rawTransitionsChildren children addr 0 :=
    rawTransitionsChildren_mem children addr 0 i child t hGet (by
      simpa using hMem)
  classical
  let front : List RawTransition :=
    (if graph.empty then [transition addr TransitionKind.choiceEmpty] else []) ++
      (indicesWhere children.length graph.start).map
        (fun i => transition addr (TransitionKind.choiceStart i)) ++
      (edgesWhere children.length graph.edge).map
        (fun edge => transition addr (TransitionKind.choiceEdge edge.1 edge.2)) ++
      (indicesWhere children.length graph.finish).map
        (fun i => transition addr (TransitionKind.choiceEnd i))
  simpa [rawTransitions, front] using
    (List.mem_append_right front hChild)

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
    (body redo : POWL2 Activity) :
    rawPre (POWL2.loop body redo)
      (transition [] TransitionKind.loopStart) (entry []) = 1 := by
  simp [rawPre, rawPreFor, rawMark, entry, transition]

theorem loop_start_produces_body_entry
    (body redo : POWL2 Activity) :
    rawPost (POWL2.loop body redo)
      (transition [] TransitionKind.loopStart) (childEntry [] 0) = 1 := by
  simp [rawPost, rawPostFor, rawMark, childEntry, childAddr, entry, transition]

theorem loop_redo_produces_redo_entry
    (body redo : POWL2 Activity) :
    rawPost (POWL2.loop body redo)
      (transition [] TransitionKind.loopRedo) (childEntry [] 1) = 1 := by
  simp [rawPost, rawPostFor, rawMark, childEntry, childAddr, entry, transition]

theorem loop_exit_consumes_body_exit
    (body redo : POWL2 Activity) :
    rawPre (POWL2.loop body redo)
      (transition [] TransitionKind.loopExit) (childExit [] 0) = 1 := by
  simp [rawPre, rawPreFor, rawMark, childExit, childAddr, exit, transition]

theorem loop_exit_produces_exit
    (body redo : POWL2 Activity) :
    rawPost (POWL2.loop body redo)
      (transition [] TransitionKind.loopExit) (exit []) = 1 := by
  simp [rawPost, rawPostFor, rawMark, exit, transition]

theorem loop_redo_consumes_body_exit
    (body redo : POWL2 Activity) :
    rawPre (POWL2.loop body redo)
      (transition [] TransitionKind.loopRedo) (childExit [] 0) = 1 := by
  simp [rawPre, rawPreFor, rawMark, childExit, childAddr, exit, transition]

theorem loop_back_consumes_redo_exit
    (body redo : POWL2 Activity) :
    rawPre (POWL2.loop body redo)
      (transition [] TransitionKind.loopBack) (childExit [] 1) = 1 := by
  simp [rawPre, rawPreFor, rawMark, childExit, childAddr, exit, transition]

theorem loop_back_produces_body_entry
    (body redo : POWL2 Activity) :
    rawPost (POWL2.loop body redo)
      (transition [] TransitionKind.loopBack) (childEntry [] 0) = 1 := by
  simp [rawPost, rawPostFor, rawMark, childEntry, childAddr, entry, transition]

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
    :
    rawPre (POWL2.partialOrder children order)
      (transition [] TransitionKind.poFork) (entry []) = 1 := by
  simp [rawPre, rawPreFor, rawMark, entry, transition]

theorem partialOrder_fork_empty_produces_exit
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (hEmpty : children.length = 0) :
    rawPost (POWL2.partialOrder children order)
      (transition [] TransitionKind.poFork) (exit []) = 1 := by
  simp [rawPost, rawPostFor, rawMark, exit, transition, hEmpty]

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
    (i : Nat) :
    rawPost (POWL2.partialOrder children order)
      (transition [] (TransitionKind.poBegin i)) (childEntry [] i) = 1 := by
  simp [rawPost, rawPostFor, rawMark, childEntry, childAddr, entry, transition]

theorem partialOrder_complete_consumes_child_exit
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (i : Nat) :
    rawPre (POWL2.partialOrder children order)
      (transition [] (TransitionKind.poComplete i)) (childExit [] i) = 1 := by
  simp [rawPre, rawPreFor, rawMark, childExit, childAddr, exit, transition]

theorem partialOrder_join_produces_exit
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    :
    rawPost (POWL2.partialOrder children order)
      (transition [] TransitionKind.poJoin) (exit []) = 1 := by
  simp [rawPost, rawPostFor, rawMark, exit, transition]

theorem choiceGraph_empty_transition_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (addr : Address) (h : graph.empty) :
    transition addr TransitionKind.choiceEmpty ∈
      rawTransitions (POWL2.choiceGraph children graph) addr := by
  classical
  simp [rawTransitions, h]

theorem choiceGraph_empty_consumes_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    :
    rawPre (POWL2.choiceGraph children graph)
      (transition [] TransitionKind.choiceEmpty) (entry []) = 1 := by
  simp [rawPre, rawPreFor, rawMark, entry, transition]

theorem choiceGraph_empty_produces_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    :
    rawPost (POWL2.choiceGraph children graph)
      (transition [] TransitionKind.choiceEmpty) (exit []) = 1 := by
  simp [rawPost, rawPostFor, rawMark, exit, transition]

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
    (i : Nat) :
    rawPre (POWL2.choiceGraph children graph)
      (transition [] (TransitionKind.choiceStart i)) (entry []) = 1 := by
  simp [rawPre, rawPreFor, rawMark, entry, transition]

theorem choiceGraph_start_produces_child_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (i : Nat) :
    rawPost (POWL2.choiceGraph children graph)
      (transition [] (TransitionKind.choiceStart i)) (childEntry [] i) = 1 := by
  simp [rawPost, rawPostFor, rawMark, childEntry, childAddr, entry, transition]

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
    (i j : Nat) :
    rawPre (POWL2.choiceGraph children graph)
      (transition [] (TransitionKind.choiceEdge i j)) (childExit [] i) = 1 := by
  simp [rawPre, rawPreFor, rawMark, childExit, childAddr, exit, transition]

theorem choiceGraph_edge_produces_target_child_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (i j : Nat) :
    rawPost (POWL2.choiceGraph children graph)
      (transition [] (TransitionKind.choiceEdge i j)) (childEntry [] j) = 1 := by
  simp [rawPost, rawPostFor, rawMark, childEntry, childAddr, entry, transition]

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
    (i : Nat) :
    rawPre (POWL2.choiceGraph children graph)
      (transition [] (TransitionKind.choiceEnd i)) (childExit [] i) = 1 := by
  simp [rawPre, rawPreFor, rawMark, childExit, childAddr, exit, transition]

theorem choiceGraph_end_produces_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (i : Nat) :
    rawPost (POWL2.choiceGraph children graph)
      (transition [] (TransitionKind.choiceEnd i)) (exit []) = 1 := by
  simp [rawPost, rawPostFor, rawMark, exit, transition]

end Structural

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
