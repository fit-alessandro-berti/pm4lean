import Pm4Lean.Conversion.POWL2ToSoundWfNet.Structural.Core

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace Structural

def lastChildIndex (n : Nat) : Nat := n - 1
noncomputable def poBeginPre
    (addr : Address) (order : Nat → Nat → Prop) (n i : Nat) :
    List RawPlace :=
  by
    classical
    exact
      (if ∃ j, j < n ∧ order j i then
        []
      else
        [poReady addr i]) ++
        (indicesWhere n (fun j => order j i)).map (fun j => poPredDone addr j i)

noncomputable def poCompletePost
    (addr : Address) (order : Nat → Nat → Prop) (n i : Nat) :
    List RawPlace :=
  [poDone addr i] ++
    (indicesWhere n (fun j => order i j)).map (fun j => poPredDone addr i j)

theorem prefixPlace_injective (pref : Address) :
    Function.Injective (prefixPlace pref) := by
  intro q r h
  cases q
  cases r
  simp [prefixPlace] at h
  rcases h with ⟨hAddr, hKind⟩
  simp [hAddr, hKind]

@[simp] theorem prefixPlace_entry (pref addr : Address) :
    prefixPlace pref (entry addr) = entry (pref ++ addr) := by
  rfl

@[simp] theorem prefixPlace_exit (pref addr : Address) :
    prefixPlace pref (exit addr) = exit (pref ++ addr) := by
  rfl

@[simp] theorem prefixPlace_childEntry
    (pref addr : Address) (i : Nat) :
    prefixPlace pref (childEntry addr i) =
      childEntry (pref ++ addr) i := by
  simp [prefixPlace, childEntry, childAddr, entry]

@[simp] theorem prefixPlace_childExit
    (pref addr : Address) (i : Nat) :
    prefixPlace pref (childExit addr i) =
      childExit (pref ++ addr) i := by
  simp [prefixPlace, childExit, childAddr, exit]

@[simp] theorem prefixPlace_poReady
    (pref addr : Address) (i : Nat) :
    prefixPlace pref (poReady addr i) =
      poReady (pref ++ addr) i := by
  rfl

@[simp] theorem prefixPlace_poDone
    (pref addr : Address) (i : Nat) :
    prefixPlace pref (poDone addr i) =
      poDone (pref ++ addr) i := by
  rfl

@[simp] theorem prefixPlace_poPredDone
    (pref addr : Address) (i j : Nat) :
    prefixPlace pref (poPredDone addr i j) =
      poPredDone (pref ++ addr) i j := by
  rfl

theorem rawMark_map_prefix
    (pref : Address) (xs : List RawPlace) (q : RawPlace) :
    rawMark (xs.map (prefixPlace pref)) (prefixPlace pref q) =
      rawMark xs q := by
  have hIff :
      (∃ a, a ∈ xs ∧ prefixPlace pref a = prefixPlace pref q) ↔
        q ∈ xs := by
    constructor
    · rintro ⟨a, hMem, hEq⟩
      have hA : a = q := prefixPlace_injective pref hEq
      simpa [hA] using hMem
    · intro hMem
      exact ⟨q, hMem, rfl⟩
  simp [rawMark, List.mem_map, hIff]

theorem rawMark_singleton_prefix
    (pref : Address) (x q : RawPlace) :
    rawMark [prefixPlace pref x] (prefixPlace pref q) =
      rawMark [x] q := by
  simpa using rawMark_map_prefix pref [x] q

def HasPlacePrefix (pref : Address) (q : RawPlace) : Prop :=
  ∃ base : RawPlace, q = prefixPlace pref base

theorem rawMark_map_prefix_zero
    (pref : Address) (xs : List RawPlace) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark (xs.map (prefixPlace pref)) q = 0 := by
  have hNotMem : q ∉ xs.map (prefixPlace pref) := by
    intro hMem
    rcases List.mem_map.mp hMem with ⟨base, _hBase, hEq⟩
    exact hNoPrefix ⟨base, hEq.symm⟩
  simp [rawMark, hNotMem]

theorem rawMark_singleton_prefix_zero
    (pref : Address) (x q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [prefixPlace pref x] q = 0 := by
  simpa using rawMark_map_prefix_zero pref [x] q hNoPrefix

theorem rawMark_entry_prefix
    (pref addr : Address) (q : RawPlace) :
    rawMark [entry (pref ++ addr)] (prefixPlace pref q) =
      rawMark [entry addr] q := by
  simpa using rawMark_singleton_prefix pref (entry addr) q

theorem rawMark_exit_prefix
    (pref addr : Address) (q : RawPlace) :
    rawMark [exit (pref ++ addr)] (prefixPlace pref q) =
      rawMark [exit addr] q := by
  simpa using rawMark_singleton_prefix pref (exit addr) q

theorem rawMark_childEntry_prefix
    (pref addr : Address) (i : Nat) (q : RawPlace) :
    rawMark [childEntry (pref ++ addr) i] (prefixPlace pref q) =
      rawMark [childEntry addr i] q := by
  simpa using rawMark_singleton_prefix pref (childEntry addr i) q

theorem rawMark_childExit_prefix
    (pref addr : Address) (i : Nat) (q : RawPlace) :
    rawMark [childExit (pref ++ addr) i] (prefixPlace pref q) =
      rawMark [childExit addr i] q := by
  simpa using rawMark_singleton_prefix pref (childExit addr i) q

theorem rawMark_entry_prefix_zero
    (pref addr : Address) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [entry (pref ++ addr)] q = 0 := by
  simpa using rawMark_singleton_prefix_zero pref (entry addr) q hNoPrefix

theorem rawMark_exit_prefix_zero
    (pref addr : Address) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [exit (pref ++ addr)] q = 0 := by
  simpa using rawMark_singleton_prefix_zero pref (exit addr) q hNoPrefix

theorem rawMark_childEntry_prefix_zero
    (pref addr : Address) (i : Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [childEntry (pref ++ addr) i] q = 0 := by
  simpa using
    rawMark_singleton_prefix_zero pref (childEntry addr i) q hNoPrefix

theorem rawMark_childExit_prefix_zero
    (pref addr : Address) (i : Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [childExit (pref ++ addr) i] q = 0 := by
  simpa using
    rawMark_singleton_prefix_zero pref (childExit addr i) q hNoPrefix

theorem rawMark_poDone_prefix
    (pref addr : Address) (n : Nat) (q : RawPlace) :
    rawMark ((List.range n).map (poDone (pref ++ addr)))
        (prefixPlace pref q) =
      rawMark ((List.range n).map (poDone addr)) q := by
  simpa [prefixPlace, poDone, List.map_map] using
    rawMark_map_prefix pref ((List.range n).map (poDone addr)) q

theorem rawMark_poReady_prefix
    (pref addr : Address) (xs : List Nat) (q : RawPlace) :
    rawMark (xs.map (poReady (pref ++ addr))) (prefixPlace pref q) =
      rawMark (xs.map (poReady addr)) q := by
  simpa [prefixPlace, poReady, List.map_map] using
    rawMark_map_prefix pref (xs.map (poReady addr)) q

theorem rawMark_poDone_prefix_zero
    (pref addr : Address) (n : Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark ((List.range n).map (poDone (pref ++ addr))) q = 0 := by
  simpa [prefixPlace, poDone, List.map_map] using
    rawMark_map_prefix_zero pref ((List.range n).map (poDone addr)) q
      hNoPrefix

theorem rawMark_poReady_prefix_zero
    (pref addr : Address) (xs : List Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark (xs.map (poReady (pref ++ addr))) q = 0 := by
  simpa [prefixPlace, poReady, List.map_map] using
    rawMark_map_prefix_zero pref (xs.map (poReady addr)) q hNoPrefix

theorem poBeginPre_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat) :
    poBeginPre (pref ++ addr) order n i =
      (poBeginPre addr order n i).map (prefixPlace pref) := by
  classical
  unfold poBeginPre
  split <;> simp [prefixPlace, poReady, poPredDone, List.map_map]

theorem poCompletePost_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat) :
    poCompletePost (pref ++ addr) order n i =
      (poCompletePost addr order n i).map (prefixPlace pref) := by
  simp [poCompletePost, prefixPlace, poDone, poPredDone, List.map_map]

theorem rawMark_poBeginPre_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat)
    (q : RawPlace) :
    rawMark (poBeginPre (pref ++ addr) order n i) (prefixPlace pref q) =
      rawMark (poBeginPre addr order n i) q := by
  rw [poBeginPre_prefix]
  exact rawMark_map_prefix pref (poBeginPre addr order n i) q

theorem rawMark_poBeginPre_prefix_zero
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat)
    (q : RawPlace) (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark (poBeginPre (pref ++ addr) order n i) q = 0 := by
  rw [poBeginPre_prefix]
  exact rawMark_map_prefix_zero pref (poBeginPre addr order n i) q hNoPrefix

theorem rawMark_poCompletePost_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat)
    (q : RawPlace) :
    rawMark (poCompletePost (pref ++ addr) order n i)
        (prefixPlace pref q) =
      rawMark (poCompletePost addr order n i) q := by
  rw [poCompletePost_prefix]
  exact rawMark_map_prefix pref (poCompletePost addr order n i) q

theorem rawMark_poCompletePost_prefix_zero
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat)
    (q : RawPlace) (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark (poCompletePost (pref ++ addr) order n i) q = 0 := by
  rw [poCompletePost_prefix]
  exact
    rawMark_map_prefix_zero pref (poCompletePost addr order n i) q
      hNoPrefix

theorem rawMark_partialOrderForkPost_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n : Nat)
    (q : RawPlace) :
    rawMark
        (if n = 0 then [exit (pref ++ addr)]
         else (indicesWhere n (fun i => ¬ (∃ j, j < n ∧ order j i))).map
              (poReady (pref ++ addr)))
        (prefixPlace pref q) =
      rawMark
        (if n = 0 then [exit addr]
         else (indicesWhere n (fun i => ¬ (∃ j, j < n ∧ order j i))).map
              (poReady addr)) q := by
  by_cases h : n = 0
  · simpa [h, prefixPlace, exit] using
      rawMark_singleton_prefix pref (exit addr) q
  · simp [h, rawMark_poReady_prefix]

theorem rawMark_partialOrderForkPost_list_prefix
    (pref addr : Address) (order : Nat → Nat → Prop)
    (children : List (POWL2 Activity)) (q : RawPlace) :
    rawMark
        (if children.length = 0 then [exit (pref ++ addr)]
         else
          (indicesWhere children.length
            (fun i => ¬ (∃ j, j < children.length ∧ order j i))).map
            (poReady (pref ++ addr)))
        (prefixPlace pref q) =
      rawMark
        (if children.length = 0 then [exit addr]
         else
          (indicesWhere children.length
            (fun i => ¬ (∃ j, j < children.length ∧ order j i))).map
            (poReady addr))
        q := by
  simpa using
    rawMark_partialOrderForkPost_prefix pref addr order children.length q

theorem rawMark_exit_or_poReady_prefix
    (pref addr : Address) (condition : Prop) [Decidable condition]
    (indices : List Nat) (q : RawPlace) :
    rawMark
        (if condition then [exit (pref ++ addr)]
         else indices.map (poReady (pref ++ addr)))
        (prefixPlace pref q) =
      rawMark
        (if condition then [exit addr]
         else indices.map (poReady addr))
        q := by
  by_cases h : condition
  · simp [h, rawMark_exit_prefix]
  · simp [h, rawMark_poReady_prefix]

theorem rawMark_exit_or_poReady_prefix_zero
    (pref addr : Address) (condition : Prop) [Decidable condition]
    (indices : List Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark
        (if condition then [exit (pref ++ addr)]
         else indices.map (poReady (pref ++ addr)))
        q = 0 := by
  by_cases h : condition
  · simp [h, rawMark_exit_prefix_zero, hNoPrefix]
  · simp [h, rawMark_poReady_prefix_zero, hNoPrefix]

def childAt : POWL2 Activity → Address → Option (POWL2 Activity)
  | p, [] => some p
  | POWL2.partialOrder children _, i :: rest =>
      match POWL2.listGet? children i with
      | some child => childAt child rest
      | none => none
  | POWL2.choiceGraph children _, i :: rest =>
      match POWL2.listGet? children i with
      | some child => childAt child rest
      | none => none
  | POWL2.loop body _, 0 :: rest => childAt body rest
  | POWL2.loop _ redo, 1 :: rest => childAt redo rest
  | _, _ :: _ => none

@[simp] theorem childAt_nil (p : POWL2 Activity) :
    childAt p [] = some p := by
  rfl

noncomputable def rawPreFor
    (active : POWL2 Activity) (t : RawTransition) (place : RawPlace) :
    Nat :=
  match active, t.kind with
  | POWL2.tau, TransitionKind.atom => rawMark [entry t.addr] place
  | POWL2.activity _, TransitionKind.atom => rawMark [entry t.addr] place
  | POWL2.partialOrder _ _, TransitionKind.poFork => rawMark [entry t.addr] place
  | POWL2.partialOrder children order, TransitionKind.poBegin i =>
      rawMark (poBeginPre t.addr order children.length i) place
  | POWL2.partialOrder _ _, TransitionKind.poComplete i =>
      rawMark [childExit t.addr i] place
  | POWL2.partialOrder children _, TransitionKind.poJoin =>
      rawMark ((List.range children.length).map (poDone t.addr)) place
  | POWL2.loop _ _, TransitionKind.loopStart => rawMark [entry t.addr] place
  | POWL2.loop _ _, TransitionKind.loopExit => rawMark [childExit t.addr 0] place
  | POWL2.loop _ _, TransitionKind.loopRedo => rawMark [childExit t.addr 0] place
  | POWL2.loop _ _, TransitionKind.loopBack => rawMark [childExit t.addr 1] place
  | POWL2.choiceGraph _ _, TransitionKind.choiceEmpty => rawMark [entry t.addr] place
  | POWL2.choiceGraph _ _, TransitionKind.choiceStart _ => rawMark [entry t.addr] place
  | POWL2.choiceGraph _ _, TransitionKind.choiceEdge i _ =>
      rawMark [childExit t.addr i] place
  | POWL2.choiceGraph _ _, TransitionKind.choiceEnd i =>
      rawMark [childExit t.addr i] place
  | _, _ => 0

noncomputable def rawPostFor
    (active : POWL2 Activity) (t : RawTransition) (place : RawPlace) :
    Nat :=
  match active, t.kind with
  | POWL2.tau, TransitionKind.atom => rawMark [exit t.addr] place
  | POWL2.activity _, TransitionKind.atom => rawMark [exit t.addr] place
  | POWL2.partialOrder children order, TransitionKind.poFork =>
      rawMark
        (if children.length = 0 then
          [exit t.addr]
        else
          (indicesWhere children.length
            (fun i => ¬ (∃ j, j < children.length ∧ order j i))).map
            (poReady t.addr))
        place
  | POWL2.partialOrder _ _, TransitionKind.poBegin i =>
      rawMark [childEntry t.addr i] place
  | POWL2.partialOrder children order, TransitionKind.poComplete i =>
      rawMark (poCompletePost t.addr order children.length i) place
  | POWL2.partialOrder _ _, TransitionKind.poJoin => rawMark [exit t.addr] place
  | POWL2.loop _ _, TransitionKind.loopStart =>
      rawMark [childEntry t.addr 0] place
  | POWL2.loop _ _, TransitionKind.loopExit => rawMark [exit t.addr] place
  | POWL2.loop _ _, TransitionKind.loopRedo =>
      rawMark [childEntry t.addr 1] place
  | POWL2.loop _ _, TransitionKind.loopBack =>
      rawMark [childEntry t.addr 0] place
  | POWL2.choiceGraph _ _, TransitionKind.choiceEmpty =>
      rawMark [exit t.addr] place
  | POWL2.choiceGraph _ _, TransitionKind.choiceStart i =>
      rawMark [childEntry t.addr i] place
  | POWL2.choiceGraph _ _, TransitionKind.choiceEdge _ j =>
      rawMark [childEntry t.addr j] place
  | POWL2.choiceGraph _ _, TransitionKind.choiceEnd _ =>
      rawMark [exit t.addr] place
  | _, _ => 0

noncomputable def rawPre :
    POWL2 Activity → RawTransition → RawPlace → Nat
  | p, t, place =>
      match childAt p t.addr with
      | none => 0
      | some active => rawPreFor active t place

noncomputable def rawPost :
    POWL2 Activity → RawTransition → RawPlace → Nat
  | p, t, place =>
      match childAt p t.addr with
      | none => 0
      | some active => rawPostFor active t place

theorem rawPreFor_prefix
    (active : POWL2 Activity) (pref : Address)
    (t : RawTransition) (q : RawPlace) :
    rawPreFor active (prefixTransition pref t) (prefixPlace pref q) =
      rawPreFor active t q := by
  cases t with
  | mk addr kind =>
      cases kind <;> cases active <;>
        simp [rawPreFor, prefixTransition, rawMark_entry_prefix,
          rawMark_childExit_prefix, rawMark_poBeginPre_prefix,
          rawMark_poDone_prefix]

theorem rawPostFor_prefix
    (active : POWL2 Activity) (pref : Address)
    (t : RawTransition) (q : RawPlace) :
    rawPostFor active (prefixTransition pref t) (prefixPlace pref q) =
      rawPostFor active t q := by
  cases t with
  | mk addr kind =>
      cases kind <;> cases active <;>
        simp [rawPostFor, prefixTransition, rawMark_exit_prefix,
          rawMark_childEntry_prefix, rawMark_poCompletePost_prefix,
          rawMark_exit_or_poReady_prefix]

theorem rawPreFor_prefix_zero
    (active : POWL2 Activity) (pref : Address)
    (t : RawTransition) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawPreFor active (prefixTransition pref t) q = 0 := by
  cases t with
  | mk addr kind =>
      cases kind <;> cases active <;>
        simp [rawPreFor, prefixTransition, rawMark_entry_prefix_zero,
          rawMark_childExit_prefix_zero, rawMark_poBeginPre_prefix_zero,
          rawMark_poDone_prefix_zero, hNoPrefix]

theorem rawPostFor_prefix_zero
    (active : POWL2 Activity) (pref : Address)
    (t : RawTransition) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawPostFor active (prefixTransition pref t) q = 0 := by
  cases t with
  | mk addr kind =>
      cases kind <;> cases active <;>
        simp [rawPostFor, prefixTransition, rawMark_exit_prefix_zero,
          rawMark_childEntry_prefix_zero, rawMark_poCompletePost_prefix_zero,
          rawMark_exit_or_poReady_prefix_zero, hNoPrefix]

def rawLabel (p : POWL2 Activity) (t : RawTransition) : Option Activity :=
  match t.kind, childAt p t.addr with
  | TransitionKind.atom, some (POWL2.activity a) => some a
  | _, _ => none

theorem childAt_loop_body_prefix
    (body redo : POWL2 Activity) (addr : Address) :
    childAt (POWL2.loop body redo) (0 :: addr) = childAt body addr := by
  rfl

theorem childAt_loop_redo_prefix
    (body redo : POWL2 Activity) (addr : Address) :
    childAt (POWL2.loop body redo) (1 :: addr) = childAt redo addr := by
  rfl

theorem childAt_partialOrder_child_prefix
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (addr : Address)
    (hGet : POWL2.listGet? children i = some child) :
    childAt (POWL2.partialOrder children order) (i :: addr) =
      childAt child addr := by
  simp [childAt, hGet]

theorem childAt_choiceGraph_child_prefix
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (addr : Address)
    (hGet : POWL2.listGet? children i = some child) :
    childAt (POWL2.choiceGraph children graph) (i :: addr) =
      childAt child addr := by
  simp [childAt, hGet]

theorem rawPre_child_prefix_of_childAt
    (parent child : POWL2 Activity) (pref : Address)
    (hChild : ∀ addr, childAt parent (pref ++ addr) = childAt child addr)
    (t : RawTransition) (q : RawPlace) :
    rawPre parent (prefixTransition pref t) (prefixPlace pref q) =
      rawPre child t q := by
  cases t with
  | mk addr kind =>
      simp only [rawPre, prefixTransition]
      rw [hChild addr]
      cases h : childAt child addr with
      | none =>
          rfl
      | some active =>
          simpa [prefixTransition] using
            rawPreFor_prefix active pref { addr := addr, kind := kind } q

theorem rawPost_child_prefix_of_childAt
    (parent child : POWL2 Activity) (pref : Address)
    (hChild : ∀ addr, childAt parent (pref ++ addr) = childAt child addr)
    (t : RawTransition) (q : RawPlace) :
    rawPost parent (prefixTransition pref t) (prefixPlace pref q) =
      rawPost child t q := by
  cases t with
  | mk addr kind =>
      simp only [rawPost, prefixTransition]
      rw [hChild addr]
      cases h : childAt child addr with
      | none =>
          rfl
      | some active =>
          simpa [prefixTransition] using
            rawPostFor_prefix active pref { addr := addr, kind := kind } q

theorem rawPre_child_prefix_zero_of_childAt
    (parent child : POWL2 Activity) (pref : Address)
    (hChild : ∀ addr, childAt parent (pref ++ addr) = childAt child addr)
    (t : RawTransition) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawPre parent (prefixTransition pref t) q = 0 := by
  cases t with
  | mk addr kind =>
      simp only [rawPre, prefixTransition]
      rw [hChild addr]
      cases h : childAt child addr with
      | none =>
          rfl
      | some active =>
          exact
            rawPreFor_prefix_zero active pref { addr := addr, kind := kind } q
              hNoPrefix

theorem rawPost_child_prefix_zero_of_childAt
    (parent child : POWL2 Activity) (pref : Address)
    (hChild : ∀ addr, childAt parent (pref ++ addr) = childAt child addr)
    (t : RawTransition) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawPost parent (prefixTransition pref t) q = 0 := by
  cases t with
  | mk addr kind =>
      simp only [rawPost, prefixTransition]
      rw [hChild addr]
      cases h : childAt child addr with
      | none =>
          rfl
      | some active =>
          exact
            rawPostFor_prefix_zero active pref { addr := addr, kind := kind } q
              hNoPrefix

theorem rawPre_loop_body_prefix
    (body redo : POWL2 Activity) (t : RawTransition) (q : RawPlace) :
    rawPre (POWL2.loop body redo) (prefixTransition [0] t)
        (prefixPlace [0] q) =
      rawPre body t q := by
  exact rawPre_child_prefix_of_childAt (POWL2.loop body redo) body [0]
    (by intro addr; exact childAt_loop_body_prefix body redo addr) t q

theorem rawPost_loop_body_prefix
    (body redo : POWL2 Activity) (t : RawTransition) (q : RawPlace) :
    rawPost (POWL2.loop body redo) (prefixTransition [0] t)
        (prefixPlace [0] q) =
      rawPost body t q := by
  exact rawPost_child_prefix_of_childAt (POWL2.loop body redo) body [0]
    (by intro addr; exact childAt_loop_body_prefix body redo addr) t q

theorem rawPre_loop_redo_prefix
    (body redo : POWL2 Activity) (t : RawTransition) (q : RawPlace) :
    rawPre (POWL2.loop body redo) (prefixTransition [1] t)
        (prefixPlace [1] q) =
      rawPre redo t q := by
  exact rawPre_child_prefix_of_childAt (POWL2.loop body redo) redo [1]
    (by intro addr; exact childAt_loop_redo_prefix body redo addr) t q

theorem rawPost_loop_redo_prefix
    (body redo : POWL2 Activity) (t : RawTransition) (q : RawPlace) :
    rawPost (POWL2.loop body redo) (prefixTransition [1] t)
        (prefixPlace [1] q) =
      rawPost redo t q := by
  exact rawPost_child_prefix_of_childAt (POWL2.loop body redo) redo [1]
    (by intro addr; exact childAt_loop_redo_prefix body redo addr) t q

theorem rawPre_partialOrder_child_prefix
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition) (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child) :
    rawPre (POWL2.partialOrder children order) (prefixTransition [i] t)
        (prefixPlace [i] q) =
      rawPre child t q := by
  exact rawPre_child_prefix_of_childAt
    (POWL2.partialOrder children order) child [i]
    (by
      intro addr
      exact childAt_partialOrder_child_prefix children order addr hGet)
    t q

theorem rawPost_partialOrder_child_prefix
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition) (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child) :
    rawPost (POWL2.partialOrder children order) (prefixTransition [i] t)
        (prefixPlace [i] q) =
      rawPost child t q := by
  exact rawPost_child_prefix_of_childAt
    (POWL2.partialOrder children order) child [i]
    (by
      intro addr
      exact childAt_partialOrder_child_prefix children order addr hGet)
    t q

theorem rawPre_choiceGraph_child_prefix
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition) (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child) :
    rawPre (POWL2.choiceGraph children graph) (prefixTransition [i] t)
        (prefixPlace [i] q) =
      rawPre child t q := by
  exact rawPre_child_prefix_of_childAt
    (POWL2.choiceGraph children graph) child [i]
    (by
      intro addr
      exact childAt_choiceGraph_child_prefix children graph addr hGet)
    t q

theorem rawPost_choiceGraph_child_prefix
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition) (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child) :
    rawPost (POWL2.choiceGraph children graph) (prefixTransition [i] t)
        (prefixPlace [i] q) =
      rawPost child t q := by
  exact rawPost_child_prefix_of_childAt
    (POWL2.choiceGraph children graph) child [i]
    (by
      intro addr
      exact childAt_choiceGraph_child_prefix children graph addr hGet)
    t q

theorem rawPre_loop_body_prefix_zero
    (body redo : POWL2 Activity) (t : RawTransition) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix [0] q) :
    rawPre (POWL2.loop body redo) (prefixTransition [0] t) q = 0 :=
  rawPre_child_prefix_zero_of_childAt (POWL2.loop body redo) body [0]
    (by intro addr; exact childAt_loop_body_prefix body redo addr)
    t q hNoPrefix

theorem rawPost_loop_body_prefix_zero
    (body redo : POWL2 Activity) (t : RawTransition) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix [0] q) :
    rawPost (POWL2.loop body redo) (prefixTransition [0] t) q = 0 :=
  rawPost_child_prefix_zero_of_childAt (POWL2.loop body redo) body [0]
    (by intro addr; exact childAt_loop_body_prefix body redo addr)
    t q hNoPrefix

theorem rawPre_loop_redo_prefix_zero
    (body redo : POWL2 Activity) (t : RawTransition) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix [1] q) :
    rawPre (POWL2.loop body redo) (prefixTransition [1] t) q = 0 :=
  rawPre_child_prefix_zero_of_childAt (POWL2.loop body redo) redo [1]
    (by intro addr; exact childAt_loop_redo_prefix body redo addr)
    t q hNoPrefix

theorem rawPost_loop_redo_prefix_zero
    (body redo : POWL2 Activity) (t : RawTransition) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix [1] q) :
    rawPost (POWL2.loop body redo) (prefixTransition [1] t) q = 0 :=
  rawPost_child_prefix_zero_of_childAt (POWL2.loop body redo) redo [1]
    (by intro addr; exact childAt_loop_redo_prefix body redo addr)
    t q hNoPrefix

theorem rawPre_partialOrder_child_prefix_zero
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition) (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child)
    (hNoPrefix : ¬ HasPlacePrefix [i] q) :
    rawPre (POWL2.partialOrder children order) (prefixTransition [i] t)
        q = 0 :=
  rawPre_child_prefix_zero_of_childAt
    (POWL2.partialOrder children order) child [i]
    (by
      intro addr
      exact childAt_partialOrder_child_prefix children order addr hGet)
    t q hNoPrefix

theorem rawPost_partialOrder_child_prefix_zero
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition) (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child)
    (hNoPrefix : ¬ HasPlacePrefix [i] q) :
    rawPost (POWL2.partialOrder children order) (prefixTransition [i] t)
        q = 0 :=
  rawPost_child_prefix_zero_of_childAt
    (POWL2.partialOrder children order) child [i]
    (by
      intro addr
      exact childAt_partialOrder_child_prefix children order addr hGet)
    t q hNoPrefix

theorem rawPre_choiceGraph_child_prefix_zero
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition) (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child)
    (hNoPrefix : ¬ HasPlacePrefix [i] q) :
    rawPre (POWL2.choiceGraph children graph) (prefixTransition [i] t)
        q = 0 :=
  rawPre_child_prefix_zero_of_childAt
    (POWL2.choiceGraph children graph) child [i]
    (by
      intro addr
      exact childAt_choiceGraph_child_prefix children graph addr hGet)
    t q hNoPrefix

theorem rawPost_choiceGraph_child_prefix_zero
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition) (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child)
    (hNoPrefix : ¬ HasPlacePrefix [i] q) :
    rawPost (POWL2.choiceGraph children graph) (prefixTransition [i] t)
        q = 0 :=
  rawPost_child_prefix_zero_of_childAt
    (POWL2.choiceGraph children graph) child [i]
    (by
      intro addr
      exact childAt_choiceGraph_child_prefix children graph addr hGet)
    t q hNoPrefix

theorem rawLabel_loop_body_prefix
    (body redo : POWL2 Activity) (t : RawTransition) :
    rawLabel (POWL2.loop body redo) (prefixTransition [0] t) =
      rawLabel body t := by
  cases t
  simp [rawLabel, prefixTransition, childAt_loop_body_prefix]

theorem rawLabel_loop_redo_prefix
    (body redo : POWL2 Activity) (t : RawTransition) :
    rawLabel (POWL2.loop body redo) (prefixTransition [1] t) =
      rawLabel redo t := by
  cases t
  simp [rawLabel, prefixTransition, childAt_loop_redo_prefix]

theorem rawLabel_partialOrder_child_prefix
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition)
    (hGet : POWL2.listGet? children i = some child) :
    rawLabel (POWL2.partialOrder children order) (prefixTransition [i] t) =
      rawLabel child t := by
  cases t
  simp [rawLabel, prefixTransition, childAt_partialOrder_child_prefix,
    hGet]

theorem rawLabel_choiceGraph_child_prefix
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition)
    (hGet : POWL2.listGet? children i = some child) :
    rawLabel (POWL2.choiceGraph children graph) (prefixTransition [i] t) =
      rawLabel child t := by
  cases t
  simp [rawLabel, prefixTransition, childAt_choiceGraph_child_prefix,
    hGet]

def compiled (p : POWL2 Activity) : POWL2 Activity :=
  normalize p

def rawPlacesRoot (p : POWL2 Activity) : List RawPlace :=
  rawPlaces (compiled p) []

noncomputable def rawTransitionsRoot (p : POWL2 Activity) : List RawTransition :=
  rawTransitions (compiled p) []

end Structural
end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
