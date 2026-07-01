import Pm4Lean.Conversion.POWL2ToSoundWfNet.Structural.Marking

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace Structural

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
