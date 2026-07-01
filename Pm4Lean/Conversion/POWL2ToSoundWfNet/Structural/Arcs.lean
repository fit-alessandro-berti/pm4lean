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

noncomputable def rawPre :
    POWL2 Activity → RawTransition → RawPlace → Nat
  | p, t, place =>
      match p, t.kind with
      | POWL2.tau, TransitionKind.atom => rawMark [entry t.addr] place
      | POWL2.activity _, TransitionKind.atom => rawMark [entry t.addr] place
      | POWL2.partialOrder _ _, TransitionKind.poFork => rawMark [entry t.addr] place
      | POWL2.partialOrder children order, TransitionKind.poBegin i =>
          rawMark (poBeginPre t.addr order children.length i) place
      | POWL2.partialOrder _ _, TransitionKind.poComplete i => rawMark [childExit t.addr i] place
      | POWL2.partialOrder children _, TransitionKind.poJoin =>
          rawMark ((List.range children.length).map (poDone t.addr)) place
      | POWL2.loop _ _, TransitionKind.loopStart => rawMark [entry t.addr] place
      | POWL2.loop _ _, TransitionKind.loopExit => rawMark [childExit t.addr 0] place
      | POWL2.loop _ _, TransitionKind.loopRedo => rawMark [childExit t.addr 0] place
      | POWL2.loop _ _, TransitionKind.loopBack => rawMark [childExit t.addr 1] place
      | POWL2.choiceGraph _ _, TransitionKind.choiceEmpty => rawMark [entry t.addr] place
      | POWL2.choiceGraph _ _, TransitionKind.choiceStart _ => rawMark [entry t.addr] place
      | POWL2.choiceGraph _ _, TransitionKind.choiceEdge i _ => rawMark [childExit t.addr i] place
      | POWL2.choiceGraph _ _, TransitionKind.choiceEnd i => rawMark [childExit t.addr i] place
      | _, _ => 0

noncomputable def rawPost :
    POWL2 Activity → RawTransition → RawPlace → Nat
  | p, t, place =>
      match p, t.kind with
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
      | POWL2.partialOrder _ _, TransitionKind.poBegin i => rawMark [childEntry t.addr i] place
      | POWL2.partialOrder children order, TransitionKind.poComplete i =>
          rawMark (poCompletePost t.addr order children.length i) place
      | POWL2.partialOrder _ _, TransitionKind.poJoin => rawMark [exit t.addr] place
      | POWL2.loop _ _, TransitionKind.loopStart => rawMark [childEntry t.addr 0] place
      | POWL2.loop _ _, TransitionKind.loopExit => rawMark [exit t.addr] place
      | POWL2.loop _ _, TransitionKind.loopRedo => rawMark [childEntry t.addr 1] place
      | POWL2.loop _ _, TransitionKind.loopBack => rawMark [childEntry t.addr 0] place
      | POWL2.choiceGraph _ _, TransitionKind.choiceEmpty => rawMark [exit t.addr] place
      | POWL2.choiceGraph _ _, TransitionKind.choiceStart i => rawMark [childEntry t.addr i] place
      | POWL2.choiceGraph _ _, TransitionKind.choiceEdge _ j => rawMark [childEntry t.addr j] place
      | POWL2.choiceGraph _ _, TransitionKind.choiceEnd _ => rawMark [exit t.addr] place
      | _, _ => 0

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

def rawLabel (p : POWL2 Activity) (t : RawTransition) : Option Activity :=
  match t.kind, childAt p t.addr with
  | TransitionKind.atom, some (POWL2.activity a) => some a
  | _, _ => none

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
