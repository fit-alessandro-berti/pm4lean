import Pm4Lean.Models.POWL2.Semantics
import Pm4Lean.Models.Petri.WFNet.Language

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

abbrev Address := List Nat

inductive PlaceKind where
  | entry
  | exit
  | poReady : Nat → PlaceKind
  | poPredDone : Nat → Nat → PlaceKind
  | poDone : Nat → PlaceKind
deriving DecidableEq, Repr

structure RawPlace where
  addr : Address
  kind : PlaceKind
deriving DecidableEq, Repr

inductive TransitionKind where
  | atom
  | poFork
  | poBegin : Nat → TransitionKind
  | poComplete : Nat → TransitionKind
  | poJoin
  | loopStart
  | loopExit
  | loopRedo
  | loopBack
  | choiceEmpty
  | choiceStart : Nat → TransitionKind
  | choiceEdge : Nat → Nat → TransitionKind
  | choiceEnd : Nat → TransitionKind
deriving DecidableEq, Repr

structure RawTransition where
  addr : Address
  kind : TransitionKind
deriving DecidableEq, Repr

namespace Structural

def entry (addr : Address) : RawPlace := ⟨addr, PlaceKind.entry⟩
def exit (addr : Address) : RawPlace := ⟨addr, PlaceKind.exit⟩
def childAddr (addr : Address) (i : Nat) : Address := addr ++ [i]
def childEntry (addr : Address) (i : Nat) : RawPlace := entry (childAddr addr i)
def childExit (addr : Address) (i : Nat) : RawPlace := exit (childAddr addr i)

def poReady (addr : Address) (i : Nat) : RawPlace :=
  ⟨addr, PlaceKind.poReady i⟩

def poPredDone (addr : Address) (i j : Nat) : RawPlace :=
  ⟨addr, PlaceKind.poPredDone i j⟩

def poDone (addr : Address) (i : Nat) : RawPlace :=
  ⟨addr, PlaceKind.poDone i⟩

def transition (addr : Address) (kind : TransitionKind) : RawTransition :=
  ⟨addr, kind⟩

def prefixPlace (pref : Address) (q : RawPlace) : RawPlace :=
  ⟨pref ++ q.addr, q.kind⟩

def prefixTransition (pref : Address) (t : RawTransition) : RawTransition :=
  ⟨pref ++ t.addr, t.kind⟩

def rawMark (places : List RawPlace) : RawPlace → Nat :=
  fun p => if p ∈ places then 1 else 0

def pairsUpTo (n : Nat) : List (Nat × Nat) :=
  ((List.range n).map (fun i => (List.range n).map (fun j => (i, j)))).flatten

noncomputable def filterProp {α : Type u} :
    List α → (α → Prop) → List α :=
  fun xs p =>
    by
      classical
      exact xs.filter p

def placesForPartialOrder (addr : Address) (n : Nat) : List RawPlace :=
  [entry addr, exit addr] ++
    (List.range n).map (poReady addr) ++
    (List.range n).map (poDone addr) ++
    (pairsUpTo n).map (fun edge => poPredDone addr edge.1 edge.2)

def transitionsForPartialOrder
    (addr : Address) (n : Nat) : List RawTransition :=
  if n = 0 then
    [transition addr TransitionKind.poFork]
  else
    [transition addr TransitionKind.poFork] ++
      (List.range n).map (fun i => transition addr (TransitionKind.poBegin i)) ++
      (List.range n).map (fun i => transition addr (TransitionKind.poComplete i)) ++
      [transition addr TransitionKind.poJoin]

noncomputable def indicesWhere (n : Nat) (p : Nat → Prop) : List Nat :=
  filterProp (List.range n) p

noncomputable def edgesWhere
    (n : Nat) (p : Nat → Nat → Prop) : List (Nat × Nat) :=
  filterProp (pairsUpTo n) (fun edge => p edge.1 edge.2)

def normalize : POWL2 Activity → POWL2 Activity
  | POWL2.tau => POWL2.tau
  | POWL2.activity a => POWL2.activity a
  | POWL2.loop body redo => POWL2.loop (normalize body) (normalize redo)
  | POWL2.choiceGraph children graph =>
      POWL2.choiceGraph (children.map normalize) graph
  | POWL2.partialOrder children order =>
      POWL2.partialOrder (children.map normalize) order

mutual
  def rawPlaces :
      POWL2 Activity → Address → List RawPlace
    | POWL2.tau, addr => [entry addr, exit addr]
    | POWL2.activity _, addr => [entry addr, exit addr]
    | POWL2.loop body redo, addr =>
        [entry addr, exit addr] ++
          rawPlaces body (childAddr addr 0) ++
          rawPlaces redo (childAddr addr 1)
    | POWL2.choiceGraph children _, addr =>
        [entry addr, exit addr] ++ rawPlacesChildren children addr 0
    | POWL2.partialOrder children _, addr =>
        placesForPartialOrder addr children.length ++
          rawPlacesChildren children addr 0

  def rawPlacesChildren :
      List (POWL2 Activity) → Address → Nat → List RawPlace
    | [], _, _ => []
    | child :: rest, addr, i =>
        rawPlaces child (childAddr addr i) ++
          rawPlacesChildren rest addr (i + 1)
end

mutual
  noncomputable def rawTransitions :
      POWL2 Activity → Address → List RawTransition
    | POWL2.tau, addr => [transition addr TransitionKind.atom]
    | POWL2.activity _, addr => [transition addr TransitionKind.atom]
    | POWL2.loop body redo, addr =>
        [ transition addr TransitionKind.loopStart,
          transition addr TransitionKind.loopExit,
          transition addr TransitionKind.loopRedo,
          transition addr TransitionKind.loopBack ] ++
          rawTransitions body (childAddr addr 0) ++
          rawTransitions redo (childAddr addr 1)
    | POWL2.choiceGraph children graph, addr =>
        by
          classical
          exact
            (if graph.empty then [transition addr TransitionKind.choiceEmpty] else []) ++
              (indicesWhere children.length graph.start).map
                (fun i => transition addr (TransitionKind.choiceStart i)) ++
              (edgesWhere children.length graph.edge).map
                (fun edge => transition addr (TransitionKind.choiceEdge edge.1 edge.2)) ++
              (indicesWhere children.length graph.finish).map
                (fun i => transition addr (TransitionKind.choiceEnd i)) ++
              rawTransitionsChildren children addr 0
    | POWL2.partialOrder children _, addr =>
        transitionsForPartialOrder addr children.length ++
          rawTransitionsChildren children addr 0

  noncomputable def rawTransitionsChildren :
      List (POWL2 Activity) → Address → Nat → List RawTransition
    | [], _, _ => []
    | child :: rest, addr, i =>
        rawTransitions child (childAddr addr i) ++
          rawTransitionsChildren rest addr (i + 1)
end

end Structural
end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
