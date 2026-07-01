import Pm4Lean.Conversion.POWL2ToSoundWfNet.Target
import Pm4Lean.Conversion.POWL2ToSoundWfNet.Structural.Shape

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

noncomputable def transitionOf
    (p : POWL2 Activity) (t : RawTransition)
    (h : t ∈ Structural.rawTransitionsRoot p) :
    (target p).wfnet.net.Transition :=
  ⟨t, h⟩

def placeOf
    (p : POWL2 Activity) (q : RawPlace)
    (h : q ∈ Structural.rawPlacesRoot p) :
    (target p).wfnet.net.Place :=
  ⟨q, h⟩

noncomputable def loopBodyTransitionOf
    (body redo : POWL2 Activity) (t : RawTransition)
    (hMem :
      t ∈ Structural.rawTransitions (Structural.normalize body)
        (Structural.childAddr [] 0)) :
    (target (POWL2.loop body redo)).wfnet.net.Transition :=
  transitionOf (POWL2.loop body redo) t (by
    simpa [Structural.rawTransitionsRoot, Structural.compiled,
      Structural.normalize] using
      Structural.loop_body_transition_mem
        (Structural.normalize body) (Structural.normalize redo) [] hMem)

noncomputable def loopRedoTransitionOf
    (body redo : POWL2 Activity) (t : RawTransition)
    (hMem :
      t ∈ Structural.rawTransitions (Structural.normalize redo)
        (Structural.childAddr [] 1)) :
    (target (POWL2.loop body redo)).wfnet.net.Transition :=
  transitionOf (POWL2.loop body redo) t (by
    simpa [Structural.rawTransitionsRoot, Structural.compiled,
      Structural.normalize] using
      Structural.loop_redo_transition_child_mem
        (Structural.normalize body) (Structural.normalize redo) [] hMem)

def loopBodyPlaceOf
    (body redo : POWL2 Activity) (q : RawPlace)
    (hMem :
      q ∈ Structural.rawPlaces (Structural.normalize body)
        (Structural.childAddr [] 0)) :
    (target (POWL2.loop body redo)).wfnet.net.Place :=
  placeOf (POWL2.loop body redo) q (by
    simpa [Structural.rawPlacesRoot, Structural.compiled,
      Structural.normalize] using
      Structural.loop_body_place_mem
        (Structural.normalize body) (Structural.normalize redo) [] hMem)

def loopRedoPlaceOf
    (body redo : POWL2 Activity) (q : RawPlace)
    (hMem :
      q ∈ Structural.rawPlaces (Structural.normalize redo)
        (Structural.childAddr [] 1)) :
    (target (POWL2.loop body redo)).wfnet.net.Place :=
  placeOf (POWL2.loop body redo) q (by
    simpa [Structural.rawPlacesRoot, Structural.compiled,
      Structural.normalize] using
      Structural.loop_redo_place_mem
        (Structural.normalize body) (Structural.normalize redo) [] hMem)

noncomputable def partialOrderChildTransitionOf
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition)
    (hGet :
      POWL2.listGet? (children.map Structural.normalize) i = some child)
    (hMem : t ∈ Structural.rawTransitions child (Structural.childAddr [] i)) :
    (target (POWL2.partialOrder children order)).wfnet.net.Transition :=
  transitionOf (POWL2.partialOrder children order) t (by
    simpa [Structural.rawTransitionsRoot, Structural.compiled,
      Structural.normalize] using
      Structural.partialOrder_child_transition_mem
        (children.map Structural.normalize) order [] hGet hMem)

def partialOrderChildPlaceOf
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (q : RawPlace)
    (hGet :
      POWL2.listGet? (children.map Structural.normalize) i = some child)
    (hMem : q ∈ Structural.rawPlaces child (Structural.childAddr [] i)) :
    (target (POWL2.partialOrder children order)).wfnet.net.Place :=
  placeOf (POWL2.partialOrder children order) q (by
    simpa [Structural.rawPlacesRoot, Structural.compiled,
      Structural.normalize] using
      Structural.partialOrder_child_place_mem
        (children.map Structural.normalize) order [] hGet hMem)

noncomputable def choiceGraphChildTransitionOf
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition)
    (hGet :
      POWL2.listGet? (children.map Structural.normalize) i = some child)
    (hMem : t ∈ Structural.rawTransitions child (Structural.childAddr [] i)) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.Transition :=
  transitionOf (POWL2.choiceGraph children graph) t (by
    simpa [Structural.rawTransitionsRoot, Structural.compiled,
      Structural.normalize] using
      Structural.choiceGraph_child_transition_mem
        (children.map Structural.normalize) graph [] hGet hMem)

def choiceGraphChildPlaceOf
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (q : RawPlace)
    (hGet :
      POWL2.listGet? (children.map Structural.normalize) i = some child)
    (hMem : q ∈ Structural.rawPlaces child (Structural.childAddr [] i)) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.Place :=
  placeOf (POWL2.choiceGraph children graph) q (by
    simpa [Structural.rawPlacesRoot, Structural.compiled,
      Structural.normalize] using
      Structural.choiceGraph_child_place_mem
        (children.map Structural.normalize) graph [] hGet hMem)

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
