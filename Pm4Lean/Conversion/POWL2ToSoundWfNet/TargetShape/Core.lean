import Pm4Lean.Conversion.POWL2ToSoundWfNet.Target
import Pm4Lean.Conversion.POWL2ToSoundWfNet.Structural.Shape
import Pm4Lean.Models.POWL2.Verification

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

noncomputable def loopBodyRootTransitionOf
    (body redo : POWL2 Activity)
    (t : (target body).wfnet.net.Transition) :
    (target (POWL2.loop body redo)).wfnet.net.Transition :=
  loopBodyTransitionOf body redo (Structural.prefixTransition [0] t.1) (by
    simpa [Structural.rawTransitionsRoot, Structural.compiled,
      Structural.childAddr] using
      Structural.rawTransitions_prefix_mem
        (Structural.compiled body) [0] [] t.2)

noncomputable def loopRedoRootTransitionOf
    (body redo : POWL2 Activity)
    (t : (target redo).wfnet.net.Transition) :
    (target (POWL2.loop body redo)).wfnet.net.Transition :=
  loopRedoTransitionOf body redo (Structural.prefixTransition [1] t.1) (by
    simpa [Structural.rawTransitionsRoot, Structural.compiled,
      Structural.childAddr] using
      Structural.rawTransitions_prefix_mem
        (Structural.compiled redo) [1] [] t.2)

theorem loopBodyRootTransition_label
    (body redo : POWL2 Activity)
    (t : (target body).wfnet.net.Transition) :
    (target (POWL2.loop body redo)).label
        (loopBodyRootTransitionOf body redo t) =
      (target body).label t := by
  cases t
  simp [loopBodyRootTransitionOf, loopBodyTransitionOf, transitionOf,
    target, Structural.target, Structural.compiled, Structural.normalize,
    Structural.rawLabel_loop_body_prefix]

theorem loopRedoRootTransition_label
    (body redo : POWL2 Activity)
    (t : (target redo).wfnet.net.Transition) :
    (target (POWL2.loop body redo)).label
        (loopRedoRootTransitionOf body redo t) =
      (target redo).label t := by
  cases t
  simp [loopRedoRootTransitionOf, loopRedoTransitionOf, transitionOf,
    target, Structural.target, Structural.compiled, Structural.normalize,
    Structural.rawLabel_loop_redo_prefix]

theorem loopBodyRootTransition_traceOf
    (body redo : POWL2 Activity)
    (ts : List (target body).wfnet.net.Transition) :
    Petri.LabeledWFNet.traceOf (target (POWL2.loop body redo))
        (ts.map (loopBodyRootTransitionOf body redo)) =
      Petri.LabeledWFNet.traceOf (target body) ts :=
  Petri.LabeledWFNet.traceOf_map (target body)
    (target (POWL2.loop body redo))
    (loopBodyRootTransitionOf body redo)
    (loopBodyRootTransition_label body redo) ts

theorem loopRedoRootTransition_traceOf
    (body redo : POWL2 Activity)
    (ts : List (target redo).wfnet.net.Transition) :
    Petri.LabeledWFNet.traceOf (target (POWL2.loop body redo))
        (ts.map (loopRedoRootTransitionOf body redo)) =
      Petri.LabeledWFNet.traceOf (target redo) ts :=
  Petri.LabeledWFNet.traceOf_map (target redo)
    (target (POWL2.loop body redo))
    (loopRedoRootTransitionOf body redo)
    (loopRedoRootTransition_label body redo) ts

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

def loopBodyRootPlaceOf
    (body redo : POWL2 Activity)
    (q : (target body).wfnet.net.Place) :
    (target (POWL2.loop body redo)).wfnet.net.Place :=
  loopBodyPlaceOf body redo (Structural.prefixPlace [0] q.1) (by
    simpa [Structural.rawPlacesRoot, Structural.compiled,
      Structural.childAddr] using
      Structural.rawPlaces_prefix_mem
        (Structural.compiled body) [0] [] q.2)

theorem loopBodyRootPlaceOf_injective
    (body redo : POWL2 Activity) :
    Function.Injective (loopBodyRootPlaceOf body redo) := by
  intro q r h
  apply Subtype.ext
  apply Structural.prefixPlace_injective [0]
  exact congrArg Subtype.val h

theorem loop_body_rawPlacesRoot_unprefix
    (body redo : POWL2 Activity) {base : RawPlace}
    (hMem :
      Structural.prefixPlace [0] base ∈
        Structural.rawPlacesRoot (POWL2.loop body redo)) :
    base ∈ Structural.rawPlacesRoot body := by
  have hSplit := hMem
  simp [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize, Structural.rawPlaces] at hSplit
  rcases hSplit with hEntry | hExit | hBody | hRedo
  · cases base
    simp [Structural.prefixPlace, Structural.entry] at hEntry
  · cases base
    simp [Structural.prefixPlace, Structural.exit] at hExit
  · simpa [Structural.rawPlacesRoot, Structural.compiled,
      Structural.childAddr] using
      Structural.rawPlaces_unprefix_mem
        (Structural.normalize body) [0] [] hBody
  · exact False.elim
      (Structural.prefixPlace_ne_mem_rawPlaces_of_child_index_ne
        (Structural.normalize redo) (by decide : 0 ≠ 1) base
        (by simpa [Structural.childAddr] using hRedo))

theorem loopBodyRootPlaceOf_surjective_of_prefix
    (body redo : POWL2 Activity)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hPrefix : Structural.HasPlacePrefix [0] q.1) :
    ∃ p : (target body).wfnet.net.Place,
      loopBodyRootPlaceOf body redo p = q := by
  rcases hPrefix with ⟨base, hBase⟩
  have hMem :
      Structural.prefixPlace [0] base ∈
        Structural.rawPlacesRoot (POWL2.loop body redo) := by
    simpa [hBase] using q.2
  let p : (target body).wfnet.net.Place :=
    ⟨base, loop_body_rawPlacesRoot_unprefix body redo hMem⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  simp [p, loopBodyRootPlaceOf, loopBodyPlaceOf, placeOf, hBase]

def loopRedoRootPlaceOf
    (body redo : POWL2 Activity)
    (q : (target redo).wfnet.net.Place) :
    (target (POWL2.loop body redo)).wfnet.net.Place :=
  loopRedoPlaceOf body redo (Structural.prefixPlace [1] q.1) (by
    simpa [Structural.rawPlacesRoot, Structural.compiled,
      Structural.childAddr] using
      Structural.rawPlaces_prefix_mem
        (Structural.compiled redo) [1] [] q.2)

theorem loopRedoRootPlaceOf_injective
    (body redo : POWL2 Activity) :
    Function.Injective (loopRedoRootPlaceOf body redo) := by
  intro q r h
  apply Subtype.ext
  apply Structural.prefixPlace_injective [1]
  exact congrArg Subtype.val h

theorem loop_redo_rawPlacesRoot_unprefix
    (body redo : POWL2 Activity) {base : RawPlace}
    (hMem :
      Structural.prefixPlace [1] base ∈
        Structural.rawPlacesRoot (POWL2.loop body redo)) :
    base ∈ Structural.rawPlacesRoot redo := by
  have hSplit := hMem
  simp [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize, Structural.rawPlaces] at hSplit
  rcases hSplit with hEntry | hExit | hBody | hRedo
  · cases base
    simp [Structural.prefixPlace, Structural.entry] at hEntry
  · cases base
    simp [Structural.prefixPlace, Structural.exit] at hExit
  · exact False.elim
      (Structural.prefixPlace_ne_mem_rawPlaces_of_child_index_ne
        (Structural.normalize body) (by decide : 1 ≠ 0) base
        (by simpa [Structural.childAddr] using hBody))
  · simpa [Structural.rawPlacesRoot, Structural.compiled,
      Structural.childAddr] using
      Structural.rawPlaces_unprefix_mem
        (Structural.normalize redo) [1] [] hRedo

theorem loopRedoRootPlaceOf_surjective_of_prefix
    (body redo : POWL2 Activity)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hPrefix : Structural.HasPlacePrefix [1] q.1) :
    ∃ p : (target redo).wfnet.net.Place,
      loopRedoRootPlaceOf body redo p = q := by
  rcases hPrefix with ⟨base, hBase⟩
  have hMem :
      Structural.prefixPlace [1] base ∈
        Structural.rawPlacesRoot (POWL2.loop body redo) := by
    simpa [hBase] using q.2
  let p : (target redo).wfnet.net.Place :=
    ⟨base, loop_redo_rawPlacesRoot_unprefix body redo hMem⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  simp [p, loopRedoRootPlaceOf, loopRedoPlaceOf, placeOf, hBase]

theorem loopBodyRootPlace_initial
    (body redo : POWL2 Activity) :
    loopBodyRootPlaceOf body redo (target body).wfnet.i =
      placeOf (POWL2.loop body redo) (Structural.childEntry [] 0)
        (by
          simpa [Structural.rawPlacesRoot, Structural.compiled,
            Structural.normalize] using
            Structural.loop_body_entry_mem
              (Structural.normalize body) (Structural.normalize redo) []) := by
  apply Subtype.ext
  simp [loopBodyRootPlaceOf, loopBodyPlaceOf, placeOf, target,
    Structural.target, Structural.wfnet, Structural.childEntry,
    Structural.childAddr, Structural.prefixPlace, Structural.entry]

theorem loopBodyRootPlace_final
    (body redo : POWL2 Activity) :
    loopBodyRootPlaceOf body redo (target body).wfnet.o =
      placeOf (POWL2.loop body redo) (Structural.childExit [] 0)
        (by
          simpa [Structural.rawPlacesRoot, Structural.compiled,
            Structural.normalize] using
            Structural.loop_body_exit_mem
              (Structural.normalize body) (Structural.normalize redo) []) := by
  apply Subtype.ext
  simp [loopBodyRootPlaceOf, loopBodyPlaceOf, placeOf, target,
    Structural.target, Structural.wfnet, Structural.childExit,
    Structural.childAddr, Structural.prefixPlace, Structural.exit]

theorem loopRedoRootPlace_initial
    (body redo : POWL2 Activity) :
    loopRedoRootPlaceOf body redo (target redo).wfnet.i =
      placeOf (POWL2.loop body redo) (Structural.childEntry [] 1)
        (by
          simpa [Structural.rawPlacesRoot, Structural.compiled,
            Structural.normalize] using
            Structural.loop_redo_entry_mem
              (Structural.normalize body) (Structural.normalize redo) []) := by
  apply Subtype.ext
  simp [loopRedoRootPlaceOf, loopRedoPlaceOf, placeOf, target,
    Structural.target, Structural.wfnet, Structural.childEntry,
    Structural.childAddr, Structural.prefixPlace, Structural.entry]

theorem loopRedoRootPlace_final
    (body redo : POWL2 Activity) :
    loopRedoRootPlaceOf body redo (target redo).wfnet.o =
      placeOf (POWL2.loop body redo) (Structural.childExit [] 1)
        (by
          simpa [Structural.rawPlacesRoot, Structural.compiled,
            Structural.normalize] using
            Structural.loop_redo_exit_mem
              (Structural.normalize body) (Structural.normalize redo) []) := by
  apply Subtype.ext
  simp [loopRedoRootPlaceOf, loopRedoPlaceOf, placeOf, target,
    Structural.target, Structural.wfnet, Structural.childExit,
    Structural.childAddr, Structural.prefixPlace, Structural.exit]

theorem loopBodyRootTransition_pre
    (body redo : POWL2 Activity)
    (t : (target body).wfnet.net.Transition)
    (q : (target body).wfnet.net.Place) :
    (target (POWL2.loop body redo)).wfnet.net.pre
        (loopBodyRootTransitionOf body redo t)
        (loopBodyRootPlaceOf body redo q) =
      (target body).wfnet.net.pre t q := by
  cases t
  cases q
  simp [loopBodyRootTransitionOf, loopBodyTransitionOf,
    loopBodyRootPlaceOf, loopBodyPlaceOf, transitionOf, placeOf,
    target, Structural.target, Structural.wfnet, Structural.net,
    Structural.compiled, Structural.normalize,
    Structural.rawPre_loop_body_prefix]

theorem loopBodyRootTransition_post
    (body redo : POWL2 Activity)
    (t : (target body).wfnet.net.Transition)
    (q : (target body).wfnet.net.Place) :
    (target (POWL2.loop body redo)).wfnet.net.post
        (loopBodyRootTransitionOf body redo t)
        (loopBodyRootPlaceOf body redo q) =
      (target body).wfnet.net.post t q := by
  cases t
  cases q
  simp [loopBodyRootTransitionOf, loopBodyTransitionOf,
    loopBodyRootPlaceOf, loopBodyPlaceOf, transitionOf, placeOf,
    target, Structural.target, Structural.wfnet, Structural.net,
    Structural.compiled, Structural.normalize,
    Structural.rawPost_loop_body_prefix]

theorem loopBodyRootTransition_pre_zero_of_not_prefix
    (body redo : POWL2 Activity)
    (t : (target body).wfnet.net.Transition)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hNoPrefix : ¬ Structural.HasPlacePrefix [0] q.1) :
    (target (POWL2.loop body redo)).wfnet.net.pre
        (loopBodyRootTransitionOf body redo t) q = 0 := by
  cases t
  cases q
  simp [loopBodyRootTransitionOf, loopBodyTransitionOf,
    transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre_loop_body_prefix_zero, hNoPrefix]

theorem loopBodyRootTransition_post_zero_of_not_prefix
    (body redo : POWL2 Activity)
    (t : (target body).wfnet.net.Transition)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hNoPrefix : ¬ Structural.HasPlacePrefix [0] q.1) :
    (target (POWL2.loop body redo)).wfnet.net.post
        (loopBodyRootTransitionOf body redo t) q = 0 := by
  cases t
  cases q
  simp [loopBodyRootTransitionOf, loopBodyTransitionOf,
    transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost_loop_body_prefix_zero, hNoPrefix]

theorem loopBodyRootTransition_pre_zero_of_not_mapped
    (body redo : POWL2 Activity)
    (t : (target body).wfnet.net.Transition)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hNotMapped :
      ¬ ∃ p : (target body).wfnet.net.Place,
        loopBodyRootPlaceOf body redo p = q) :
    (target (POWL2.loop body redo)).wfnet.net.pre
        (loopBodyRootTransitionOf body redo t) q = 0 :=
  loopBodyRootTransition_pre_zero_of_not_prefix body redo t q (by
    intro hPrefix
    exact hNotMapped
      (loopBodyRootPlaceOf_surjective_of_prefix body redo q hPrefix))

theorem loopBodyRootTransition_post_zero_of_not_mapped
    (body redo : POWL2 Activity)
    (t : (target body).wfnet.net.Transition)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hNotMapped :
      ¬ ∃ p : (target body).wfnet.net.Place,
        loopBodyRootPlaceOf body redo p = q) :
    (target (POWL2.loop body redo)).wfnet.net.post
        (loopBodyRootTransitionOf body redo t) q = 0 :=
  loopBodyRootTransition_post_zero_of_not_prefix body redo t q (by
    intro hPrefix
    exact hNotMapped
      (loopBodyRootPlaceOf_surjective_of_prefix body redo q hPrefix))

theorem loopRedoRootTransition_pre
    (body redo : POWL2 Activity)
    (t : (target redo).wfnet.net.Transition)
    (q : (target redo).wfnet.net.Place) :
    (target (POWL2.loop body redo)).wfnet.net.pre
        (loopRedoRootTransitionOf body redo t)
        (loopRedoRootPlaceOf body redo q) =
      (target redo).wfnet.net.pre t q := by
  cases t
  cases q
  simp [loopRedoRootTransitionOf, loopRedoTransitionOf,
    loopRedoRootPlaceOf, loopRedoPlaceOf, transitionOf, placeOf,
    target, Structural.target, Structural.wfnet, Structural.net,
    Structural.compiled, Structural.normalize,
    Structural.rawPre_loop_redo_prefix]

theorem loopRedoRootTransition_post
    (body redo : POWL2 Activity)
    (t : (target redo).wfnet.net.Transition)
    (q : (target redo).wfnet.net.Place) :
    (target (POWL2.loop body redo)).wfnet.net.post
        (loopRedoRootTransitionOf body redo t)
        (loopRedoRootPlaceOf body redo q) =
      (target redo).wfnet.net.post t q := by
  cases t
  cases q
  simp [loopRedoRootTransitionOf, loopRedoTransitionOf,
    loopRedoRootPlaceOf, loopRedoPlaceOf, transitionOf, placeOf,
    target, Structural.target, Structural.wfnet, Structural.net,
    Structural.compiled, Structural.normalize,
    Structural.rawPost_loop_redo_prefix]

theorem loopRedoRootTransition_pre_zero_of_not_prefix
    (body redo : POWL2 Activity)
    (t : (target redo).wfnet.net.Transition)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hNoPrefix : ¬ Structural.HasPlacePrefix [1] q.1) :
    (target (POWL2.loop body redo)).wfnet.net.pre
        (loopRedoRootTransitionOf body redo t) q = 0 := by
  cases t
  cases q
  simp [loopRedoRootTransitionOf, loopRedoTransitionOf,
    transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre_loop_redo_prefix_zero, hNoPrefix]

theorem loopRedoRootTransition_post_zero_of_not_prefix
    (body redo : POWL2 Activity)
    (t : (target redo).wfnet.net.Transition)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hNoPrefix : ¬ Structural.HasPlacePrefix [1] q.1) :
    (target (POWL2.loop body redo)).wfnet.net.post
        (loopRedoRootTransitionOf body redo t) q = 0 := by
  cases t
  cases q
  simp [loopRedoRootTransitionOf, loopRedoTransitionOf,
    transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost_loop_redo_prefix_zero, hNoPrefix]

theorem loopRedoRootTransition_pre_zero_of_not_mapped
    (body redo : POWL2 Activity)
    (t : (target redo).wfnet.net.Transition)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hNotMapped :
      ¬ ∃ p : (target redo).wfnet.net.Place,
        loopRedoRootPlaceOf body redo p = q) :
    (target (POWL2.loop body redo)).wfnet.net.pre
        (loopRedoRootTransitionOf body redo t) q = 0 :=
  loopRedoRootTransition_pre_zero_of_not_prefix body redo t q (by
    intro hPrefix
    exact hNotMapped
      (loopRedoRootPlaceOf_surjective_of_prefix body redo q hPrefix))

theorem loopRedoRootTransition_post_zero_of_not_mapped
    (body redo : POWL2 Activity)
    (t : (target redo).wfnet.net.Transition)
    (q : (target (POWL2.loop body redo)).wfnet.net.Place)
    (hNotMapped :
      ¬ ∃ p : (target redo).wfnet.net.Place,
        loopRedoRootPlaceOf body redo p = q) :
    (target (POWL2.loop body redo)).wfnet.net.post
        (loopRedoRootTransitionOf body redo t) q = 0 :=
  loopRedoRootTransition_post_zero_of_not_prefix body redo t q (by
    intro hPrefix
    exact hNotMapped
      (loopRedoRootPlaceOf_surjective_of_prefix body redo q hPrefix))

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

noncomputable def partialOrderOriginalChildTransitionOf
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition)
    (hGet : POWL2.listGet? children i = some child)
    (hMem :
      t ∈ Structural.rawTransitions (Structural.normalize child)
        (Structural.childAddr [] i)) :
    (target (POWL2.partialOrder children order)).wfnet.net.Transition :=
  partialOrderChildTransitionOf children order t
    (POWL2.listGet?_map Structural.normalize hGet) hMem

noncomputable def partialOrderOriginalChildRootTransitionOf
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition) :
    (target (POWL2.partialOrder children order)).wfnet.net.Transition :=
  partialOrderOriginalChildTransitionOf children order
    (Structural.prefixTransition [i] t.1) hGet (by
      simpa [Structural.rawTransitionsRoot, Structural.compiled,
        Structural.childAddr] using
        Structural.rawTransitions_prefix_mem
          (Structural.compiled child) [i] [] t.2)

theorem partialOrderOriginalChildRootTransition_label
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition) :
    (target (POWL2.partialOrder children order)).label
        (partialOrderOriginalChildRootTransitionOf children order hGet t) =
      (target child).label t := by
  cases t
  simp [partialOrderOriginalChildRootTransitionOf,
    partialOrderOriginalChildTransitionOf, partialOrderChildTransitionOf,
    transitionOf, target, Structural.target, Structural.compiled,
    Structural.normalize, Structural.rawLabel_partialOrder_child_prefix,
    POWL2.listGet?_map, hGet]

theorem partialOrderOriginalChildRootTransition_traceOf
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (ts : List (target child).wfnet.net.Transition) :
    Petri.LabeledWFNet.traceOf (target (POWL2.partialOrder children order))
        (ts.map (partialOrderOriginalChildRootTransitionOf
          children order hGet)) =
      Petri.LabeledWFNet.traceOf (target child) ts :=
  Petri.LabeledWFNet.traceOf_map (target child)
    (target (POWL2.partialOrder children order))
    (partialOrderOriginalChildRootTransitionOf children order hGet)
    (partialOrderOriginalChildRootTransition_label children order hGet) ts

def partialOrderOriginalChildPlaceOf
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity} (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child)
    (hMem :
      q ∈ Structural.rawPlaces (Structural.normalize child)
        (Structural.childAddr [] i)) :
    (target (POWL2.partialOrder children order)).wfnet.net.Place :=
  partialOrderChildPlaceOf children order q
    (POWL2.listGet?_map Structural.normalize hGet) hMem

def partialOrderOriginalChildRootPlaceOf
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (q : (target child).wfnet.net.Place) :
    (target (POWL2.partialOrder children order)).wfnet.net.Place :=
  partialOrderOriginalChildPlaceOf children order
    (Structural.prefixPlace [i] q.1) hGet (by
      simpa [Structural.rawPlacesRoot, Structural.compiled,
        Structural.childAddr] using
      Structural.rawPlaces_prefix_mem
        (Structural.compiled child) [i] [] q.2)

theorem partialOrderOriginalChildRootPlaceOf_injective
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child) :
    Function.Injective
      (partialOrderOriginalChildRootPlaceOf children order hGet) := by
  intro q r h
  apply Subtype.ext
  apply Structural.prefixPlace_injective [i]
  exact congrArg Subtype.val h

theorem partialOrderOriginalChildRootTransition_pre
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition)
    (q : (target child).wfnet.net.Place) :
    (target (POWL2.partialOrder children order)).wfnet.net.pre
        (partialOrderOriginalChildRootTransitionOf children order hGet t)
        (partialOrderOriginalChildRootPlaceOf children order hGet q) =
      (target child).wfnet.net.pre t q := by
  cases t
  cases q
  simp [partialOrderOriginalChildRootTransitionOf,
    partialOrderOriginalChildTransitionOf, partialOrderChildTransitionOf,
    partialOrderOriginalChildRootPlaceOf,
    partialOrderOriginalChildPlaceOf, partialOrderChildPlaceOf,
    transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre_partialOrder_child_prefix, POWL2.listGet?_map, hGet]

theorem partialOrderOriginalChildRootTransition_post
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition)
    (q : (target child).wfnet.net.Place) :
    (target (POWL2.partialOrder children order)).wfnet.net.post
        (partialOrderOriginalChildRootTransitionOf children order hGet t)
        (partialOrderOriginalChildRootPlaceOf children order hGet q) =
      (target child).wfnet.net.post t q := by
  cases t
  cases q
  simp [partialOrderOriginalChildRootTransitionOf,
    partialOrderOriginalChildTransitionOf, partialOrderChildTransitionOf,
    partialOrderOriginalChildRootPlaceOf,
    partialOrderOriginalChildPlaceOf, partialOrderChildPlaceOf,
    transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost_partialOrder_child_prefix, POWL2.listGet?_map, hGet]

theorem partialOrderOriginalChildRootTransition_pre_zero_of_not_prefix
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition)
    (q : (target (POWL2.partialOrder children order)).wfnet.net.Place)
    (hNoPrefix : ¬ Structural.HasPlacePrefix [i] q.1) :
    (target (POWL2.partialOrder children order)).wfnet.net.pre
        (partialOrderOriginalChildRootTransitionOf children order hGet t)
        q = 0 := by
  cases t
  cases q
  simp [partialOrderOriginalChildRootTransitionOf,
    partialOrderOriginalChildTransitionOf, partialOrderChildTransitionOf,
    transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre_partialOrder_child_prefix_zero,
    POWL2.listGet?_map, hGet, hNoPrefix]

theorem partialOrderOriginalChildRootTransition_post_zero_of_not_prefix
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition)
    (q : (target (POWL2.partialOrder children order)).wfnet.net.Place)
    (hNoPrefix : ¬ Structural.HasPlacePrefix [i] q.1) :
    (target (POWL2.partialOrder children order)).wfnet.net.post
        (partialOrderOriginalChildRootTransitionOf children order hGet t)
        q = 0 := by
  cases t
  cases q
  simp [partialOrderOriginalChildRootTransitionOf,
    partialOrderOriginalChildTransitionOf, partialOrderChildTransitionOf,
    transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost_partialOrder_child_prefix_zero,
    POWL2.listGet?_map, hGet, hNoPrefix]

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

noncomputable def choiceGraphOriginalChildTransitionOf
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (t : RawTransition)
    (hGet : POWL2.listGet? children i = some child)
    (hMem :
      t ∈ Structural.rawTransitions (Structural.normalize child)
        (Structural.childAddr [] i)) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.Transition :=
  choiceGraphChildTransitionOf children graph t
    (POWL2.listGet?_map Structural.normalize hGet) hMem

noncomputable def choiceGraphOriginalChildRootTransitionOf
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.Transition :=
  choiceGraphOriginalChildTransitionOf children graph
    (Structural.prefixTransition [i] t.1) hGet (by
      simpa [Structural.rawTransitionsRoot, Structural.compiled,
        Structural.childAddr] using
        Structural.rawTransitions_prefix_mem
          (Structural.compiled child) [i] [] t.2)

theorem choiceGraphOriginalChildRootTransition_label
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition) :
    (target (POWL2.choiceGraph children graph)).label
        (choiceGraphOriginalChildRootTransitionOf children graph hGet t) =
      (target child).label t := by
  cases t
  simp [choiceGraphOriginalChildRootTransitionOf,
    choiceGraphOriginalChildTransitionOf, choiceGraphChildTransitionOf,
    transitionOf, target, Structural.target, Structural.compiled,
    Structural.normalize, Structural.rawLabel_choiceGraph_child_prefix,
    POWL2.listGet?_map, hGet]

theorem choiceGraphOriginalChildRootTransition_traceOf
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (ts : List (target child).wfnet.net.Transition) :
    Petri.LabeledWFNet.traceOf (target (POWL2.choiceGraph children graph))
        (ts.map (choiceGraphOriginalChildRootTransitionOf
          children graph hGet)) =
      Petri.LabeledWFNet.traceOf (target child) ts :=
  Petri.LabeledWFNet.traceOf_map (target child)
    (target (POWL2.choiceGraph children graph))
    (choiceGraphOriginalChildRootTransitionOf children graph hGet)
    (choiceGraphOriginalChildRootTransition_label children graph hGet) ts

def choiceGraphOriginalChildPlaceOf
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity} (q : RawPlace)
    (hGet : POWL2.listGet? children i = some child)
    (hMem :
      q ∈ Structural.rawPlaces (Structural.normalize child)
        (Structural.childAddr [] i)) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.Place :=
  choiceGraphChildPlaceOf children graph q
    (POWL2.listGet?_map Structural.normalize hGet) hMem

def choiceGraphOriginalChildRootPlaceOf
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (q : (target child).wfnet.net.Place) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.Place :=
  choiceGraphOriginalChildPlaceOf children graph
    (Structural.prefixPlace [i] q.1) hGet (by
      simpa [Structural.rawPlacesRoot, Structural.compiled,
        Structural.childAddr] using
      Structural.rawPlaces_prefix_mem
        (Structural.compiled child) [i] [] q.2)

theorem choiceGraphOriginalChildRootPlaceOf_injective
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child) :
    Function.Injective
      (choiceGraphOriginalChildRootPlaceOf children graph hGet) := by
  intro q r h
  apply Subtype.ext
  apply Structural.prefixPlace_injective [i]
  exact congrArg Subtype.val h

theorem choiceGraphOriginalChildRootTransition_pre
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition)
    (q : (target child).wfnet.net.Place) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.pre
        (choiceGraphOriginalChildRootTransitionOf children graph hGet t)
        (choiceGraphOriginalChildRootPlaceOf children graph hGet q) =
      (target child).wfnet.net.pre t q := by
  cases t
  cases q
  simp [choiceGraphOriginalChildRootTransitionOf,
    choiceGraphOriginalChildTransitionOf, choiceGraphChildTransitionOf,
    choiceGraphOriginalChildRootPlaceOf,
    choiceGraphOriginalChildPlaceOf, choiceGraphChildPlaceOf,
    transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre_choiceGraph_child_prefix, POWL2.listGet?_map, hGet]

theorem choiceGraphOriginalChildRootTransition_post
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition)
    (q : (target child).wfnet.net.Place) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.post
        (choiceGraphOriginalChildRootTransitionOf children graph hGet t)
        (choiceGraphOriginalChildRootPlaceOf children graph hGet q) =
      (target child).wfnet.net.post t q := by
  cases t
  cases q
  simp [choiceGraphOriginalChildRootTransitionOf,
    choiceGraphOriginalChildTransitionOf, choiceGraphChildTransitionOf,
    choiceGraphOriginalChildRootPlaceOf,
    choiceGraphOriginalChildPlaceOf, choiceGraphChildPlaceOf,
    transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost_choiceGraph_child_prefix, POWL2.listGet?_map, hGet]

theorem choiceGraphOriginalChildRootTransition_pre_zero_of_not_prefix
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition)
    (q : (target (POWL2.choiceGraph children graph)).wfnet.net.Place)
    (hNoPrefix : ¬ Structural.HasPlacePrefix [i] q.1) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.pre
        (choiceGraphOriginalChildRootTransitionOf children graph hGet t)
        q = 0 := by
  cases t
  cases q
  simp [choiceGraphOriginalChildRootTransitionOf,
    choiceGraphOriginalChildTransitionOf, choiceGraphChildTransitionOf,
    transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre_choiceGraph_child_prefix_zero,
    POWL2.listGet?_map, hGet, hNoPrefix]

theorem choiceGraphOriginalChildRootTransition_post_zero_of_not_prefix
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} {child : POWL2 Activity}
    (hGet : POWL2.listGet? children i = some child)
    (t : (target child).wfnet.net.Transition)
    (q : (target (POWL2.choiceGraph children graph)).wfnet.net.Place)
    (hNoPrefix : ¬ Structural.HasPlacePrefix [i] q.1) :
    (target (POWL2.choiceGraph children graph)).wfnet.net.post
        (choiceGraphOriginalChildRootTransitionOf children graph hGet t)
        q = 0 := by
  cases t
  cases q
  simp [choiceGraphOriginalChildRootTransitionOf,
    choiceGraphOriginalChildTransitionOf, choiceGraphChildTransitionOf,
    transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost_choiceGraph_child_prefix_zero,
    POWL2.listGet?_map, hGet, hNoPrefix]

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
