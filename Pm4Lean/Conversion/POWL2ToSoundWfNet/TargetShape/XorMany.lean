import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.ChoiceGraph

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

theorem xorMany_rawPlacesRoot_eq_choiceGraph
    (children : List (POWL2 Activity)) :
    Structural.rawPlacesRoot (POWL2.xorMany children) =
      Structural.rawPlacesRoot
        (POWL2.choiceGraph children (POWL2.xorChoiceGraph children.length)) := by
  simp [Structural.rawPlacesRoot, Structural.compiled, Structural.normalize]

theorem xorMany_rawTransitionsRoot_eq_choiceGraph
    (children : List (POWL2 Activity)) :
    Structural.rawTransitionsRoot (POWL2.xorMany children) =
      Structural.rawTransitionsRoot
        (POWL2.choiceGraph children (POWL2.xorChoiceGraph children.length)) := by
  simp [Structural.rawTransitionsRoot, Structural.compiled, Structural.normalize]

theorem xorMany_empty_root_mem :
    Structural.transition [] TransitionKind.choiceEmpty ∈
      Structural.rawTransitionsRoot (POWL2.xorMany ([] : List (POWL2 Activity))) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize, POWL2.xorChoiceGraph] using
    Structural.choiceGraph_empty_transition_mem
      ([] : List (POWL2 Activity)) (POWL2.xorChoiceGraph 0) [] rfl

theorem xorMany_start_root_mem
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    Structural.transition [] (TransitionKind.choiceStart i) ∈
      Structural.rawTransitionsRoot (POWL2.xorMany children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize, POWL2.xorChoiceGraph] using
    Structural.choiceGraph_start_transition_mem
      (children.map Structural.normalize) (POWL2.xorChoiceGraph children.length)
      [] hRange hRange'

theorem xorMany_end_root_mem
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    Structural.transition [] (TransitionKind.choiceEnd i) ∈
      Structural.rawTransitionsRoot (POWL2.xorMany children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize, POWL2.xorChoiceGraph] using
    Structural.choiceGraph_end_transition_mem
      (children.map Structural.normalize) (POWL2.xorChoiceGraph children.length)
      [] hRange hRange'

theorem xorMany_child_entry_root_mem
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    Structural.childEntry [] i ∈
      Structural.rawPlacesRoot (POWL2.xorMany children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  have hChild :
      Structural.childEntry [] i ∈
        Structural.rawPlacesChildren (children.map Structural.normalize) [] 0 :=
    Structural.rawChildEntry_mem (children.map Structural.normalize) [] hRange'
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize, Structural.rawPlaces] using Or.inr (Or.inr hChild)

theorem xorMany_child_exit_root_mem
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    Structural.childExit [] i ∈
      Structural.rawPlacesRoot (POWL2.xorMany children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  have hChild :
      Structural.childExit [] i ∈
        Structural.rawPlacesChildren (children.map Structural.normalize) [] 0 :=
    Structural.rawChildExit_mem (children.map Structural.normalize) [] hRange'
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize, Structural.rawPlaces] using Or.inr (Or.inr hChild)

theorem xorMany_has_empty_transition :
    ∃ t : (target (POWL2.xorMany ([] : List (POWL2 Activity)))).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.choiceEmpty := by
  refine ⟨transitionOf (POWL2.xorMany ([] : List (POWL2 Activity)))
    (Structural.transition [] TransitionKind.choiceEmpty) xorMany_empty_root_mem, rfl⟩

theorem xorMany_empty_consumes_target_entry :
    let p := POWL2.xorMany ([] : List (POWL2 Activity))
    let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
      xorMany_empty_root_mem
    let q := placeOf p (Structural.entry [])
      (Structural.source_mem p)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    POWL2.xorChoiceGraph, Structural.choiceGraph_empty_consumes_entry]

theorem xorMany_empty_produces_target_exit :
    let p := POWL2.xorMany ([] : List (POWL2 Activity))
    let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
      xorMany_empty_root_mem
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    POWL2.xorChoiceGraph, Structural.choiceGraph_empty_produces_exit]

theorem xorMany_empty_pre_singleton :
    let p := POWL2.xorMany ([] : List (POWL2 Activity))
    let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
      xorMany_empty_root_mem
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    POWL2.xorChoiceGraph, Structural.rawPre, Structural.rawMark,
    Structural.entry, Structural.transition, Petri.Marking.singleton]

theorem xorMany_empty_post_singleton :
    let p := POWL2.xorMany ([] : List (POWL2 Activity))
    let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
      xorMany_empty_root_mem
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    POWL2.xorChoiceGraph, Structural.rawPost, Structural.rawMark,
    Structural.exit, Structural.transition, Petri.Marking.singleton]

theorem xorMany_empty_operational_epsilon :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.xorMany ([] : List (POWL2 Activity)))) [] := by
  let p := POWL2.xorMany ([] : List (POWL2 Activity))
  let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
    xorMany_empty_root_mem
  have hRun :
      Petri.LabeledWFNet.operationalLanguage (target p)
        (Petri.LabeledWFNet.traceOf (target p) [t]) :=
    Petri.LabeledWFNet.operationalLanguage_of_singleton_pre_post
      (target p) t xorMany_empty_pre_singleton xorMany_empty_post_singleton
  simpa [p, t, Petri.LabeledWFNet.traceOf, transitionOf, target,
    Structural.target, Structural.compiled, Structural.normalize,
    POWL2.xorChoiceGraph, Structural.rawLabel, Structural.childAt,
    Structural.transition] using hRun

theorem xorMany_empty_language_realized_by_firing
    {σ : Trace Activity}
    (h : POWL2.language (POWL2.xorMany ([] : List (POWL2 Activity))) σ) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.xorMany ([] : List (POWL2 Activity)))) σ := by
  simp [POWL2.language, POWL2.choiceGraphLanguage, POWL2.xorChoiceGraph] at h
  rcases h with ⟨path, hPath, hLang⟩
  cases hPath with
  | empty _ =>
      simp [POWL2.pathLanguage, Language.epsilon] at hLang
      subst hLang
      exact xorMany_empty_operational_epsilon
  | start hStart _ =>
      exact False.elim hStart

theorem xorMany_has_start_transition
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    ∃ t : (target (POWL2.xorMany children)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.choiceStart i) := by
  refine ⟨transitionOf (POWL2.xorMany children)
    (Structural.transition [] (TransitionKind.choiceStart i))
    (xorMany_start_root_mem children hRange), rfl⟩

theorem xorMany_start_consumes_target_entry
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    let p := POWL2.xorMany children
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceStart i))
      (xorMany_start_root_mem children hRange)
    let q := placeOf p (Structural.entry [])
      (Structural.source_mem p)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    POWL2.xorChoiceGraph, Structural.choiceGraph_start_consumes_entry]

theorem xorMany_start_produces_target_child_entry
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    let p := POWL2.xorMany children
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceStart i))
      (xorMany_start_root_mem children hRange)
    let q := placeOf p (Structural.childEntry [] i)
      (xorMany_child_entry_root_mem children hRange)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    POWL2.xorChoiceGraph, Structural.choiceGraph_start_produces_child_entry]

theorem xorMany_has_end_transition
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    ∃ t : (target (POWL2.xorMany children)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.choiceEnd i) := by
  refine ⟨transitionOf (POWL2.xorMany children)
    (Structural.transition [] (TransitionKind.choiceEnd i))
    (xorMany_end_root_mem children hRange), rfl⟩

theorem xorMany_end_consumes_target_child_exit
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    let p := POWL2.xorMany children
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceEnd i))
      (xorMany_end_root_mem children hRange)
    let q := placeOf p (Structural.childExit [] i)
      (xorMany_child_exit_root_mem children hRange)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    POWL2.xorChoiceGraph, Structural.choiceGraph_end_consumes_child_exit]

theorem xorMany_end_produces_target_exit
    (children : List (POWL2 Activity)) {i : Nat} (hRange : i < children.length) :
    let p := POWL2.xorMany children
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceEnd i))
      (xorMany_end_root_mem children hRange)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    POWL2.xorChoiceGraph, Structural.choiceGraph_end_produces_exit]

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
