import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.Core
import Pm4Lean.Models.Petri.WFNet.Behavior.OneStep

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

theorem parallel_fork_root_mem
    (children : List (POWL2 Activity)) :
    Structural.transition [] TransitionKind.poFork ∈
      Structural.rawTransitionsRoot (POWL2.parallel children) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.parallel_fork_transition_mem
      (children.map Structural.normalize) []

theorem parallel_begin_root_mem
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    Structural.transition [] (TransitionKind.poBegin i) ∈
      Structural.rawTransitionsRoot (POWL2.parallel children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.parallel_begin_transition_mem
      (children.map Structural.normalize) [] hRange'

theorem parallel_complete_root_mem
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    Structural.transition [] (TransitionKind.poComplete i) ∈
      Structural.rawTransitionsRoot (POWL2.parallel children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.parallel_complete_transition_mem
      (children.map Structural.normalize) [] hRange'

theorem parallel_join_root_mem
    (children : List (POWL2 Activity)) (hNonempty : children.length ≠ 0) :
    Structural.transition [] TransitionKind.poJoin ∈
      Structural.rawTransitionsRoot (POWL2.parallel children) := by
  have hNonempty' : (children.map Structural.normalize).length ≠ 0 := by
    simpa using hNonempty
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.parallel_join_transition_mem
      (children.map Structural.normalize) [] hNonempty'

theorem parallel_child_entry_root_mem
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    Structural.childEntry [] i ∈
      Structural.rawPlacesRoot (POWL2.parallel children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize] using
    Structural.parallel_child_entry_mem
      (children.map Structural.normalize) [] hRange'

theorem parallel_child_exit_root_mem
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    Structural.childExit [] i ∈
      Structural.rawPlacesRoot (POWL2.parallel children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize] using
    Structural.parallel_child_exit_mem
      (children.map Structural.normalize) [] hRange'

theorem parallel_has_fork_transition
    (children : List (POWL2 Activity)) :
    ∃ t : (target (POWL2.parallel children)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.poFork := by
  refine ⟨transitionOf (POWL2.parallel children)
    (Structural.transition [] TransitionKind.poFork)
    (parallel_fork_root_mem children), rfl⟩

theorem parallel_fork_consumes_target_entry
    (children : List (POWL2 Activity)) :
    let p := POWL2.parallel children
    let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
      (parallel_fork_root_mem children)
    let q := placeOf p (Structural.entry [])
      (Structural.source_mem p)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.parallel_fork_consumes_entry]

theorem parallel_fork_empty_produces_target_exit
    (children : List (POWL2 Activity)) (hEmpty : children.length = 0) :
    let p := POWL2.parallel children
    let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
      (parallel_fork_root_mem children)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  have hEmpty' : (children.map Structural.normalize).length = 0 := by
    simpa using hEmpty
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.parallel_fork_empty_produces_exit, hEmpty']

theorem parallel_empty_fork_pre_singleton :
    let p := POWL2.parallel ([] : List (POWL2 Activity))
    let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
      (parallel_fork_root_mem [])
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawMark, Structural.entry,
    Structural.transition, Petri.Marking.singleton]

theorem parallel_empty_fork_post_singleton :
    let p := POWL2.parallel ([] : List (POWL2 Activity))
    let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
      (parallel_fork_root_mem [])
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawMark, Structural.exit,
    Structural.transition, Petri.Marking.singleton,
    POWL2.parallelOrder]

theorem parallel_empty_operational_epsilon :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.parallel ([] : List (POWL2 Activity)))) [] := by
  let p := POWL2.parallel ([] : List (POWL2 Activity))
  let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
    (parallel_fork_root_mem [])
  have hRun :
      Petri.LabeledWFNet.operationalLanguage (target p)
        (Petri.LabeledWFNet.traceOf (target p) [t]) :=
    Petri.LabeledWFNet.operationalLanguage_of_singleton_pre_post
      (target p) t parallel_empty_fork_pre_singleton
      parallel_empty_fork_post_singleton
  simpa [p, t, Petri.LabeledWFNet.traceOf, transitionOf, target,
    Structural.target, Structural.compiled, Structural.normalize,
    Structural.rawLabel, Structural.childAt, Structural.transition] using hRun

theorem parallel_empty_language_realized_by_firing
    {σ : Trace Activity}
    (h : POWL2.language (POWL2.parallel ([] : List (POWL2 Activity))) σ) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.parallel ([] : List (POWL2 Activity)))) σ := by
  rw [POWL2.parallel_language] at h
  have hσ : σ = [] :=
    (Language.partialOrder_nil_iff POWL2.parallelOrder σ).1 h
  rw [hσ]
  exact parallel_empty_operational_epsilon

theorem parallel_has_begin_transition
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    ∃ t : (target (POWL2.parallel children)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.poBegin i) := by
  refine ⟨transitionOf (POWL2.parallel children)
    (Structural.transition [] (TransitionKind.poBegin i))
    (parallel_begin_root_mem children hRange), rfl⟩

theorem parallel_begin_produces_target_child_entry
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    let p := POWL2.parallel children
    let t := transitionOf p (Structural.transition [] (TransitionKind.poBegin i))
      (parallel_begin_root_mem children hRange)
    let q := placeOf p (Structural.childEntry [] i)
      (parallel_child_entry_root_mem children hRange)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.parallel_begin_produces_child_entry]

theorem parallel_has_complete_transition
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    ∃ t : (target (POWL2.parallel children)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.poComplete i) := by
  refine ⟨transitionOf (POWL2.parallel children)
    (Structural.transition [] (TransitionKind.poComplete i))
    (parallel_complete_root_mem children hRange), rfl⟩

theorem parallel_complete_consumes_target_child_exit
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    let p := POWL2.parallel children
    let t := transitionOf p (Structural.transition [] (TransitionKind.poComplete i))
      (parallel_complete_root_mem children hRange)
    let q := placeOf p (Structural.childExit [] i)
      (parallel_child_exit_root_mem children hRange)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.parallel_complete_consumes_child_exit]

theorem parallel_has_join_transition
    (children : List (POWL2 Activity)) (hNonempty : children.length ≠ 0) :
    ∃ t : (target (POWL2.parallel children)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.poJoin := by
  refine ⟨transitionOf (POWL2.parallel children)
    (Structural.transition [] TransitionKind.poJoin)
    (parallel_join_root_mem children hNonempty), rfl⟩

theorem parallel_join_produces_target_exit
    (children : List (POWL2 Activity)) (hNonempty : children.length ≠ 0) :
    let p := POWL2.parallel children
    let t := transitionOf p (Structural.transition [] TransitionKind.poJoin)
      (parallel_join_root_mem children hNonempty)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.parallel_join_produces_exit]

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
