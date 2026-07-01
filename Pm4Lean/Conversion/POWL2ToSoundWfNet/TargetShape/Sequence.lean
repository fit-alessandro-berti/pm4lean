import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.Core
import Pm4Lean.Models.Petri.WFNet.Behavior.OneStep

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

theorem sequence_start_root_mem
    (children : List (POWL2 Activity)) :
    Structural.transition [] TransitionKind.seqStart ∈
      Structural.rawTransitionsRoot (POWL2.sequence children) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.sequence_start_transition_mem
      (children.map Structural.normalize) []

theorem sequence_next_root_mem
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length - 1) :
    Structural.transition [] (TransitionKind.seqNext i) ∈
      Structural.rawTransitionsRoot (POWL2.sequence children) := by
  have hRange' : i < (children.map Structural.normalize).length - 1 := by
    simpa using hRange
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.sequence_next_transition_mem
      (children.map Structural.normalize) [] hRange'

theorem sequence_end_root_mem
    (children : List (POWL2 Activity)) (hNonempty : children.length ≠ 0) :
    Structural.transition [] TransitionKind.seqEnd ∈
      Structural.rawTransitionsRoot (POWL2.sequence children) := by
  have hNonempty' : (children.map Structural.normalize).length ≠ 0 := by
    simpa using hNonempty
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.sequence_end_transition_mem
      (children.map Structural.normalize) [] hNonempty'

theorem sequence_child_entry_root_mem
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    Structural.childEntry [] i ∈
      Structural.rawPlacesRoot (POWL2.sequence children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize] using
    Structural.sequence_child_entry_mem
      (children.map Structural.normalize) [] hRange'

theorem sequence_child_exit_root_mem
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length) :
    Structural.childExit [] i ∈
      Structural.rawPlacesRoot (POWL2.sequence children) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize] using
    Structural.sequence_child_exit_mem
      (children.map Structural.normalize) [] hRange'

theorem sequence_has_start_transition
    (children : List (POWL2 Activity)) :
    ∃ t : (target (POWL2.sequence children)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.seqStart := by
  refine ⟨transitionOf (POWL2.sequence children)
    (Structural.transition [] TransitionKind.seqStart)
    (sequence_start_root_mem children), rfl⟩

theorem sequence_start_consumes_target_entry
    (children : List (POWL2 Activity)) :
    let p := POWL2.sequence children
    let t := transitionOf p (Structural.transition [] TransitionKind.seqStart)
      (sequence_start_root_mem children)
    let q := placeOf p (Structural.entry [])
      (Structural.source_mem p)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.sequence_start_consumes_entry]

theorem sequence_start_empty_produces_target_exit
    (children : List (POWL2 Activity)) (hEmpty : children.length = 0) :
    let p := POWL2.sequence children
    let t := transitionOf p (Structural.transition [] TransitionKind.seqStart)
      (sequence_start_root_mem children)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  have hEmpty' : (children.map Structural.normalize).length = 0 := by
    simpa using hEmpty
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.sequence_start_empty_produces_exit, hEmpty']

theorem sequence_empty_start_pre_singleton :
    let p := POWL2.sequence ([] : List (POWL2 Activity))
    let t := transitionOf p (Structural.transition [] TransitionKind.seqStart)
      (sequence_start_root_mem [])
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawMark, Structural.entry,
    Structural.transition, Petri.Marking.singleton]

theorem sequence_empty_start_post_singleton :
    let p := POWL2.sequence ([] : List (POWL2 Activity))
    let t := transitionOf p (Structural.transition [] TransitionKind.seqStart)
      (sequence_start_root_mem [])
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawMark, Structural.exit,
    Structural.transition, Petri.Marking.singleton]

theorem sequence_empty_operational_epsilon :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.sequence ([] : List (POWL2 Activity)))) [] := by
  let p := POWL2.sequence ([] : List (POWL2 Activity))
  let t := transitionOf p (Structural.transition [] TransitionKind.seqStart)
    (sequence_start_root_mem [])
  have hRun :
      Petri.LabeledWFNet.operationalLanguage (target p)
        (Petri.LabeledWFNet.traceOf (target p) [t]) :=
    Petri.LabeledWFNet.operationalLanguage_of_singleton_pre_post
      (target p) t sequence_empty_start_pre_singleton
      sequence_empty_start_post_singleton
  simpa [p, t, Petri.LabeledWFNet.traceOf, transitionOf, target,
    Structural.target, Structural.compiled, Structural.normalize,
    Structural.rawLabel, Structural.childAt, Structural.transition] using hRun

theorem sequence_empty_language_realized_by_firing
    {σ : Trace Activity}
    (h : POWL2.language (POWL2.sequence ([] : List (POWL2 Activity))) σ) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.sequence ([] : List (POWL2 Activity)))) σ := by
  rw [POWL2.sequence_language] at h
  have hσ : σ = [] :=
    (Language.partialOrder_nil_iff (POWL2.sequenceOrder 0) σ).1 h
  rw [hσ]
  exact sequence_empty_operational_epsilon

theorem sequence_start_nonempty_produces_target_first_entry
    (children : List (POWL2 Activity)) (hNonempty : children.length ≠ 0) :
    let p := POWL2.sequence children
    let t := transitionOf p (Structural.transition [] TransitionKind.seqStart)
      (sequence_start_root_mem children)
    let q := placeOf p (Structural.childEntry [] 0)
      (sequence_child_entry_root_mem children (by
        cases hLen : children.length with
        | zero => exact False.elim (hNonempty hLen)
        | succ n => simp))
    (target p).wfnet.net.post t q = 1 := by
  have hNonempty' : (children.map Structural.normalize).length ≠ 0 := by
    simpa using hNonempty
  simpa [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize] using
    Structural.sequence_start_nonempty_produces_first_entry
      (children.map Structural.normalize) [] hNonempty'

theorem sequence_has_next_transition
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length - 1) :
    ∃ t : (target (POWL2.sequence children)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.seqNext i) := by
  refine ⟨transitionOf (POWL2.sequence children)
    (Structural.transition [] (TransitionKind.seqNext i))
    (sequence_next_root_mem children hRange), rfl⟩

theorem sequence_next_consumes_target_child_exit
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length - 1) :
    let p := POWL2.sequence children
    let t := transitionOf p (Structural.transition [] (TransitionKind.seqNext i))
      (sequence_next_root_mem children hRange)
    let q := placeOf p (Structural.childExit [] i)
      (sequence_child_exit_root_mem children
        (Nat.lt_of_lt_of_le hRange (Nat.sub_le _ _)))
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.sequence_next_consumes_child_exit]

theorem sequence_next_produces_target_next_entry
    (children : List (POWL2 Activity)) {i : Nat}
    (hRange : i < children.length - 1) (hNext : i + 1 < children.length) :
    let p := POWL2.sequence children
    let t := transitionOf p (Structural.transition [] (TransitionKind.seqNext i))
      (sequence_next_root_mem children hRange)
    let q := placeOf p (Structural.childEntry [] (i + 1))
      (sequence_child_entry_root_mem children hNext)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.sequence_next_produces_next_entry]

theorem sequence_has_end_transition
    (children : List (POWL2 Activity)) (hNonempty : children.length ≠ 0) :
    ∃ t : (target (POWL2.sequence children)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.seqEnd := by
  refine ⟨transitionOf (POWL2.sequence children)
    (Structural.transition [] TransitionKind.seqEnd)
    (sequence_end_root_mem children hNonempty), rfl⟩

theorem sequence_end_consumes_target_last_exit
    (children : List (POWL2 Activity)) (hNonempty : children.length ≠ 0) :
    let p := POWL2.sequence children
    let t := transitionOf p (Structural.transition [] TransitionKind.seqEnd)
      (sequence_end_root_mem children hNonempty)
    let q := placeOf p (Structural.childExit [] (Structural.lastChildIndex children.length))
      (sequence_child_exit_root_mem children (by
        cases hLen : children.length with
        | zero => exact False.elim (hNonempty hLen)
        | succ n => simp [Structural.lastChildIndex]))
    (target p).wfnet.net.pre t q = 1 := by
  simpa [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize] using
    Structural.sequence_end_consumes_last_exit
      (children.map Structural.normalize) []

theorem sequence_end_produces_target_exit
    (children : List (POWL2 Activity)) (hNonempty : children.length ≠ 0) :
    let p := POWL2.sequence children
    let t := transitionOf p (Structural.transition [] TransitionKind.seqEnd)
      (sequence_end_root_mem children hNonempty)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.sequence_end_produces_exit]

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
