import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.Core
import Pm4Lean.Models.Petri.WFNet.Behavior.OneStep

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

theorem partialOrder_fork_root_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop) :
    Structural.transition [] TransitionKind.poFork ∈
      Structural.rawTransitionsRoot (POWL2.partialOrder children order) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.partialOrder_fork_transition_mem
      (children.map Structural.normalize) order []

theorem partialOrder_has_fork_transition
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop) :
    ∃ t : (target (POWL2.partialOrder children order)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.poFork := by
  refine ⟨transitionOf (POWL2.partialOrder children order)
    (Structural.transition [] TransitionKind.poFork)
    (partialOrder_fork_root_mem children order), rfl⟩

theorem partialOrder_fork_consumes_target_entry
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop) :
    let p := POWL2.partialOrder children order
    let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
      (partialOrder_fork_root_mem children order)
    let q := placeOf p (Structural.entry [])
      (Structural.source_mem p)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.partialOrder_fork_consumes_entry]

theorem partialOrder_fork_empty_produces_target_exit
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (hEmpty : children.length = 0) :
    let p := POWL2.partialOrder children order
    let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
      (partialOrder_fork_root_mem children order)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  have hEmpty' : (children.map Structural.normalize).length = 0 := by
    simpa using hEmpty
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.partialOrder_fork_empty_produces_exit, hEmpty']

theorem partialOrder_empty_fork_pre_singleton
    (order : Nat → Nat → Prop) :
    let p := POWL2.partialOrder ([] : List (POWL2 Activity)) order
    let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
      (partialOrder_fork_root_mem [] order)
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawPreFor, Structural.rawMark, Structural.entry,
    Structural.transition, Petri.Marking.singleton]

theorem partialOrder_empty_fork_post_singleton
    (order : Nat → Nat → Prop) :
    let p := POWL2.partialOrder ([] : List (POWL2 Activity)) order
    let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
      (partialOrder_fork_root_mem [] order)
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawPostFor, Structural.rawMark, Structural.exit,
    Structural.transition, Petri.Marking.singleton]

theorem partialOrder_empty_operational_epsilon
    (order : Nat → Nat → Prop) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.partialOrder ([] : List (POWL2 Activity)) order)) [] := by
  let p := POWL2.partialOrder ([] : List (POWL2 Activity)) order
  let t := transitionOf p (Structural.transition [] TransitionKind.poFork)
    (partialOrder_fork_root_mem [] order)
  have hRun :
      Petri.LabeledWFNet.operationalLanguage (target p)
        (Petri.LabeledWFNet.traceOf (target p) [t]) :=
    Petri.LabeledWFNet.operationalLanguage_of_singleton_pre_post
      (target p) t (partialOrder_empty_fork_pre_singleton order)
      (partialOrder_empty_fork_post_singleton order)
  simpa [p, t, Petri.LabeledWFNet.traceOf, transitionOf, target,
    Structural.target, Structural.compiled, Structural.normalize,
    Structural.rawLabel, Structural.childAt, Structural.transition] using hRun

theorem partialOrder_empty_language_realized_by_firing
    (order : Nat → Nat → Prop) {σ : Trace Activity}
    (h : POWL2.language
      (POWL2.partialOrder ([] : List (POWL2 Activity)) order) σ) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.partialOrder ([] : List (POWL2 Activity)) order)) σ := by
  rw [POWL2.partialOrder_language] at h
  have hσ : σ = [] :=
    (Language.partialOrder_nil_iff order σ).1 h
  rw [hσ]
  exact partialOrder_empty_operational_epsilon order

theorem partialOrder_empty_language_firing_witness
    (order : Nat → Nat → Prop) {σ : Trace Activity}
    (h : POWL2.language
      (POWL2.partialOrder ([] : List (POWL2 Activity)) order) σ) :
    ∃ ts : List
        (target (POWL2.partialOrder ([] : List (POWL2 Activity)) order)).wfnet.net.Transition,
      Petri.FiringSequence
        (target (POWL2.partialOrder ([] : List (POWL2 Activity)) order)).wfnet.net
        (target (POWL2.partialOrder ([] : List (POWL2 Activity)) order)).wfnet.initial ts
        (target (POWL2.partialOrder ([] : List (POWL2 Activity)) order)).wfnet.final ∧
      Petri.LabeledWFNet.traceOf
        (target (POWL2.partialOrder ([] : List (POWL2 Activity)) order)) ts = σ := by
  simpa [Petri.LabeledWFNet.operationalLanguage] using
    partialOrder_empty_language_realized_by_firing order h

theorem partialOrder_begin_root_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} (hRange : i < children.length) :
    Structural.transition [] (TransitionKind.poBegin i) ∈
      Structural.rawTransitionsRoot (POWL2.partialOrder children order) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.partialOrder_begin_transition_mem
      (children.map Structural.normalize) order [] hRange'

theorem partialOrder_complete_root_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} (hRange : i < children.length) :
    Structural.transition [] (TransitionKind.poComplete i) ∈
      Structural.rawTransitionsRoot (POWL2.partialOrder children order) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.partialOrder_complete_transition_mem
      (children.map Structural.normalize) order [] hRange'

theorem partialOrder_child_entry_root_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} (hRange : i < children.length) :
    Structural.childEntry [] i ∈
      Structural.rawPlacesRoot (POWL2.partialOrder children order) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  have hChild :
      Structural.childEntry [] i ∈
        Structural.rawPlacesChildren (children.map Structural.normalize) [] 0 :=
    Structural.rawChildEntry_mem (children.map Structural.normalize) [] hRange'
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize, Structural.rawPlaces] using Or.inr hChild

theorem partialOrder_child_exit_root_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} (hRange : i < children.length) :
    Structural.childExit [] i ∈
      Structural.rawPlacesRoot (POWL2.partialOrder children order) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  have hChild :
      Structural.childExit [] i ∈
        Structural.rawPlacesChildren (children.map Structural.normalize) [] 0 :=
    Structural.rawChildExit_mem (children.map Structural.normalize) [] hRange'
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize, Structural.rawPlaces] using Or.inr hChild

theorem partialOrder_has_begin_transition
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} (hRange : i < children.length) :
    ∃ t : (target (POWL2.partialOrder children order)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.poBegin i) := by
  refine ⟨transitionOf (POWL2.partialOrder children order)
    (Structural.transition [] (TransitionKind.poBegin i))
    (partialOrder_begin_root_mem children order hRange), rfl⟩

theorem partialOrder_begin_produces_target_child_entry
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} (hRange : i < children.length) :
    let p := POWL2.partialOrder children order
    let t := transitionOf p (Structural.transition [] (TransitionKind.poBegin i))
      (partialOrder_begin_root_mem children order hRange)
    let q := placeOf p (Structural.childEntry [] i)
      (partialOrder_child_entry_root_mem children order hRange)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.partialOrder_begin_produces_child_entry]

theorem partialOrder_has_complete_transition
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} (hRange : i < children.length) :
    ∃ t : (target (POWL2.partialOrder children order)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.poComplete i) := by
  refine ⟨transitionOf (POWL2.partialOrder children order)
    (Structural.transition [] (TransitionKind.poComplete i))
    (partialOrder_complete_root_mem children order hRange), rfl⟩

theorem partialOrder_complete_consumes_target_child_exit
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    {i : Nat} (hRange : i < children.length) :
    let p := POWL2.partialOrder children order
    let t := transitionOf p (Structural.transition [] (TransitionKind.poComplete i))
      (partialOrder_complete_root_mem children order hRange)
    let q := placeOf p (Structural.childExit [] i)
      (partialOrder_child_exit_root_mem children order hRange)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.partialOrder_complete_consumes_child_exit]

theorem partialOrder_join_root_mem
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (hNonempty : children.length ≠ 0) :
    Structural.transition [] TransitionKind.poJoin ∈
      Structural.rawTransitionsRoot (POWL2.partialOrder children order) := by
  have hNonempty' : (children.map Structural.normalize).length ≠ 0 := by
    simpa using hNonempty
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.partialOrder_join_transition_mem
      (children.map Structural.normalize) order [] hNonempty'

theorem partialOrder_has_join_transition
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (hNonempty : children.length ≠ 0) :
    ∃ t : (target (POWL2.partialOrder children order)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.poJoin := by
  refine ⟨transitionOf (POWL2.partialOrder children order)
    (Structural.transition [] TransitionKind.poJoin)
    (partialOrder_join_root_mem children order hNonempty), rfl⟩

theorem partialOrder_join_produces_target_exit
    (children : List (POWL2 Activity)) (order : Nat → Nat → Prop)
    (hNonempty : children.length ≠ 0) :
    let p := POWL2.partialOrder children order
    let t := transitionOf p (Structural.transition [] TransitionKind.poJoin)
      (partialOrder_join_root_mem children order hNonempty)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.partialOrder_join_produces_exit]

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
