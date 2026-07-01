import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.Embedding
import Pm4Lean.Models.Petri.WFNet.Behavior.OneStep

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

theorem loop_start_root_mem
    (body redo : POWL2 Activity) :
    Structural.transition [] TransitionKind.loopStart ∈
      Structural.rawTransitionsRoot (POWL2.loop body redo) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.loop_start_transition_mem
      (Structural.normalize body) (Structural.normalize redo) []

theorem loop_exit_root_mem
    (body redo : POWL2 Activity) :
    Structural.transition [] TransitionKind.loopExit ∈
      Structural.rawTransitionsRoot (POWL2.loop body redo) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.loop_exit_transition_mem
      (Structural.normalize body) (Structural.normalize redo) []

theorem loop_redo_root_mem
    (body redo : POWL2 Activity) :
    Structural.transition [] TransitionKind.loopRedo ∈
      Structural.rawTransitionsRoot (POWL2.loop body redo) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.loop_redo_transition_mem
      (Structural.normalize body) (Structural.normalize redo) []

theorem loop_back_root_mem
    (body redo : POWL2 Activity) :
    Structural.transition [] TransitionKind.loopBack ∈
      Structural.rawTransitionsRoot (POWL2.loop body redo) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.loop_back_transition_mem
      (Structural.normalize body) (Structural.normalize redo) []

theorem loop_body_entry_root_mem
    (body redo : POWL2 Activity) :
    Structural.childEntry [] 0 ∈
      Structural.rawPlacesRoot (POWL2.loop body redo) := by
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize] using
    Structural.loop_body_entry_mem
      (Structural.normalize body) (Structural.normalize redo) []

theorem loop_body_exit_root_mem
    (body redo : POWL2 Activity) :
    Structural.childExit [] 0 ∈
      Structural.rawPlacesRoot (POWL2.loop body redo) := by
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize] using
    Structural.loop_body_exit_mem
      (Structural.normalize body) (Structural.normalize redo) []

theorem loop_redo_entry_root_mem
    (body redo : POWL2 Activity) :
    Structural.childEntry [] 1 ∈
      Structural.rawPlacesRoot (POWL2.loop body redo) := by
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize] using
    Structural.loop_redo_entry_mem
      (Structural.normalize body) (Structural.normalize redo) []

theorem loop_redo_exit_root_mem
    (body redo : POWL2 Activity) :
    Structural.childExit [] 1 ∈
      Structural.rawPlacesRoot (POWL2.loop body redo) := by
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize] using
    Structural.loop_redo_exit_mem
      (Structural.normalize body) (Structural.normalize redo) []

theorem loop_has_start_transition
    (body redo : POWL2 Activity) :
    ∃ t : (target (POWL2.loop body redo)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.loopStart := by
  refine ⟨transitionOf (POWL2.loop body redo)
    (Structural.transition [] TransitionKind.loopStart)
    (loop_start_root_mem body redo), rfl⟩

theorem loop_start_consumes_target_entry
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopStart)
      (loop_start_root_mem body redo)
    let q := placeOf p (Structural.entry [])
      (Structural.source_mem p)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.loop_start_consumes_entry]

theorem loop_start_produces_target_body_entry
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopStart)
      (loop_start_root_mem body redo)
    let q := placeOf p (Structural.childEntry [] 0)
      (loop_body_entry_root_mem body redo)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.loop_start_produces_body_entry]

theorem loop_start_pre_singleton
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopStart)
      (loop_start_root_mem body redo)
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawPreFor, Structural.rawMark,
    Structural.entry, Structural.transition, Petri.Marking.singleton]

theorem loop_start_post_singleton
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopStart)
      (loop_start_root_mem body redo)
    let bodyEntry := placeOf p (Structural.childEntry [] 0)
      (loop_body_entry_root_mem body redo)
    (target p).wfnet.net.post t =
      Petri.Marking.singleton bodyEntry := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawPostFor, Structural.rawMark,
    Structural.childEntry, Structural.childAddr, Structural.entry,
    Structural.transition, Petri.Marking.singleton]

theorem loop_start_firingSequence
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopStart)
      (loop_start_root_mem body redo)
    let bodyEntry := placeOf p (Structural.childEntry [] 0)
      (loop_body_entry_root_mem body redo)
    Petri.FiringSequence (target p).wfnet.net (target p).wfnet.initial [t]
      (Petri.Marking.singleton bodyEntry) := by
  intro p t bodyEntry
  simpa [Petri.WFNet.initial] using
    Petri.FiringSequence.singleton_of_pre_post (target p).wfnet.i bodyEntry t
      (loop_start_pre_singleton body redo)
      (loop_start_post_singleton body redo)

theorem loop_start_label
    (body redo : POWL2 Activity) :
    (target (POWL2.loop body redo)).label
      (transitionOf (POWL2.loop body redo)
        (Structural.transition [] TransitionKind.loopStart)
        (loop_start_root_mem body redo)) = none := by
  simp [transitionOf, target, Structural.target, Structural.compiled,
    Structural.normalize, Structural.rawLabel, Structural.transition]

theorem loop_has_exit_transition
    (body redo : POWL2 Activity) :
    ∃ t : (target (POWL2.loop body redo)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.loopExit := by
  refine ⟨transitionOf (POWL2.loop body redo)
    (Structural.transition [] TransitionKind.loopExit)
    (loop_exit_root_mem body redo), rfl⟩

theorem loop_exit_consumes_target_body_exit
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopExit)
      (loop_exit_root_mem body redo)
    let q := placeOf p (Structural.childExit [] 0)
      (loop_body_exit_root_mem body redo)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.loop_exit_consumes_body_exit]

theorem loop_exit_produces_target_exit
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopExit)
      (loop_exit_root_mem body redo)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.loop_exit_produces_exit]

theorem loop_exit_pre_singleton
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopExit)
      (loop_exit_root_mem body redo)
    let bodyExit := placeOf p (Structural.childExit [] 0)
      (loop_body_exit_root_mem body redo)
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton bodyExit := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawPreFor, Structural.rawMark,
    Structural.childExit, Structural.childAddr, Structural.exit,
    Structural.transition, Petri.Marking.singleton]

theorem loop_exit_post_singleton
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopExit)
      (loop_exit_root_mem body redo)
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawPostFor, Structural.rawMark,
    Structural.exit, Structural.transition, Petri.Marking.singleton]

theorem loop_exit_firingSequence
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopExit)
      (loop_exit_root_mem body redo)
    let bodyExit := placeOf p (Structural.childExit [] 0)
      (loop_body_exit_root_mem body redo)
    Petri.FiringSequence (target p).wfnet.net
      (Petri.Marking.singleton bodyExit) [t] (target p).wfnet.final := by
  intro p t bodyExit
  simpa [Petri.WFNet.final] using
    Petri.FiringSequence.singleton_of_pre_post bodyExit (target p).wfnet.o t
      (loop_exit_pre_singleton body redo)
      (loop_exit_post_singleton body redo)

theorem loop_exit_label
    (body redo : POWL2 Activity) :
    (target (POWL2.loop body redo)).label
      (transitionOf (POWL2.loop body redo)
        (Structural.transition [] TransitionKind.loopExit)
        (loop_exit_root_mem body redo)) = none := by
  simp [transitionOf, target, Structural.target, Structural.compiled,
    Structural.normalize, Structural.rawLabel, Structural.transition]

theorem loop_has_redo_transition
    (body redo : POWL2 Activity) :
    ∃ t : (target (POWL2.loop body redo)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.loopRedo := by
  refine ⟨transitionOf (POWL2.loop body redo)
    (Structural.transition [] TransitionKind.loopRedo)
    (loop_redo_root_mem body redo), rfl⟩

theorem loop_redo_consumes_target_body_exit
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopRedo)
      (loop_redo_root_mem body redo)
    let q := placeOf p (Structural.childExit [] 0)
      (loop_body_exit_root_mem body redo)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.loop_redo_consumes_body_exit]

theorem loop_redo_produces_target_redo_entry
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopRedo)
      (loop_redo_root_mem body redo)
    let q := placeOf p (Structural.childEntry [] 1)
      (loop_redo_entry_root_mem body redo)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.loop_redo_produces_redo_entry]

theorem loop_redo_pre_singleton
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopRedo)
      (loop_redo_root_mem body redo)
    let bodyExit := placeOf p (Structural.childExit [] 0)
      (loop_body_exit_root_mem body redo)
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton bodyExit := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawPreFor, Structural.rawMark,
    Structural.childExit, Structural.childAddr, Structural.exit,
    Structural.transition, Petri.Marking.singleton]

theorem loop_redo_post_singleton
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopRedo)
      (loop_redo_root_mem body redo)
    let redoEntry := placeOf p (Structural.childEntry [] 1)
      (loop_redo_entry_root_mem body redo)
    (target p).wfnet.net.post t =
      Petri.Marking.singleton redoEntry := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawPostFor, Structural.rawMark,
    Structural.childEntry, Structural.childAddr, Structural.entry,
    Structural.transition, Petri.Marking.singleton]

theorem loop_redo_firingSequence
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopRedo)
      (loop_redo_root_mem body redo)
    let bodyExit := placeOf p (Structural.childExit [] 0)
      (loop_body_exit_root_mem body redo)
    let redoEntry := placeOf p (Structural.childEntry [] 1)
      (loop_redo_entry_root_mem body redo)
    Petri.FiringSequence (target p).wfnet.net
      (Petri.Marking.singleton bodyExit) [t]
      (Petri.Marking.singleton redoEntry) := by
  intro p t bodyExit redoEntry
  exact
    Petri.FiringSequence.singleton_of_pre_post bodyExit redoEntry t
      (loop_redo_pre_singleton body redo)
      (loop_redo_post_singleton body redo)

theorem loop_redo_label
    (body redo : POWL2 Activity) :
    (target (POWL2.loop body redo)).label
      (transitionOf (POWL2.loop body redo)
        (Structural.transition [] TransitionKind.loopRedo)
        (loop_redo_root_mem body redo)) = none := by
  simp [transitionOf, target, Structural.target, Structural.compiled,
    Structural.normalize, Structural.rawLabel, Structural.transition]

theorem loop_has_back_transition
    (body redo : POWL2 Activity) :
    ∃ t : (target (POWL2.loop body redo)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.loopBack := by
  refine ⟨transitionOf (POWL2.loop body redo)
    (Structural.transition [] TransitionKind.loopBack)
    (loop_back_root_mem body redo), rfl⟩

theorem loop_back_consumes_target_redo_exit
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopBack)
      (loop_back_root_mem body redo)
    let q := placeOf p (Structural.childExit [] 1)
      (loop_redo_exit_root_mem body redo)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.loop_back_consumes_redo_exit]

theorem loop_back_produces_target_body_entry
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopBack)
      (loop_back_root_mem body redo)
    let q := placeOf p (Structural.childEntry [] 0)
      (loop_body_entry_root_mem body redo)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.loop_back_produces_body_entry]

theorem loop_back_pre_singleton
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopBack)
      (loop_back_root_mem body redo)
    let redoExit := placeOf p (Structural.childExit [] 1)
      (loop_redo_exit_root_mem body redo)
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton redoExit := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawPreFor, Structural.rawMark,
    Structural.childExit, Structural.childAddr, Structural.exit,
    Structural.transition, Petri.Marking.singleton]

theorem loop_back_post_singleton
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopBack)
      (loop_back_root_mem body redo)
    let bodyEntry := placeOf p (Structural.childEntry [] 0)
      (loop_body_entry_root_mem body redo)
    (target p).wfnet.net.post t =
      Petri.Marking.singleton bodyEntry := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawPostFor, Structural.rawMark,
    Structural.childEntry, Structural.childAddr, Structural.entry,
    Structural.transition, Petri.Marking.singleton]

theorem loop_back_firingSequence
    (body redo : POWL2 Activity) :
    let p := POWL2.loop body redo
    let t := transitionOf p (Structural.transition [] TransitionKind.loopBack)
      (loop_back_root_mem body redo)
    let redoExit := placeOf p (Structural.childExit [] 1)
      (loop_redo_exit_root_mem body redo)
    let bodyEntry := placeOf p (Structural.childEntry [] 0)
      (loop_body_entry_root_mem body redo)
    Petri.FiringSequence (target p).wfnet.net
      (Petri.Marking.singleton redoExit) [t]
      (Petri.Marking.singleton bodyEntry) := by
  intro p t redoExit bodyEntry
  exact
    Petri.FiringSequence.singleton_of_pre_post redoExit bodyEntry t
      (loop_back_pre_singleton body redo)
      (loop_back_post_singleton body redo)

theorem loop_back_label
    (body redo : POWL2 Activity) :
    (target (POWL2.loop body redo)).label
      (transitionOf (POWL2.loop body redo)
        (Structural.transition [] TransitionKind.loopBack)
        (loop_back_root_mem body redo)) = none := by
  simp [transitionOf, target, Structural.target, Structural.compiled,
    Structural.normalize, Structural.rawLabel, Structural.transition]

theorem loop_body_once_firingSequence
    (body redo : POWL2 Activity)
    {ts : List (target body).wfnet.net.Transition}
    (hBody : Petri.FiringSequence (target body).wfnet.net
      (target body).wfnet.initial ts (target body).wfnet.final) :
    Petri.FiringSequence (target (POWL2.loop body redo)).wfnet.net
      (target (POWL2.loop body redo)).wfnet.initial
      ([transitionOf (POWL2.loop body redo)
          (Structural.transition [] TransitionKind.loopStart)
          (loop_start_root_mem body redo)] ++
        ts.map (loopBodyRootTransitionOf body redo) ++
        [transitionOf (POWL2.loop body redo)
          (Structural.transition [] TransitionKind.loopExit)
          (loop_exit_root_mem body redo)])
      (target (POWL2.loop body redo)).wfnet.final := by
  let p := POWL2.loop body redo
  let start :=
    transitionOf p (Structural.transition [] TransitionKind.loopStart)
      (loop_start_root_mem body redo)
  let exit :=
    transitionOf p (Structural.transition [] TransitionKind.loopExit)
      (loop_exit_root_mem body redo)
  let bodyEntry :=
    placeOf p (Structural.childEntry [] 0)
      (loop_body_entry_root_mem body redo)
  let bodyExit :=
    placeOf p (Structural.childExit [] 0)
      (loop_body_exit_root_mem body redo)
  have hStart :
      Petri.FiringSequence (target p).wfnet.net
        (target p).wfnet.initial [start]
        (Petri.Marking.singleton bodyEntry) := by
    simpa [p, start, bodyEntry] using loop_start_firingSequence body redo
  have hEmbedded :
      Petri.FiringSequence (target p).wfnet.net
        (Petri.Marking.singleton bodyEntry)
        (ts.map (loopBodyRootTransitionOf body redo))
        (Petri.Marking.singleton bodyExit) := by
    simpa [p, bodyEntry, bodyExit] using
      loopBodyRoot_firingSequence body redo hBody
  have hExit :
      Petri.FiringSequence (target p).wfnet.net
        (Petri.Marking.singleton bodyExit) [exit]
        (target p).wfnet.final := by
    simpa [p, exit, bodyExit] using loop_exit_firingSequence body redo
  simpa [p, start, exit] using
    Petri.FiringSequence.append
      (Petri.FiringSequence.append hStart hEmbedded) hExit

theorem loop_body_once_traceOf
    (body redo : POWL2 Activity)
    (ts : List (target body).wfnet.net.Transition) :
    Petri.LabeledWFNet.traceOf (target (POWL2.loop body redo))
      ([transitionOf (POWL2.loop body redo)
          (Structural.transition [] TransitionKind.loopStart)
          (loop_start_root_mem body redo)] ++
        ts.map (loopBodyRootTransitionOf body redo) ++
        [transitionOf (POWL2.loop body redo)
          (Structural.transition [] TransitionKind.loopExit)
          (loop_exit_root_mem body redo)]) =
      Petri.LabeledWFNet.traceOf (target body) ts := by
  simp [Petri.LabeledWFNet.traceOf_append,
    Petri.LabeledWFNet.traceOf, loop_start_label, loop_exit_label,
    loopBodyRootTransition_traceOf]

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
