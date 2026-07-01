import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.Core

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

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
