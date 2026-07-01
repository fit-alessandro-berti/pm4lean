import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.Core
import Pm4Lean.Models.Petri.WFNet.Behavior.OneStep

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

theorem tau_atom_root_mem :
    Structural.transition [] TransitionKind.atom ∈
      Structural.rawTransitionsRoot (POWL2.tau : POWL2 Activity) := by
  simp [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize, Structural.rawTransitions, Structural.transition]

theorem activity_atom_root_mem (a : Activity) :
    Structural.transition [] TransitionKind.atom ∈
      Structural.rawTransitionsRoot (POWL2.activity a) := by
  simp [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize, Structural.rawTransitions, Structural.transition]

theorem tau_atom_consumes_target_entry :
    let p := (POWL2.tau : POWL2 Activity)
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      tau_atom_root_mem
    let q := placeOf p (Structural.entry [])
      (Structural.source_mem p)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawMark, Structural.entry,
    Structural.transition]

theorem tau_atom_produces_target_exit :
    let p := (POWL2.tau : POWL2 Activity)
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      tau_atom_root_mem
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawMark, Structural.exit,
    Structural.transition]

theorem tau_atom_pre_singleton :
    let p := (POWL2.tau : POWL2 Activity)
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      tau_atom_root_mem
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawMark, Structural.entry,
    Structural.transition, Petri.Marking.singleton]

theorem tau_atom_post_singleton :
    let p := (POWL2.tau : POWL2 Activity)
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      tau_atom_root_mem
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawMark, Structural.exit,
    Structural.transition, Petri.Marking.singleton]

theorem tau_operational_epsilon :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.tau : POWL2 Activity)) [] := by
  let p := (POWL2.tau : POWL2 Activity)
  let t := transitionOf p (Structural.transition [] TransitionKind.atom)
    tau_atom_root_mem
  have hRun :
      Petri.LabeledWFNet.operationalLanguage (target p)
        (Petri.LabeledWFNet.traceOf (target p) [t]) :=
    Petri.LabeledWFNet.operationalLanguage_of_singleton_pre_post
      (target p) t tau_atom_pre_singleton tau_atom_post_singleton
  simpa [p, t, Petri.LabeledWFNet.traceOf, transitionOf, target,
    Structural.target, Structural.compiled, Structural.normalize,
    Structural.rawLabel, Structural.childAt, Structural.transition] using hRun

theorem tau_language_realized_by_firing
    {σ : Trace Activity}
    (h : POWL2.language (POWL2.tau : POWL2 Activity) σ) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.tau : POWL2 Activity)) σ := by
  simp [POWL2.language, Language.epsilon] at h
  subst h
  exact tau_operational_epsilon

theorem activity_atom_label (a : Activity) :
    let p := POWL2.activity a
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      (activity_atom_root_mem a)
    (target p).label t = some a := by
  simp [transitionOf, target, Structural.target, Structural.compiled,
    Structural.normalize, Structural.rawLabel, Structural.childAt,
    Structural.transition]

theorem activity_atom_pre_singleton (a : Activity) :
    let p := POWL2.activity a
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      (activity_atom_root_mem a)
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawMark, Structural.entry,
    Structural.transition, Petri.Marking.singleton]

theorem activity_atom_post_singleton (a : Activity) :
    let p := POWL2.activity a
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      (activity_atom_root_mem a)
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawMark, Structural.exit,
    Structural.transition, Petri.Marking.singleton]

theorem activity_operational_singleton (a : Activity) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.activity a)) [a] := by
  let p := POWL2.activity a
  let t := transitionOf p (Structural.transition [] TransitionKind.atom)
    (activity_atom_root_mem a)
  have hRun :
      Petri.LabeledWFNet.operationalLanguage (target p)
        (Petri.LabeledWFNet.traceOf (target p) [t]) :=
    Petri.LabeledWFNet.operationalLanguage_of_singleton_pre_post
      (target p) t (activity_atom_pre_singleton a)
        (activity_atom_post_singleton a)
  simpa [p, t, Petri.LabeledWFNet.traceOf, transitionOf, target,
    Structural.target, Structural.compiled, Structural.normalize,
    Structural.rawLabel, Structural.childAt, Structural.transition] using hRun

theorem activity_language_realized_by_firing
    (a : Activity) {σ : Trace Activity}
    (h : POWL2.language (POWL2.activity a) σ) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.activity a)) σ := by
  simp [POWL2.language, Language.singleton] at h
  subst h
  exact activity_operational_singleton a

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
