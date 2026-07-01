import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.Atomic

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

theorem ofPOWL_tau_atom_root_mem :
    Structural.transition [] TransitionKind.atom ∈
      Structural.rawTransitionsRoot
        (POWL2.ofPOWL (POWL.tau : POWL Activity)) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize, Structural.ofPOWL] using
    (tau_atom_root_mem : Structural.transition [] TransitionKind.atom ∈
      Structural.rawTransitionsRoot (POWL2.tau : POWL2 Activity))

theorem ofPOWL_activity_atom_root_mem (a : Activity) :
    Structural.transition [] TransitionKind.atom ∈
      Structural.rawTransitionsRoot (POWL2.ofPOWL (POWL.activity a)) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize, Structural.ofPOWL] using
    activity_atom_root_mem a

theorem ofPOWL_tau_atom_pre_singleton :
    let p := POWL2.ofPOWL (POWL.tau : POWL Activity)
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      ofPOWL_tau_atom_root_mem
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.ofPOWL, Structural.rawPre, Structural.rawMark,
    Structural.entry, Structural.transition, Petri.Marking.singleton]

theorem ofPOWL_tau_atom_post_singleton :
    let p := POWL2.ofPOWL (POWL.tau : POWL Activity)
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      ofPOWL_tau_atom_root_mem
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.ofPOWL, Structural.rawPost, Structural.rawMark,
    Structural.exit, Structural.transition, Petri.Marking.singleton]

theorem ofPOWL_tau_operational_epsilon :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.ofPOWL (POWL.tau : POWL Activity))) [] := by
  let p := POWL2.ofPOWL (POWL.tau : POWL Activity)
  let t := transitionOf p (Structural.transition [] TransitionKind.atom)
    ofPOWL_tau_atom_root_mem
  have hRun :
      Petri.LabeledWFNet.operationalLanguage (target p)
        (Petri.LabeledWFNet.traceOf (target p) [t]) :=
    Petri.LabeledWFNet.operationalLanguage_of_singleton_pre_post
      (target p) t ofPOWL_tau_atom_pre_singleton
      ofPOWL_tau_atom_post_singleton
  simpa [p, t, Petri.LabeledWFNet.traceOf, transitionOf, target,
    Structural.target, Structural.compiled, Structural.normalize,
    Structural.ofPOWL, Structural.rawLabel, Structural.childAt,
    Structural.transition] using hRun

theorem ofPOWL_tau_language_realized_by_firing
    {σ : Trace Activity}
    (h : POWL2.language (POWL2.ofPOWL (POWL.tau : POWL Activity)) σ) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.ofPOWL (POWL.tau : POWL Activity))) σ := by
  rw [POWL2.ofPOWL_language] at h
  simp [POWL.language, Language.epsilon] at h
  subst h
  exact ofPOWL_tau_operational_epsilon

theorem ofPOWL_activity_atom_pre_singleton (a : Activity) :
    let p := POWL2.ofPOWL (POWL.activity a)
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      (ofPOWL_activity_atom_root_mem a)
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.ofPOWL, Structural.rawPre, Structural.rawMark,
    Structural.entry, Structural.transition, Petri.Marking.singleton]

theorem ofPOWL_activity_atom_post_singleton (a : Activity) :
    let p := POWL2.ofPOWL (POWL.activity a)
    let t := transitionOf p (Structural.transition [] TransitionKind.atom)
      (ofPOWL_activity_atom_root_mem a)
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.ofPOWL, Structural.rawPost, Structural.rawMark,
    Structural.exit, Structural.transition, Petri.Marking.singleton]

theorem ofPOWL_activity_operational_singleton (a : Activity) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.ofPOWL (POWL.activity a))) [a] := by
  let p := POWL2.ofPOWL (POWL.activity a)
  let t := transitionOf p (Structural.transition [] TransitionKind.atom)
    (ofPOWL_activity_atom_root_mem a)
  have hRun :
      Petri.LabeledWFNet.operationalLanguage (target p)
        (Petri.LabeledWFNet.traceOf (target p) [t]) :=
    Petri.LabeledWFNet.operationalLanguage_of_singleton_pre_post
      (target p) t (ofPOWL_activity_atom_pre_singleton a)
      (ofPOWL_activity_atom_post_singleton a)
  simpa [p, t, Petri.LabeledWFNet.traceOf, transitionOf, target,
    Structural.target, Structural.compiled, Structural.normalize,
    Structural.ofPOWL, Structural.rawLabel, Structural.childAt,
    Structural.transition] using hRun

theorem ofPOWL_activity_language_realized_by_firing
    (a : Activity) {σ : Trace Activity}
    (h : POWL2.language (POWL2.ofPOWL (POWL.activity a)) σ) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.ofPOWL (POWL.activity a))) σ := by
  rw [POWL2.ofPOWL_language] at h
  simp [POWL.language, Language.singleton] at h
  subst h
  exact ofPOWL_activity_operational_singleton a

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
