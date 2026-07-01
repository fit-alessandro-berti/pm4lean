import Pm4Lean.Models.Petri.WFNet.Language

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem singleton_of_pre_post
    {N : Net} (source sink : N.Place) (t : N.Transition)
    (hPre : N.pre t = Marking.singleton source)
    (hPost : N.post t = Marking.singleton sink) :
    FiringSequence N (Marking.singleton source) [t]
      (Marking.singleton sink) := by
  refine FiringSequence.cons ?_ ?_
  · rw [Enabled, hPre]
    exact Marking.le_refl _
  · have hFire :
        fire N (Marking.singleton source) t = Marking.singleton sink := by
      apply Marking.ext
      intro p
      rw [fire_apply]
      rw [hPre, hPost]
      simp [Marking.singleton]
    rw [hFire]
    exact FiringSequence.nil (Marking.singleton sink)

end FiringSequence

namespace WFNet

theorem firingSequence_singleton_of_pre_post
    (W : WFNet) (t : W.net.Transition)
    (hPre : W.net.pre t = Marking.singleton W.i)
    (hPost : W.net.post t = Marking.singleton W.o) :
    FiringSequence W.net W.initial [t] W.final := by
  simpa [initial, final] using
    FiringSequence.singleton_of_pre_post W.i W.o t hPre hPost

end WFNet

namespace LabeledWFNet

variable {Activity : Type u}

theorem operationalLanguage_of_singleton_pre_post
    (LW : LabeledWFNet Activity) (t : LW.wfnet.net.Transition)
    (hPre : LW.wfnet.net.pre t = Marking.singleton LW.wfnet.i)
    (hPost : LW.wfnet.net.post t = Marking.singleton LW.wfnet.o) :
    operationalLanguage LW (traceOf LW [t]) :=
  language_of_firingSequence LW
    (WFNet.firingSequence_singleton_of_pre_post LW.wfnet t hPre hPost)

end LabeledWFNet

end Petri
end Pm4Lean
