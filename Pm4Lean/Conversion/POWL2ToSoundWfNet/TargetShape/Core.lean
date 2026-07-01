import Pm4Lean.Conversion.POWL2ToSoundWfNet.Target
import Pm4Lean.Conversion.POWL2ToSoundWfNet.Structural.Shape

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

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
