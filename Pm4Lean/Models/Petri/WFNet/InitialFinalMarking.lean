import Pm4Lean.Models.Petri.WFNet.Basic

namespace Pm4Lean
namespace Petri
namespace WFNet

/-- The standard WF-net initial marking: one token in the input place. -/
def initial (W : WFNet) : W.Marking :=
  Marking.singleton W.i

/-- The standard WF-net final marking: one token in the output place. -/
def final (W : WFNet) : W.Marking :=
  Marking.singleton W.o

theorem initial_apply_self (W : WFNet) :
    W.initial W.i = 1 :=
  Marking.singleton_self W.i

theorem final_apply_self (W : WFNet) :
    W.final W.o = 1 :=
  Marking.singleton_self W.o

end WFNet
end Petri
end Pm4Lean
