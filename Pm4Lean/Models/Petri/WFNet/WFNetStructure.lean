import Pm4Lean.Models.Petri.WFNet.InitialFinalMarking

namespace Pm4Lean
namespace Petri

/-- The structural side conditions of a classical workflow net. -/
structure WFNetStructure (W : WFNet) : Prop where
  initial_source : SourcePlace W.net W.i
  final_sink : SinkPlace W.net W.o
  unique_source : ∀ p : W.net.Place, SourcePlace W.net p → p = W.i
  unique_sink : ∀ p : W.net.Place, SinkPlace W.net p → p = W.o
  every_node_on_path : EveryNodeOnPath W.net W.i W.o

/-- A workflow net bundled with its classical structural side conditions. -/
structure StructuredWFNet where
  wfnet : WFNet
  structure_ok : WFNetStructure wfnet

namespace StructuredWFNet

abbrev Marking (W : StructuredWFNet) := W.wfnet.Marking

def initial (W : StructuredWFNet) : W.Marking :=
  W.wfnet.initial

def final (W : StructuredWFNet) : W.Marking :=
  W.wfnet.final

end StructuredWFNet

namespace WFNetStructure

theorem no_incoming_to_initial {W : WFNet} (h : WFNetStructure W) :
    SourcePlace W.net W.i :=
  h.initial_source

theorem no_outgoing_from_final {W : WFNet} (h : WFNetStructure W) :
    SinkPlace W.net W.o :=
  h.final_sink

theorem every_transition_on_start_to_end_path {W : WFNet}
    (h : WFNetStructure W) (t : W.net.Transition) :
    Path W.net (.place W.i) (.transition t) ∧
      Path W.net (.transition t) (.place W.o) :=
  h.every_node_on_path (.transition t)

end WFNetStructure
end Petri
end Pm4Lean
