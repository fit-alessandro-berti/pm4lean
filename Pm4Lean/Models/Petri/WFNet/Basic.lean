import Pm4Lean.Models.Petri.Structure.SourceSink

namespace Pm4Lean
namespace Petri

/-- A workflow net is a Petri net with distinguished initial and final places. -/
structure WFNet where
  net : Net
  i : net.Place
  o : net.Place

namespace WFNet

abbrev Marking (W : WFNet) := W.net.Marking

end WFNet
end Petri
end Pm4Lean
