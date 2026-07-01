import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Definitions.Covers.Cut

namespace Pm4Lean
namespace Petri

/--
A concrete run with two comparable cuts.  This names the factored-run cut
self-cover shape as the direct target expected from a finite/Dickson
extraction over cuts of one long sequence.
-/
abbrev ComparableCutsInRun (W : WFNet) : Prop :=
  FactoredRunCutSelfCover W

end Petri
end Pm4Lean
