import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Samples

namespace Pm4Lean
namespace Petri

namespace FiringSequence

/-- The initial prefix cut of a concrete run, packaged as a sample. -/
def initialPrefixCutSample
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (hRun : FiringSequence N M₀ ts Mend) :
    PrefixCutSample N M₀ ts Mend where
  pref := []
  marking := M₀
  isCut := ⟨ts, by simp, hRun, FiringSequence.nil M₀⟩

/-- The full prefix cut of a concrete run, packaged as a sample. -/
def fullPrefixCutSample
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (hRun : FiringSequence N M₀ ts Mend) :
    PrefixCutSample N M₀ ts Mend where
  pref := ts
  marking := Mend
  isCut := ⟨[], by simp, hRun, hRun⟩

/-- The two endpoint prefix cuts of a concrete run. -/
def endpointPrefixCutSamples
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (hRun : FiringSequence N M₀ ts Mend) :
    List (PrefixCutSample N M₀ ts Mend) :=
  [initialPrefixCutSample hRun, fullPrefixCutSample hRun]

end FiringSequence
end Petri
end Pm4Lean
