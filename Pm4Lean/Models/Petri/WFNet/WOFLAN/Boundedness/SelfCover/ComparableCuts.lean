import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Sequence

namespace Pm4Lean
namespace Petri

theorem factoredRunCutSelfCover_of_comparableCutsInRun
    {W : WFNet}
    (hCover : ComparableCutsInRun W) :
    FactoredRunCutSelfCover W :=
  hCover

theorem localFactoredRunCutSelfCover_of_comparableCutsInRun
    {W : WFNet}
    (hCover : ComparableCutsInRun W) :
    LocalFactoredRunCutSelfCover W := by
  obtain ⟨pref, loop, suffix, Mend, M, M',
    hRun, hPref, hPrefLoop, hLe, hNe⟩ := hCover
  obtain ⟨Mcut, hPrefCut, hLoop⟩ :=
    FiringSequence.split_append hPrefLoop
  have hMcut : Mcut = M :=
    FiringSequence.deterministic hPrefCut hPref
  exact ⟨pref, loop, suffix, Mend, M, M',
    hRun,
    hPref,
    by simpa [hMcut] using hLoop,
    hLe,
    hNe⟩

theorem largeSequencesProduceFactoredRunCutSelfCover_of_comparableCuts
    {W : WFNet}
    (hExtract : LargeSequencesProduceComparableCutsInRun W) :
    LargeSequencesProduceFactoredRunCutSelfCover W := by
  intro hLarge
  exact factoredRunCutSelfCover_of_comparableCutsInRun (hExtract hLarge)

theorem largeSequencesProduceLocalFactoredRunCutSelfCover_of_comparableCuts
    {W : WFNet}
    (hExtract : LargeSequencesProduceComparableCutsInRun W) :
    LargeSequencesProduceLocalFactoredRunCutSelfCover W := by
  intro hLarge
  exact localFactoredRunCutSelfCover_of_comparableCutsInRun (hExtract hLarge)

end Petri
end Pm4Lean
