import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Definitions

namespace Pm4Lean
namespace Petri

theorem reachableSelfCover_of_firingSequenceSelfCover
    {W : WFNet}
    (hCover : FiringSequenceSelfCover W) :
    ReachableSelfCover W := by
  obtain ⟨_prefix, _loop, M, M', hPrefix, hLoop, hLe, hNe⟩ := hCover
  exact ⟨M, M',
    Reachable.of_firingSequence hPrefix,
    Reachable.of_firingSequence hLoop,
    hLe,
    hNe⟩

theorem firingSequenceSelfCover_of_cutSelfCover
    {W : WFNet}
    (hCover : CutSelfCover W) :
    FiringSequenceSelfCover W := by
  obtain ⟨pref, loop, M, M', hPref, hPrefLoop, hLe, hNe⟩ := hCover
  exact ⟨pref, loop, M, M',
    hPref,
    FiringSequence.between_prefixes hPref hPrefLoop,
    hLe,
    hNe⟩

theorem cutSelfCover_of_factoredRunCutSelfCover
    {W : WFNet}
    (hCover : FactoredRunCutSelfCover W) :
    CutSelfCover W := by
  obtain ⟨pref, loop, _suffix, _Mend, M, M',
    _hRun, hPref, hPrefLoop, hLe, hNe⟩ := hCover
  exact ⟨pref, loop, M, M', hPref, hPrefLoop, hLe, hNe⟩

theorem factoredRunCutSelfCover_of_local
    {W : WFNet}
    (hCover : LocalFactoredRunCutSelfCover W) :
    FactoredRunCutSelfCover W := by
  obtain ⟨pref, loop, suffix, Mend, M, M',
    hRun, hPref, hLoop, hLe, hNe⟩ := hCover
  exact ⟨pref, loop, suffix, Mend, M, M',
    hRun,
    hPref,
    FiringSequence.append hPref hLoop,
    hLe,
    hNe⟩

end Petri
end Pm4Lean
