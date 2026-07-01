import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut
import Pm4Lean.Util.NatListMax

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def NoComparablePrefixCutPredecessorsBounded
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) (k : Nat) : Prop :=
  ∀ sample : PrefixCutSample N M₀ ts Mend,
    sample ∈ samples →
      ¬ HasComparablePrefixCutPredecessor sample →
        ∀ p : N.Place, sample.marking p ≤ k

theorem noComparablePrefixCutPredecessorsBounded_mono
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k k' : Nat}
    (hLe : k ≤ k')
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    NoComparablePrefixCutPredecessorsBounded samples k' := by
  intro sample hSampleMem hNoPredecessor p
  exact Nat.le_trans
    (hBounded sample hSampleMem hNoPredecessor p)
    hLe

theorem noComparablePrefixCutPredecessorsBounded_max_left
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k k' : Nat}
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    NoComparablePrefixCutPredecessorsBounded samples (Nat.max k k') :=
  noComparablePrefixCutPredecessorsBounded_mono
    (Nat.le_max_left k k') hBounded

theorem noComparablePrefixCutPredecessorsBounded_max_right
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k k' : Nat}
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k') :
    NoComparablePrefixCutPredecessorsBounded samples (Nat.max k k') :=
  noComparablePrefixCutPredecessorsBounded_mono
    (Nat.le_max_right k k') hBounded

theorem noComparablePrefixCutPredecessorsBounded_natListMax
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {bounds : List Nat} {k : Nat}
    (hMem : k ∈ bounds)
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    NoComparablePrefixCutPredecessorsBounded samples (NatListMax bounds) :=
  noComparablePrefixCutPredecessorsBounded_mono
    (le_natListMax_of_mem hMem) hBounded

theorem largeSamplesHaveComparablePrefixCutPredecessor_of_bad_bound
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    LargeSamplesHaveComparablePrefixCutPredecessor samples k := by
  intro second hSecondMem hLarge
  exact Classical.byContradiction (fun hNoPredecessor => by
    obtain ⟨p, hLt⟩ := hLarge
    exact Nat.not_lt_of_ge
      (hBounded second hSecondMem hNoPredecessor p)
      hLt)

end FiringSequence
end Petri
end Pm4Lean
