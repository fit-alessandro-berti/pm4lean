import Pm4Lean.Conversion.ProcessTree
import Pm4Lean.Models.POWL.Semantics

namespace Pm4Lean
namespace ProcessModel

/-- A behavior-preserving conversion from process trees to POWL models. -/
def PreservesProcessTreeToPOWL
    {Activity : Type u}
    (powlLanguage : POWL Activity → Language Activity)
    (C : Conversion (ProcessTree Activity) (POWL Activity)) : Prop :=
  PreservesProcessTreeLanguage powlLanguage C

namespace ProcessTreeToPOWL

/--
The direct syntax translation from process trees into the overlapping POWL
constructors.  Sequence and binary parallelism are represented as two-child
partial-order nodes; the order relation enforces left-before-right for sequence
and has no edges for parallelism.
-/
def map {Activity : Type u} : ProcessTree Activity → POWL Activity
  | ProcessTree.tau => POWL.tau
  | ProcessTree.activity a => POWL.activity a
  | ProcessTree.sequence l r =>
      POWL.partialOrder [map l, map r] (fun i j => i = 0 ∧ j = 1)
  | ProcessTree.exclusiveChoice l r => POWL.xor (map l) (map r)
  | ProcessTree.parallel l r =>
      POWL.partialOrder [map l, map r] (fun _ _ => False)
  | ProcessTree.loop body redo => POWL.loop (map body) (map redo)

/-- The direct process-tree-to-POWL conversion. -/
def conversion {Activity : Type u} :
    Conversion (ProcessTree Activity) (POWL Activity) :=
  ⟨map⟩

theorem preserves_language {Activity : Type u} :
    PreservesProcessTreeToPOWL (Activity := Activity)
      POWL.language conversion := by
  intro T
  induction T with
  | tau =>
      simp [ProcessTree.language, POWL.language, conversion, map,
        Language.equivalent_refl]
  | activity a =>
      simp [ProcessTree.language, POWL.language, conversion, map,
        Language.equivalent_refl]
  | sequence l r ihL ihR =>
      simpa [PreservesProcessTreeLanguage, PreservesLanguage,
        ProcessTree.language, POWL.partialOrder_pair_sequence_language,
        conversion, map] using
        (Language.seq_congr ihL ihR)
  | exclusiveChoice l r ihL ihR =>
      simpa [PreservesProcessTreeLanguage, PreservesLanguage,
        ProcessTree.language, POWL.language, conversion, map] using
        (Language.union_congr ihL ihR)
  | parallel l r ihL ihR =>
      simpa [PreservesProcessTreeLanguage, PreservesLanguage,
        ProcessTree.language, POWL.partialOrder_pair_parallel_language,
        conversion, map] using
        (Language.parallel_congr ihL ihR)
  | loop body redo ihBody ihRedo =>
      simpa [PreservesProcessTreeLanguage, PreservesLanguage,
        ProcessTree.language, POWL.language, conversion, map] using
        (Language.seq_congr ihBody
          (Language.star_congr (Language.seq_congr ihRedo ihBody)))

end ProcessTreeToPOWL
end ProcessModel
end Pm4Lean
