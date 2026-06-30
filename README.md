# pm4lean

Process model properties in Lean 4.

This repository is a Lake project for formalizing process-mining model
families, their behavioral properties, and correctness obligations for
conversions between models.

The current focus of the Petri-net side is the formal proof content behind
WOFLAN-style reasoning for workflow nets: relate behavioral soundness of a
WF-net to liveness and boundedness of its short-circuited net.

## Build

```bash
lake build
```

The project is pinned to Lean `v4.29.1` in `lean-toolchain`.

## Current Library Shape

The Petri/WF-net development currently follows this dependency order:

```text
markings
-> Petri net firing semantics
-> firing sequences and reachability
-> WF-net structure and initial/final markings
-> option to complete / proper completion / no dead transitions
-> easy, relaxed, weak, behavioral, and classical soundness predicates
-> WOFLAN short-circuit construction
-> WOFLAN liveness and boundedness infrastructure
-> conditional soundness-via-short-circuit theorems
```

## WOFLAN Proof Status

This section describes the status of the WOFLAN-related proof development in
the current codebase.  The intended end state is a collection of checked Lean
proofs for the WOFLAN characterization of WF-net soundness.  An executable
checker is not the immediate goal.

"Done" means the theorem or proof layer is already checked by Lean.  "Partly
done" means the library proves a conditional result or has the right formal
interface, but a key premise is still supplied by the caller.  "Not done" means
the proof obligation is not yet discharged in the repository.

### DONE

- Short-circuit construction and structural facts.

  `Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit` defines
  `shortCircuit W`, preserves the original places, embeds each original
  transition, and adds the return transition from the final place `o` to the
  initial place `i`.  The library proves the pre/post behavior of original
  transitions and the return transition, enabledness of the return transition
  at the final marking, and the exact marking produced by firing the return
  transition.

- Reachability transfer for original behavior.

  Original WF-net steps and firing sequences can be embedded into the
  short-circuited net.  No-return short-circuit firing sequences can be
  projected back to original firing sequences.  There are also lemmas extracting
  an original reachability-to-final-cover prefix from a short-circuit path that
  reaches a return-enabled marking.

- Short-circuit reachability under proper completion.

  If the original WF-net has proper completion, then markings reachable in the
  short-circuited net from the initial marking are reachable in the original
  net.  The return transition at the final marking is proved to reach the
  initial marking.

- Boundedness proof vocabulary.

  The library defines `BoundedBy`, `Bounded`, `Safe`,
  `TokenSumBoundedReachable`, and `LinearTokenGrowthAt`, together with basic
  conversions between per-place boundedness and token-sum boundedness.

- Original-vs-short-circuit boundedness transfer.

  If the original net is token-bounded and proper completion holds, then the
  short-circuited net is bounded.  If the short-circuited net is bounded, then
  the original reachable markings are bounded.

- Liveness proof vocabulary and liveness/soundness implications.

  The library defines `LiveTransition` and `Live`.  It proves:

  - soundness of the original WF-net implies liveness of the short-circuited
    net, assuming the existing soundness components;
  - liveness of the short-circuited net plus proper completion gives option to
    complete and no dead transitions for the original WF-net;
  - liveness of the short-circuited net plus proper completion implies
    behavioral soundness of the original WF-net.

- Extra-final-cover formalization.

  The library defines `HasExtraTokensAtFinalCover W M` and proves that such a
  marking has a strictly positive extra remainder somewhere.  It also proves
  that firing the short-circuit return transition from such a marking creates
  reachable markings exceeding the initial marking at some place.

- Conditional pumping-to-unboundedness lemmas.

  Several pumping interfaces are formalized and connected:

  - linear pumping at a place,
  - accumulated growth,
  - closed-form growth,
  - closed-form step growth,
  - accumulation plans,
  - pumping above every bound.

  The code proves that these obligations imply unboundedness of the
  short-circuited net when an extra-final-cover marking exists.

- Conditional soundness-via-short-circuit theorem family.

  The main checked bridge has this shape:

  ```lean
  Sound W ↔
    Live (shortCircuit W) W.initial ∧
      Bounded (shortCircuit W) W.initial
  ```

  under explicit assumptions such as:

  - original reachable markings are bounded, and
  - live-and-bounded short-circuit behavior excludes extra-final-cover
    markings, or a stronger pumping/growth condition that implies this
    exclusion.

### PARTLY DONE

- The main WOFLAN proof is formalized, but only conditionally.

  The code proves soundness-via-short-circuit for WF-nets when the missing
  boundedness/exclusion obligations are supplied as hypotheses.  It does not
  yet prove those obligations from standard WF-net structure alone.

- Proper completion is connected to boundedness, but through an explicit
  extra-token exclusion condition.

  The library proves:

  ```lean
  ProperCompletion W ↔
    ∀ M, ¬ HasExtraTokensAtFinalCover W M
  ```

  and shows that bounded short-circuit behavior gives proper completion when
  `ShortCircuitBoundedExcludesExtraFinalCover W` is available.  The missing
  part is a general proof that live and bounded short-circuit nets exclude
  extra-final-cover markings for the intended class of WF-nets.

- Pumping obligations are represented, not yet proved generally.

  Interfaces such as `ExtraFinalCoverClosedFormGrowth`,
  `ExtraFinalCoverClosedFormStep`, and `ExtraFinalCoverAccumulationPlanAt`
  describe ways to prove that extra-final-cover markings cause unboundedness.
  The library proves the implications between these interfaces, but it does
  not yet prove such plans from arbitrary WF-net structure.

- Boundedness is available as a theorem premise.

  `Bounded` is a logical property over all reachable markings.  The current
  WOFLAN proof bridge can use boundedness once provided, and can move between
  original-net boundedness and short-circuit boundedness under the proved side
  conditions.  What is missing is the proof layer that derives the needed
  boundedness/exclusion facts from the standard WOFLAN hypotheses.

- Liveness is available as a theorem premise and consequence.

  `Live` is a logical property over all reachable markings and transitions.
  The code proves the forward direction from `Sound W` to
  `Live (shortCircuit W) W.initial`, and proves useful consequences of
  short-circuit liveness.  The remaining proof work is not a checker, but a
  stronger unconditional theorem that combines liveness and boundedness into
  soundness without additional ad hoc premises.

### NOT DONE

- No unconditional WOFLAN soundness theorem yet.

  The desired proof target is the standard theorem, in Lean form, that for the
  intended class of WF-nets:

  ```lean
  Sound W ↔
    Live (shortCircuit W) W.initial ∧
      Bounded (shortCircuit W) W.initial
  ```

  The library has conditional versions of this statement, but not yet the
  fully discharged theorem from standard WF-net assumptions.

- No general proof of the extra-final-cover exclusion lemma.

  The library has the conditional theorem family, but the key
  extra-final-cover exclusion/pumping argument is still externalized as a
  hypothesis.

- No general construction of pumping/growth plans.

  The library proves that several pumping/growth formulations imply
  short-circuit unboundedness.  It does not yet prove that every reachable
  extra-final-cover marking in the relevant setting yields one of those
  growth plans.

- No full proof that bounded and live short-circuit nets force proper
  completion of the original WF-net.

  The current proof obtains proper completion from boundedness and liveness
  only after an explicit exclusion/pumping condition is supplied.

- No proof-level diagnostics for unsoundness.

  A proof-oriented version could characterize failure modes such as missing
  option to complete, improper completion, dead transitions, unboundedness, or
  non-liveness.  Those decomposition theorems are not yet developed.

- No use of WOFLAN proofs in conversion soundness proofs yet.

  Conversion modules can state preservation and target-soundness obligations,
  but they do not yet use the WOFLAN theorem family to discharge target
  soundness.

### Out Of Scope For Now

- Executable WOFLAN decision procedures.
- Coverability graph or state-space exploration algorithms.
- Diagnostic result types for a practical checker.

Those may be useful later, but the current README treats WOFLAN as a proof
development, not as an implementation target.

## Module Layout

The main aggregate imports are:

```text
Pm4Lean/
  Models.lean
  Models/
    Language.lean
    Petri.lean
    ProcessTree.lean
    POWL.lean
    BPMN.lean
  Conversion.lean
```

Important Petri/WF-net entry points:

- `Pm4Lean.Models.Petri.Basic.Marking`
- `Pm4Lean.Models.Petri.Basic.Net`
- `Pm4Lean.Models.Petri.Semantics.Reachability`
- `Pm4Lean.Models.Petri.WFNet.WFNetStructure`
- `Pm4Lean.Models.Petri.WFNet.Soundness.Soundness`
- `Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit`
- `Pm4Lean.Models.Petri.WFNet.WOFLAN.Liveness`
- `Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness`
- `Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit`

The WOFLAN modules are split by responsibility:

```text
Pm4Lean/Models/Petri/WFNet/WOFLAN/
  ShortCircuit.lean
  ShortCircuit/
    Basic.lean
    Sequences.lean
    Reachability.lean
    ProperCompletion.lean
  Liveness.lean
  Liveness/
    Basic.lean
    ToBehavior.lean
    FromSound.lean
  Boundedness.lean
  Boundedness/
    Basic.lean
    Original.lean
    ExtraFinalCover.lean
    Growth.lean
    Pumping.lean
    Exclusion.lean
    ProperCompletion.lean
  SoundnessViaShortCircuit.lean
  SoundnessViaShortCircuit/
    Forward.lean
    ToSound.lean
    Iff.lean
```

## Non-WOFLAN Scope

The repository also contains model and conversion infrastructure outside the
WOFLAN path:

- generic trace languages and language equivalence,
- process-tree syntax and trace semantics,
- POWL syntax and trace semantics,
- BPMN syntax, graph-walk trace semantics, and examples,
- conversion correctness predicates,
- a direct process-tree-to-POWL conversion with a preservation theorem,
- an atomic process-tree-to-labeled-WF-net conversion for visible activity
  leaves with a proved language-equivalence theorem.

These pieces are separate from the WOFLAN proof status above.

## Disabling Folders

`Pm4Lean.lean` imports only:

```lean
import Pm4Lean.Models
import Pm4Lean.Conversion
```

Comment out `import Pm4Lean.Conversion` to skip all conversion files.

To disable one model family, comment out its aggregate import in
`Pm4Lean/Models.lean`, for example:

```lean
-- import Pm4Lean.Models.BPMN
```

If a conversion depends on that family, also comment out the corresponding
conversion import in `Pm4Lean/Conversion.lean`, for example:

```lean
-- import Pm4Lean.Conversion.ProcessTreeToBPMN
```
