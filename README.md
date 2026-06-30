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
  conversions between per-place boundedness and token-sum boundedness.  It
  also proves classical negation forms such as:

  ```lean
  ¬ Bounded N M₀ ↔
    ∀ k, ∃ M, Reachable N M₀ M ∧ ∃ p, k < M p
  ```

  It also proves that a finite list covering all reachable markings implies
  `Bounded N M₀`, and conversely that an unbounded net has no such finite
  reachable cover.  This gives a reusable finite-state route to boundedness.

- Original-vs-short-circuit boundedness transfer.

  If the original net is token-bounded and proper completion holds, then the
  short-circuited net is bounded.  If the short-circuited net is bounded, then
  the original reachable markings are bounded.

- Generic firing-sequence infrastructure.

  Firing sequences can be appended, split over `xs ++ ys`, split over
  `(xs ++ ys) ++ zs`, and are deterministic for a fixed initial marking and
  transition list.  These lemmas support the final finite extraction step in
  the WOFLAN proof.  The semantics layer also proves token-sum growth bounds:
  one firing increases the total token count over a finite place list by at
  most the fired transition's post-weight sum, and a concrete firing sequence
  is bounded by its length times a uniform post-weight bound.  The uniform
  post-weight bound is computed from the net's finite transition enumeration.

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

- Extra-final-cover pumping and unboundedness.

  Several pumping interfaces are formalized and connected:

  - linear pumping at a place,
  - accumulated growth,
  - closed-form growth,
  - closed-form step growth,
  - accumulation plans,
  - pumping above every bound.

  The code proves the concrete closed-form step for every extra-final-cover
  marking.  Therefore an extra-final-cover marking in the original net gives
  unbounded growth in the short-circuited net.  Consequently, bounded
  short-circuit behavior excludes extra-final-cover markings and gives proper
  completion of the original net.

- Reverse WOFLAN direction.

  The library proves:

  ```lean
  Live (shortCircuit W) W.initial →
    Bounded (shortCircuit W) W.initial →
      Sound W
  ```

  This no longer requires an external extra-final-cover exclusion or pumping
  hypothesis.

- Soundness-via-short-circuit theorem family.

  The library proves the exact boundary currently available without the final
  finite/Dickson extraction:

  ```lean
  Sound W ∧ TokenBoundedReachableOriginal W ↔
    Live (shortCircuit W) W.initial ∧
      Bounded (shortCircuit W) W.initial
  ```

  It also proves the classic theorem from one remaining proof obligation:

  ```lean
  WoflanProofObligations W →
    (Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial)
  ```

- Self-cover bridge for original boundedness.

  The remaining boundedness step has been reduced to a finite extraction
  statement over concrete firing sequences.  The library proves:

  - unbounded original reachable markings are equivalent to arbitrarily large
    concrete firing-sequence markings;
  - arbitrarily large concrete markings are equivalent to arbitrarily large
    total token sums over the net's finite place enumeration;
  - arbitrarily large total token sums imply arbitrarily long concrete firing
    sequences, using the finite transition post-weight bound;
  - a comparable cut trace, stated as a factored run with local prefix/loop
    executions whose markings satisfy `M ≤ M'` and `M ≠ M'`, gives the
    comparable-cuts witness used downstream;
  - the public extraction obligation is now a finite threshold: every concrete
    run longer than that threshold must contain a comparable cut trace;
  - behavioral soundness excludes reachable and concrete firing-sequence
    self-covers;
  - therefore the remaining finite extraction implies original boundedness
    under soundness.

### PARTLY DONE

- The main WOFLAN proof is formalized, but still conditionally.

  The code proves soundness-via-short-circuit for WF-nets when the remaining
  finite extraction obligation is supplied as a hypothesis.  It does not yet
  prove that obligation from the finite enumeration data in `Net`.

- The remaining obligation is now a single Dickson-style extraction.

  The public obligation is:

  ```lean
  HasLongRunComparableCutTraceThreshold W
  ```

  Expanded:

  ```lean
  ∃ n,
    ∀ ts Mend,
      FiringSequence W.net W.initial ts Mend →
        n < ts.length →
          ComparableCutTrace W
  ```

  The library now proves the preliminary large-run bridge:

  ```lean
  ArbitrarilyLargeFiringSequenceMarking W →
    ArbitrarilyLongFiringSequences W
  ```

  The remaining unproved part is exactly the finite/Dickson or pigeonhole
  argument that produces such a threshold from the finite place enumeration.

### NOT DONE

- No unconditional classic WOFLAN soundness theorem yet.

  The desired proof target is the standard theorem, in Lean form, that for the
  intended class of WF-nets:

  ```lean
  Sound W ↔
    Live (shortCircuit W) W.initial ∧
      Bounded (shortCircuit W) W.initial
  ```

  The library has conditional versions of this statement, but not yet the
  fully discharged theorem because the finite/Dickson extraction above is not
  yet proved.

- No formal Dickson lemma for finite place markings yet.

  The final missing mathematical ingredient is a theorem that arbitrarily
  large concrete firing-sequence markings contain two comparable cuts in a
  factored run.  The current library has all downstream bridges from that
  statement to the WOFLAN theorem.

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
