# pm4lean

Process model properties in Lean 4.

This repository is a Lake project for formalizing process-mining model
families, their behavioral properties, and correctness obligations for
conversions between models.

## Build

```bash
lake build
```

The project is currently pinned to Lean `v4.29.1` in `lean-toolchain`.

## Current Library Shape

The initial development follows the dependency order in the project notes:

```text
markings
-> Petri net firing semantics
-> reachability
-> WF-net structure
-> option to complete / proper completion / no dead transitions
-> easy, relaxed, weak, and classical soundness predicates
-> WOFLAN-oriented liveness, boundedness, and short-circuit statement shape
```

## Module Layout

The code is organized so model families and conversions can be compiled
independently.

```text
Pm4Lean/
  Models.lean                 aggregate imports for model families
  Models/
    Language.lean             shared trace-language definitions
    Petri.lean                aggregate imports for Petri nets/WF-nets/WOFLAN
    Petri/...
    ProcessTree.lean          aggregate imports for process trees
    ProcessTree/Basic.lean
    ProcessTree/Semantics.lean
    POWL.lean                 aggregate imports for POWL
    POWL/Basic.lean
    POWL/Semantics.lean
    BPMN.lean                 aggregate imports for BPMN
    BPMN/Basic.lean
    BPMN/Semantics.lean
    BPMN/Examples.lean
  Conversion.lean             aggregate imports for conversions
  Conversion/
    Basic.lean
    ProcessTree.lean
    ProcessTreeToPOWL.lean
    ProcessTreeToBPMN.lean
    ProcessTreeToWFNet.lean
    ProcessTreeToWFNet/Atomic.lean
```

Important entry points:

- `Pm4Lean.Models.Petri.Basic.Marking`
- `Pm4Lean.Models.Petri.Basic.Net`
- `Pm4Lean.Models.Petri.Semantics.Reachability`
- `Pm4Lean.Models.Petri.WFNet.WFNetStructure`
- `Pm4Lean.Models.Petri.WFNet.Soundness.Soundness`
- `Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit`
- `Pm4Lean.Models.ProcessTree.Basic`
- `Pm4Lean.Models.POWL.Basic`
- `Pm4Lean.Models.BPMN.Basic`
- `Pm4Lean.Conversion.Basic`

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

## Scope Implemented So Far

The first checked-in foundation includes:

- finite Petri nets represented by explicit finite place and transition lists,
- markings as `Place -> Nat`,
- enabledness, firing, one-step execution, firing sequences, and reachability,
- extraction of concrete firing sequences from reachability proofs,
- graph nodes, adjacency, paths, source/sink places, and WF-net structure,
- WF-net initial/final markings,
- labeled WF-net trace semantics, with silent transitions and visible
  activity labels over firing sequences,
- a one-transition labeled WF-net example with a proved singleton-trace
  acceptance theorem,
- option to complete, proper completion, no-dead-transition, easy soundness,
  relaxed soundness, weak soundness, and classical soundness predicates,
- projection and constructor lemmas for soundness,
- sink-place token monotonicity over steps and reachability,
- the provable core of the option-to-complete/proper-completion argument:
  if the final place is a sink, any reachable marking covering the final
  marking cannot overmark the final place,
- the full option-to-complete-to-proper-completion theorem under an explicit
  no-extra-tokens-at-final-cover invariant,
- an equivalence between no-dead transitions and enabledness after some
  concrete firing sequence,
- a concrete short-circuit construction for WF-nets that preserves places,
  embeds original transitions, and adds one return transition from `o` to `i`,
- basic short-circuit lemmas for original-transition behavior and the return
  transition fired at the final marking,
- generic trace languages and language equivalence,
- reusable language combinators for epsilon, singleton activities, choice,
  sequence, shuffle-based parallelism, and finite repetition,
- concrete process-tree trace semantics, including tau, activity, sequence,
  exclusive choice, parallel interleaving, and loop behavior,
- semantic sanity lemmas for tau sequencing and process-tree loop execution,
- concrete POWL trace semantics for tau, activity, xor, loop, two-child
  sequence/parallel partial orders, and general multi-child interleavings,
- concrete BPMN graph-walk trace semantics, where entering task nodes emits
  visible activities and events/gateways emit epsilon,
- a single-task BPMN constructor with a proved task-trace inclusion theorem,
- a generic conversion predicate for trace-language preservation,
- process-tree-specific conversion correctness predicates targeting WF-nets,
  BPMN, and POWL,
- a direct process-tree-to-POWL conversion with a proved trace-language
  preservation theorem,
- a WF-net conversion proof obligation combining preservation and target
  soundness,
- a labeled-WF-net conversion proof obligation combining concrete trace
  preservation and soundness of the underlying WF-net,
- an atomic process-tree-to-labeled-WF-net conversion artifact for visible
  activity leaves, with a proved language-equivalence theorem.

## Next Proof Targets

The next useful proof layer is the remaining WOFLAN-oriented infrastructure:

- transition occurrence lemmas for relaxed soundness,
- structured process-tree-to-labeled-WF-net conversions with preservation and
  soundness proofs beyond atomic activity leaves,
- richer BPMN semantics for gateway synchronization, branching constraints, and
  structured fragments,
- a refined POWL semantics for precedence-constrained interleavings of
  arbitrary-size partial-order nodes,
- boundedness and safeness lemmas for marked nets,
- liveness lemmas for short-circuited workflow nets,
- stronger proper-completion theorems under standard WF-net invariants that
  actually rule out extra tokens outside the final place.

The current `SoundnessViaShortCircuitStatement` is now stated directly over the
concrete `shortCircuit W` net; proving that statement remains a long-term
WOFLAN target.
