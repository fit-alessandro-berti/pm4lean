# pm4lean

Lean 4 formalization work around process-mining models, with the current
center of gravity on Petri nets, workflow nets, and WOFLAN-style soundness
arguments.

The WOFLAN proof is still incomplete.  The repository currently keeps the
checked Petri-net infrastructure, the WF-net soundness predicates, and the
conditional WOFLAN theorem boundaries needed for continuing that proof.

## Build

```bash
lake build
```

The Lean version is pinned in `lean-toolchain`.

## Library Shape

- `Pm4Lean.Models.Petri.Basic`: Petri net and marking definitions.
- `Pm4Lean.Models.Petri.Semantics`: enabledness, firing, firing sequences, and
  reachability.
- `Pm4Lean.Models.Petri.Behavior`: boundedness, liveness, and related behavior
  predicates.
- `Pm4Lean.Models.Petri.WFNet`: workflow-net structure, language, easy and
  relaxed soundness, proper completion, and classical soundness.
- `Pm4Lean.Models.Petri.WFNet.WOFLAN`: short-circuit construction, liveness and
  boundedness bridges, and conditional soundness-via-short-circuit theorems.

The non-Petri model files are still present for the broader process-mining
context, but the active proof work is organized around the Petri/WF-net tree.

## WOFLAN Status

Checked pieces include:

- short-circuit construction and basic reachability transfer;
- WF-net behavior predicates such as easy soundness, relaxed soundness, option
  to complete, proper completion, and no-dead-transitions;
- liveness and boundedness interfaces for the short-circuited net;
- the reverse direction from live and bounded short-circuit behavior to WF-net
  soundness;
- conditional theorem families that expose the remaining finite extraction
  obligation explicitly.

The missing part is the final Dickson-style finite extraction argument used to
remove that remaining obligation.

## Development Notes

The Petri and WOFLAN files are intentionally split into small facade modules
and focused proof modules.  Prefer adding new proof content next to the
smallest relevant module, then re-export it from the nearest facade when it is
part of the public interface.
