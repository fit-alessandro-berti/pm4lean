import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.Core
import Pm4Lean.Models.Petri.WFNet.Behavior.OneStep

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

theorem choiceGraph_empty_root_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (h : graph.empty) :
    Structural.transition [] TransitionKind.choiceEmpty ∈
      Structural.rawTransitionsRoot (POWL2.choiceGraph children graph) := by
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.choiceGraph_empty_transition_mem
      (children.map Structural.normalize) graph [] h

theorem choiceGraph_child_entry_root_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hRange : i < children.length) :
    Structural.childEntry [] i ∈
      Structural.rawPlacesRoot (POWL2.choiceGraph children graph) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  have hChild :
      Structural.childEntry [] i ∈
        Structural.rawPlacesChildren (children.map Structural.normalize) [] 0 :=
    Structural.rawChildEntry_mem (children.map Structural.normalize) [] hRange'
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize, Structural.rawPlaces] using Or.inr (Or.inr hChild)

theorem choiceGraph_child_exit_root_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hRange : i < children.length) :
    Structural.childExit [] i ∈
      Structural.rawPlacesRoot (POWL2.choiceGraph children graph) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  have hChild :
      Structural.childExit [] i ∈
        Structural.rawPlacesChildren (children.map Structural.normalize) [] 0 :=
    Structural.rawChildExit_mem (children.map Structural.normalize) [] hRange'
  simpa [Structural.rawPlacesRoot, Structural.compiled,
    Structural.normalize, Structural.rawPlaces] using Or.inr (Or.inr hChild)

theorem choiceGraph_has_empty_transition
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (h : graph.empty) :
    ∃ t : (target (POWL2.choiceGraph children graph)).wfnet.net.Transition,
      t.1 = Structural.transition [] TransitionKind.choiceEmpty := by
  refine ⟨transitionOf (POWL2.choiceGraph children graph)
    (Structural.transition [] TransitionKind.choiceEmpty)
    (choiceGraph_empty_root_mem children graph h), rfl⟩

theorem choiceGraph_empty_consumes_target_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (h : graph.empty) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
      (choiceGraph_empty_root_mem children graph h)
    let q := placeOf p (Structural.entry [])
      (Structural.source_mem p)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.choiceGraph_empty_consumes_entry]

theorem choiceGraph_empty_produces_target_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (h : graph.empty) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
      (choiceGraph_empty_root_mem children graph h)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.choiceGraph_empty_produces_exit]

theorem choiceGraph_empty_pre_singleton
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (h : graph.empty) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
      (choiceGraph_empty_root_mem children graph h)
    (target p).wfnet.net.pre t =
      Petri.Marking.singleton (target p).wfnet.i := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPre, Structural.rawPreFor, Structural.rawMark, Structural.entry,
    Structural.transition, Petri.Marking.singleton]

theorem choiceGraph_empty_post_singleton
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (h : graph.empty) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
      (choiceGraph_empty_root_mem children graph h)
    (target p).wfnet.net.post t =
      Petri.Marking.singleton (target p).wfnet.o := by
  apply Petri.Marking.ext
  intro q
  cases q
  simp [transitionOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.rawPost, Structural.rawPostFor, Structural.rawMark, Structural.exit,
    Structural.transition, Petri.Marking.singleton]

theorem choiceGraph_empty_operational_epsilon
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (h : graph.empty) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.choiceGraph children graph)) [] := by
  let p := POWL2.choiceGraph children graph
  let t := transitionOf p (Structural.transition [] TransitionKind.choiceEmpty)
    (choiceGraph_empty_root_mem children graph h)
  have hRun :
      Petri.LabeledWFNet.operationalLanguage (target p)
        (Petri.LabeledWFNet.traceOf (target p) [t]) :=
    Petri.LabeledWFNet.operationalLanguage_of_singleton_pre_post
      (target p) t
      (choiceGraph_empty_pre_singleton children graph h)
      (choiceGraph_empty_post_singleton children graph h)
  simpa [p, t, Petri.LabeledWFNet.traceOf, transitionOf, target,
    Structural.target, Structural.compiled, Structural.normalize,
    Structural.rawLabel, Structural.childAt, Structural.transition] using hRun

theorem choiceGraph_empty_language_epsilon
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (h : graph.empty) :
    POWL2.language (POWL2.choiceGraph children graph) [] := by
  simp [POWL2.language, POWL2.choiceGraphLanguage]
  exact ⟨[], POWL2.ChoicePath.empty h, rfl⟩

theorem choiceGraph_empty_language_realized_by_firing
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    (h : graph.empty)
    (_hLang : POWL2.language (POWL2.choiceGraph children graph) []) :
    Petri.LabeledWFNet.operationalLanguage
      (target (POWL2.choiceGraph children graph)) [] :=
  choiceGraph_empty_operational_epsilon children graph h

theorem choiceGraph_start_root_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hStart : graph.start i) (hRange : i < children.length) :
    Structural.transition [] (TransitionKind.choiceStart i) ∈
      Structural.rawTransitionsRoot (POWL2.choiceGraph children graph) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.choiceGraph_start_transition_mem
      (children.map Structural.normalize) graph [] hStart hRange'

theorem choiceGraph_has_start_transition
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hStart : graph.start i) (hRange : i < children.length) :
    ∃ t : (target (POWL2.choiceGraph children graph)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.choiceStart i) := by
  refine ⟨transitionOf (POWL2.choiceGraph children graph)
    (Structural.transition [] (TransitionKind.choiceStart i))
    (choiceGraph_start_root_mem children graph hStart hRange), rfl⟩

theorem choiceGraph_start_consumes_target_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hStart : graph.start i) (hRange : i < children.length) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceStart i))
      (choiceGraph_start_root_mem children graph hStart hRange)
    let q := placeOf p (Structural.entry [])
      (Structural.source_mem p)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.choiceGraph_start_consumes_entry]

theorem choiceGraph_start_produces_target_child_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hStart : graph.start i) (hRange : i < children.length) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceStart i))
      (choiceGraph_start_root_mem children graph hStart hRange)
    let q := placeOf p (Structural.childEntry [] i)
      (choiceGraph_child_entry_root_mem children graph hRange)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.choiceGraph_start_produces_child_entry]

theorem choiceGraph_edge_root_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i j : Nat} (hEdge : graph.edge i j)
    (hI : i < children.length) (hJ : j < children.length) :
    Structural.transition [] (TransitionKind.choiceEdge i j) ∈
      Structural.rawTransitionsRoot (POWL2.choiceGraph children graph) := by
  have hI' : i < (children.map Structural.normalize).length := by
    simpa using hI
  have hJ' : j < (children.map Structural.normalize).length := by
    simpa using hJ
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.choiceGraph_edge_transition_mem
      (children.map Structural.normalize) graph [] hEdge hI' hJ'

theorem choiceGraph_has_edge_transition
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i j : Nat} (hEdge : graph.edge i j)
    (hI : i < children.length) (hJ : j < children.length) :
    ∃ t : (target (POWL2.choiceGraph children graph)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.choiceEdge i j) := by
  refine ⟨transitionOf (POWL2.choiceGraph children graph)
    (Structural.transition [] (TransitionKind.choiceEdge i j))
    (choiceGraph_edge_root_mem children graph hEdge hI hJ), rfl⟩

theorem choiceGraph_edge_consumes_target_source_child_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i j : Nat} (hEdge : graph.edge i j)
    (hI : i < children.length) (hJ : j < children.length) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceEdge i j))
      (choiceGraph_edge_root_mem children graph hEdge hI hJ)
    let q := placeOf p (Structural.childExit [] i)
      (choiceGraph_child_exit_root_mem children graph hI)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.choiceGraph_edge_consumes_source_child_exit]

theorem choiceGraph_edge_produces_target_target_child_entry
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i j : Nat} (hEdge : graph.edge i j)
    (hI : i < children.length) (hJ : j < children.length) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceEdge i j))
      (choiceGraph_edge_root_mem children graph hEdge hI hJ)
    let q := placeOf p (Structural.childEntry [] j)
      (choiceGraph_child_entry_root_mem children graph hJ)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.choiceGraph_edge_produces_target_child_entry]

theorem choiceGraph_end_root_mem
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hFinish : graph.finish i) (hRange : i < children.length) :
    Structural.transition [] (TransitionKind.choiceEnd i) ∈
      Structural.rawTransitionsRoot (POWL2.choiceGraph children graph) := by
  have hRange' : i < (children.map Structural.normalize).length := by
    simpa using hRange
  simpa [Structural.rawTransitionsRoot, Structural.compiled,
    Structural.normalize] using
    Structural.choiceGraph_end_transition_mem
      (children.map Structural.normalize) graph [] hFinish hRange'

theorem choiceGraph_has_end_transition
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hFinish : graph.finish i) (hRange : i < children.length) :
    ∃ t : (target (POWL2.choiceGraph children graph)).wfnet.net.Transition,
      t.1 = Structural.transition [] (TransitionKind.choiceEnd i) := by
  refine ⟨transitionOf (POWL2.choiceGraph children graph)
    (Structural.transition [] (TransitionKind.choiceEnd i))
    (choiceGraph_end_root_mem children graph hFinish hRange), rfl⟩

theorem choiceGraph_end_consumes_target_child_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hFinish : graph.finish i) (hRange : i < children.length) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceEnd i))
      (choiceGraph_end_root_mem children graph hFinish hRange)
    let q := placeOf p (Structural.childExit [] i)
      (choiceGraph_child_exit_root_mem children graph hRange)
    (target p).wfnet.net.pre t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.choiceGraph_end_consumes_child_exit]

theorem choiceGraph_end_produces_target_exit
    (children : List (POWL2 Activity)) (graph : POWL2ChoiceGraph)
    {i : Nat} (hFinish : graph.finish i) (hRange : i < children.length) :
    let p := POWL2.choiceGraph children graph
    let t := transitionOf p (Structural.transition [] (TransitionKind.choiceEnd i))
      (choiceGraph_end_root_mem children graph hFinish hRange)
    let q := placeOf p (Structural.exit [])
      (Structural.sink_mem p)
    (target p).wfnet.net.post t q = 1 := by
  simp [transitionOf, placeOf, target, Structural.target, Structural.wfnet,
    Structural.net, Structural.compiled, Structural.normalize,
    Structural.choiceGraph_end_produces_exit]

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
