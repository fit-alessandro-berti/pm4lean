import Pm4Lean.Models.POWL.Verification
import Pm4Lean.Models.POWL2.Basic

namespace Pm4Lean
namespace ProcessModel
namespace POWL2

variable {Activity : Type u}

theorem sequenceOrder_irreflexive (n : Nat) :
    POWL.IrreflexiveOnRange n (sequenceOrder n) := by
  intro i _ h
  exact Nat.lt_irrefl i h.1

theorem sequenceOrder_transitive (n : Nat) :
    POWL.TransitiveOnRange n (sequenceOrder n) := by
  intro i j k _ _ _ hij hjk
  exact ⟨Nat.lt_trans hij.1 hjk.1, hjk.2⟩

theorem parallelOrder_irreflexive (n : Nat) :
    POWL.IrreflexiveOnRange n parallelOrder := by
  intro _ _ h
  exact h

theorem parallelOrder_transitive (n : Nat) :
    POWL.TransitiveOnRange n parallelOrder := by
  intro _ _ _ _ _ _ h _
  exact False.elim h

theorem wellFormed_iff_toPOWL (p : POWL2 Activity) :
    WellFormed p ↔ POWL.WellFormed (toPOWL p) :=
  Iff.rfl

theorem ofPOWL_wellFormed {p : POWL Activity}
    (h : POWL.WellFormed p) :
    WellFormed (ofPOWL p) :=
  by simpa [WellFormed, toPOWL] using h

theorem sequence_child_wellFormed
    {children : List (POWL2 Activity)}
    (h : WellFormed (sequence children))
    {child : POWL2 Activity} (hChild : child ∈ children) :
    WellFormed child := by
  have hCore :
      POWL.WellFormed
        (POWL.partialOrder (children.map toPOWL)
          (sequenceOrder children.length)) := by
    simpa [WellFormed, toPOWL] using h
  exact
    POWL.partialOrder_child_wellFormed hCore
      (List.mem_map_of_mem (f := toPOWL) hChild)

theorem parallel_child_wellFormed
    {children : List (POWL2 Activity)}
    (h : WellFormed (parallel children))
    {child : POWL2 Activity} (hChild : child ∈ children) :
    WellFormed child := by
  have hCore :
      POWL.WellFormed
        (POWL.partialOrder (children.map toPOWL) parallelOrder) := by
    simpa [WellFormed, toPOWL] using h
  exact
    POWL.partialOrder_child_wellFormed hCore
      (List.mem_map_of_mem (f := toPOWL) hChild)

theorem partialOrder_child_wellFormed
    {children : List (POWL2 Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order))
    {child : POWL2 Activity} (hChild : child ∈ children) :
    WellFormed child := by
  have hCore :
      POWL.WellFormed
        (POWL.partialOrder (children.map toPOWL) order) := by
    simpa [WellFormed, toPOWL] using h
  exact
    POWL.partialOrder_child_wellFormed hCore
      (List.mem_map_of_mem (f := toPOWL) hChild)

end POWL2
end ProcessModel
end Pm4Lean
