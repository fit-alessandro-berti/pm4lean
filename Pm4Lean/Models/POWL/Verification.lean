import Pm4Lean.Models.POWL.Basic

namespace Pm4Lean
namespace ProcessModel
namespace POWL

variable {Activity : Type u}

theorem xor_left_wellFormed {l r : POWL Activity}
    (h : WellFormed (xor l r)) :
    WellFormed l := by
  have h' : WellFormed l ∧ WellFormed r := by
    simpa [WellFormed] using h
  exact h'.1

theorem xor_right_wellFormed {l r : POWL Activity}
    (h : WellFormed (xor l r)) :
    WellFormed r := by
  have h' : WellFormed l ∧ WellFormed r := by
    simpa [WellFormed] using h
  exact h'.2

theorem loop_body_wellFormed {body redo : POWL Activity}
    (h : WellFormed (loop body redo)) :
    WellFormed body := by
  have h' : WellFormed body ∧ WellFormed redo := by
    simpa [WellFormed] using h
  exact h'.1

theorem loop_redo_wellFormed {body redo : POWL Activity}
    (h : WellFormed (loop body redo)) :
    WellFormed redo := by
  have h' : WellFormed body ∧ WellFormed redo := by
    simpa [WellFormed] using h
  exact h'.2

theorem partialOrder_child_wellFormed
    {children : List (POWL Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order))
    {child : POWL Activity} (hChild : child ∈ children) :
    WellFormed child := by
  have h' :
      (∀ child ∈ children, WellFormed child) ∧
        IrreflexiveOnRange children.length order ∧
          TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.1 child hChild

theorem partialOrder_irreflexive
    {children : List (POWL Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order)) :
    IrreflexiveOnRange children.length order := by
  have h' :
      (∀ child ∈ children, WellFormed child) ∧
        IrreflexiveOnRange children.length order ∧
          TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.2.1

theorem partialOrder_transitive
    {children : List (POWL Activity)} {order : Nat → Nat → Prop}
    (h : WellFormed (partialOrder children order)) :
    TransitiveOnRange children.length order := by
  have h' :
      (∀ child ∈ children, WellFormed child) ∧
        IrreflexiveOnRange children.length order ∧
          TransitiveOnRange children.length order := by
    simpa [WellFormed] using h
  exact h'.2.2

end POWL
end ProcessModel
end Pm4Lean
