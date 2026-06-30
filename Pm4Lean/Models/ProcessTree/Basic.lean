namespace Pm4Lean
namespace ProcessModel

/-- Basic process-tree syntax. -/
inductive ProcessTree (Activity : Type u) where
  | tau : ProcessTree Activity
  | activity : Activity → ProcessTree Activity
  | sequence : ProcessTree Activity → ProcessTree Activity → ProcessTree Activity
  | exclusiveChoice : ProcessTree Activity → ProcessTree Activity → ProcessTree Activity
  | parallel : ProcessTree Activity → ProcessTree Activity → ProcessTree Activity
  | loop : ProcessTree Activity → ProcessTree Activity → ProcessTree Activity
deriving Repr

namespace ProcessTree

variable {Activity : Type u}

/-- Number of visible activity leaves. -/
def activityCount : ProcessTree Activity → Nat
  | tau => 0
  | activity _ => 1
  | sequence l r => activityCount l + activityCount r
  | exclusiveChoice l r => activityCount l + activityCount r
  | parallel l r => activityCount l + activityCount r
  | loop body redo => activityCount body + activityCount redo

theorem activityCount_nonnegative (T : ProcessTree Activity) :
    0 ≤ activityCount T :=
  Nat.zero_le _

end ProcessTree
end ProcessModel
end Pm4Lean
