import Pm4Lean.Util.NatListBasis.Greedy.Membership
import Pm4Lean.Util.NatListMax

namespace Pm4Lean

theorem le_natListMax_flatten_of_mem_natListGreedyBasis
    {vectors : List (List Nat)} {coords : List Nat} {x : Nat}
    (hCoordsMem : coords ∈ natListGreedyBasis vectors)
    (hXMem : x ∈ coords) :
    x ≤ NatListMax vectors.flatten := by
  exact le_natListMax_of_mem
    (List.mem_flatten.mpr
      ⟨coords, mem_natListGreedyBasis hCoordsMem, hXMem⟩)

theorem forall_le_natListMax_flatten_of_mem_natListGreedyBasis
    {vectors : List (List Nat)} {coords : List Nat}
    (hCoordsMem : coords ∈ natListGreedyBasis vectors) :
    ∀ x : Nat, x ∈ coords → x ≤ NatListMax vectors.flatten := by
  intro x hXMem
  exact le_natListMax_flatten_of_mem_natListGreedyBasis
    hCoordsMem hXMem

end Pm4Lean
