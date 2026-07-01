import Pm4Lean.Util.NatListBasis.Greedy.Membership

namespace Pm4Lean

theorem natListGreedyBasis_length_of_mem
    {vectors : List (List Nat)} {n : Nat}
    (hLength : ∀ xs : List Nat, xs ∈ vectors → xs.length = n)
    {upper : List Nat}
    (hMem : upper ∈ natListGreedyBasis vectors) :
    upper.length = n :=
  hLength upper (mem_natListGreedyBasis hMem)

end Pm4Lean
