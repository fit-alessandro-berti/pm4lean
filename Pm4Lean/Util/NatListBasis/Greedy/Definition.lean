import Pm4Lean.Util.NatListBasis.Coverage

namespace Pm4Lean

noncomputable def natListGreedyBasisFrom :
    List (List Nat) → List (List Nat) → List (List Nat)
  | [], basis => basis
  | x :: xs, basis =>
      by
        classical
        exact
          if NatListDominatedBy x basis then
            natListGreedyBasisFrom xs basis
          else
            natListGreedyBasisFrom xs (x :: basis)

noncomputable def natListGreedyBasis
    (vectors : List (List Nat)) : List (List Nat) :=
  natListGreedyBasisFrom vectors []

end Pm4Lean
