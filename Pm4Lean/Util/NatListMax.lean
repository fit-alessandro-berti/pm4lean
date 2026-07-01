namespace Pm4Lean

def NatListMax : List Nat → Nat
  | [] => 0
  | n :: ns => Nat.max n (NatListMax ns)

theorem le_natListMax_of_mem {n : Nat} {ns : List Nat}
    (hMem : n ∈ ns) :
    n ≤ NatListMax ns := by
  induction ns with
  | nil =>
      cases hMem
  | cons m ns ih =>
      cases hMem with
      | head =>
          exact Nat.le_max_left _ _
      | tail _ hTail =>
          exact Nat.le_trans (ih hTail) (Nat.le_max_right _ _)

theorem natListMax_le_of_forall {ns : List Nat} {k : Nat}
    (hBound : ∀ n : Nat, n ∈ ns → n ≤ k) :
    NatListMax ns ≤ k := by
  induction ns with
  | nil =>
      exact Nat.zero_le k
  | cons n ns ih =>
      exact Nat.max_le.2
        ⟨hBound n (List.Mem.head ns),
          ih (fun m hMem => hBound m (List.Mem.tail n hMem))⟩

end Pm4Lean
