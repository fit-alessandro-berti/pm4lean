import Pm4Lean.Conversion.POWL2ToSoundWfNet.Structural.Core

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace Structural

def lastChildIndex (n : Nat) : Nat := n - 1
noncomputable def poBeginPre
    (addr : Address) (order : Nat → Nat → Prop) (n i : Nat) :
    List RawPlace :=
  by
    classical
    exact
      (if ∃ j, j < n ∧ order j i then
        []
      else
        [poReady addr i]) ++
        (indicesWhere n (fun j => order j i)).map (fun j => poPredDone addr j i)

noncomputable def poCompletePost
    (addr : Address) (order : Nat → Nat → Prop) (n i : Nat) :
    List RawPlace :=
  [poDone addr i] ++
    (indicesWhere n (fun j => order i j)).map (fun j => poPredDone addr i j)

theorem prefixPlace_injective (pref : Address) :
    Function.Injective (prefixPlace pref) := by
  intro q r h
  cases q
  cases r
  simp [prefixPlace] at h
  rcases h with ⟨hAddr, hKind⟩
  simp [hAddr, hKind]

@[simp] theorem prefixPlace_entry (pref addr : Address) :
    prefixPlace pref (entry addr) = entry (pref ++ addr) := by
  rfl

@[simp] theorem prefixPlace_exit (pref addr : Address) :
    prefixPlace pref (exit addr) = exit (pref ++ addr) := by
  rfl

@[simp] theorem prefixPlace_childEntry
    (pref addr : Address) (i : Nat) :
    prefixPlace pref (childEntry addr i) =
      childEntry (pref ++ addr) i := by
  simp [prefixPlace, childEntry, childAddr, entry]

@[simp] theorem prefixPlace_childExit
    (pref addr : Address) (i : Nat) :
    prefixPlace pref (childExit addr i) =
      childExit (pref ++ addr) i := by
  simp [prefixPlace, childExit, childAddr, exit]

@[simp] theorem prefixPlace_poReady
    (pref addr : Address) (i : Nat) :
    prefixPlace pref (poReady addr i) =
      poReady (pref ++ addr) i := by
  rfl

@[simp] theorem prefixPlace_poDone
    (pref addr : Address) (i : Nat) :
    prefixPlace pref (poDone addr i) =
      poDone (pref ++ addr) i := by
  rfl

@[simp] theorem prefixPlace_poPredDone
    (pref addr : Address) (i j : Nat) :
    prefixPlace pref (poPredDone addr i j) =
      poPredDone (pref ++ addr) i j := by
  rfl

theorem rawMark_map_prefix
    (pref : Address) (xs : List RawPlace) (q : RawPlace) :
    rawMark (xs.map (prefixPlace pref)) (prefixPlace pref q) =
      rawMark xs q := by
  have hIff :
      (∃ a, a ∈ xs ∧ prefixPlace pref a = prefixPlace pref q) ↔
        q ∈ xs := by
    constructor
    · rintro ⟨a, hMem, hEq⟩
      have hA : a = q := prefixPlace_injective pref hEq
      simpa [hA] using hMem
    · intro hMem
      exact ⟨q, hMem, rfl⟩
  simp [rawMark, List.mem_map, hIff]

theorem rawMark_singleton_prefix
    (pref : Address) (x q : RawPlace) :
    rawMark [prefixPlace pref x] (prefixPlace pref q) =
      rawMark [x] q := by
  simpa using rawMark_map_prefix pref [x] q

def HasPlacePrefix (pref : Address) (q : RawPlace) : Prop :=
  ∃ base : RawPlace, q = prefixPlace pref base

theorem rawMark_map_prefix_zero
    (pref : Address) (xs : List RawPlace) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark (xs.map (prefixPlace pref)) q = 0 := by
  have hNotMem : q ∉ xs.map (prefixPlace pref) := by
    intro hMem
    rcases List.mem_map.mp hMem with ⟨base, _hBase, hEq⟩
    exact hNoPrefix ⟨base, hEq.symm⟩
  simp [rawMark, hNotMem]

theorem rawMark_singleton_prefix_zero
    (pref : Address) (x q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [prefixPlace pref x] q = 0 := by
  simpa using rawMark_map_prefix_zero pref [x] q hNoPrefix

theorem rawMark_entry_prefix
    (pref addr : Address) (q : RawPlace) :
    rawMark [entry (pref ++ addr)] (prefixPlace pref q) =
      rawMark [entry addr] q := by
  simpa using rawMark_singleton_prefix pref (entry addr) q

theorem rawMark_exit_prefix
    (pref addr : Address) (q : RawPlace) :
    rawMark [exit (pref ++ addr)] (prefixPlace pref q) =
      rawMark [exit addr] q := by
  simpa using rawMark_singleton_prefix pref (exit addr) q

theorem rawMark_childEntry_prefix
    (pref addr : Address) (i : Nat) (q : RawPlace) :
    rawMark [childEntry (pref ++ addr) i] (prefixPlace pref q) =
      rawMark [childEntry addr i] q := by
  simpa using rawMark_singleton_prefix pref (childEntry addr i) q

theorem rawMark_childExit_prefix
    (pref addr : Address) (i : Nat) (q : RawPlace) :
    rawMark [childExit (pref ++ addr) i] (prefixPlace pref q) =
      rawMark [childExit addr i] q := by
  simpa using rawMark_singleton_prefix pref (childExit addr i) q

theorem rawMark_entry_prefix_zero
    (pref addr : Address) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [entry (pref ++ addr)] q = 0 := by
  simpa using rawMark_singleton_prefix_zero pref (entry addr) q hNoPrefix

theorem rawMark_exit_prefix_zero
    (pref addr : Address) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [exit (pref ++ addr)] q = 0 := by
  simpa using rawMark_singleton_prefix_zero pref (exit addr) q hNoPrefix

theorem rawMark_childEntry_prefix_zero
    (pref addr : Address) (i : Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [childEntry (pref ++ addr) i] q = 0 := by
  simpa using
    rawMark_singleton_prefix_zero pref (childEntry addr i) q hNoPrefix

theorem rawMark_childExit_prefix_zero
    (pref addr : Address) (i : Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark [childExit (pref ++ addr) i] q = 0 := by
  simpa using
    rawMark_singleton_prefix_zero pref (childExit addr i) q hNoPrefix

theorem rawMark_poDone_prefix
    (pref addr : Address) (n : Nat) (q : RawPlace) :
    rawMark ((List.range n).map (poDone (pref ++ addr)))
        (prefixPlace pref q) =
      rawMark ((List.range n).map (poDone addr)) q := by
  simpa [prefixPlace, poDone, List.map_map] using
    rawMark_map_prefix pref ((List.range n).map (poDone addr)) q

theorem rawMark_poReady_prefix
    (pref addr : Address) (xs : List Nat) (q : RawPlace) :
    rawMark (xs.map (poReady (pref ++ addr))) (prefixPlace pref q) =
      rawMark (xs.map (poReady addr)) q := by
  simpa [prefixPlace, poReady, List.map_map] using
    rawMark_map_prefix pref (xs.map (poReady addr)) q

theorem rawMark_poDone_prefix_zero
    (pref addr : Address) (n : Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark ((List.range n).map (poDone (pref ++ addr))) q = 0 := by
  simpa [prefixPlace, poDone, List.map_map] using
    rawMark_map_prefix_zero pref ((List.range n).map (poDone addr)) q
      hNoPrefix

theorem rawMark_poReady_prefix_zero
    (pref addr : Address) (xs : List Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark (xs.map (poReady (pref ++ addr))) q = 0 := by
  simpa [prefixPlace, poReady, List.map_map] using
    rawMark_map_prefix_zero pref (xs.map (poReady addr)) q hNoPrefix

theorem poBeginPre_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat) :
    poBeginPre (pref ++ addr) order n i =
      (poBeginPre addr order n i).map (prefixPlace pref) := by
  classical
  unfold poBeginPre
  split <;> simp [prefixPlace, poReady, poPredDone, List.map_map]

theorem poCompletePost_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat) :
    poCompletePost (pref ++ addr) order n i =
      (poCompletePost addr order n i).map (prefixPlace pref) := by
  simp [poCompletePost, prefixPlace, poDone, poPredDone, List.map_map]

theorem rawMark_poBeginPre_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat)
    (q : RawPlace) :
    rawMark (poBeginPre (pref ++ addr) order n i) (prefixPlace pref q) =
      rawMark (poBeginPre addr order n i) q := by
  rw [poBeginPre_prefix]
  exact rawMark_map_prefix pref (poBeginPre addr order n i) q

theorem rawMark_poBeginPre_prefix_zero
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat)
    (q : RawPlace) (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark (poBeginPre (pref ++ addr) order n i) q = 0 := by
  rw [poBeginPre_prefix]
  exact rawMark_map_prefix_zero pref (poBeginPre addr order n i) q hNoPrefix

theorem rawMark_poCompletePost_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat)
    (q : RawPlace) :
    rawMark (poCompletePost (pref ++ addr) order n i)
        (prefixPlace pref q) =
      rawMark (poCompletePost addr order n i) q := by
  rw [poCompletePost_prefix]
  exact rawMark_map_prefix pref (poCompletePost addr order n i) q

theorem rawMark_poCompletePost_prefix_zero
    (pref addr : Address) (order : Nat → Nat → Prop) (n i : Nat)
    (q : RawPlace) (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark (poCompletePost (pref ++ addr) order n i) q = 0 := by
  rw [poCompletePost_prefix]
  exact
    rawMark_map_prefix_zero pref (poCompletePost addr order n i) q
      hNoPrefix

theorem rawMark_partialOrderForkPost_prefix
    (pref addr : Address) (order : Nat → Nat → Prop) (n : Nat)
    (q : RawPlace) :
    rawMark
        (if n = 0 then [exit (pref ++ addr)]
         else (indicesWhere n (fun i => ¬ (∃ j, j < n ∧ order j i))).map
              (poReady (pref ++ addr)))
        (prefixPlace pref q) =
      rawMark
        (if n = 0 then [exit addr]
         else (indicesWhere n (fun i => ¬ (∃ j, j < n ∧ order j i))).map
              (poReady addr)) q := by
  by_cases h : n = 0
  · simpa [h, prefixPlace, exit] using
      rawMark_singleton_prefix pref (exit addr) q
  · simp [h, rawMark_poReady_prefix]

theorem rawMark_partialOrderForkPost_list_prefix
    (pref addr : Address) (order : Nat → Nat → Prop)
    (children : List (POWL2 Activity)) (q : RawPlace) :
    rawMark
        (if children.length = 0 then [exit (pref ++ addr)]
         else
          (indicesWhere children.length
            (fun i => ¬ (∃ j, j < children.length ∧ order j i))).map
            (poReady (pref ++ addr)))
        (prefixPlace pref q) =
      rawMark
        (if children.length = 0 then [exit addr]
         else
          (indicesWhere children.length
            (fun i => ¬ (∃ j, j < children.length ∧ order j i))).map
            (poReady addr))
        q := by
  simpa using
    rawMark_partialOrderForkPost_prefix pref addr order children.length q

theorem rawMark_exit_or_poReady_prefix
    (pref addr : Address) (condition : Prop) [Decidable condition]
    (indices : List Nat) (q : RawPlace) :
    rawMark
        (if condition then [exit (pref ++ addr)]
         else indices.map (poReady (pref ++ addr)))
        (prefixPlace pref q) =
      rawMark
        (if condition then [exit addr]
         else indices.map (poReady addr))
        q := by
  by_cases h : condition
  · simp [h, rawMark_exit_prefix]
  · simp [h, rawMark_poReady_prefix]

theorem rawMark_exit_or_poReady_prefix_zero
    (pref addr : Address) (condition : Prop) [Decidable condition]
    (indices : List Nat) (q : RawPlace)
    (hNoPrefix : ¬ HasPlacePrefix pref q) :
    rawMark
        (if condition then [exit (pref ++ addr)]
         else indices.map (poReady (pref ++ addr)))
        q = 0 := by
  by_cases h : condition
  · simp [h, rawMark_exit_prefix_zero, hNoPrefix]
  · simp [h, rawMark_poReady_prefix_zero, hNoPrefix]

end Structural
end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
