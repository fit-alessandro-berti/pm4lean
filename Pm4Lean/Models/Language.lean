namespace Pm4Lean
namespace ProcessModel

/-- A finite execution trace over visible activities. -/
abbrev Trace (Activity : Type u) := List Activity

/-- A trace language is represented extensionally as a predicate on traces. -/
abbrev Language (Activity : Type u) := Trace Activity → Prop

/-- Interleavings of two traces, preserving the internal order of both. -/
inductive Shuffle {Activity : Type u} :
    Trace Activity → Trace Activity → Trace Activity → Prop where
  | nil_left (ys : Trace Activity) : Shuffle [] ys ys
  | nil_right (xs : Trace Activity) : Shuffle xs [] xs
  | left {x : Activity} {xs ys zs : Trace Activity} :
      Shuffle xs ys zs → Shuffle (x :: xs) ys (x :: zs)
  | right {y : Activity} {xs ys zs : Trace Activity} :
      Shuffle xs ys zs → Shuffle xs (y :: ys) (y :: zs)

/-- Interleaving of a finite list of traces. -/
inductive Interleaves {Activity : Type u} :
    List (Trace Activity) → Trace Activity → Prop where
  | nil : Interleaves [] []
  | cons {σ τ out : Trace Activity} {rest : List (Trace Activity)} :
      Interleaves rest τ → Shuffle σ τ out → Interleaves (σ :: rest) out

/-- Pointwise membership of traces in a matching list of languages. -/
inductive TracesIn {Activity : Type u} :
    List (Language Activity) → List (Trace Activity) → Prop where
  | nil : TracesIn [] []
  | cons {L : Language Activity} {Ls : List (Language Activity)}
      {σ : Trace Activity} {traces : List (Trace Activity)} :
      L σ → TracesIn Ls traces → TracesIn (L :: Ls) (σ :: traces)

/-- Language inclusion. -/
def Language.Subset {Activity : Type u}
    (L₁ L₂ : Language Activity) : Prop :=
  ∀ σ, L₁ σ → L₂ σ

/-- Language equivalence. -/
def Language.Equivalent {Activity : Type u}
    (L₁ L₂ : Language Activity) : Prop :=
  Language.Subset L₁ L₂ ∧ Language.Subset L₂ L₁

namespace Language

/-- The empty language. -/
def empty {Activity : Type u} : Language Activity :=
  fun _ => False

/-- The language containing only the empty trace. -/
def epsilon {Activity : Type u} : Language Activity :=
  fun σ => σ = []

/-- The singleton language containing one visible activity. -/
def singleton {Activity : Type u} (a : Activity) : Language Activity :=
  fun σ => σ = [a]

/-- Language union, used for exclusive choice. -/
def union {Activity : Type u} (L₁ L₂ : Language Activity) : Language Activity :=
  fun σ => L₁ σ ∨ L₂ σ

/-- Sequential composition of trace languages. -/
def seq {Activity : Type u} (L₁ L₂ : Language Activity) : Language Activity :=
  fun σ => ∃ σ₁ σ₂, L₁ σ₁ ∧ L₂ σ₂ ∧ σ = σ₁ ++ σ₂

/-- Parallel composition as all order-preserving interleavings. -/
def parallel {Activity : Type u} (L₁ L₂ : Language Activity) : Language Activity :=
  fun σ => ∃ σ₁ σ₂, L₁ σ₁ ∧ L₂ σ₂ ∧ Shuffle σ₁ σ₂ σ

/-- Parallel composition of a finite list of component languages. -/
def interleaving {Activity : Type u}
    (Ls : List (Language Activity)) : Language Activity :=
  fun σ => ∃ traces : List (Trace Activity),
    TracesIn Ls traces ∧ Interleaves traces σ

/-- Kleene-style finite repetition of a language. -/
inductive Star {Activity : Type u} (L : Language Activity) :
    Language Activity where
  | nil : Star L []
  | cons {σ₁ σ₂ : Trace Activity} :
      L σ₁ → Star L σ₂ → Star L (σ₁ ++ σ₂)

theorem equivalent_refl {Activity : Type u} (L : Language Activity) :
    Equivalent L L :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem equivalent_symm {Activity : Type u} {L₁ L₂ : Language Activity}
    (h : Equivalent L₁ L₂) : Equivalent L₂ L₁ :=
  ⟨h.2, h.1⟩

theorem equivalent_trans {Activity : Type u} {L₁ L₂ L₃ : Language Activity}
    (h₁₂ : Equivalent L₁ L₂) (h₂₃ : Equivalent L₂ L₃) :
    Equivalent L₁ L₃ :=
  ⟨fun σ h => h₂₃.1 σ (h₁₂.1 σ h),
   fun σ h => h₁₂.2 σ (h₂₃.2 σ h)⟩

theorem seq_epsilon_left {Activity : Type u} (L : Language Activity) :
    Equivalent (seq epsilon L) L := by
  constructor
  · intro σ h
    obtain ⟨σ₁, σ₂, hEps, hL, hEq⟩ := h
    subst hEq
    subst hEps
    simpa using hL
  · intro σ hL
    exact ⟨[], σ, rfl, hL, rfl⟩

theorem seq_epsilon_right {Activity : Type u} (L : Language Activity) :
    Equivalent (seq L epsilon) L := by
  constructor
  · intro σ h
    obtain ⟨σ₁, σ₂, hL, hEps, hEq⟩ := h
    subst hEq
    subst hEps
    simpa using hL
  · intro σ hL
    exact ⟨σ, [], hL, rfl, by simp⟩

theorem union_comm {Activity : Type u} (L₁ L₂ : Language Activity) :
    Equivalent (union L₁ L₂) (union L₂ L₁) :=
  ⟨fun _ h => Or.symm h, fun _ h => Or.symm h⟩

theorem union_congr {Activity : Type u}
    {L₁ L₁' L₂ L₂' : Language Activity}
    (h₁ : Equivalent L₁ L₁') (h₂ : Equivalent L₂ L₂') :
    Equivalent (union L₁ L₂) (union L₁' L₂') := by
  constructor
  · intro σ h
    cases h with
    | inl hL => exact Or.inl (h₁.1 σ hL)
    | inr hL => exact Or.inr (h₂.1 σ hL)
  · intro σ h
    cases h with
    | inl hL => exact Or.inl (h₁.2 σ hL)
    | inr hL => exact Or.inr (h₂.2 σ hL)

theorem seq_congr {Activity : Type u}
    {L₁ L₁' L₂ L₂' : Language Activity}
    (h₁ : Equivalent L₁ L₁') (h₂ : Equivalent L₂ L₂') :
    Equivalent (seq L₁ L₂) (seq L₁' L₂') := by
  constructor
  · intro σ h
    obtain ⟨σ₁, σ₂, hL₁, hL₂, hEq⟩ := h
    exact ⟨σ₁, σ₂, h₁.1 σ₁ hL₁, h₂.1 σ₂ hL₂, hEq⟩
  · intro σ h
    obtain ⟨σ₁, σ₂, hL₁, hL₂, hEq⟩ := h
    exact ⟨σ₁, σ₂, h₁.2 σ₁ hL₁, h₂.2 σ₂ hL₂, hEq⟩

theorem parallel_congr {Activity : Type u}
    {L₁ L₁' L₂ L₂' : Language Activity}
    (h₁ : Equivalent L₁ L₁') (h₂ : Equivalent L₂ L₂') :
    Equivalent (parallel L₁ L₂) (parallel L₁' L₂') := by
  constructor
  · intro σ h
    obtain ⟨σ₁, σ₂, hL₁, hL₂, hShuffle⟩ := h
    exact ⟨σ₁, σ₂, h₁.1 σ₁ hL₁, h₂.1 σ₂ hL₂, hShuffle⟩
  · intro σ h
    obtain ⟨σ₁, σ₂, hL₁, hL₂, hShuffle⟩ := h
    exact ⟨σ₁, σ₂, h₁.2 σ₁ hL₁, h₂.2 σ₂ hL₂, hShuffle⟩

theorem star_subset_of_subset {Activity : Type u}
    {L₁ L₂ : Language Activity}
    (hSubset : Subset L₁ L₂) :
    Subset (Star L₁) (Star L₂) := by
  intro σ h
  induction h with
  | nil =>
      exact Star.nil
  | cons hHead _ ih =>
      exact Star.cons (hSubset _ hHead) ih

theorem star_congr {Activity : Type u}
    {L₁ L₂ : Language Activity}
    (h : Equivalent L₁ L₂) :
    Equivalent (Star L₁) (Star L₂) :=
  ⟨star_subset_of_subset h.1, star_subset_of_subset h.2⟩

theorem shuffle_nil_right_eq {Activity : Type u}
    {xs zs : Trace Activity} (h : Shuffle xs [] zs) :
    zs = xs := by
  cases h with
  | nil_left ys =>
      rfl
  | nil_right xs =>
      rfl
  | left h =>
      congr
      exact shuffle_nil_right_eq h

theorem interleaving_nil {Activity : Type u} :
    interleaving ([] : List (Language Activity)) [] := by
  exact ⟨[], TracesIn.nil, Interleaves.nil⟩

theorem interleaving_singleton {Activity : Type u}
    (L : Language Activity) :
    Equivalent (interleaving [L]) L := by
  constructor
  · intro σ h
    obtain ⟨traces, hIn, hInter⟩ := h
    cases hIn with
    | cons hL hRest =>
        cases hRest
        cases hInter with
        | cons hInterRest hShuffle =>
            cases hInterRest
            rw [shuffle_nil_right_eq hShuffle]
            exact hL
  · intro σ hL
    exact ⟨[σ], TracesIn.cons hL TracesIn.nil,
      Interleaves.cons Interleaves.nil (Shuffle.nil_right σ)⟩

end Language
end ProcessModel
end Pm4Lean
