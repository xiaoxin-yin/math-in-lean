import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

theorem Solutions_S01_Sets_ex1 : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  . use xs; right; exact xu

theorem Solutions_S01_Sets_ex2 : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  use xs
  · intro xt
    exact xntu (Or.inl xt)
  intro xu
  apply xntu (Or.inr xu)

theorem Solutions_S01_Sets_ex3 : s ∩ t = t ∩ s :=
    Subset.antisymm
    (fun x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) fun x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩

theorem Solutions_S01_Sets_ex4 : s ∩ (s ∪ t) = s := by
  ext x; constructor
  · rintro ⟨xs, _⟩
    exact xs
  . intro xs
    use xs; left; exact xs

theorem Solutions_S01_Sets_ex5 : s ∪ s ∩ t = s := by
  ext x; constructor
  · rintro (xs | ⟨xs, xt⟩) <;> exact xs
  . intro xs; left; exact xs

theorem Solutions_S01_Sets_ex6 : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, nxt⟩ | xt)
    · left
      exact xs
    . right
      exact xt
  by_cases h : x ∈ t
  · intro
    right
    exact h
  rintro (xs | xt)
  · left
    use xs
  right; exact xt

theorem Solutions_S01_Sets_ex7 : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      left
      exact xs
      rintro ⟨_, xt⟩
      contradiction
    . constructor
      right
      exact xt
      rintro ⟨xs, _⟩
      contradiction
  rintro ⟨xs | xt, nxst⟩
  · left
    use xs
    intro xt
    apply nxst
    constructor <;> assumption
  . right; use xt; intro xs
    apply nxst
    constructor <;> assumption

theorem Solutions_S01_Sets_ex8 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro nprime
  rcases Nat.Prime.eq_two_or_odd nprime with h | h
  · rw [h]
    intro
    linarith
  rw [Nat.even_iff, h]
  norm_num

end

section

variable (s t : Set ℕ)

section
variable (ssubt : s ⊆ t)

theorem Solutions_S01_Sets_ex9 (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x (ssubt xs)
  apply h₁ x (ssubt xs)

theorem Solutions_S01_Sets_ex10 (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, _, px⟩
  use x, ssubt xs

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

theorem Solutions_S01_Sets_ex11 : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (xs | xI)
    · intro i
      right
      exact xs
    intro i
    left
    exact xI i
  intro h
  by_cases xs : x ∈ s
  · left
    exact xs
  right
  intro i
  cases h i
  · assumption
  contradiction

def primes : Set ℕ :=
  { x | Nat.Prime x }

theorem Solutions_S01_Sets_ex12 : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  rcases Nat.exists_infinite_primes x with ⟨p, primep, pge⟩
  use p, pge

end

