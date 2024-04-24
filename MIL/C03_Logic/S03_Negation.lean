import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

theorem ex1 (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

theorem ex2 (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

theorem ex3 (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

theorem ex4 : ¬FnHasUb fun x ↦ x :=
  sorry

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

theorem ex5 (h : Monotone f) (h' : f a < f b) : a < b := by
  sorry

theorem ex6 (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry

theorem ex7 : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by sorry
  have h' : f 1 ≤ f 0 := le_refl _
  sorry

theorem ex8 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

theorem ex9 (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

theorem ex10 (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

theorem ex11 (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

theorem ex12 (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry

theorem ex13 (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

theorem ex14 (h : ¬¬Q) : Q := by
  sorry

theorem ex15 (h : Q) : ¬¬Q := by
  sorry

end

section
variable (f : ℝ → ℝ)

theorem ex16 (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry

theorem ex17 (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

theorem ex18 (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

theorem ex19 (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  sorry

theorem ex20 (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

theorem ex21 (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

theorem ex22 (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

theorem ex23 (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

theorem ex24 (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end

