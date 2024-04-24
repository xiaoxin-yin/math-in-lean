import MIL.Common
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace C03S02

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

section

variable {f g : ℝ → ℝ}

theorem Solutions_S02_The_Existential_Quantifier_ex1 (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  intro x
  exact add_le_add (lbfa x) (lbgb x)

theorem Solutions_S02_The_Existential_Quantifier_ex2 {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa⟩
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (ubfa x) h

end

section
variable {a b c : ℕ}

theorem Solutions_S02_The_Existential_Quantifier_ex3 (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩
  rcases divbc with ⟨e, rfl⟩
  use d * e; ring

theorem Solutions_S02_The_Existential_Quantifier_ex4 (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩
  rcases divac with ⟨e, rfl⟩
  use d + e; ring

end

section

open Function

theorem Solutions_S02_The_Existential_Quantifier_ex5 {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  dsimp; rw [mul_div_cancel' _ h]

theorem Solutions_S02_The_Existential_Quantifier_ex6 {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  field_simp [h] ; ring

end

section
open Function
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

theorem Solutions_S02_The_Existential_Quantifier_ex7 (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro z
  rcases surjg z with ⟨y, rfl⟩
  rcases surjf y with ⟨x, rfl⟩
  use x

end
