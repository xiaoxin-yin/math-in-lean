import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

theorem S05_Disjunction_ex1 (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

theorem S05_Disjunction_ex2 (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

theorem S05_Disjunction_ex3 (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

theorem S05_Disjunction_ex4 (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

theorem S05_Disjunction_ex5 : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

theorem S05_Disjunction_ex6 : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

theorem S05_Disjunction_ex7 : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


theorem S05_Disjunction_ex8 : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  sorry

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  sorry

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

end

theorem S05_Disjunction_ex9 {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

theorem S05_Disjunction_ex10 {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

theorem S05_Disjunction_ex11 {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry

theorem S05_Disjunction_ex12 {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

theorem S05_Disjunction_ex13 {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

theorem S05_Disjunction_ex14 (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

theorem S05_Disjunction_ex15 (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

theorem S05_Disjunction_ex16 (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

theorem S05_Disjunction_ex17 (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

theorem S05_Disjunction_ex18 (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry

