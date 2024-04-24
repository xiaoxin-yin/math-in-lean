import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

theorem S04_More_on_Order_and_Divisibility_ex1 : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

theorem S04_More_on_Order_and_Divisibility_ex2 : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

theorem S04_More_on_Order_and_Divisibility_ex3 : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

theorem S04_More_on_Order_and_Divisibility_ex4 : max a b = max b a := by
  sorry
theorem S04_More_on_Order_and_Divisibility_ex5 : min (min a b) c = min a (min b c) := by
  sorry
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  sorry
theorem S04_More_on_Order_and_Divisibility_ex6 : min a b + c = min (a + c) (b + c) := by
  sorry
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

theorem S04_More_on_Order_and_Divisibility_ex7 : |a| - |b| ≤ |a - b| :=
  sorry
end

section
variable (w x y z : ℕ)

theorem S04_More_on_Order_and_Divisibility_ex8 (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

theorem S04_More_on_Order_and_Divisibility_ex9 : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

theorem S04_More_on_Order_and_Divisibility_ex10 : x ∣ x ^ 2 := by
  apply dvd_mul_left

theorem S04_More_on_Order_and_Divisibility_ex11 (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  sorry
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

theorem S04_More_on_Order_and_Divisibility_ex12 : Nat.gcd m n = Nat.gcd n m := by
  sorry
end


