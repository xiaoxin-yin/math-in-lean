import MIL.Common
import Mathlib.Data.Real.Basic
-- An example.
theorem S01_Calculating_ex1 (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
theorem S01_Calculating_ex2 (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

theorem S01_Calculating_ex3 (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

-- An example.
theorem S01_Calculating_ex4 (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
theorem S01_Calculating_ex5 (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

theorem S01_Calculating_ex6 (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

-- Using facts from the local context.
theorem S01_Calculating_ex7 (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

theorem S01_Calculating_ex8 (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

theorem S01_Calculating_ex9 (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

theorem S01_Calculating_ex10 (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d e f : ℝ)

theorem S01_Calculating_ex11 (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

theorem S01_Calculating_ex12 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

theorem S01_Calculating_ex13 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

theorem S01_Calculating_ex14 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

theorem S01_Calculating_ex15 : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry

theorem S01_Calculating_ex16 (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

theorem S01_Calculating_ex17 (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

theorem S01_Calculating_ex18 : c * b * a = b * (a * c) := by
  ring

theorem S01_Calculating_ex19 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

theorem S01_Calculating_ex20 : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

theorem S01_Calculating_ex21 (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

theorem S01_Calculating_ex22 (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
