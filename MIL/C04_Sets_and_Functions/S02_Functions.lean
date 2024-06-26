import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

theorem S02_Functions_ex1 : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

theorem S02_Functions_ex2 : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

theorem S02_Functions_ex3 : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

theorem S02_Functions_ex4 : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry

theorem S02_Functions_ex5 (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

theorem S02_Functions_ex6 : f '' (f ⁻¹' u) ⊆ u := by
  sorry

theorem S02_Functions_ex7 (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

theorem S02_Functions_ex8 (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

theorem S02_Functions_ex9 (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

theorem S02_Functions_ex10 : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

theorem S02_Functions_ex11 : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

theorem S02_Functions_ex12 (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

theorem S02_Functions_ex13 : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

theorem S02_Functions_ex14 : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

theorem S02_Functions_ex15 : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

theorem S02_Functions_ex16 : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

theorem S02_Functions_ex17 : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

theorem S02_Functions_ex18 : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

theorem S02_Functions_ex19 : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  sorry

theorem S02_Functions_ex20 : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

theorem S02_Functions_ex21 (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

theorem S02_Functions_ex22 : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

theorem S02_Functions_ex23 : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

theorem S02_Functions_ex24 : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

theorem S02_Functions_ex25 : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


theorem S02_Functions_ex26 : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

theorem S02_Functions_ex27 : InjOn sqrt { x | x ≥ 0 } := by
  sorry

theorem S02_Functions_ex28 : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

theorem S02_Functions_ex29 : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

theorem S02_Functions_ex30 : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

theorem S02_Functions_ex31 : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

theorem S02_Functions_ex32 : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

theorem S02_Functions_ex33 : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
