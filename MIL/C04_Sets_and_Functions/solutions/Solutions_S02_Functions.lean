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

theorem Solutions_S02_Functions_ex1 : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    have : f x ∈ f '' s := mem_image_of_mem _ xs
    exact h this
  intro h y ymem
  rcases ymem with ⟨x, xs, fxeq⟩
  rw [← fxeq]
  apply h xs

theorem Solutions_S02_Functions_ex2 (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fxeq⟩
  rw [← h fxeq]
  exact ys

theorem Solutions_S02_Functions_ex3 : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xmem, rfl⟩
  exact xmem

theorem Solutions_S02_Functions_ex4 (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fxeq⟩
  use x
  constructor
  · show f x ∈ u
    rw [fxeq]
    exact yu
  exact fxeq

theorem Solutions_S02_Functions_ex5 (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, fxeq⟩
  use x, h xs

theorem Solutions_S02_Functions_ex6 (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x; apply h

theorem Solutions_S02_Functions_ex7 : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x; rfl

theorem Solutions_S02_Functions_ex8 : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  . use x, xs
  . use x, xt

theorem Solutions_S02_Functions_ex9 (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂t, fx₂eq⟩⟩
  use x₁
  constructor
  . use x₁s
    rw [← h fx₂eq]
    exact x₂t
  . rfl

theorem Solutions_S02_Functions_ex10 : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x₁, x₁s, rfl⟩, h⟩
  use x₁
  constructor
  . constructor
    . exact x₁s
    . intro h'
      apply h
      use x₁, h'
  . rfl

theorem Solutions_S02_Functions_ex11 : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun x ↦ id

theorem Solutions_S02_Functions_ex12 : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  rintro ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩
  exact ⟨⟨x, xs, rfl⟩, fxv⟩

theorem Solutions_S02_Functions_ex13 : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

theorem Solutions_S02_Functions_ex14 : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

theorem Solutions_S02_Functions_ex15 : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left
    exact ⟨x, xs, rfl⟩
  right; exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

theorem Solutions_S02_Functions_ex16 : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩

theorem Solutions_S02_Functions_ex17 : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩

theorem Solutions_S02_Functions_ex18 (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp
  intro h
  rcases h i with ⟨x, xAi, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq

theorem Solutions_S02_Functions_ex19 : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

theorem Solutions_S02_Functions_ex20 : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

end

section

open Set Real

theorem Solutions_S02_Functions_ex21 : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt xnonneg]
    _ = sqrt y ^ 2 := by rw [e]
    _ = y := by rw [sq_sqrt ynonneg]


theorem Solutions_S02_Functions_ex22 : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  dsimp at *
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq xnonneg]
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := by rw [sqrt_sq ynonneg]


theorem Solutions_S02_Functions_ex23 : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, ⟨xnonneg, rfl⟩⟩
    apply sqrt_nonneg
  intro ynonneg
  use y ^ 2
  dsimp at *
  constructor
  apply pow_nonneg ynonneg
  apply sqrt_sq
  assumption

theorem Solutions_S02_Functions_ex24 : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    dsimp at *
    apply pow_two_nonneg
  intro ynonneg
  use sqrt y
  exact sq_sqrt ynonneg

end

section
variable {α β : Type*} [Inhabited α]

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

theorem Solutions_S02_Functions_ex25 : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h y
    apply h
    apply inverse_spec
    use y
  intro h x1 x2 e
  rw [← h x1, ← h x2, e]

theorem Solutions_S02_Functions_ex26 : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨fun h y ↦ h (inverse_spec _ ⟨y, rfl⟩), fun h x1 x2 e ↦ by rw [← h x1, ← h x2, e]⟩

theorem Solutions_S02_Functions_ex27 : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    apply inverse_spec
    apply h
  intro h y
  use inverse f y
  apply h

theorem Solutions_S02_Functions_ex28 : Surjective f ↔ RightInverse (inverse f) f :=
  ⟨fun h y ↦ inverse_spec _ (h _), fun h y ↦ ⟨inverse f y, h _⟩⟩

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
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

end
