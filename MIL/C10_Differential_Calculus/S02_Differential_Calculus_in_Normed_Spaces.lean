import MIL.Common
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.IsROrC
import Mathlib.Analysis.Calculus.FDeriv.Prod


open Set Filter

open Topology Filter

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E]

theorem S02_Differential_Calculus_in_Normed_Spaces_ex1 (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x

theorem S02_Differential_Calculus_in_Normed_Spaces_ex2 {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

theorem S02_Differential_Calculus_in_Normed_Spaces_ex3 (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

theorem S02_Differential_Calculus_in_Normed_Spaces_ex4 : MetricSpace E := by infer_instance

theorem S02_Differential_Calculus_in_Normed_Spaces_ex5 {X : Type*} [TopologicalSpace X] {f : X → E} (hf : Continuous f) :
    Continuous fun x ↦ ‖f x‖ :=
  hf.norm

variable [NormedSpace ℝ E]

theorem S02_Differential_Calculus_in_Normed_Spaces_ex6 (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  norm_smul a x

theorem S02_Differential_Calculus_in_Normed_Spaces_ex7 [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance

theorem S02_Differential_Calculus_in_Normed_Spaces_ex8 (𝕜 : Type*) [NontriviallyNormedField 𝕜] (x y : 𝕜) : ‖x * y‖ = ‖x‖ * ‖y‖ :=
  norm_mul x y

theorem S02_Differential_Calculus_in_Normed_Spaces_ex9 (𝕜 : Type*) [NontriviallyNormedField 𝕜] : ∃ x : 𝕜, 1 < ‖x‖ :=
  NormedField.exists_one_lt_norm 𝕜

theorem S02_Differential_Calculus_in_Normed_Spaces_ex10 (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem S02_Differential_Calculus_in_Normed_Spaces_ex11 : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E

theorem S02_Differential_Calculus_in_Normed_Spaces_ex12 (f : E →L[𝕜] F) : E → F :=
  f

theorem S02_Differential_Calculus_in_Normed_Spaces_ex13 (f : E →L[𝕜] F) : Continuous f :=
  f.cont

theorem S02_Differential_Calculus_in_Normed_Spaces_ex14 (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
  f.map_add x y

theorem S02_Differential_Calculus_in_Normed_Spaces_ex15 (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
  f.map_smul a x

variable (f : E →L[𝕜] F)

theorem S02_Differential_Calculus_in_Normed_Spaces_ex16 (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_op_norm x

theorem S02_Differential_Calculus_in_Normed_Spaces_ex17 {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.op_norm_le_bound hMp hM

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Metric

theorem S02_Differential_Calculus_in_Normed_Spaces_ex18 {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n`
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- each of these sets is closed
  have hc : ∀ n : ℕ, IsClosed (e n)
  sorry
  -- the union is the entire space; this is where we use `h`
  have hU : (⋃ n : ℕ, e n) = univ
  sorry
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
       `e m` contains some `x` -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ‖k‖ := sorry
  -- show all elements in the ball have norm bounded by `m` after applying any `g i`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m
  sorry
  have εk_pos : 0 < ε / ‖k‖ := sorry
  refine' ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.op_norm_le_of_shell ε_pos _ hk _⟩
  sorry
  sorry

end

open Asymptotics

theorem S02_Differential_Calculus_in_Normed_Spaces_ex19 {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F] (c : ℝ)
    (l : Filter α) (f : α → E) (g : α → F) : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff

theorem S02_Differential_Calculus_in_Normed_Spaces_ex20 {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =O[l] g ↔ ∃ C, IsBigOWith C l f g :=
  isBigO_iff_isBigOWith

theorem S02_Differential_Calculus_in_Normed_Spaces_ex21 {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =o[l] g ↔ ∀ C > 0, IsBigOWith C l f g :=
  isLittleO_iff_forall_isBigOWith

theorem S02_Differential_Calculus_in_Normed_Spaces_ex22 {α : Type*} {E : Type*} [NormedAddCommGroup E] (l : Filter α) (f g : α → E) :
    f ~[l] g ↔ (f - g) =o[l] g :=
  Iff.rfl

section

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem S02_Differential_Calculus_in_Normed_Spaces_ex23 (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔ (fun x ↦ f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] fun x ↦ x - x₀ :=
  hasFDerivAtFilter_iff_isLittleO ..

theorem S02_Differential_Calculus_in_Normed_Spaces_ex24 (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) : fderiv 𝕜 f x₀ = f' :=
  hff'.fderiv

theorem S02_Differential_Calculus_in_Normed_Spaces_ex25 (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  iteratedFDeriv 𝕜 n f

theorem S02_Differential_Calculus_in_Normed_Spaces_ex26 (n : WithTop ℕ) {f : E → F} :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, (m : WithTop ℕ) ≤ n → Continuous fun x ↦ iteratedFDeriv 𝕜 m f x) ∧
        ∀ m : ℕ, (m : WithTop ℕ) < n → Differentiable 𝕜 fun x ↦ iteratedFDeriv 𝕜 m f x :=
  contDiff_iff_continuous_differentiable

theorem S02_Differential_Calculus_in_Normed_Spaces_ex27 {𝕂 : Type*} [IsROrC 𝕂] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕂 F] {f : E → F} {x : E} {n : WithTop ℕ}
    (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) : HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt hn

section LocalInverse
variable [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

theorem S02_Differential_Calculus_in_Normed_Spaces_ex28 (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : F → E :=
  HasStrictFDerivAt.localInverse f f' a hf

theorem S02_Differential_Calculus_in_Normed_Spaces_ex29 (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  hf.eventually_left_inverse

theorem S02_Differential_Calculus_in_Normed_Spaces_ex30 (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 (f a), f (hf.localInverse f f' a x) = x :=
  hf.eventually_right_inverse

theorem S02_Differential_Calculus_in_Normed_Spaces_ex31 {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
  (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (HasStrictFDerivAt.localInverse f f' a hf) (f'.symm : F →L[𝕜] E) (f a) :=
  HasStrictFDerivAt.to_localInverse hf

end LocalInverse

#check HasFDerivWithinAt

#check HasFDerivAtFilter

end
