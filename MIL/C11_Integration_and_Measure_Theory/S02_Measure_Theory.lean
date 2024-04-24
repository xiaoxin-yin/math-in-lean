import MIL.Common
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

noncomputable section

variable {α : Type*} [MeasurableSpace α]

theorem ex1 : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

theorem ex2 : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

theorem ex3 {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

theorem ex4 : Encodable ℕ := by infer_instance

theorem ex5 (n : ℕ) : Encodable (Fin n) := by infer_instance

variable {ι : Type*} [Encodable ι]

theorem ex6 {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

theorem ex7 {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h

open MeasureTheory
variable {μ : Measure α}

theorem ex8 (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

theorem ex9 (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

theorem ex10 {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis

theorem ex11 {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in μ.ae, P x :=
  Iff.rfl
