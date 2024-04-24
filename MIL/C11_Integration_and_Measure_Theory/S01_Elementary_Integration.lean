import MIL.Common
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Set Filter

open Topology Filter

noncomputable section

open MeasureTheory intervalIntegral

open Interval
-- this introduces the notation `[[a, b]]` for the segment from `min a b` to `max a b`

theorem ex1 (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

theorem ex2 {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
  integral_one_div h

theorem ex3 (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
        hf.continuousAt).hasDerivAt.deriv

theorem ex4 {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'

open Convolution

theorem ex5 (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x ↦ ∫ t, f t * g (x - t) :=
  rfl
