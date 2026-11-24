import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszL2Pressure
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Leaf `PartII-b:T12/1/1/2/45`: the pair contraction on `L²`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

With `G_i = Σ_k S_{ik} f_k`, the pressure identity `Σ_i ⟨f_i, G_i⟩ = Σ_i ‖G_i‖²`
(`rieszL2Pressure`) gives `Σ_i ‖f_i - G_i‖² = Σ_i ‖f_i‖² - Σ_i ‖G_i‖² ≤ Σ_i ‖f_i‖²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/45`.**  `Σ_i ‖f_i - Σ_k S_{ik} f_k‖² ≤ Σ_i ‖f_i‖²` on `L²`. -/
theorem rieszL2Contraction : UnforcedLeray.Short.IIb.PlaneRiesz.RieszL2Contraction := by
  intro T hT f
  have hP := rieszL2Pressure T hT f
  have hEq : ∑ i, ‖f i - ∑ k, T i k (f k)‖ ^ 2 =
      ∑ i, ‖f i‖ ^ 2 - ∑ i, ‖∑ k, T i k (f k)‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => norm_sub_sq_real (f i) (∑ k, T i k (f k))),
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hP]
    ring
  rw [hEq]
  have hnn : 0 ≤ ∑ i, ‖∑ k, T i k (f k)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

end UnforcedLeray.Short.IIb.PlaneRiesz
