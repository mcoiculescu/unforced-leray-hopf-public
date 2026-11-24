import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneRieszKernelMeasurable

/-!
# Strong measurability of the planar kernel integral

Source of record: `the November 2 reference manuscript`, line 1670 (the planar
projection `P_0 = I - ∇Δ⁻¹ div`) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory, Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

For a strongly measurable `φ` on the plane, the map `x ↦ ∫ K_{ik}(x - y) φ(y) dy` is strongly
measurable. The proof is the planar analogue of `stronglyMeasurable_kernelIntegral` in
`Lib/CZL2/L2OffSupport.lean`: the integrand `(x, y) ↦ K_{ik}(x - y) φ(y)` is strongly measurable
on the product, and the partial integral of a strongly measurable function on a product is
strongly measurable (`StronglyMeasurable.integral_prod_right'`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- `x ↦ ∫ K_{ik}(x - y) φ(y) dy` is strongly measurable (`KernelIntegralMeasurable`). -/
theorem kernelIntegralMeasurable : KernelIntegralMeasurable := by
  intro i k φ hφ
  have hK : ∀ i k : Fin 2, Measurable (planeRieszKernel i k) := planeRieszKernelMeasurable
  have h : StronglyMeasurable
      (fun p : Pl × Pl => planeRieszKernel i k (p.1 - p.2) * φ p.2) :=
    ((hK i k).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.mul
      (hφ.comp_measurable measurable_snd)
  exact h.integral_prod_right'

end UnforcedLeray.Short.IIb.PlaneRiesz
