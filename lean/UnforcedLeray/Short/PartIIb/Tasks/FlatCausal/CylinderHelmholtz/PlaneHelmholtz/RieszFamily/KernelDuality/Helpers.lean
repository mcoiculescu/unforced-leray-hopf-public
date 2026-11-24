import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneRieszKernelBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneRieszKernelMeasurable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Helpers for the kernel duality (`PartII-b:T12/1/1/2/49`)

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

Two facts used in the duality proof: disjoint compact planar sets are at positive distance, and the
Fubini integrand `K_{ik}(x - y) g(x) f'(y)` is integrable when `g` and `f'` are supported at
positive distance.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- Disjoint compact sets in the plane are at positive distance. -/
theorem kd_exists_pos_le_norm_sub {A B : Set Pl} (hA : IsCompact A) (hB : IsCompact B)
    (h : Disjoint A B) : ∃ δ > 0, ∀ x ∈ A, ∀ y ∈ B, δ ≤ ‖x - y‖ := by
  obtain ⟨δ, hδ, hsub⟩ := hB.exists_cthickening_subset_open hA.isClosed.isOpen_compl
    (fun y hyB hyA => Set.disjoint_left.mp h hyA hyB)
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have hxB : x ∈ cthickening δ B :=
    Metric.mem_cthickening_of_dist_le x y δ B hy (by rw [dist_eq_norm]; exact hlt.le)
  exact hsub hxB hx

/-- Fubini integrability of `(x, y) ↦ K_{ik}(x - y) g(x) f'(y)` when `g` and `f'` are supported
at distance at least `δ` from one another. -/
theorem kd_fubini_integrable (i k : Fin 2) {g f' : Pl → ℝ} {S : Set Pl} {δ : ℝ} (hδ : 0 < δ)
    (hgi : Integrable g volume) (hgc : Continuous g) (hf'i : Integrable f' volume)
    (hf'm : StronglyMeasurable f')
    (hsep : ∀ x ∈ tsupport g, ∀ y ∈ S, δ ≤ ‖x - y‖) (hf'S : ∀ y, f' y ≠ 0 → y ∈ S) :
    Integrable (Function.uncurry fun x y => planeRieszKernel i k (x - y) * g x * f' y)
      (volume.prod volume) := by
  have hK : Measurable (planeRieszKernel i k) := planeRieszKernelMeasurable i k
  have hFm : StronglyMeasurable
      (fun p : Pl × Pl => planeRieszKernel i k (p.1 - p.2) * g p.1 * f' p.2) :=
    (((hK.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.mul
      (hgc.comp continuous_fst).stronglyMeasurable).mul (hf'm.comp_measurable measurable_snd))
  refine (((hgi.mul_prod hf'i).norm).const_mul (δ ^ 2)⁻¹).mono' hFm.aestronglyMeasurable ?_
  refine Eventually.of_forall fun p => ?_
  change ‖planeRieszKernel i k (p.1 - p.2) * g p.1 * f' p.2‖ ≤ (δ ^ 2)⁻¹ * ‖g p.1 * f' p.2‖
  by_cases h0 : g p.1 * f' p.2 = 0
  · rw [mul_assoc, h0]
    simp
  · have hg0 : g p.1 ≠ 0 := left_ne_zero_of_mul h0
    have hf0 : f' p.2 ≠ 0 := right_ne_zero_of_mul h0
    have hb := planeRieszKernelBound i k δ (p.1 - p.2) hδ
      (hsep p.1 (subset_tsupport g hg0) p.2 (hf'S p.2 hf0))
    rw [mul_assoc, norm_mul, Real.norm_eq_abs (planeRieszKernel i k (p.1 - p.2))]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

end UnforcedLeray.Short.IIb.PlaneRiesz
