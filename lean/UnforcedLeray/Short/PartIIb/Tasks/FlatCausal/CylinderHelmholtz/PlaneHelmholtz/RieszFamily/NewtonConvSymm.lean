import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonKernelLocInt
import Mathlib.Analysis.Convolution

/-!
# Leaf `PartII-b:T12/1/1/2/35`: self-adjointness of the planar Newton potential on tests

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For planar tests `f, g`, `∫ g (N * f) = ∫ (N * g) f`. This follows from Fubini on the product
of two compact supports (where the integrand is integrable because `N` is locally integrable)
and the evenness `N(-z) = N(z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The Newton kernel is even. -/
theorem newtonKernel_neg_arg (z : Pl) : newtonKernel (-z) = newtonKernel z := by
  simp [newtonKernel]

/-- **Leaf `PartII-b:T12/1/1/2/35`.**  Self-adjointness of the Newton potential on tests:
`∫ g (N * f) = ∫ (N * g) f`. -/
theorem newtonConvSymm : NewtonConvSymm := by
  intro f g hf hg
  obtain ⟨hfs, hfc⟩ := hf
  obtain ⟨hgs, hgc⟩ := hg
  have hfcont : Continuous f := hfs.continuous
  have hgcont : Continuous g := hgs.continuous
  have hfint : Integrable f volume := hfcont.integrable_of_hasCompactSupport hfc
  -- a radius containing all differences of points of the two supports
  have hK1 : IsCompact (tsupport g) := hgc
  have hK2 : IsCompact (tsupport f) := hfc
  have hKimg : IsCompact ((fun p : Pl × Pl => p.1 - p.2) '' (tsupport g ×ˢ tsupport f)) :=
    (hK1.prod hK2).image (continuous_fst.sub continuous_snd)
  obtain ⟨R, hRpos, hR⟩ := hKimg.isBounded.exists_pos_norm_le
  -- the truncated kernel is integrable
  have hloc : LocallyIntegrable newtonKernel volume := newtonKernelLocInt
  have hNR : Integrable (Set.indicator (Metric.closedBall (0 : Pl) R) newtonKernel) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (hloc.integrableOn_isCompact (isCompact_closedBall _ _))
  -- integrability of `(x, y) ↦ NR(x - y) f(y)` on the product
  have hK : Integrable
      (fun p : Pl × Pl => Set.indicator (Metric.closedBall (0 : Pl) R) newtonKernel
        (p.1 - p.2) * f p.2) (volume.prod volume) := by
    have h := hfint.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hNR
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [ContinuousLinearMap.mul_apply', mul_comm]
  -- integrability of `(x, y) ↦ g(x) N(x - y) f(y)` on the product
  obtain ⟨C, hC⟩ := hgcont.bounded_above_of_compact_support hgc
  have hF : Integrable
      (fun p : Pl × Pl => g p.1 * (Set.indicator (Metric.closedBall (0 : Pl) R) newtonKernel
        (p.1 - p.2) * f p.2)) (volume.prod volume) :=
    hK.bdd_mul (hgcont.comp continuous_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hC _)
  have hI : Integrable (Function.uncurry fun x y : Pl => g x * (newtonKernel (x - y) * f y))
      (volume.prod volume) := by
    refine hF.congr (Filter.Eventually.of_forall fun p => ?_)
    show g p.1 * (Set.indicator (Metric.closedBall (0 : Pl) R) newtonKernel
        (p.1 - p.2) * f p.2) = g p.1 * (newtonKernel (p.1 - p.2) * f p.2)
    rcases eq_or_ne (g p.1) 0 with h1 | h1
    · simp [h1]
    rcases eq_or_ne (f p.2) 0 with h2 | h2
    · simp [h2]
    have hmem : p.1 - p.2 ∈ Metric.closedBall (0 : Pl) R := by
      rw [mem_closedBall_zero_iff]
      exact hR _ ⟨(p.1, p.2), ⟨subset_tsupport _ (Function.mem_support.mpr h1),
        subset_tsupport _ (Function.mem_support.mpr h2)⟩, rfl⟩
    rw [Set.indicator_of_mem hmem]
  -- the three steps of the computation
  have step1 : ∫ x, g x * newtonConv f x = ∫ x, ∫ y, g x * (newtonKernel (x - y) * f y) := by
    congr 1
    funext x
    rw [newtonConv, integral_const_mul]
  have step3 : ∀ y : Pl, ∫ x, g x * (newtonKernel (x - y) * f y) = newtonConv g y * f y := by
    intro y
    rw [newtonConv, ← integral_mul_const]
    congr 1
    funext x
    rw [show x - y = -(y - x) by abel, newtonKernel_neg_arg]
    ring
  calc ∫ x, g x * newtonConv f x
      = ∫ x, ∫ y, g x * (newtonKernel (x - y) * f y) := step1
    _ = ∫ y, ∫ x, g x * (newtonKernel (x - y) * f y) := integral_integral_swap hI
    _ = ∫ y, newtonConv g y * f y := by
        congr 1
        funext y
        exact step3 y
    _ = ∫ x, newtonConv g x * f x := rfl

end UnforcedLeray.Short.IIb.PlaneRiesz
