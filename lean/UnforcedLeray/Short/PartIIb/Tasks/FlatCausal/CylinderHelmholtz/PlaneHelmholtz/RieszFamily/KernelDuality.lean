import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.KernelDuality.Helpers
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneRieszKernelSymmNeg
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszL2Transpose
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestOffSupport
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Leaf `PartII-b:T12/1/1/2/49`: duality for the planar kernel representation

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For `f ∈ L²` vanishing a.e. off a compact `S` and a test `g` with `tsupport g ⊆ Sᶜ`,
`∫ g · S_{ik} f = ∫ g(x) ∫ K_{ik}(x - y) f(y) dy dx`.  The proof is the planar analogue of the
duality block in `Lib/CZL2/L2OffSupport.lean`: transpose `T_{ik}` against the test `g`
(`rieszL2Transpose`), identify `T_{ki} g` with the test-level `S_{ki} g` (`rieszTestMemLp`),
use the kernel representation off the support of `g` (`rieszTestOffSupport`) with the symmetry
`K_{ki}(-z) = K_{ik}(z)`, and finish with Fubini (`kd_fubini_integrable`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/49`.**  Duality for the kernel representation of the `L²` Riesz
pairs off a compact support. -/
theorem kernelDuality : KernelDuality := by
  intro T hT i k f S hS hf g hg hgS
  obtain ⟨hgc, hgs⟩ := id hg
  have hgcont : Continuous g := hgc.continuous
  have hgi : Integrable g volume := hgcont.integrable_of_hasCompactSupport hgs
  have hgmem : MemLp g 2 volume := hgcont.memLp_of_hasCompactSupport hgs
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  set f' : Pl → ℝ := S.indicator (fun y => f y) with hf'def
  have hff' : (fun y => f y) =ᵐ[volume] f' := by
    filter_upwards [hf] with y hy
    by_cases hyS : y ∈ S
    · rw [hf'def, indicator_of_mem hyS]
    · rw [hf'def, indicator_of_notMem hyS, hy hyS]
  have hf'S : ∀ y, f' y ≠ 0 → y ∈ S := fun y hy => Set.mem_of_indicator_ne_zero hy
  have hf'i : Integrable f' volume := by
    rw [hf'def, integrable_indicator_iff hSm]
    exact ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hS
  have hf'm : StronglyMeasurable f' := (Lp.stronglyMeasurable f).indicator hSm
  obtain ⟨δ, hδ, hsep⟩ := kd_exists_pos_le_norm_sub hgs.isCompact hS
    (Set.subset_compl_iff_disjoint_right.mp hgS)
  have hint := kd_fubini_integrable i k hδ hgi hgcont hf'i hf'm hsep hf'S
  -- the kernel integral against `f'` and its agreement with the one against `f`
  have hrow : ∀ x, ∫ y, planeRieszKernel i k (x - y) * g x * f' y =
      g x * ∫ y, planeRieszKernel i k (x - y) * f' y := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    ring
  have hKfeq : ∀ x, ∫ y, planeRieszKernel i k (x - y) * f y =
      ∫ y, planeRieszKernel i k (x - y) * f' y := by
    intro x
    refine integral_congr_ae ?_
    filter_upwards [hff'] with y hy
    beta_reduce at hy ⊢
    rw [hy]
  have hgK : Integrable (fun x => g x * ∫ y, planeRieszKernel i k (x - y) * f' y) volume :=
    hint.integral_prod_left.congr (Eventually.of_forall fun x => hrow x)
  -- transposition of `T_{ik}` against `g`, and identification of `T_{ki} g`
  have hG : ∫ x, g x * T i k f x = ∫ x, T i k f x * (hgmem.toLp g) x := by
    refine integral_congr_ae ?_
    filter_upwards [hgmem.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  have hT1 : ∫ x, T i k f x * (hgmem.toLp g) x = ∫ x, f x * T k i (hgmem.toLp g) x :=
    rieszL2Transpose T hT i k f (hgmem.toLp g)
  have hTG : T k i (hgmem.toLp g) = (rieszTestMemLp k i g hg).toLp (rieszTest k i g) :=
    hT k i g hg hgmem (rieszTestMemLp k i g hg)
  have hA : ∫ x, f x * T k i (hgmem.toLp g) x = ∫ y, f' y * rieszTest k i g y := by
    rw [hTG]
    refine integral_congr_ae ?_
    filter_upwards [(rieszTestMemLp k i g hg).coeFn_toLp, hff'] with y h1 h2
    beta_reduce at h2
    rw [h1, h2]
  -- off the support of `g`, the kernel representation and the symmetry of `K`
  have hB : ∀ y, f' y * rieszTest k i g y =
      (∫ x, planeRieszKernel i k (x - y) * g x) * f' y := by
    intro y
    by_cases hy : f' y = 0
    · simp [hy]
    · have hyg : y ∉ tsupport g := fun h => hgS h (hf'S y hy)
      have hR : rieszTest k i g y = ∫ x, planeRieszKernel k i (y - x) * g x :=
        rieszTestOffSupport k i g hg y hyg
      have hI : (∫ x, planeRieszKernel k i (y - x) * g x) =
          ∫ x, planeRieszKernel i k (x - y) * g x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        have hs : planeRieszKernel k i (-(x - y)) = planeRieszKernel i k (x - y) :=
          planeRieszKernelSymmNeg i k (x - y)
        beta_reduce
        rw [show y - x = -(x - y) by abel, hs]
      rw [hR, hI, mul_comm (f' y)]
  -- the chain of equalities, closed by Fubini
  have hfin : ∫ x, g x * T i k f x = ∫ x, g x * ∫ y, planeRieszKernel i k (x - y) * f' y := by
    calc ∫ x, g x * T i k f x = ∫ x, T i k f x * (hgmem.toLp g) x := hG
      _ = ∫ x, f x * T k i (hgmem.toLp g) x := hT1
      _ = ∫ y, f' y * rieszTest k i g y := hA
      _ = ∫ y, (∫ x, planeRieszKernel i k (x - y) * g x) * f' y :=
          integral_congr_ae (Eventually.of_forall hB)
      _ = ∫ y, ∫ x, planeRieszKernel i k (x - y) * g x * f' y := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [integral_mul_const]
      _ = ∫ x, ∫ y, planeRieszKernel i k (x - y) * g x * f' y :=
          (integral_integral_swap hint).symm
      _ = ∫ x, g x * ∫ y, planeRieszKernel i k (x - y) * f' y :=
          integral_congr_ae (Eventually.of_forall hrow)
  refine ⟨hgK.congr (Eventually.of_forall fun x => congrArg (fun t => g x * t) (hKfeq x).symm), ?_⟩
  exact hfin.trans
    (integral_congr_ae (Eventually.of_forall fun x => congrArg (fun t => g x * t) (hKfeq x).symm))

end UnforcedLeray.Short.IIb.PlaneRiesz
