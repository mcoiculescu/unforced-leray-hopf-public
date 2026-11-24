import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.KernelIntegralMeasurable
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.KernelIntegralBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.KernelDuality

/-!
# Leaf `PartII-b:T12/1/1/2/51`: off-support kernel representation of the planar `L²` Riesz pairs

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

If `f ∈ L²(ℝ²)` vanishes a.e. outside a compact `S`, then for a.e. `x ∉ S`,
`(T_{ik} f)(x) = ∫ K_{ik}(x - y) f(y) dy`.  The proof is the planar analogue of the off-support
representation in `Lib/CZL2/L2OffSupport.lean`: with `f' = 1_S f` and
`Kf x = ∫ K_{ik}(x - y) f'(y) dy`, the difference `T_{ik} f - Kf` is locally integrable on the
open set `Sᶜ` (`kernelIntegralBound`, `kernelIntegralMeasurable`) and has zero integral against
every test supported in `Sᶜ` (`kernelDuality`), hence vanishes a.e. there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/51`.**  Off-support kernel representation of `T_{ik} f` on `L²`. -/
theorem rieszL2OffSupport : RieszL2OffSupport := by
  intro T hT i k f S hS hf
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
  set Kf : Pl → ℝ := fun x => ∫ y, planeRieszKernel i k (x - y) * f' y with hKf
  have hKfeq : ∀ x, (∫ y, planeRieszKernel i k (x - y) * f y) = Kf x := fun x =>
    integral_congr_ae (by filter_upwards [hff'] with y hy; rw [hy])
  have hKfm : StronglyMeasurable Kf := kernelIntegralMeasurable i k f' hf'm
  -- local integrability of `Kf` on `Sᶜ`
  have hKfloc : LocallyIntegrableOn Kf Sᶜ volume := by
    rw [locallyIntegrableOn_iff hS.isClosed.isOpen_compl.isLocallyClosed]
    intro C hCU hC
    obtain ⟨δ, hδ, hsep⟩ := kd_exists_pos_le_norm_sub hC hS
      (Set.subset_compl_iff_disjoint_right.mp hCU)
    refine Measure.integrableOn_of_bounded hC.measure_lt_top.ne hKfm.aestronglyMeasurable
      (M := (δ ^ 2)⁻¹ * ∫ y, |f' y|) ?_
    rw [ae_restrict_iff' hC.measurableSet]
    exact Eventually.of_forall fun x hx =>
      kernelIntegralBound i k f' δ x hf'i hδ fun y hy => hsep x hx y (hf'S y hy)
  -- the duality identity against tests supported in `Sᶜ`
  have key : ∀ g : Pl → ℝ, IsTest g → tsupport g ⊆ Sᶜ →
      Integrable (fun x => g x * Kf x) volume ∧
        ∫ x, g x * T i k f x = ∫ x, g x * Kf x := by
    intro g hg hgS
    obtain ⟨hgint, hid⟩ := kernelDuality T hT i k f S hS hf g hg hgS
    refine ⟨hgint.congr (Eventually.of_forall fun x => congrArg (fun t => g x * t) (hKfeq x)), ?_⟩
    refine hid.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
    exact congrArg (fun t => g x * t) (hKfeq x)
  -- conclude on the open set `Sᶜ`
  have hRloc : LocallyIntegrable (T i k f) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hloc : LocallyIntegrableOn (fun x => T i k f x - Kf x) Sᶜ volume :=
    (hRloc.locallyIntegrableOn _).sub hKfloc
  have hzero := hS.isClosed.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hgd hgc hgS => by
      obtain ⟨hgK, hid⟩ := key g ⟨hgd, hgc⟩ hgS
      have hgR : Integrable (fun x => g x * T i k f x) volume :=
        memLp_one_iff_integrable.mp
          ((Lp.memLp (T i k f)).mul' (hgd.continuous.memLp_of_hasCompactSupport hgc (p := 2)))
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub hgR hgK, hid, sub_self])
  filter_upwards [hzero] with x hx hxS
  rw [hKfeq x]
  exact sub_eq_zero.mp (hx hxS)

end UnforcedLeray.Short.IIb.PlaneRiesz
