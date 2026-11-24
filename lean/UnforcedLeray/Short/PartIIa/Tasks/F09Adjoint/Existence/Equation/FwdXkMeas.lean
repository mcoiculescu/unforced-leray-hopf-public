import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1_1

/-!
# Part II-a, task `PartII-a:F09/1/3/1/1/2`: measurability of the forward slice remainder

Source `the November 2 reference manuscript`, lines 1403-1413, 1426-1428.
Proves `FwdXkMeas`: for a smooth phase test `Φ`, the map `y ↦ fwdXk ν s K t Φ y` is measurable.
Mirror of `SliceCalc.measurable_Xk` (Tasks/F02BodyResolventEquation/SliceTaylor/Bounds.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- The forward generator of a smooth spatial field is continuous. -/
theorem fwdMeas_continuous_fwdGen (ν : ℝ) {u : SpatialField} (hu : ContDiff ℝ ∞ u) :
    Continuous (fwdGen ν u) := by
  unfold fwdGen
  have hcL : Continuous (UnforcedLeray.B0418.vecLaplacian u) :=
    UnforcedLeray.B0418.continuous_vecLaplacian hu
  have hcD : Continuous (fun y : Space => fderiv ℝ u y y) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_id
  have hc1 : Continuous (fun y : Space => ν • UnforcedLeray.B0418.vecLaplacian u y) :=
    hcL.const_smul ν
  have hc2 : Continuous (fun y : Space => (1 / 2 : ℝ) • fderiv ℝ u y y) :=
    hcD.const_smul (1 / 2 : ℝ)
  have hc3 : Continuous (fun y : Space => (1 / 2 : ℝ) • u y) :=
    hu.continuous.const_smul (1 / 2 : ℝ)
  exact (hc1.add hc2).add hc3

/-- The forward free evolution of a continuous field is measurable. -/
theorem fwdMeas_measurable_freeEvolution {u : SpatialField} (hu : Continuous u) (ν s : ℝ) :
    Measurable (AncientLocalization.freeEvolution ν s u) := by
  have h1 := UnforcedLeray.B0418.measurable_flow_uncurry hu
  have h2 : Measurable (fun y : Space =>
      (AncientLocalization.similarityDilation s • y, ν * (Real.exp s - 1))) :=
    (measurable_const_smul _).prodMk measurable_const
  have h3 : Measurable (fun y : Space =>
      UnforcedLeray.Heat.flow u (ν * (Real.exp s - 1))
        (AncientLocalization.similarityDilation s • y)) :=
    h1.comp h2
  unfold AncientLocalization.freeEvolution SpatialScaling.spatialScale
  exact h3.const_smul (AncientLocalization.similarityDilation s)

/-- **Measurability of the forward remainder** (task `PartII-a:F09/1/3/1/1/2`). -/
theorem fwdXkMeas : FwdXkMeas := by
  intro ν s K t Φ hΦ
  have hu : ContDiff ℝ ∞ (fun z : Space => K (Φ (t, z))) :=
    K.contDiff.comp (hΦ.comp (contDiff_const.prodMk contDiff_id))
  have hcu : Continuous (fun z : Space => K (Φ (t, z))) := hu.continuous
  have h1 := fwdMeas_measurable_freeEvolution hcu ν s
  have h2 : Measurable (fun y : Space => K (Φ (t, y))) := hcu.measurable
  have h3 : Measurable (fun y : Space => s • fwdGen ν (fun z => K (Φ (t, z))) y) :=
    (fwdMeas_continuous_fwdGen ν hu).measurable.const_smul s
  unfold fwdXk
  exact (h1.sub h2).sub h3

end UnforcedLeray.Short.PartIIa
