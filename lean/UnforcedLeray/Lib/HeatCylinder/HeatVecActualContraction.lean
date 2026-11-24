import UnforcedLeray.Lib.HeatCylinder.HeatVecConvolution

/-!
# Contraction of the actual quotient vector heat operator

This identifies the conjugated B0284 quotient operator with its literal Euclidean-vector
Gaussian integral and transfers the direct vector-kernel contraction to the operator.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)

private theorem memLp_planeHeat_for_vector {c θ : ℝ} (hc : 0 < c)
    {f : Plane → Plane} (hf : Measurable f) (hper : IsQPeriodic c f)
    (hmem : MemLp f 2 (cellMeasure c)) :
    MemLp (UnforcedLeray.B0284.heat θ f) 2 (cellMeasure c) := by
  refine ⟨UnforcedLeray.B0296.aestronglyMeasurable_heat c θ hf.aestronglyMeasurable, ?_⟩
  have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := θ) hc hper
    hf.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
  exact lt_of_le_of_lt hcontract hmem.eLpNorm_ne_top.lt_top

private theorem ae_heatKernelPlane_integrable {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {f : Plane → Plane} (hf : AEStronglyMeasurable f volume)
    (hper : IsQPeriodic c f) (hmem : MemLp f 2 (cellMeasure c)) :
    ∀ᵐ z ∂(cellMeasure c),
      Integrable (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w • f (z - w)) := by
  let k : Plane → ℝ≥0∞ := fun w => ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w)
  have hk : Measurable k := ENNReal.measurable_ofReal.comp
    (UnforcedLeray.B0284.measurable_heatKernel2_right θ)
  have hk' : ∀ w, k w ≠ ⊤ := fun w => ENNReal.ofReal_ne_top
  have hmass : ∫⁻ w : Plane, k w = 1 := by
    dsimp [k]
    exact UnforcedLeray.B0284.lintegral_heatKernel2 hθ
  have hfin := UnforcedLeray.B0296.ae_kernelAbs_lt_top' hc hk hk'
    (by rw [hmass]; exact ENNReal.one_ne_top) hper hf
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmem.eLpNorm_ne_top
  filter_upwards [hfin] with z hz
  have hA : ∀ w x : Plane,
      ‖UnforcedLeray.B0284.heatKernel2 θ w • x‖ₑ ≤ k w * ‖x‖ₑ := by
    intro w x
    rw [enorm_smul, Real.enorm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
  have hmeas : AEStronglyMeasurable
      (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w • f (z - w)) volume := by
    exact (UnforcedLeray.B0284.measurable_heatKernel2_right θ).aestronglyMeasurable.smul
      (UnforcedLeray.B0296.aestronglyMeasurable_comp_sub_left hf z)
  exact UnforcedLeray.B0296.integrable_kconv_of_lt_top
    (A := fun w x : Plane => UnforcedLeray.B0284.heatKernel2 θ w • x)
    hA z hmeas hz

private theorem heatL2_value_ae_for_vector {c θ : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    (heatL2 hc θ x : Plane → Plane) =ᵐ[cellMeasure c]
      UnforcedLeray.B0284.heat θ (planeRep hc x) := by
  let f := planeRep hc x
  have hf := planeRep_spec hc x
  have hm := memLp_planeRep hc x
  have hh := memLp_planeHeat_for_vector (θ := θ) hc hf.1 hf.2.1 hm
  change (hh.toLp (UnforcedLeray.B0284.heat θ f) : Plane → Plane) =ᵐ[
    cellMeasure c] UnforcedLeray.B0284.heat θ f
  exact hh.coeFn_toLp

private theorem toVec_heat_integral {θ : ℝ} (hθ : 0 < θ) {f : Plane → Plane}
    {z : Plane} (hint : Integrable
      (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w • f (z - w))) :
    UnforcedLeray.Train.toVec (∫ w : Plane,
      UnforcedLeray.B0284.heatKernel2 θ w • f (z - w)) =
      ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w •
        UnforcedLeray.Train.toVec (f (z - w)) := by
  calc
    UnforcedLeray.Train.toVec (∫ w : Plane,
        UnforcedLeray.B0284.heatKernel2 θ w • f (z - w)) =
      ∫ w : Plane, UnforcedLeray.Train.toVec
        (UnforcedLeray.B0284.heatKernel2 θ w • f (z - w)) :=
      (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).integral_comp_comm hint |>.symm
    _ = ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w •
        UnforcedLeray.Train.toVec (f (z - w)) := by
      congr 1
      funext w
      exact map_smul _ _ _

/-- The conjugated quotient operator has the literal Gaussian-vector convolution value almost
 everywhere on the normalized cell. -/
theorem heatVecL2CLM_value_ae {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : Lp Vec 2 (cellMeasure c)) :
    (heatVecL2CLM hc θ x : Plane → Vec) =ᵐ[cellMeasure c]
      heatVecConvolution θ (fun z => UnforcedLeray.Train.toVec
        (planeRep hc ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
          2 (cellMeasure c) x) z)) := by
  let xP : Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c) x
  let f : Plane → Plane := planeRep hc xP
  let g : Plane → Vec := fun z => UnforcedLeray.Train.toVec (f z)
  have hf := planeRep_spec hc xP
  have hm := memLp_planeRep hc xP
  have hInt := ae_heatKernelPlane_integrable hc hθ hf.1.aestronglyMeasurable hf.2.1 hm
  have hOut := heatL2_value_ae_for_vector (θ := θ) hc xP
  have hA := (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).coeFn_compLpL
    (p := (2 : ℝ≥0∞)) (μ := cellMeasure c) (heatL2CLM hc θ xP)
  filter_upwards [hInt, hOut, hA] with z hzInt hzOut hzA
  have hHeat : UnforcedLeray.B0284.heat θ f z =
      ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w • f (z - w) :=
    UnforcedLeray.B0284.heat_apply_of_pos hθ f z
  have hzOut : (heatL2 hc θ xP : Plane → Plane) z =
      UnforcedLeray.B0284.heat θ f z := by
    exact hzOut
  calc
    (heatVecL2CLM hc θ x : Plane → Vec) z =
        UnforcedLeray.Train.toVec ((heatL2CLM hc θ xP : Lp Plane 2 (cellMeasure c)) z) := by
      simpa [xP, heatVecL2CLM_apply] using hzA
    _ = UnforcedLeray.Train.toVec (heatL2 hc θ xP z) := by
      rw [UnforcedLeray.HeatCylinder.heatL2CLM_apply]
    _ = UnforcedLeray.Train.toVec (UnforcedLeray.B0284.heat θ f z) := by rw [hzOut]
    _ = heatVecConvolution θ g z := by
      rw [heatVecConvolution, hHeat]
      exact toVec_heat_integral hθ hzInt

/-- The actual Euclidean-vector quotient heat is contractive in normalized-cell `L²` for
positive ages. -/
theorem norm_heatVecL2CLM_le_one_of_pos {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    ‖heatVecL2CLM hc θ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  let xP : Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c) x
  let f : Plane → Vec := fun z => UnforcedLeray.Train.toVec
    (planeRep hc xP z)
  have hfmeas : AEStronglyMeasurable f volume := by
    exact Continuous.comp_aestronglyMeasurable
      (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).continuous
      (planeRep_spec hc xP).1.aestronglyMeasurable
  have hfper : IsQPeriodic c f := by
    intro z
    change UnforcedLeray.Train.toVec (planeRep hc xP (z.1 + c, z.2)) =
      UnforcedLeray.Train.toVec (planeRep hc xP z)
    exact congrArg UnforcedLeray.Train.toVec ((planeRep_spec hc xP).2.1 z)
  have hfx : f =ᵐ[cellMeasure c] (x : Plane → Vec) := by
    have hrep := (planeRep_spec hc xP).2.2
    have hC := (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).coeFn_compLpL
      (p := (2 : ℝ≥0∞)) (μ := cellMeasure c) x
    filter_upwards [hrep, hC] with z hzrep hzC
    change UnforcedLeray.Train.toVec (planeRep hc xP z) = x z
    calc
      UnforcedLeray.Train.toVec (planeRep hc xP z) =
          UnforcedLeray.Train.toVec (xP z) := congrArg UnforcedLeray.Train.toVec hzrep
      _ = UnforcedLeray.Train.toVec (UnforcedLeray.Train.toVecL.symm (x z)) :=
        congrArg UnforcedLeray.Train.toVec hzC
      _ = x z := UnforcedLeray.Train.toVecL.apply_symm_apply (x z)
  have hcontract := eLpNorm_heatVecConvolution_le hc hθ hfper hfmeas
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
  have hOut := heatVecL2CLM_value_ae hc hθ x
  have hOut' : (heatVecL2CLM hc θ x : Plane → Vec) =ᵐ[cellMeasure c]
      heatVecConvolution θ f := by
    simpa only [f, xP] using hOut
  simp only [one_mul]
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top x)
  calc
    eLpNorm (heatVecL2CLM hc θ x : Plane → Vec) 2 (cellMeasure c) ≤
        eLpNorm (heatVecConvolution θ f) 2 (cellMeasure c) := by
      rw [eLpNorm_congr_ae hOut']
    _ ≤ eLpNorm f 2 (cellMeasure c) := hcontract
    _ = eLpNorm (x : Plane → Vec) 2 (cellMeasure c) := eLpNorm_congr_ae hfx

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecL2CLM_value_ae
#print axioms UnforcedLeray.HeatCylinder.norm_heatVecL2CLM_le_one_of_pos
