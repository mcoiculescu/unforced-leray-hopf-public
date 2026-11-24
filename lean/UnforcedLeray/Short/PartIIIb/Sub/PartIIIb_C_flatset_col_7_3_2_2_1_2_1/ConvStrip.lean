import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2_1
import UnforcedLeray.Lib.HeatCylinder.HeatVecActualContraction
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2ZeroAge
import UnforcedLeray.Lib.HeatCylinder.HeatL2Operator
import UnforcedLeray.Units.B0289.Periodize
import UnforcedLeray.Units.B0284.Contraction

/-!
# `VecConvStripCont` (source `the November 2 reference manuscript` lines 1650-1656)

For a `c`-periodic `Vec`-valued `u` with finite strip mass, the Gaussian convolution
`heatVecConvolution θ u` converges to `u` in strip `L²` as `θ ↓ 0`.

The strip integral is `c` times the normalized-cell integral (`B0224.strip` and `B0284.cell` are the
same set `Ioc 0 c ×ˢ univ`). On the cell the convolution is a.e. the actual quotient
`heatVecL2CLM θ x` of the class `x` of `u` (`HeatCylinder.heatVecL2CLM_value_ae`), and the periodic
lift of `x` agrees with `u` on the whole plane (`B0289.ae_of_ae_cellMeasure`). Conclude with
`HeatCylinder.tendsto_heatVecL2CLM_apply_zero`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

open UnforcedLeray.Train (Vec)

/-- The strip integral of a function on `strip c` is `c` times its normalized-cell integral. -/
theorem vecStrip_lintegral_eq_cellMeasure {c : ℝ} (hc : 0 < c) (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ z in UnforcedLeray.B0224.strip c, f z =
      (c.toNNReal : ℝ≥0∞) * ∫⁻ z, f z ∂(UnforcedLeray.B0284.cellMeasure c) := by
  have hn : c.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hc).ne'
  show ∫⁻ z in UnforcedLeray.B0284.cell c, f z = _
  rw [UnforcedLeray.B0284.cellMeasure, lintegral_smul_measure]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ hn, ENNReal.coe_one, one_mul]

/-- The periodic lift of the class of `u` agrees a.e. with `u` on the whole plane. -/
theorem vecLift_ae_volume {c : ℝ} (hc : 0 < c) {u : ℝ × ℝ → Vec}
    (hpq : UnforcedLeray.B0284.IsQPeriodic c u) (x : Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c))
    (hxu : (x : ℝ × ℝ → Vec) =ᵐ[UnforcedLeray.B0284.cellMeasure c] u) :
    (fun z => UnforcedLeray.Train.toVec (UnforcedLeray.HeatCylinder.planeRep hc
        ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] (ℝ × ℝ)).compLpL 2
          (UnforcedLeray.B0284.cellMeasure c) x) z))
      =ᵐ[volume] u := by
  have hspec := UnforcedLeray.HeatCylinder.planeRep_spec hc
    ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] (ℝ × ℝ)).compLpL 2
      (UnforcedLeray.B0284.cellMeasure c) x)
  have hL := ContinuousLinearMap.coeFn_compLpL
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] (ℝ × ℝ)) x
  have hcoe : ∀ᵐ z ∂(UnforcedLeray.B0284.cellMeasure c),
      UnforcedLeray.Train.toVec (UnforcedLeray.HeatCylinder.planeRep hc
        ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] (ℝ × ℝ)).compLpL 2
          (UnforcedLeray.B0284.cellMeasure c) x) z) = u z := by
    filter_upwards [hspec.2.2, hL, hxu] with z h1 h2 h3
    have h2' : ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] (ℝ × ℝ)).compLpL 2
        (UnforcedLeray.B0284.cellMeasure c) x) z
        = UnforcedLeray.Train.toVecL.symm (x z) := h2
    rw [h1, h2', h3]
    exact UnforcedLeray.Train.toVecL.apply_symm_apply (u z)
  apply UnforcedLeray.B0289.ae_of_ae_cellMeasure hc
    (P := fun z => UnforcedLeray.Train.toVec (UnforcedLeray.HeatCylinder.planeRep hc
        ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] (ℝ × ℝ)).compLpL 2
          (UnforcedLeray.B0284.cellMeasure c) x) z) = u z)
  · intro z
    show (UnforcedLeray.Train.toVec (UnforcedLeray.HeatCylinder.planeRep hc
        ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] (ℝ × ℝ)).compLpL 2
          (UnforcedLeray.B0284.cellMeasure c) x) (z.1 + c, z.2)) = u (z.1 + c, z.2))
      = (UnforcedLeray.Train.toVec (UnforcedLeray.HeatCylinder.planeRep hc
        ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] (ℝ × ℝ)).compLpL 2
          (UnforcedLeray.B0284.cellMeasure c) x) z) = u z)
    rw [hspec.2.1 z, hpq z]
  · exact hcoe

/-- The Gaussian convolution depends only on the a.e. class of its argument, pointwise. -/
theorem heatVecConv_congr_pt {θ : ℝ} {f g : ℝ × ℝ → Vec} (hfg : f =ᵐ[volume] g) (z : ℝ × ℝ) :
    UnforcedLeray.HeatCylinder.heatVecConvolution θ f z =
      UnforcedLeray.HeatCylinder.heatVecConvolution θ g z := by
  unfold UnforcedLeray.HeatCylinder.heatVecConvolution
  have hmap : MeasurePreserving (fun w : ℝ × ℝ => -w + z) volume volume :=
    (measurePreserving_add_right volume z).comp (Measure.measurePreserving_neg volume)
  have hshift : (fun w : ℝ × ℝ => f (z - w)) =ᵐ[volume] fun w => g (z - w) := by
    have h := hmap.quasiMeasurePreserving.ae hfg
    filter_upwards [h] with w hw
    simpa only [sub_eq_add_neg, add_comm] using hw
  apply integral_congr_ae
  filter_upwards [hshift] with w hw
  simp [hw]

/-- The `L²` norm to the power two of an `Lp` element is its lintegral of squared enorms. -/
theorem vecLp_enorm_sq_eq {μ : Measure (ℝ × ℝ)} (f : Lp Vec 2 μ) :
    ‖f‖ₑ ^ 2 = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
  rw [Lp.enorm_def]
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := (f : ℝ × ℝ → Vec)) (μ := μ) (p := 2)
    (by norm_num)
  simpa [ENNReal.rpow_two] using h

theorem vecConvStrip_main {c : ℝ} (hc : 0 < c) {u : ℝ × ℝ → Vec}
    (hpq : UnforcedLeray.B0284.IsQPeriodic c u) (x : Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c))
    (hxu : (x : ℝ × ℝ → Vec) =ᵐ[UnforcedLeray.B0284.cellMeasure c] u) :
    Tendsto (fun θ : ℝ => ∫⁻ z in UnforcedLeray.B0224.strip c,
        ‖UnforcedLeray.HeatCylinder.heatVecConvolution θ u z - u z‖ₑ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hT := UnforcedLeray.HeatCylinder.tendsto_heatVecL2CLM_apply_zero hc x
  have hG : Tendsto (fun θ : ℝ => UnforcedLeray.HeatCylinder.heatVecL2CLM hc θ x - x)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hT.sub_const x
  have hE : Tendsto (fun θ : ℝ => ‖UnforcedLeray.HeatCylinder.heatVecL2CLM hc θ x - x‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun θ : ℝ => ‖UnforcedLeray.HeatCylinder.heatVecL2CLM hc θ x - x‖ₑ)
        (𝓝[>] 0) (𝓝 ‖(0 : Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c))‖ₑ) :=
      (continuous_enorm.tendsto _).comp hG
    simpa using h
  have hP : Tendsto (fun θ : ℝ => ‖UnforcedLeray.HeatCylinder.heatVecL2CLM hc θ x - x‖ₑ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.mul hE (Or.inr ENNReal.zero_ne_top) hE (Or.inr ENNReal.zero_ne_top)
    simpa [sq] using h
  have hEq : (fun θ : ℝ => (c.toNNReal : ℝ≥0∞) *
        ‖UnforcedLeray.HeatCylinder.heatVecL2CLM hc θ x - x‖ₑ ^ 2) =ᶠ[𝓝[>] 0]
      (fun θ : ℝ => ∫⁻ z in UnforcedLeray.B0224.strip c,
        ‖UnforcedLeray.HeatCylinder.heatVecConvolution θ u z - u z‖ₑ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθ' : 0 < θ := hθ
    rw [vecStrip_lintegral_eq_cellMeasure hc, vecLp_enorm_sq_eq]
    congr 1
    apply lintegral_congr_ae
    have hGe := Lp.coeFn_sub (UnforcedLeray.HeatCylinder.heatVecL2CLM hc θ x) x
    have hv : ∀ᵐ z ∂(UnforcedLeray.B0284.cellMeasure c),
        UnforcedLeray.HeatCylinder.heatVecL2CLM hc θ x z =
          UnforcedLeray.HeatCylinder.heatVecConvolution θ u z := by
      filter_upwards [UnforcedLeray.HeatCylinder.heatVecL2CLM_value_ae hc hθ' x] with z hz
      rw [hz]
      exact heatVecConv_congr_pt (vecLift_ae_volume hc hpq x hxu) z
    filter_upwards [hv, hxu, hGe] with z h1 h2 h3
    rw [h3, Pi.sub_apply, h1, h2]
  exact Tendsto.congr' hEq (by simpa using ENNReal.Tendsto.const_mul hP (Or.inr ENNReal.coe_ne_top))

theorem vecConvStripCont_holds (c : ℝ) (hc : 0 < c) :
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.VecConvStripCont c := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.VecConvStripCont
  intro u hm hp hfin
  have hpq : UnforcedLeray.B0284.IsQPeriodic c u := fun z => hp z
  have hn : c.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hc).ne'
  have hlin : ∫⁻ z, ‖u z‖ₑ ^ 2 ∂(UnforcedLeray.B0284.cellMeasure c) < ∞ := by
    rw [vecStrip_lintegral_eq_cellMeasure hc] at hfin
    rcases ENNReal.mul_lt_top_iff.1 hfin with h | h | h
    · exact h.2
    · exact absurd h (ENNReal.coe_ne_zero.2 hn)
    · rw [h]
      exact ENNReal.zero_lt_top
  have hMem : MemLp u 2 (UnforcedLeray.B0284.cellMeasure c) := by
    refine ⟨hm.aestronglyMeasurable.mono_ac (UnforcedLeray.B0284.cellMeasure_ac c), ?_⟩
    exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)).2
      (by simpa [ENNReal.rpow_two] using hlin)
  exact vecConvStrip_main hc hpq (hMem.toLp u) hMem.coeFn_toLp

end UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong
