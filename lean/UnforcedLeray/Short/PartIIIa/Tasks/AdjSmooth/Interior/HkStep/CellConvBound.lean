import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellPeriodicLocInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellShiftBound
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import UnforcedLeray.Units.B0284.Contraction

/-!
# `PartIII-a:T21/2/7/2/1/1/5/4`: weighted Young inequality for periodic fields

Source of record: `the November 2 reference manuscript` (SP), lines 3044-3047.

Proof: write `K ⋆ f (x) = ∫ K(z) f(x - z) dz`, bound its norm pointwise by `∫ |K(z)| |f(x - z)|`,
apply Minkowski's integral inequality (lintegral form, `NonUniqueEuler.Conv.eLpNorm_lintegral_le`)
in `L²(cellMeasure c (-m))`, and bound each translate with `cellShiftBound` (`‖z‖ ≤ 1`; for
`‖z‖ > 1` the kernel vanishes). The constant is `C := C'` from `cellShiftBound c m hc`.
Measurability: `K ⋆ f` is continuous (`HasCompactSupport.continuous_convolution_left`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

lemma ccb_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num

/-- A continuous real kernel vanishing outside the closed unit ball has compact support. -/
theorem ccb_hasCompactSupport {K : ℝ × ℝ → ℝ}
    (hKsupp : ∀ y : ℝ × ℝ, 1 < ‖y‖ → K y = 0) : HasCompactSupport K := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) 1) (fun y hy => hKsupp y ?_)
  exact not_le.mp (fun h => hy (mem_closedBall_zero_iff.2 h))

/-- **Weighted Young inequality for periodic fields** (SP 3044-3047). -/
theorem cellConvBound : UnforcedLeray.Short.IIIa.CellConvBound := by
  intro c m hc
  obtain ⟨C', hC'0, hC'⟩ := cellShiftBound c m hc
  refine ⟨C', hC'0, fun K f hKc hKsupp hper hf => ?_⟩
  have : SigmaFinite (B0579.cellMeasure c (-m)) := by
    unfold B0579.cellMeasure; infer_instance
  set μ : Measure (ℝ × ℝ) := B0579.cellMeasure c (-m) with hμ
  have hloc : LocallyIntegrable f volume := (cellPeriodicLocInt c m f hc hper hf).2
  have hfaesm : AEStronglyMeasurable f volume := (cellPeriodicLocInt c m f hc hper hf).1
  have hKcs : HasCompactSupport K := ccb_hasCompactSupport hKsupp
  have hKint : Integrable K volume := hKc.integrable_of_hasCompactSupport hKcs
  have hM : ENNReal.ofReal (∫ y, |K y|) = ∫⁻ y, ‖K y‖ₑ := by
    have h := ofReal_integral_norm_eq_lintegral_enorm hKint
    simpa only [Real.norm_eq_abs] using h
  have hconv_meas : Measurable (fun z : ℝ × ℝ => ‖K z‖ₑ) := hKc.enorm.measurable
  -- measurability of `(x, z) ↦ ‖K z‖ₑ * ‖f (x - z)‖ₑ` for the product `μ ⊗ volume`
  have hac : μ.prod (volume : Measure (ℝ × ℝ)) ≪ (volume : Measure (ℝ × ℝ)).prod volume :=
    ((B0579.cellMeasure_ac c (-m)).prod Measure.AbsolutelyContinuous.rfl).trans
      ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
        Measure.AbsolutelyContinuous.rfl)
  have hsub : AEStronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => f (q.1 - q.2))
      ((volume : Measure (ℝ × ℝ)).prod volume) :=
    hfaesm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (ℝ × ℝ)) volume)
  have hF : AEMeasurable (Function.uncurry fun x z : ℝ × ℝ => ‖K z‖ₑ * ‖f (x - z)‖ₑ)
      (μ.prod (volume : Measure (ℝ × ℝ))) := by
    have h1 : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ‖f (q.1 - q.2)‖ₑ)
        (μ.prod (volume : Measure (ℝ × ℝ))) :=
      (hsub.enorm).mono_ac hac
    exact (hconv_meas.comp measurable_snd).aemeasurable.mul h1
  -- pointwise: the norm of the convolution is bounded by the convolution of the norms
  have hpt : ∀ x : ℝ × ℝ, ‖cellConv K f x‖ₑ ≤ ‖∫⁻ z, ‖K z‖ₑ * ‖f (x - z)‖ₑ‖ₑ := by
    intro x
    rw [enorm_eq_self]
    unfold cellConv
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun z => ?_))
    exact enorm_smul _ _
  have hstep1 : eLpNorm (cellConv K f) 2 μ ≤
      eLpNorm (fun x => ∫⁻ z, ‖K z‖ₑ * ‖f (x - z)‖ₑ) 2 μ :=
    eLpNorm_mono_enorm hpt
  -- Minkowski's integral inequality in `L²(μ)`
  have hstep2 : eLpNorm (fun x => ∫⁻ z, ‖K z‖ₑ * ‖f (x - z)‖ₑ) 2 μ ≤
      ∫⁻ z, eLpNorm (fun x => ‖K z‖ₑ * ‖f (x - z)‖ₑ) 2 μ :=
    NonUniqueEuler.Conv.eLpNorm_lintegral_le hF (by norm_num) ccb_two_ne_top
  -- each translate: the kernel vanishes off the unit ball; otherwise `cellShiftBound`
  have hstep3 : ∀ z : ℝ × ℝ, eLpNorm (fun x => ‖K z‖ₑ * ‖f (x - z)‖ₑ) 2 μ ≤
      ‖K z‖ₑ * (ENNReal.ofReal C' * eLpNorm f 2 μ) := by
    intro z
    rw [UnforcedLeray.B0284.eLpNorm_const_mul_ennreal (enorm_ne_top) (fun x => ‖f (x - z)‖ₑ) two_ne_zero
      ccb_two_ne_top]
    by_cases hz : 1 < ‖z‖
    · rw [hKsupp z hz, enorm_zero, zero_mul]
      exact zero_le
    · push Not at hz
      have hmem := hC' f z hper hf hz
      rw [eLpNorm_enorm (fun x => f (x - z))]
      exact mul_le_mul_of_nonneg_left hmem.2 zero_le
  have hstep4 : ∫⁻ z, eLpNorm (fun x => ‖K z‖ₑ * ‖f (x - z)‖ₑ) 2 μ ≤
      (∫⁻ z, ‖K z‖ₑ) * (ENNReal.ofReal C' * eLpNorm f 2 μ) :=
    (lintegral_mono hstep3).trans_eq (lintegral_mul_const _ hconv_meas)
  have hbound : eLpNorm (cellConv K f) 2 μ ≤
      ENNReal.ofReal (C' * ∫ y, |K y|) * eLpNorm f 2 μ := by
    refine hstep1.trans (hstep2.trans hstep4) |>.trans_eq ?_
    rw [ENNReal.ofReal_mul hC'0, hM]
    ring
  -- continuity of the convolution gives measurability
  have hcont : Continuous (cellConv K f) := by
    rw [cellConv_eq_convolution]
    exact hKcs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hKc hloc
  have hmem : MemLp (cellConv K f) 2 μ :=
    ⟨hcont.aestronglyMeasurable,
      lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)⟩
  refine ⟨hmem, ?_⟩
  unfold xNorm
  exact hbound

end UnforcedLeray.Short.IIIa
