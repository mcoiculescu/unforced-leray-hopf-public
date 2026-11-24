import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep.Transpose
import UnforcedLeray.Lib.PhaseTrace.Lift
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedFieldRepMinimalAE
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Localization on `ℝ × ℝ³` (helper of `PartII-b:S3/1/1/2/1/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523.

* `locallyIntegrable_rep`: the joint representative of `f ∈ Y_q` is locally integrable on
  `ℝ × ℝ³`;
* `ae_eq_zero_of_test`: a locally integrable field whose iterated pairings with all smooth
  compactly supported tests vanish is zero almost everywhere;
* `iterated_identity_of_hasPhaseOp`: `T₀w = b` in distributions, unfolded on compactly supported
  tests as iterated integrals of the joint representatives.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb.BaseRepSub

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.BochnerTime UnforcedLeray.RieszLp

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-! ## 1. Local integrability of the joint representative -/

theorem integral_norm_ball_rep_le (f : Yq P q) (R t : ℝ) :
    ∫ y in Metric.closedBall (0 : Space) R, ‖rep f t y‖ ≤
      (volume (Metric.closedBall (0 : Space) R) ^ (1 - q.toReal⁻¹)).toReal *
        ‖f (t : AddCircle P)‖ := by
  set μB : Measure Space := volume.restrict (Metric.closedBall (0 : Space) R) with hμB
  haveI : IsFiniteMeasure μB := isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hslice : (fun y => rep f t y) =ᵐ[volume] (f (t : AddCircle P) : Space → CVec3) :=
    rep_slice f t
  have hm : MemLp (fun y => rep f t y) q μB :=
    ((Lp.memLp (f (t : AddCircle P))).ae_eq hslice.symm).restrict _
  have hint : Integrable (fun y => rep f t y) μB := hm.integrable hq.out
  have h1 : eLpNorm (fun y => rep f t y) 1 μB ≤
      eLpNorm (fun y => rep f t y) q μB * μB univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / q.toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq.out hm.1
  have h2 : eLpNorm (fun y => rep f t y) q μB ≤ ‖f (t : AddCircle P)‖ₑ := by
    calc eLpNorm (fun y => rep f t y) q μB ≤ eLpNorm (fun y => rep f t y) q volume :=
          eLpNorm_restrict_le _ _ _ _
      _ = eLpNorm (f (t : AddCircle P) : Space → CVec3) q volume := eLpNorm_congr_ae hslice
      _ = ‖f (t : AddCircle P)‖ₑ := (Lp.enorm_def _).symm
  have hμ : μB univ = volume (Metric.closedBall (0 : Space) R) := by
    rw [hμB, Measure.restrict_apply_univ]
  have hfin : volume (Metric.closedBall (0 : Space) R) ^ (1 - q.toReal⁻¹) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by
      have h1q : 1 ≤ q.toReal ∨ q = ⊤ := by
        rcases eq_or_ne q ⊤ with h | h
        · exact Or.inr h
        · exact Or.inl (by
            have := ENNReal.toReal_mono h hq.out
            simpa using this)
      rcases h1q with h | h
      · have : q.toReal⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
        linarith
      · simp [h]) measure_closedBall_lt_top.ne
  rw [integral_norm_eq_lintegral_enorm hint.1]
  rw [← eLpNorm_one_eq_lintegral_enorm]
  have h3 : eLpNorm (fun y => rep f t y) 1 μB ≤
      ‖f (t : AddCircle P)‖ₑ * volume (Metric.closedBall (0 : Space) R) ^ (1 - q.toReal⁻¹) := by
    refine h1.trans ?_
    rw [hμ]
    simp only [ENNReal.toReal_one, div_one, one_div]
    gcongr
  calc (eLpNorm (fun y => rep f t y) 1 μB).toReal
      ≤ (‖f (t : AddCircle P)‖ₑ * volume (Metric.closedBall (0 : Space) R) ^
          (1 - q.toReal⁻¹)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hfin) h3
    _ = (volume (Metric.closedBall (0 : Space) R) ^ (1 - q.toReal⁻¹)).toReal *
          ‖f (t : AddCircle P)‖ := by
        rw [ENNReal.toReal_mul, toReal_enorm, mul_comm]

theorem integrableOn_box_rep (f : Yq P q) (a b R : ℝ) :
    IntegrableOn (fun x : ℝ × Space => rep f x.1 x.2) (Icc a b ×ˢ Metric.closedBall (0 : Space) R)
      volume := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hmeas : AEStronglyMeasurable (fun x : ℝ × Space => rep f x.1 x.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Metric.closedBall (0 : Space) R))) :=
    (stronglyMeasurable_rep f).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).2 ⟨Eventually.of_forall fun t => ?_, ?_⟩
  · have hm : MemLp (fun y => rep f t y) q (volume.restrict (Metric.closedBall (0 : Space) R)) :=
      ((Lp.memLp (f (t : AddCircle P))).ae_eq (rep_slice f t).symm).restrict _
    exact hm.integrable hq.out
  · set C : ℝ := (volume (Metric.closedBall (0 : Space) R) ^ (1 - q.toReal⁻¹)).toReal
    have hg : IntegrableOn (fun t : ℝ => C * ‖f (t : AddCircle P)‖) (Icc a b) volume := by
      rcases le_or_gt a b with hab | hab
      · have h1 := (intervalIntegrable_comp_mk f a b).norm.const_mul C
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at h1
        exact h1
      · rw [Icc_eq_empty (not_le.2 hab)]
        exact integrableOn_empty
    refine Integrable.mono' hg ?_ (Eventually.of_forall fun t => ?_)
    · exact ((stronglyMeasurable_rep f).norm.integral_prod_right'
        (ν := volume.restrict (Metric.closedBall (0 : Space) R))).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      exact integral_norm_ball_rep_le f R t

theorem locallyIntegrable_rep (f : Yq P q) :
    LocallyIntegrable (fun x : ℝ × Space => rep f x.1 x.2) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × Space)
  refine (integrableOn_box_rep f (-R) R R).mono_set fun x hx => ?_
  have hx' := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx'
  refine ⟨?_, ?_⟩
  · have := (norm_fst_le x).trans hx'
    rw [Real.norm_eq_abs] at this
    exact abs_le.1 this
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_snd_le x).trans hx'

/-! ## 2. Localization -/

/-- A locally integrable field on `ℝ × ℝ³` whose iterated pairings with all smooth compactly
supported tests vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_test {D : ℝ × Space → CVec3} (hD : LocallyIntegrable D volume)
    (h : ∀ K : ℝ × Space → CVec3, ContDiff ℝ ∞ K → HasCompactSupport K →
      ∫ t, ∫ y, dotL (K (t, y)) (D (t, y)) = 0) :
    ∀ᵐ x ∂volume, D x = 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hD fun g hg hgc => ?_
  ext i
  have hK : ContDiff ℝ ∞ (fun x => (g x : ℂ) • (EuclideanSpace.single i (1 : ℂ) : CVec3)) :=
    (Complex.ofRealCLM.contDiff.comp hg).smul contDiff_const
  have hKc : HasCompactSupport (fun x => (g x : ℂ) • (EuclideanSpace.single i (1 : ℂ) : CVec3)) :=
    (hgc.comp_left Complex.ofReal_zero).smul_right
  have h0 := h _ hK hKc
  have hint : Integrable (fun x : ℝ × Space => g x • D x) volume :=
    hD.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
  have hint' : Integrable (fun x : ℝ × Space =>
      dotL ((g x : ℂ) • (EuclideanSpace.single i (1 : ℂ) : CVec3)) (D x)) volume := by
    refine ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ |>.integrable_comp hint).congr
      (Eventually.of_forall fun x => ?_)
    simp [dotL_apply, Pi.single_apply, Finset.sum_ite_eq']
  have hprod : ∫ x, dotL ((g x : ℂ) • (EuclideanSpace.single i (1 : ℂ) : CVec3)) (D x) ∂volume = 0 := by
    rw [Measure.volume_eq_prod] at hint' ⊢
    rw [integral_prod _ hint']
    exact h0
  have hcomp : (∫ x, g x • D x ∂volume) i =
      ∫ x, dotL ((g x : ℂ) • (EuclideanSpace.single i (1 : ℂ) : CVec3)) (D x) ∂volume := by
    have := ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).integral_comp_comm hint
    simp only [ContinuousLinearMap.coe_restrictScalars'] at this
    rw [show (∫ x, g x • D x ∂volume) i =
      (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ) (∫ x, g x • D x ∂volume) from rfl, ← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [dotL_apply, Pi.single_apply, Finset.sum_ite_eq']
  rw [hcomp, hprod]
  simp

/-! ## 3. The distributional identity, unfolded -/

theorem iterated_identity_of_hasPhaseOp {w b : Yq P q} (hwb : HasPhaseOp driftT w b)
    {K : ℝ × Space → CVec3} (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) :
    ∫ t, ∫ y, dotL (driftT K (t, y)) (rep w t y) = ∫ t, ∫ y, dotL (K (t, y)) (rep b t y) := by
  have hK0 := isPhaseTest_zero_of_compact hK hKc
  obtain ⟨R, hR0, hT⟩ := exists_timeSupp_of_compact hKc
  have hKd0 : IsPhaseTest 0 (driftT K) := hK0.driftT
  have hTd : TimeSupp (-R) R (driftT K) := timeSupp_driftT hT
  have hΦ := isPhaseTest_perT hP.out hT hK0
  have h := hwb _ hΦ
  rw [driftT_perT hP.out hT hK, phasePair_perT hKd0 (by linarith) hTd,
    phasePair_perT hK0 (by linarith) hT] at h
  have hP0 : (P⁻¹ : ℝ) ≠ 0 := inv_ne_zero hP.out.ne'
  have h2 := smul_right_injective ℂ hP0 h
  have hpair : ∀ (G : ℝ × Space → CVec3) (hG0 : IsPhaseTest 0 G) (f : Yq P q) (t : ℝ),
      pairH hG0 f t = ∫ y, dotL (G (t, y)) (rep f t y) := by
    intro G hG0 f t
    rw [pairH_eq]
    refine integral_congr_ae ?_
    filter_upwards [rep_slice f t] with y hy
    rw [hy]
  simp only [hpair] at h2
  exact h2

end UnforcedLeray.Short.IIb.BaseRepSub

end
