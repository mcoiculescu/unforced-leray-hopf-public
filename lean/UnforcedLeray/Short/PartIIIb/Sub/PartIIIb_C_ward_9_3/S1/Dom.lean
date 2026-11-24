import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransSepDom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.X0Dom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Comm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise domination of both stream transitions with weight `2μ + 2` and arbitrary `ν, R > 0`
(source 5312-5316, 3684-3712, 4176-4214): the proof of `transSepDom`, with the weight kept and
the constants depending on `ν, R`. -/
theorem transDomW (ν μ R : ℝ) (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) (hν : 0 < ν) (hR0 : 0 < R)
    (hμ : -(1 / 4) < μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℝ), 0 < P →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
          ‖sepTrans ν μ R χy T τ y‖ₑ ≤
            ENNReal.ofReal C * transMajA (2 * μ + 2) ν R (IIIa.srcNorm T) τ y := by
  classical
  obtain ⟨Cc, hCc0, hCut⟩ := transCutPoint χy hχ
  obtain ⟨Cx, hCx0, hX0⟩ := sepX0DomW
  obtain ⟨C0, hC00, hOut⟩ := (outPrimPointwise_of IIIa.sepWDominated IIIa.sepKernelBounds :
    OutPrimPointwise) μ μ hμ
  obtain ⟨Cm, hCm0, hComm⟩ := sepCommBoundW ν μ R χy hχ hν hR0 hμ
  have hL0 : 0 < transLen ν R := mul_pos hR0 (Real.sqrt_pos.2 hν)
  set p : ℝ := max 1 (transLen ν R)⁻¹ with hpdef
  have hp1 : (1 : ℝ) ≤ p := le_max_left _ _
  have hrp : (transLen ν R)⁻¹ ≤ p := le_max_right _ _
  have hr0 : 0 ≤ (transLen ν R)⁻¹ := inv_nonneg.2 hL0.le
  refine ⟨(Cc * C0 + Cm * (2 * Cx + 2 * C0)) * p ^ (0 + 1),
    mul_nonneg (add_nonneg (mul_nonneg hCc0 hC00) (mul_nonneg hCm0 (by linarith)))
      (pow_nonneg (by linarith) _), ?_⟩
  intro P hP T hT hM hA τ y hy
  by_cases hann : y ∈ streamAnn ν R
  · have hann' : R * Real.sqrt ν ≤ ϱ y ∧ ϱ y ≤ R * Real.sqrt (5 * ν / 4) := hann
    have hin : R * Real.sqrt ν ≤ ϱ y := hann'.1
    have hrO : 0 ≤ R * Real.sqrt (5 * ν / 6) := mul_nonneg hR0.le (Real.sqrt_nonneg _)
    have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
      mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by linarith) (by linarith)) hR0
    obtain ⟨hXd0, hXd1⟩ :=
      hX0 ν μ (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P hν hμ hrO hrr hP T hT hM τ y hin
    obtain ⟨hOW, hOX⟩ :=
      hOut ν μ (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P hν ⟨le_rfl, le_rfl⟩ hrO hrr hP T
        hT τ (ϱ y) (y 2) hin
    have hXbd0 : ‖sepX0 ν μ T τ y‖ₑ ≤
        ENNReal.ofReal Cx * IIIa.sepDom (2 * μ + 2) 0 (transGap ν R) (IIIa.srcNorm T) τ y := hXd0
    have hXbd1 : ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ ≤
        ENNReal.ofReal Cx * (IIIa.sepDom (2 * μ + 2) 0 (transGap ν R) (IIIa.srcNorm T) τ y +
          IIIa.sepDom (2 * μ + 2) 1 (transGap ν R) (IIIa.srcNorm T) τ y) := hXd1
    have hOW' : ENNReal.ofReal |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)| ≤
        ENNReal.ofReal C0 * outMaj (2 * μ + 2) (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2) :=
      hOW
    have hOX' : ENNReal.ofReal |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)| ≤
        ENNReal.ofReal C0 * (2 * outMaj (2 * μ + 2) (transGap ν R) (IIIa.srcNorm T) τ (ϱ y)
          (y 2)) := hOX
    have hcut := hCut ν R hν hR0 (sepWre ν μ T) τ y hy
    simp only [Set.indicator_of_mem hann] at hcut
    have hEc : ‖streamCorr ν R χy (sepWre ν μ T) τ y‖ₑ ≤
        ENNReal.ofReal (Cc * (transLen ν R)⁻¹ ^ 2) *
          (ENNReal.ofReal C0 *
            outMaj (2 * μ + 2) (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)) :=
      le_trans hcut (tsd_mulL hOW' _)
    have hEs : ‖sepComm ν μ R χy T τ y‖ₑ ≤ ENNReal.ofReal (Cm * p ^ 0) *
        (ENNReal.ofReal Cx * IIIa.sepDom (2 * μ + 2) 0 (transGap ν R) (IIIa.srcNorm T) τ y +
          ENNReal.ofReal (transLen ν R)⁻¹ *
            (ENNReal.ofReal Cx * (IIIa.sepDom (2 * μ + 2) 0 (transGap ν R) (IIIa.srcNorm T) τ y +
              IIIa.sepDom (2 * μ + 2) 1 (transGap ν R) (IIIa.srcNorm T) τ y)) +
          ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
            (ENNReal.ofReal C0 *
              (2 * outMaj (2 * μ + 2) (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)))) := by
      rw [pow_zero, mul_one]
      refine le_trans (hComm P hP T hT hM hA τ y hann) ?_
      exact tsd_mulL
        (add_le_add (add_le_add hXbd0 (tsd_mulL hXbd1 (ENNReal.ofReal (transLen ν R)⁻¹)))
          (tsd_mulL hOX' (ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2)))) _
    have hTM : transMajA (2 * μ + 2) ν R (IIIa.srcNorm T) τ y =
        IIIa.sepDom (2 * μ + 2) 0 (transGap ν R) (IIIa.srcNorm T) τ y +
          ENNReal.ofReal (transLen ν R)⁻¹ *
            IIIa.sepDom (2 * μ + 2) 1 (transGap ν R) (IIIa.srcNorm T) τ y +
          ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
            outMaj (2 * μ + 2) (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2) := by
      simp only [transMajA, Set.indicator_of_mem hann]
    have hST : sepTrans ν μ R χy T τ y =
        streamCorr ν R χy (sepWre ν μ T) τ y + sepComm ν μ R χy T τ y := rfl
    rw [hST, hTM]
    refine (enorm_add_le _ _).trans ?_
    exact tsd_abstract Cc C0 Cx Cm p (transLen ν R)⁻¹ 0 hCc0 hC00 hCx0 hCm0 hp1 hr0 hrp
      _ _ _ _ _ hEc hEs
  · have hc := tsd_case_out ν R y hν hR0 hy hann
    rw [transVanishOff ν μ R χy hχ hν hR0 T τ y hy hc]
    simp

end UnforcedLeray.Short.PartIIIb.Concrete

end
