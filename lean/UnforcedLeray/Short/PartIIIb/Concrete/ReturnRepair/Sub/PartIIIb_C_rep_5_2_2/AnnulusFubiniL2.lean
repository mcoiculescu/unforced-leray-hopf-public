import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Lib.Axisymmetric.Measure

/-!
# `PartIII-b:C/rep/5/2/2/9` : the annulus Fubini identity in `L²`

Source `the November 2 reference manuscript` 4164-4167 (the transition annulus
`R√ν ≤ ϱ ≤ R√(5ν/4)`, horizontal area `πνR²/4`). The `L²` analogue of `annulusFubini`
(`Sub/PartIII-b_C_rep_2_4_6.lean`), with exponent `2` in place of `22/3`; inside `ltauLq` the
exponent `2/2 = 1` is absorbed, and the constant is pulled out of the phase integral and the square
root.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem streamAnn_measurableSet' (ν R : ℝ) : MeasurableSet (streamAnn ν R) := by
  have : streamAnn ν R = ϱ ⁻¹' Icc (R * Real.sqrt ν) (R * Real.sqrt (5 * ν / 4)) := by
    ext y; simp [streamAnn]
  rw [this]
  exact measurable_ϱ measurableSet_Icc

/-- The area identity for a function of the height, exponent `2` (the proof of `annulusFubini`). -/
theorem annulus_sq_lintegral (ν R : ℝ) (hν : 0 < ν) (hR : 0 < R) (G : ℝ → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ y in streamAnn ν R, G (y 2) ^ (2 : ℝ) =
      ENNReal.ofReal (Real.pi * ν * R ^ 2 / 4) * ∫⁻ s, G s ^ (2 : ℝ) := by
  set a := R * Real.sqrt ν with ha
  set b := R * Real.sqrt (5 * ν / 4) with hb
  have ha0 : 0 < a := mul_pos hR (Real.sqrt_pos.2 hν)
  have hab : a ≤ b := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hR.le
  have hmeas : MeasurableSet (streamAnn ν R) := streamAnn_measurableSet' ν R
  set q : ℝ := 2
  have hFq : Measurable fun s => G s ^ q := hG.pow_const q
  set g : ℝ × ℝ → ℝ≥0∞ := fun p => (Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) p.1 * G p.2 ^ q
    with hg
  have hgm : Measurable g := by
    refine (measurable_const.indicator measurableSet_Icc |>.comp measurable_fst).mul
      (hFq.comp measurable_snd)
  have h1 : ∫⁻ y in streamAnn ν R, G (y 2) ^ q = ∫⁻ y, g (ϱ y, y 2) := by
    rw [← lintegral_indicator hmeas]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ streamAnn ν R
    · have : ϱ y ∈ Icc a b := hy
      simp [hg, Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : ϱ y ∉ Icc a b := hy
      simp [hg, Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [h1, lintegral_axisymm g hgm]
  have h2 : ∀ p : ℝ × ℝ, ENNReal.ofReal p.1 * g p =
      ((Icc a b).indicator (fun ρ => ENNReal.ofReal ρ) p.1) * G p.2 ^ q := by
    intro p
    by_cases hp : p.1 ∈ Icc a b
    · simp [hg, Set.indicator_of_mem hp]
    · simp [hg, Set.indicator_of_notMem hp]
  simp_rw [h2]
  have hA : Measurable ((Icc a b).indicator (fun ρ => ENNReal.ofReal ρ)) :=
    ENNReal.measurable_ofReal.indicator measurableSet_Icc
  have h3 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
      ((Icc a b).indicator (fun ρ => ENNReal.ofReal ρ) p.1) * G p.2 ^ q =
      (∫⁻ ρ in Ioi (0 : ℝ), (Icc a b).indicator (fun ρ => ENNReal.ofReal ρ) ρ) *
        ∫⁻ s, G s ^ q := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    exact lintegral_prod_mul hA.aemeasurable hFq.aemeasurable
  have h4 : ∫⁻ ρ in Ioi (0 : ℝ), (Icc a b).indicator (fun ρ => ENNReal.ofReal ρ) ρ =
      ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2) := by
    have hs : Icc a b ∩ Ioi (0 : ℝ) = Icc a b :=
      inter_eq_left.2 (fun x hx => lt_of_lt_of_le ha0 hx.1)
    rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc, hs,
      ← ofReal_integral_eq_lintegral_ofReal
        (by exact (continuous_id.integrableOn_Icc : IntegrableOn (fun x : ℝ => x) (Icc a b)))
        ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall
          (fun x hx => ha0.le.trans hx.1))),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_id]
  rw [h3, h4, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have e1 : b ^ 2 = R ^ 2 * (5 * ν / 4) := by
    rw [hb, mul_pow, Real.sq_sqrt (by positivity)]
  have e2 : a ^ 2 = R ^ 2 * ν := by
    rw [ha, mul_pow, Real.sq_sqrt hν.le]
  rw [e1, e2]; ring

/-- **`annulusFubiniL2`** (source 4164-4167): the `L²_τL²` norm of the annulus indicator of
`F(τ, y₃)` is `(πνR²/4)^{1/2}` times the `L²_τL²(ℝ)` norm of `F`. -/
theorem annulusFubiniL2 : AnnulusFubiniL2 := by
  intro ν R P hν hR hP F hF
  have hpt : ∀ τ, ∫⁻ y, (streamAnn ν R).indicator (fun y => F τ (y 2)) y ^ (2 : ℝ) =
      ENNReal.ofReal (Real.pi * ν * R ^ 2 / 4) * ∫⁻ s, F τ s ^ (2 : ℝ) := by
    intro τ
    have hsec : Measurable fun s : ℝ => F τ s :=
      hF.comp (measurable_const.prodMk measurable_id)
    have hind : ∀ y, (streamAnn ν R).indicator (fun y => F τ (y 2)) y ^ (2 : ℝ) =
        (streamAnn ν R).indicator (fun y => F τ (y 2) ^ (2 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ streamAnn ν R
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    simp_rw [hind]
    rw [lintegral_indicator (streamAnn_measurableSet' ν R)]
    exact annulus_sq_lintegral ν R hν hR (fun s => F τ s) hsec
  have hcnn : (0 : ℝ) ≤ Real.pi * ν * R ^ 2 / 4 := by positivity
  simp only [IIIa.ltauLq, ltauLq1]
  simp only [hpt]
  simp only [show (2 : ℝ) / 2 = 1 from by norm_num, ENNReal.rpow_one]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← ENNReal.ofReal_rpow_of_nonneg hcnn (by norm_num),
    ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
