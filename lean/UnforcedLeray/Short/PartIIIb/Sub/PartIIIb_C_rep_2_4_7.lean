import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Lib.Axisymmetric.Measure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# `PartIII-b:C/rep/2/4/7` : the analytic core `outMajAnnulus`

Source `the November 2 reference manuscript` 4181-4192 with 3603-3647, 5219-5221.
Chain: `outMajReduce` (pointwise on the annulus), the annulus Fubini identity in `lqNorm` form
(`outAnn7_lq`, proved here from the integral identity `outAnn7_int`), `vertYoungPhase` for
`h = vprof g`, `vprofHolder`, and the scalar identity `outAnn7_alg` (all lengths are multiples of
`R√ν`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Annulus integral identity (`∫_{annulus} F(y₃)^{22/3}`), source 4164-4167. -/
theorem outAnn7_int (ν R : ℝ) (hν : 0 < ν) (hR : 0 < R) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y in streamAnn ν R, F (y 2) ^ (22 / 3 : ℝ) =
      ENNReal.ofReal (Real.pi * ν * R ^ 2 / 4) * ∫⁻ s, F s ^ (22 / 3 : ℝ) := by
  set a := R * Real.sqrt ν with ha
  set b := R * Real.sqrt (5 * ν / 4) with hb
  have ha0 : 0 < a := mul_pos hR (Real.sqrt_pos.2 hν)
  have hab : a ≤ b := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hR.le
  have hmeas : MeasurableSet (streamAnn ν R) := by
    have : streamAnn ν R = ϱ ⁻¹' Icc a b := by ext y; simp [streamAnn, a, b]
    rw [this]; exact measurable_ϱ measurableSet_Icc
  set q : ℝ := 22 / 3
  have hFq : Measurable fun s => F s ^ q := hF.pow_const q
  set g : ℝ × ℝ → ℝ≥0∞ := fun p => (Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) p.1 * F p.2 ^ q with hg
  have hgm : Measurable g := by
    refine (measurable_const.indicator measurableSet_Icc |>.comp measurable_fst).mul
      (hFq.comp measurable_snd)
  have h1 : ∫⁻ y in streamAnn ν R, F (y 2) ^ q = ∫⁻ y, g (ϱ y, y 2) := by
    rw [← lintegral_indicator hmeas]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ streamAnn ν R
    · have : ϱ y ∈ Icc a b := hy
      simp [hg, Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : ϱ y ∉ Icc a b := hy
      simp [hg, Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [h1, lintegral_axisymm g hgm]
  have h2 : ∀ p : ℝ × ℝ, ENNReal.ofReal p.1 * g p =
      ((Icc a b).indicator (fun ρ => ENNReal.ofReal ρ) p.1) * F p.2 ^ q := by
    intro p
    by_cases hp : p.1 ∈ Icc a b
    · simp [hg, Set.indicator_of_mem hp]
    · simp [hg, Set.indicator_of_notMem hp]
  simp_rw [h2]
  have hA : Measurable ((Icc a b).indicator (fun ρ => ENNReal.ofReal ρ)) :=
    ENNReal.measurable_ofReal.indicator measurableSet_Icc
  have h3 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
      ((Icc a b).indicator (fun ρ => ENNReal.ofReal ρ) p.1) * F p.2 ^ q =
      (∫⁻ ρ in Ioi (0 : ℝ), (Icc a b).indicator (fun ρ => ENNReal.ofReal ρ) ρ) *
        ∫⁻ s, F s ^ q := by
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
  rw [h3, h4, ← mul_assoc, ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 * Real.pi by positivity)]
  congr 2
  have e1 : b ^ 2 = R ^ 2 * (5 * ν / 4) := by
    rw [hb, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 5 * ν / 4 by linarith)]
  have e2 : a ^ 2 = R ^ 2 * ν := by
    rw [ha, mul_pow, Real.sq_sqrt hν.le]
  rw [e1, e2]; ring

/-- The `L^{22/3}` norm of the annulus indicator of `F(y₃)` (`lqNorm` form, source 4164-4167). -/
theorem outAnn7_lq (ν R : ℝ) (hν : 0 < ν) (hR : 0 < R) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    lqNorm (22 / 3) ((streamAnn ν R).indicator (fun y => F (y 2))) =
      ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) * lqNorm1 (22 / 3) F := by
  have hq : (0 : ℝ) < 22 / 3 := by norm_num
  have hmeas : MeasurableSet (streamAnn ν R) := by
    have hm : Measurable (fun y : Space => ϱ y) := measurable_ϱ
    have : streamAnn ν R = ϱ ⁻¹' Icc (R * Real.sqrt ν) (R * Real.sqrt (5 * ν / 4)) := by
      ext y; simp [streamAnn]
    rw [this]; exact measurable_ϱ measurableSet_Icc
  have hc : 0 ≤ Real.pi * ν * R ^ 2 / 4 :=
    div_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hν.le) (sq_nonneg R)) (by norm_num)
  have hpt : ∀ y : Space, ((streamAnn ν R).indicator (fun y => F (y 2)) y) ^ (22 / 3 : ℝ) =
      (streamAnn ν R).indicator (fun y => F (y 2) ^ (22 / 3 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ streamAnn ν R
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hq]
  have h322 : (1 / (22 / 3 : ℝ)) = 3 / 22 := by norm_num
  unfold lqNorm lqNorm1
  rw [h322]
  simp_rw [hpt]
  rw [lintegral_indicator hmeas, outAnn7_int ν R hν hR F hF,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 22),
    ← ENNReal.ofReal_rpow_of_nonneg hc (by norm_num : (0 : ℝ) ≤ 3 / 22)]

theorem outAnn7_alg_pow (x : ℝ) (hx : 0 < x) : (x ^ 2) ^ (3 / 22 : ℝ) = x ^ (3 / 11 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

/-- The scalar identity: all lengths are multiples of `rIn = R√ν`, the total power is
`3/11 + 3/11 + (-2 + 3/11) = -13/11`. -/
theorem outAnn7_alg (Cy R ν : ℝ) (hν : 0 < ν) (hR : 0 < R) :
    (Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) *
        (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ)) *
        (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ) =
      Cy * ((Real.pi / 4) ^ (3 / 22 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
        (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 11 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹) *
        (R * Real.sqrt ν) ^ (-(13 / 11 : ℝ)) := by
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hs0 : 0 ≤ Real.sqrt (5 / 6 : ℝ) := Real.sqrt_nonneg _
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  have hsq56 : Real.sqrt (5 / 6 : ℝ) ^ 2 = 5 / 6 := Real.sq_sqrt (by norm_num)
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrIn0 : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hsq : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    congr 1; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * (R * Real.sqrt ν) := by
    rw [hsq]; ring
  have hc : Real.pi * ν * R ^ 2 / 4 = (Real.pi / 4) * (R * Real.sqrt ν) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hν.le]; ring
  have hG : Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2 =
      (Real.pi * (5 / 6)) * (R * Real.sqrt ν) ^ 2 := by
    rw [hrO, mul_pow (Real.sqrt (5 / 6 : ℝ)), hsq56]; ring
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) =
      (1 - Real.sqrt (5 / 6 : ℝ)) * (R * Real.sqrt ν) := by
    rw [hrO]; ring
  have hA : (Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) =
      (Real.pi / 4) ^ (3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ) := by
    rw [hc, Real.mul_rpow (show (0:ℝ) ≤ Real.pi / 4 by positivity) (sq_nonneg _),
      outAnn7_alg_pow _ hrIn0]
  have hGp : (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ) =
      (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ) := by
    rw [hG, Real.mul_rpow (show (0:ℝ) ≤ Real.pi * (5 / 6) by positivity) (sq_nonneg _),
      outAnn7_alg_pow _ hrIn0]
  have hB : (R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) =
      (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ := by
    have h1 : (1 - Real.sqrt (5 / 6 : ℝ)) ≠ 0 := hd0.ne'
    have h2 : R * Real.sqrt ν ≠ 0 := hrIn0.ne'
    rw [hD]
    field_simp
  have hE : (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ) =
      (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 11 : ℝ) * (R * Real.sqrt ν) ^ (-2 + 3 / 11 : ℝ) := by
    rw [hD, Real.mul_rpow hd0.le hrIn0.le]
  have hpow : (R * Real.sqrt ν) ^ (3 / 11 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ) *
      (R * Real.sqrt ν) ^ (-2 + 3 / 11 : ℝ) = (R * Real.sqrt ν) ^ (-(13 / 11 : ℝ)) := by
    rw [← Real.rpow_add hrIn0, ← Real.rpow_add hrIn0]
    norm_num
  rw [hA, hGp, hB, hE]
  linear_combination (Cy * (Real.pi / 4) ^ (3 / 22 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
    (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 11 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹) * hpow

/-- **The analytic core** (`OutMajAnnulus`, source 4181-4192 with 3603-3647, 5219-5221). -/
theorem outMajAnnulus : OutMajAnnulus := by
  have hYP := vertYoungPhase
  unfold VertYoungPhase at hYP
  obtain ⟨Cy, hCy, hY⟩ := hYP
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hs0 : 0 ≤ Real.sqrt (5 / 6 : ℝ) := Real.sqrt_nonneg _
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  unfold OutMajAnnulus
  refine ⟨Cy * ((Real.pi / 4) ^ (3 / 22 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
      (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 11 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹),
    mul_nonneg hCy (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg hd0.le _)) (inv_nonneg.2 hd0.le)), ?_⟩
  intro ν R P a hν hR hP0 hP1 ha g hg hper hsupp τ
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrIn0 : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hsq : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    congr 1; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * (R * Real.sqrt ν) := by
    rw [hsq]; ring
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) =
      (1 - Real.sqrt (5 / 6 : ℝ)) * (R * Real.sqrt ν) := by
    rw [hrO]; ring
  have hD0 : 0 < R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) := by
    rw [hD]; exact mul_pos hd0 hrIn0
  have hrO0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by
    rw [hrO]; exact mul_nonneg hs0 hrIn0.le
  have hrOlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := by
    have := mul_lt_mul_of_pos_right hs1 hrIn0
    rw [hrO]; linarith
  have hq : (0 : ℝ) < 22 / 3 := by norm_num
  have hVM := vertMeasurable g hg
  have hvm : Measurable (Function.uncurry (vprof g)) := hVM.1
  have hpair : Measurable (fun s : ℝ => (τ, s)) := measurable_const.prodMk measurable_id
  have hunc : Measurable (Function.uncurry (vertRed a (R * Real.sqrt ν)
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g)) :=
    hVM.2 a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
  have hFm2 : Measurable (fun s : ℝ => Function.uncurry (vertRed a (R * Real.sqrt ν)
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g) (τ, s)) := hunc.comp hpair
  have hFm : Measurable (fun s => vertRed a (R * Real.sqrt ν)
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ s) := hFm2
  have hvper : ∀ τ' s, vprof g (τ' + P) s = vprof g τ' s := by
    intro τ' s
    simp only [vprof, hper]
  have hC := hY a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) P ha hD0 hrIn0
    hP0 hP1 (vprof g) hvm hvper τ
  have hDh := vprofHolder (R * Real.sqrt (5 * ν / 6)) P hrO0 hP0 g hg hsupp
  have stepA : lqNorm (22 / 3) ((streamAnn ν R).indicator (fun y =>
        outMaj a (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2))) ≤
      lqNorm (22 / 3) ((streamAnn ν R).indicator (fun y => vertRed a (R * Real.sqrt ν)
        (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (y 2))) := by
    refine lqNorm_mono hq fun y => ?_
    by_cases hy : y ∈ streamAnn ν R
    · simp only [Set.indicator_of_mem hy]
      exact outMajReduce a (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) hrO0 hrOlt g hg hsupp τ
        (ϱ y) (y 2) hy.1
    · simp [Set.indicator_of_notMem hy]
  have hc0 : 0 ≤ (Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) := Real.rpow_nonneg
    (div_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hν.le) (sq_nonneg R)) (by norm_num)) _
  have hGn : 0 ≤ (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) _
  have hBn : 0 ≤ (R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) :=
    div_nonneg hrIn0.le hD0.le
  have ha0 : 0 ≤ Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ) :=
    mul_nonneg (mul_nonneg hCy hBn) (Real.rpow_nonneg hD0.le _)
  have hA2 := outAnn7_lq ν R hν hR (fun s => vertRed a (R * Real.sqrt ν)
    (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ s) hFm
  refine stepA.trans (le_of_eq hA2) |>.trans ?_
  refine (mul_le_mul_right hC _).trans ?_
  refine (mul_le_mul_right (mul_le_mul_right hDh _) _).trans ?_
  have e4 : ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) *
      (ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)))
        * (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ)) *
        (ENNReal.ofReal ((Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ)) *
          IIIa.ltauLq P (22 / 19) g)) =
      ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) *
          (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
            (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ)) *
          (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ)) *
          IIIa.ltauLq P (22 / 19) g := by
    rw [ENNReal.ofReal_mul (mul_nonneg hc0 ha0), ENNReal.ofReal_mul hc0]
    ring
  rw [e4, outAnn7_alg Cy R ν hν hR]

end UnforcedLeray.Short.PartIIIb.Concrete
