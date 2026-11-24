import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Newton gradient: actual near and far integrability on R³

The coordinate kernel is the gradient of `1 / (4π |x|)`, with its value at
zero defined by real division. The radial integrability and dilation proofs
below adapt the elementary method in `NavierStokes/R3PressureNearKernel.lean`
from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd
(Apache-2.0; see LICENSE-NavierStokesAndEuler). No kernel bound is assumed.
-/

noncomputable section

namespace UnforcedLeray.PressureAnalysis

open Set Filter MeasureTheory
open scoped ENNReal

def newtonGradientKernel (i : Fin 3) (x : Space) : ℝ :=
  -(x i) / (4 * Real.pi * ‖x‖ ^ 3)

def nearNewtonKernel (R : ℝ) (i : Fin 3) (x : Space) : ℝ :=
  if ‖x‖ < R then newtonGradientKernel i x else 0

def farNewtonKernel (R : ℝ) (i : Fin 3) (x : Space) : ℝ :=
  if R ≤ ‖x‖ then newtonGradientKernel i x else 0

theorem newtonGradientKernel_measurable (i : Fin 3) : Measurable (newtonGradientKernel i) := by
  unfold newtonGradientKernel
  fun_prop

theorem nearNewtonKernel_measurable (R : ℝ) (i : Fin 3) : Measurable (nearNewtonKernel R i) := by
  exact Measurable.ite (by measurability) (newtonGradientKernel_measurable i) measurable_const

theorem farNewtonKernel_measurable (R : ℝ) (i : Fin 3) : Measurable (farNewtonKernel R i) := by
  exact Measurable.ite (by measurability) (newtonGradientKernel_measurable i) measurable_const

theorem nearNewtonKernel_add_far (R : ℝ) (i : Fin 3) (x : Space) :
    nearNewtonKernel R i x + farNewtonKernel R i x = newtonGradientKernel i x := by
  by_cases h : ‖x‖ < R
  · simp [nearNewtonKernel, farNewtonKernel, h, not_le.mpr h]
  · simp [nearNewtonKernel, farNewtonKernel, h, not_lt.mp h]

theorem norm_newtonGradientKernel_le (i : Fin 3) (x : Space) :
    ‖newtonGradientKernel i x‖ ≤ (4 * Real.pi)⁻¹ * ‖x‖ ^ (-2 : ℝ) := by
  by_cases hx : x = 0
  · simp [newtonGradientKernel, hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc : 0 < 4 * Real.pi := by positivity
  have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  rw [newtonGradientKernel, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_pos (mul_pos hc (pow_pos hn 3))]
  calc
    |x i| / (4 * Real.pi * ‖x‖ ^ 3) ≤ ‖x‖ / (4 * Real.pi * ‖x‖ ^ 3) :=
      div_le_div_of_nonneg_right hi (by positivity)
    _ = (4 * Real.pi)⁻¹ * ‖x‖ ^ (-2 : ℝ) := by
      norm_num
      field_simp

private def radialProfile (a b : ℝ) (x : Space) : ℝ :=
  if ‖x‖ < 1 then ‖x‖ ^ a else ‖x‖ ^ b

private theorem radialProfile_integrable {a b : ℝ} (ha : -3 < a) (hb : b < -3) :
    Integrable (radialProfile a b) := by
  apply (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r => if r < 1 then r ^ a else r ^ b)).mpr
  have hnear : IntegrableOn (fun r : ℝ => r ^ (2 + a)) (Ioo 0 1) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)]
    linarith
  have hfar : IntegrableOn (fun r : ℝ => r ^ (2 + b)) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num))
  have hnear' : IntegrableOn (fun r : ℝ => r ^ (Module.finrank ℝ Space - 1) •
      (if r < 1 then r ^ a else r ^ b)) (Ioo 0 1) := by
    apply hnear.congr_fun _ measurableSet_Ioo
    intro r hr
    simp only [ite_eq_left hr.2, smul_eq_mul]
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub]
    rw [← Real.rpow_natCast, ← Real.rpow_add hr.1]
    norm_num
  have hfar' : IntegrableOn (fun r : ℝ => r ^ (Module.finrank ℝ Space - 1) •
      (if r < 1 then r ^ a else r ^ b)) (Ici 1) := by
    apply hfar.congr_fun _ measurableSet_Ici
    intro r hr
    change 1 ≤ r at hr
    simp only [ite_eq_right (not_lt.mpr hr), smul_eq_mul]
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub]
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith : 0 < r)]
    norm_num
  have hsets : Ioo (0 : ℝ) 1 ∪ Ici 1 = Ioi 0 := by
    ext r
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hr : r < 1
      · exact Or.inl ⟨h, hr⟩
      · exact Or.inr (not_lt.mp hr)
  simpa only [hsets] using hnear'.union hfar'

private def nearMajorant (x : Space) : ℝ := if ‖x‖ < 1 then ‖x‖ ^ (-2 : ℝ) else 0
private def farMajorant (x : Space) : ℝ := if 1 ≤ ‖x‖ then ‖x‖ ^ (-2 : ℝ) else 0

private theorem nearMajorant_nonneg (x : Space) : 0 ≤ nearMajorant x := by
  unfold nearMajorant
  split <;> positivity

private theorem farMajorant_nonneg (x : Space) : 0 ≤ farMajorant x := by
  unfold farMajorant
  split <;> positivity

private theorem nearMajorant_measurable : Measurable nearMajorant := by
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

private theorem farMajorant_measurable : Measurable farMajorant := by
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

private theorem nearMajorant_memLp : MemLp nearMajorant (15 / 14) := by
  apply (integrable_norm_rpow_iff nearMajorant_measurable.aestronglyMeasurable
    (by norm_num : (15 / 14 : ℝ≥0∞) ≠ 0) (by finiteness : (15 / 14 : ℝ≥0∞) ≠ ⊤)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (nearMajorant_nonneg _)]
  apply (radialProfile_integrable (a := -15 / 7) (b := -4) (by norm_num) (by norm_num)).mono'
    (nearMajorant_measurable.pow_const _).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (nearMajorant_nonneg x) _)]
  unfold nearMajorant radialProfile
  split
  · rw [← Real.rpow_mul (norm_nonneg x)]
    norm_num
  · simp only [Real.zero_rpow (by norm_num : (15 / 14 : ℝ) ≠ 0)]
    positivity

private theorem farMajorant_memLp : MemLp farMajorant (5 / 3) := by
  apply (integrable_norm_rpow_iff farMajorant_measurable.aestronglyMeasurable
    (by norm_num : (5 / 3 : ℝ≥0∞) ≠ 0) (by finiteness : (5 / 3 : ℝ≥0∞) ≠ ⊤)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (farMajorant_nonneg _)]
  apply (radialProfile_integrable (a := 0) (b := -10 / 3) (by norm_num) (by norm_num)).mono'
    (farMajorant_measurable.pow_const _).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (farMajorant_nonneg x) _)]
  by_cases hx : ‖x‖ < 1
  · simp [farMajorant, radialProfile, hx, not_le.mpr hx]
  · simp only [farMajorant, radialProfile, hx, not_lt.mp hx, ite_true, ite_false]
    rw [← Real.rpow_mul (norm_nonneg x)]
    norm_num

theorem nearNewtonKernel_one_memLp (i : Fin 3) : MemLp (nearNewtonKernel 1 i) (15 / 14) := by
  apply nearMajorant_memLp.of_le_mul (c := (4 * Real.pi)⁻¹)
    (nearNewtonKernel_measurable 1 i).aestronglyMeasurable
  filter_upwards with x
  by_cases hx : ‖x‖ < 1
  · simpa [nearNewtonKernel, nearMajorant, hx,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) (-2 : ℝ))] using norm_newtonGradientKernel_le i x
  · simp [nearNewtonKernel, nearMajorant, hx]

theorem farNewtonKernel_one_memLp (i : Fin 3) : MemLp (farNewtonKernel 1 i) (5 / 3) := by
  apply farMajorant_memLp.of_le_mul (c := (4 * Real.pi)⁻¹)
    (farNewtonKernel_measurable 1 i).aestronglyMeasurable
  filter_upwards with x
  by_cases hx : 1 ≤ ‖x‖
  · simpa [farNewtonKernel, farMajorant, hx,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) (-2 : ℝ))] using norm_newtonGradientKernel_le i x
  · simp [farNewtonKernel, farMajorant, hx]

private def kernelDilation (R : ℝ) (f : Space → ℝ) (x : Space) : ℝ :=
  R ^ (-2 : ℝ) * f (R⁻¹ • x)

private theorem kernelDilation_measurable (R : ℝ) {f : Space → ℝ} (hf : Measurable f) :
    Measurable (kernelDilation R f) := by
  unfold kernelDilation
  fun_prop

private theorem kernelDilation_norm_power {R p : ℝ} (hR : 0 < R) (f : Space → ℝ) (x : Space) :
    ‖kernelDilation R f x‖ ^ p = R ^ (-2 * p) * ‖f (R⁻¹ • x)‖ ^ p := by
  rw [kernelDilation, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hR.le _),
    Real.mul_rpow (Real.rpow_nonneg hR.le _) (norm_nonneg _), ← Real.rpow_mul hR.le]

private theorem kernelDilation_memLp {R : ℝ} (hR : 0 < R) {p : ℝ≥0∞} (hp : p ≠ 0)
    (hpt : p ≠ ⊤) {f : Space → ℝ} (hf : Measurable f) (hi : MemLp f p) :
    MemLp (kernelDilation R f) p := by
  apply (integrable_norm_rpow_iff (kernelDilation_measurable R hf).aestronglyMeasurable hp hpt).mp
  simp_rw [kernelDilation_norm_power hR]
  exact (((integrable_norm_rpow_iff hf.aestronglyMeasurable hp hpt).mpr hi).comp_smul
    (inv_ne_zero hR.ne')).const_mul _

private theorem kernelDilation_lpNorm {R : ℝ} (hR : 0 < R) {p : ℝ≥0∞} (hp : p ≠ 0)
    (hpt : p ≠ ⊤) {f : Space → ℝ} (hf : Measurable f) :
    lpNorm (kernelDilation R f) p volume = R ^ (-2 + 3 / p.toReal) * lpNorm f p volume := by
  rw [lpNorm_eq_integral_norm_rpow_toReal hp hpt (kernelDilation_measurable R hf).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal hp hpt hf.aestronglyMeasurable]
  simp_rw [kernelDilation_norm_power hR]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : Space => ‖f x‖ ^ p.toReal) hR.le]
  simp only [smul_eq_mul]
  norm_num only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← mul_assoc, ← Real.rpow_natCast R 3, ← Real.rpow_add hR,
    Real.mul_rpow (Real.rpow_nonneg hR.le _)
      (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg (f x)) _)),
    ← Real.rpow_mul hR.le]
  congr 1
  congr 1
  have hpn : p.toReal ≠ 0 := (ENNReal.toReal_pos hp hpt).ne'
  field_simp
  norm_num

theorem newtonGradientKernel_inv_smul {R : ℝ} (hR : 0 < R) (i : Fin 3) (x : Space) :
    R ^ (-2 : ℝ) * newtonGradientKernel i (R⁻¹ • x) = newtonGradientKernel i x := by
  by_cases hx : x = 0
  · simp [hx, newtonGradientKernel]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [newtonGradientKernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), PiLp.smul_apply, smul_eq_mul]
  norm_num
  field_simp

private theorem nearNewtonKernel_eq_dilation {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    nearNewtonKernel R i = kernelDilation R (nearNewtonKernel 1 i) := by
  funext x
  have hnorm : ‖R⁻¹ • x‖ < 1 ↔ ‖x‖ < R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), inv_mul_lt_iff₀ hR, mul_one]
  by_cases hx : ‖x‖ < R
  · simp only [kernelDilation, nearNewtonKernel, hx, hnorm.mpr hx, ite_true]
    exact (newtonGradientKernel_inv_smul hR i x).symm
  · simp [kernelDilation, nearNewtonKernel, hx, hnorm]

private theorem farNewtonKernel_eq_dilation {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    farNewtonKernel R i = kernelDilation R (farNewtonKernel 1 i) := by
  funext x
  have hnorm : 1 ≤ ‖R⁻¹ • x‖ ↔ R ≤ ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), le_inv_mul_iff₀ hR, mul_one]
  by_cases hx : R ≤ ‖x‖
  · simp only [kernelDilation, farNewtonKernel, hx, hnorm.mpr hx, ite_true]
    exact (newtonGradientKernel_inv_smul hR i x).symm
  · simp [kernelDilation, farNewtonKernel, hx, hnorm]

theorem nearNewtonKernel_memLp {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    MemLp (nearNewtonKernel R i) (15 / 14) := by
  rw [nearNewtonKernel_eq_dilation hR]
  exact kernelDilation_memLp hR (by norm_num) (by finiteness)
    (nearNewtonKernel_measurable 1 i) (nearNewtonKernel_one_memLp i)

theorem farNewtonKernel_memLp {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    MemLp (farNewtonKernel R i) (5 / 3) := by
  rw [farNewtonKernel_eq_dilation hR]
  exact kernelDilation_memLp hR (by norm_num) (by finiteness)
    (farNewtonKernel_measurable 1 i) (farNewtonKernel_one_memLp i)

theorem nearNewtonKernel_lpNorm {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    lpNorm (nearNewtonKernel R i) (15 / 14) volume =
      R ^ (4 / 5 : ℝ) * lpNorm (nearNewtonKernel 1 i) (15 / 14) volume := by
  rw [nearNewtonKernel_eq_dilation hR]
  have h := kernelDilation_lpNorm hR (p := 15 / 14) (by norm_num) (by finiteness)
    (nearNewtonKernel_measurable 1 i)
  norm_num at h
  exact h

theorem farNewtonKernel_lpNorm {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    lpNorm (farNewtonKernel R i) (5 / 3) volume =
      R ^ (-1 / 5 : ℝ) * lpNorm (farNewtonKernel 1 i) (5 / 3) volume := by
  rw [farNewtonKernel_eq_dilation hR]
  have h := kernelDilation_lpNorm hR (p := 5 / 3) (by norm_num) (by finiteness)
    (farNewtonKernel_measurable 1 i)
  norm_num at h
  simpa only [neg_div] using h

def newtonNearConstant : ℝ := ∑ i : Fin 3, lpNorm (nearNewtonKernel 1 i) (15 / 14) volume

def newtonFarConstant : ℝ := ∑ i : Fin 3, lpNorm (farNewtonKernel 1 i) (5 / 3) volume

theorem newtonNearConstant_nonneg : 0 ≤ newtonNearConstant := by
  exact Finset.sum_nonneg (fun _ _ => lpNorm_nonneg)

theorem newtonFarConstant_nonneg : 0 ≤ newtonFarConstant := by
  exact Finset.sum_nonneg (fun _ _ => lpNorm_nonneg)

theorem nearNewtonKernel_lpNorm_le {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    lpNorm (nearNewtonKernel R i) (15 / 14) volume ≤ newtonNearConstant * R ^ (4 / 5 : ℝ) := by
  rw [nearNewtonKernel_lpNorm hR, mul_comm newtonNearConstant]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hR.le _)
  exact Finset.single_le_sum (fun _ _ => lpNorm_nonneg) (Finset.mem_univ i)

theorem farNewtonKernel_lpNorm_le {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    lpNorm (farNewtonKernel R i) (5 / 3) volume ≤ newtonFarConstant * R ^ (-1 / 5 : ℝ) := by
  rw [farNewtonKernel_lpNorm hR, mul_comm newtonFarConstant]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hR.le _)
  exact Finset.single_le_sum (fun _ _ => lpNorm_nonneg) (Finset.mem_univ i)

theorem nearNewtonKernel_eLpNorm_toReal_le {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    (eLpNorm (nearNewtonKernel R i) (15 / 14) volume).toReal ≤ newtonNearConstant * R ^ (4 / 5 : ℝ) := by
  rw [toReal_eLpNorm (nearNewtonKernel_measurable R i).aestronglyMeasurable]
  exact nearNewtonKernel_lpNorm_le hR i

theorem farNewtonKernel_eLpNorm_toReal_le {R : ℝ} (hR : 0 < R) (i : Fin 3) :
    (eLpNorm (farNewtonKernel R i) (5 / 3) volume).toReal ≤ newtonFarConstant * R ^ (-1 / 5 : ℝ) := by
  rw [toReal_eLpNorm (farNewtonKernel_measurable R i).aestronglyMeasurable]
  exact farNewtonKernel_lpNorm_le hR i

/-- The normalized gradient is an actual locally integrable function. -/
theorem newtonGradientKernel_locallyIntegrable (i : Fin 3) :
    LocallyIntegrable (newtonGradientKernel i) := by
  have h := ((nearNewtonKernel_one_memLp i).locallyIntegrable
    ((ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2 (by norm_num))).add
    ((farNewtonKernel_one_memLp i).locallyIntegrable
      ((ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2 (by norm_num)))
  exact h.congr (Filter.Eventually.of_forall (nearNewtonKernel_add_far 1 i))

theorem newtonGradientKernel_integrable_mul_test (i : Fin 3) {φ : Space → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => newtonGradientKernel i x * φ x) := by
  simpa only [smul_eq_mul] using (newtonGradientKernel_locallyIntegrable i).integrable_smul_right_of_hasCompactSupport hφ hc

end UnforcedLeray.PressureAnalysis
