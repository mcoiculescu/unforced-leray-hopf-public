import UnforcedLeray.Short.PartIIb.Sub.G4_2_1

/-!
# Part II-b, task `PartII-b:G4/2/1/1`: the Green inverse of a growing eigenpair is `O(r²)` at `0`

Source: `the November 2 reference manuscript` lines 2347-2352.

Route. Write `G = greenInverse q`, `g(s) = gaussianWeightInv s ≥ 4π`, and
`M = ∫_{(0,∞)} ‖q‖² g s · s` (finite, since `q ∈ X_G`).
1. Pointwise AM-GM with weight `r³` gives `‖∫₀^r s³ q‖ ≤ r³ (M/2 + 1/(48π))`, and with weight
   `1/(2r)` on the tail gives `‖∫_r^∞ s⁻¹ q‖ ≤ (M/2 + 1/(16π))/r`. Hence `‖G r‖ ≤ C₁ r`.
2. The eigen equation `(λ + 2iΩ) q = 2ik G` with `Re λ > 0` and `|k| ≤ 2` on `(0,1]` gives
   `‖q s‖ ≤ K s` on `(0,1]`. Then `‖∫₀^r s³ q‖ ≤ K r⁵` and
   `‖∫_r^∞ s⁻¹ q‖ ≤ K + D` (split at `1`), so `‖G r‖ ≤ C r²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

namespace GreenOrderTwoAux

lemma weight_ge (s : ℝ) : 4 * Real.pi ≤ Planar.gaussianWeightInv s := by
  unfold Planar.gaussianWeightInv
  have h1 : 1 ≤ Real.exp (s ^ 2 / 4) := Real.one_le_exp (by positivity)
  have h2 : 0 ≤ 4 * Real.pi := by positivity
  nlinarith [Real.pi_pos]

lemma weight_pos (s : ℝ) : 0 < Planar.gaussianWeightInv s := by
  linarith [weight_ge s, Real.pi_pos]

/-- The `X_G` mass of a profile on `(0, ∞)`. -/
def wMass (f : Planar.Profile) : ℝ :=
  ∫ s in Ioi (0 : ℝ), ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s

lemma wMass_nonneg (f : Planar.Profile) : 0 ≤ wMass f := by
  unfold wMass
  apply setIntegral_nonneg measurableSet_Ioi
  intro s hs
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (weight_pos s).le) (le_of_lt hs)

lemma rpow_neg_three (s : ℝ) (hs : 0 < s) : s ^ (-3 : ℝ) = 1 / s ^ 3 := by
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs.le, Real.rpow_natCast]
  ring

lemma amgm_head {L w s u : ℝ} (hL : 0 < L) (hw : 0 < w) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    s ^ 3 * u ≤ L / 2 * (u ^ 2 * w * s) + s ^ 5 / (2 * L * w) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h; simp
  · have hpos : 0 < 2 * L * w := mul_pos (mul_pos two_pos hL) hw
    have key : L / 2 * (u ^ 2 * w * s) + s ^ 5 / (2 * L * w) - s ^ 3 * u
        = s * (L * u * w - s ^ 2) ^ 2 / (2 * L * w) := by
      field_simp
      ring
    have hnn : 0 ≤ s * (L * u * w - s ^ 2) ^ 2 / (2 * L * w) :=
      div_nonneg (mul_nonneg hs (sq_nonneg _)) hpos.le
    linarith

lemma amgm_tail {w s u r : ℝ} (hr : 0 < r) (hw : 0 < w) (hs : 0 < s) :
    s⁻¹ * u ≤ 1 / (2 * r) * (u ^ 2 * w * s) + r / (2 * w * s ^ 3) := by
  have hpos : 0 < 2 * r * w * s ^ 3 := mul_pos (mul_pos (mul_pos two_pos hr) hw) (pow_pos hs 3)
  have key : 1 / (2 * r) * (u ^ 2 * w * s) + r / (2 * w * s ^ 3) - s⁻¹ * u
      = (u * w * s ^ 2 - r) ^ 2 / (2 * r * w * s ^ 3) := by
    field_simp
    ring
  have hnn : 0 ≤ (u * w * s ^ 2 - r) ^ 2 / (2 * r * w * s ^ 3) :=
    div_nonneg (sq_nonneg _) hpos.le
  linarith

/-- Head bound: `‖∫₀^r s³ q‖ ≤ r³ (M/2 + 1/(48π))`. -/
lemma norm_head_le {f : Planar.Profile} (hf : Planar.MemXG f) {r : ℝ} (hr : 0 < r) :
    ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s‖ ≤ r ^ 3 / 2 * wMass f + r ^ 3 / (48 * Real.pi) := by
  rw [intervalIntegral.integral_of_le hr.le]
  have hfin : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s) (Ioi 0) :=
    hf.integrable
  have hI : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s) (Ioc 0 r) :=
    hfin.mono_set Ioc_subset_Ioi_self
  have h8 : ∀ s : ℝ, 0 < 8 * Real.pi * r ^ 3 := fun s =>
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hr 3)
  have hc : Continuous (fun s : ℝ => s ^ 5 / (8 * Real.pi * r ^ 3)) := by fun_prop
  have hP : IntegrableOn (fun s : ℝ => s ^ 5 / (8 * Real.pi * r ^ 3)) (Ioc 0 r) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmaj : IntegrableOn (fun s : ℝ => r ^ 3 / 2 * (‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s)
      + s ^ 5 / (8 * Real.pi * r ^ 3)) (Ioc 0 r) :=
    (Integrable.const_mul hI _).add hP
  have hbd := norm_integral_le_of_norm_le hmaj (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 < s := hs.1
    have hamgm := amgm_head (L := r ^ 3) (w := Planar.gaussianWeightInv s) (s := s)
      (u := ‖f s‖) (pow_pos hr 3) (weight_pos s) hs0.le (norm_nonneg _)
    have h2 : s ^ 5 / (2 * r ^ 3 * Planar.gaussianWeightInv s) ≤ s ^ 5 / (8 * Real.pi * r ^ 3) := by
      apply div_le_div_of_nonneg_left (pow_nonneg hs0.le 5) (h8 s)
      nlinarith [weight_ge s, mul_le_mul_of_nonneg_left (weight_ge s) (pow_pos hr 3).le]
    have hnorm : ‖(s : ℂ) ^ 3 * f s‖ = s ^ 3 * ‖f s‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    show ‖(s : ℂ) ^ 3 * f s‖ ≤ _
    rw [hnorm]
    linarith)
  refine hbd.trans ?_
  rw [integral_add (Integrable.const_mul hI _) hP, integral_const_mul]
  have hA : ∫ s in Ioc 0 r, ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s ≤ wMass f := by
    unfold wMass
    apply setIntegral_mono_set hfin
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (weight_pos s).le) (le_of_lt hs)
    · exact Ioc_subset_Ioi_self.eventuallyLE
  have hB : ∫ s in Ioc 0 r, s ^ 5 / (8 * Real.pi * r ^ 3) = r ^ 3 / (48 * Real.pi) := by
    rw [← intervalIntegral.integral_of_le hr.le, intervalIntegral.integral_div, integral_pow]
    field_simp
    ring
  rw [hB]
  have h1 := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ r ^ 3 / 2)
  linarith

/-- Tail integrability: `s⁻¹ q` is integrable on `(r, ∞)` for `q ∈ X_G`. -/
lemma integrableOn_tail {f : Planar.Profile} (hf : Planar.MemXG f) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * f s) (Ioi r) := by
  have hfin : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s) (Ioi 0) :=
    hf.integrable
  have hI : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s) (Ioi r) :=
    hfin.mono_set (Ioi_subset_Ioi hr.le)
  have hP : IntegrableOn (fun s : ℝ => s ^ (-3 : ℝ)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hr
  have hmaj : IntegrableOn (fun s : ℝ => 1 / (2 * r) * (‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s)
      + r / (8 * Real.pi) * s ^ (-3 : ℝ)) (Ioi r) :=
    (Integrable.const_mul hI _).add (Integrable.const_mul hP _)
  refine Integrable.mono' hmaj ?_ ?_
  · have hm : AEStronglyMeasurable f (volume.restrict (Ioi r)) :=
      hf.measurable.mono_set (Ioi_subset_Ioi hr.le)
    have hinv : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹) (Ioi r) := by
      apply ContinuousOn.inv₀ Complex.continuous_ofReal.continuousOn
      intro s hs
      have : (0 : ℝ) < s := lt_trans hr hs
      exact_mod_cast this.ne'
    exact (hinv.aestronglyMeasurable measurableSet_Ioi).mul hm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hr hs
    show ‖(s : ℂ)⁻¹ * f s‖ ≤ _
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have hpt := amgm_tail (w := Planar.gaussianWeightInv s) (s := s) (u := ‖f s‖) hr
      (weight_pos s) hs0
    have e : r / (8 * Real.pi) * s ^ (-3 : ℝ) = r / (8 * Real.pi * s ^ 3) := by
      rw [rpow_neg_three s hs0]
      ring
    have h2 : r / (2 * Planar.gaussianWeightInv s * s ^ 3) ≤ r / (8 * Real.pi * s ^ 3) := by
      apply div_le_div_of_nonneg_left hr.le
      · exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hs0 3)
      · nlinarith [mul_le_mul_of_nonneg_right (weight_ge s) (pow_pos hs0 3).le]
    rw [e]
    linarith

/-- Tail bound: `‖∫_r^∞ s⁻¹ q‖ ≤ (M/2 + 1/(16π))/r`. -/
lemma norm_tail_le {f : Planar.Profile} (hf : Planar.MemXG f) {r : ℝ} (hr : 0 < r) :
    ‖∫ s in Ioi r, (s : ℂ)⁻¹ * f s‖ ≤ (wMass f / 2 + 1 / (16 * Real.pi)) / r := by
  have hfin : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s) (Ioi 0) :=
    hf.integrable
  have hI : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s) (Ioi r) :=
    hfin.mono_set (Ioi_subset_Ioi hr.le)
  have hP : IntegrableOn (fun s : ℝ => s ^ (-3 : ℝ)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hr
  have hmaj : IntegrableOn (fun s : ℝ => 1 / (2 * r) * (‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s)
      + r / (8 * Real.pi) * s ^ (-3 : ℝ)) (Ioi r) :=
    (Integrable.const_mul hI _).add (Integrable.const_mul hP _)
  have hbd := norm_integral_le_of_norm_le hmaj (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hr hs
    show ‖(s : ℂ)⁻¹ * f s‖ ≤ _
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have hpt := amgm_tail (w := Planar.gaussianWeightInv s) (s := s) (u := ‖f s‖) hr
      (weight_pos s) hs0
    have e : r / (8 * Real.pi) * s ^ (-3 : ℝ) = r / (8 * Real.pi * s ^ 3) := by
      rw [rpow_neg_three s hs0]
      ring
    have h2 : r / (2 * Planar.gaussianWeightInv s * s ^ 3) ≤ r / (8 * Real.pi * s ^ 3) := by
      apply div_le_div_of_nonneg_left hr.le
      · exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hs0 3)
      · nlinarith [mul_le_mul_of_nonneg_right (weight_ge s) (pow_pos hs0 3).le]
    rw [e]
    linarith)
  refine hbd.trans ?_
  rw [integral_add (Integrable.const_mul hI _) (Integrable.const_mul hP _), integral_const_mul,
    integral_const_mul]
  have hA : ∫ s in Ioi r, ‖f s‖ ^ 2 * Planar.gaussianWeightInv s * s ≤ wMass f := by
    unfold wMass
    apply setIntegral_mono_set hfin
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (weight_pos s).le) (le_of_lt hs)
    · exact (Ioi_subset_Ioi hr.le).eventuallyLE
  have hB : ∫ s in Ioi r, s ^ (-3 : ℝ) = 1 / (2 * r ^ 2) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hr, show (-3 : ℝ) + 1 = -(2 : ℝ) by norm_num,
      Real.rpow_neg hr.le, Real.rpow_two]
    field_simp
  rw [hB]
  have h1 := mul_le_mul_of_nonneg_left hA
    (div_nonneg zero_le_one (mul_nonneg two_pos.le hr.le) : (0 : ℝ) ≤ 1 / (2 * r))
  have hfinal : 1 / (2 * r) * wMass f + r / (8 * Real.pi) * (1 / (2 * r ^ 2))
      = (wMass f / 2 + 1 / (16 * Real.pi)) / r := by
    field_simp
    ring
  linarith

/-- Split formula for the Green inverse. -/
lemma norm_greenInverse_le_split (f : Planar.Profile) {r : ℝ} (hr : 0 < r) :
    ‖Planar.greenInverse f r‖ ≤ 1 / 4 * (‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s‖ / r ^ 2
      + r ^ 2 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * f s‖) := by
  unfold Planar.greenInverse
  have e1 : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by
    rw [norm_neg, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_of_nonneg (by norm_num)]
  have e2 : ‖((r : ℂ) ^ 2)⁻¹‖ = (r ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have e3 : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [norm_mul, e1]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, e2, e3]
  ring

/-- Step 1: `‖G r‖ ≤ C₁ r` for every `r > 0`. -/
lemma greenInverse_order_one {f : Planar.Profile} (hf : Planar.MemXG f) {r : ℝ} (hr : 0 < r) :
    ‖Planar.greenInverse f r‖ ≤ (wMass f + 1 / (48 * Real.pi) + 1 / (16 * Real.pi)) / 4 * r := by
  have hsplit := norm_greenInverse_le_split f hr
  have hI1 := norm_head_le hf hr
  have hI2 := norm_tail_le hf hr
  have A1 : ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s‖ / r ^ 2
      ≤ r * (wMass f / 2 + 1 / (48 * Real.pi)) := by
    rw [div_le_iff₀ (pow_pos hr 2)]
    have e : r * (wMass f / 2 + 1 / (48 * Real.pi)) * r ^ 2
        = r ^ 3 / 2 * wMass f + r ^ 3 / (48 * Real.pi) := by
      ring
    linarith
  have A2 : r ^ 2 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * f s‖ ≤ r * (wMass f / 2 + 1 / (16 * Real.pi)) := by
    have h := mul_le_mul_of_nonneg_left hI2 (pow_pos hr 2).le
    have e : r ^ 2 * ((wMass f / 2 + 1 / (16 * Real.pi)) / r)
        = r * (wMass f / 2 + 1 / (16 * Real.pi)) := by
      field_simp
    linarith
  have E : 1 / 4 * (r * (wMass f / 2 + 1 / (48 * Real.pi))
      + r * (wMass f / 2 + 1 / (16 * Real.pi)))
      = (wMass f + 1 / (48 * Real.pi) + 1 / (16 * Real.pi)) / 4 * r := by
    ring
  linarith [hsplit, A1, A2, E]

lemma abs_strainK_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : |Planar.strainK s| ≤ 2 := by
  unfold Planar.strainK
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have h1 : |s ^ 2 / 4 - 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg s]
  have h2 : Real.exp (-(s ^ 2) / 4) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg s])
  have h3 : 0 ≤ Real.exp (-(s ^ 2) / 4) := (Real.exp_pos _).le
  have := mul_le_mul h1 h2 h3 (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- The eigen equation gives `‖q s‖ ≤ (4 / Re λ) ‖G s‖` on `(0, 1]`. -/
lemma norm_le_of_eigen {f : Planar.Profile} {lam : ℂ} (hlam : 0 < lam.re)
    (heig : ∀ r : ℝ, 0 < r → Planar.generatorL0 f r = lam * f r) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) :
    ‖f s‖ ≤ 4 / lam.re * ‖Planar.greenInverse f s‖ := by
  have h := heig s hs0
  unfold Planar.generatorL0 at h
  have hz : f s * (lam + 2 * Complex.I * (Planar.vortexOmega s : ℂ))
      = 2 * Complex.I * (Planar.strainK s : ℂ) * Planar.greenInverse f s := by
    linear_combination (-1 : ℂ) * h
  have hre : lam.re ≤ ‖lam + 2 * Complex.I * (Planar.vortexOmega s : ℂ)‖ := by
    have h1 := Complex.re_le_norm (lam + 2 * Complex.I * (Planar.vortexOmega s : ℂ))
    simpa using h1
  have hn : ‖f s‖ * ‖lam + 2 * Complex.I * (Planar.vortexOmega s : ℂ)‖
      = 2 * |Planar.strainK s| * ‖Planar.greenInverse f s‖ := by
    rw [← norm_mul, hz]
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hk : |Planar.strainK s| ≤ 2 := abs_strainK_le hs0 hs1
  have hGnn := norm_nonneg (Planar.greenInverse f s)
  have hfz : ‖f s‖ * lam.re ≤ ‖f s‖ * ‖lam + 2 * Complex.I * (Planar.vortexOmega s : ℂ)‖ :=
    mul_le_mul_of_nonneg_left hre (norm_nonneg _)
  have hkG : |Planar.strainK s| * ‖Planar.greenInverse f s‖ ≤ 2 * ‖Planar.greenInverse f s‖ :=
    mul_le_mul_of_nonneg_right hk hGnn
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
  linarith

/-- Step 2 assembly: `G = O(r²)` at `0`. -/
lemma greenInverse_order_two {f : Planar.Profile} {lam : ℂ} (hf : Planar.MemXG f)
    (hlam : 0 < lam.re) (heig : ∀ r : ℝ, 0 < r → Planar.generatorL0 f r = lam * f r) :
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖Planar.greenInverse f r‖ ≤ C * r ^ 2 := by
  obtain ⟨C1, hC1⟩ : ∃ x : ℝ, x = (wMass f + 1 / (48 * Real.pi) + 1 / (16 * Real.pi)) / 4 :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ x : ℝ, x = 4 * C1 / lam.re := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ x : ℝ, x = wMass f / 2 + 1 / (16 * Real.pi) := ⟨_, rfl⟩
  have hC1nn : 0 ≤ C1 := by
    rw [hC1]
    have := wMass_nonneg f
    have h1 : (0 : ℝ) ≤ 1 / (48 * Real.pi) := by positivity
    have h2 : (0 : ℝ) ≤ 1 / (16 * Real.pi) := by positivity
    linarith
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact div_nonneg (mul_nonneg (by norm_num) hC1nn) hlam.le
  have hDnn : 0 ≤ D := by
    rw [hD]
    have := wMass_nonneg f
    have h2 : (0 : ℝ) ≤ 1 / (16 * Real.pi) := by positivity
    linarith
  -- pointwise bound on `(0, 1]`
  have hq : ∀ s : ℝ, 0 < s → s ≤ 1 → ‖f s‖ ≤ K * s := by
    intro s hs0 hs1
    have h1 := norm_le_of_eigen hlam heig hs0 hs1
    have h2 := greenInverse_order_one hf hs0
    rw [← hC1] at h2
    have h3 : 4 / lam.re * ‖Planar.greenInverse f s‖ ≤ 4 / lam.re * (C1 * s) :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg (by norm_num) hlam.le)
    have h4 : 4 / lam.re * (C1 * s) = K * s := by
      rw [hK]
      ring
    linarith
  refine ⟨(2 * K + D) / 4, fun r hr hr1 => ?_⟩
  -- head integral
  have hI1 : ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s‖ ≤ K * r ^ 4 * r := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := r)
      (C := K * r ^ 4) (f := fun s : ℝ => (s : ℂ) ^ 3 * f s) (by
        intro x hx
        rw [Set.uIoc_of_le hr.le] at hx
        have hx0 : 0 < x := hx.1
        have hxr : x ≤ r := hx.2
        show ‖(x : ℂ) ^ 3 * f x‖ ≤ K * r ^ 4
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
        have hfx := hq x hx0 (le_trans hxr hr1)
        have h3 : 0 ≤ x ^ 3 := pow_nonneg hx0.le 3
        have h4 : x ^ 3 * ‖f x‖ ≤ x ^ 3 * (K * x) := mul_le_mul_of_nonneg_left hfx h3
        have h5 : x ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ hx0.le hxr 4
        have h6 : K * x ^ 4 ≤ K * r ^ 4 := mul_le_mul_of_nonneg_left h5 hKnn
        nlinarith)
    rw [sub_zero, abs_of_pos hr] at this
    exact this
  -- tail integral, split at `1`
  have hsplit : ∫ s in Ioi r, (s : ℂ)⁻¹ * f s
      = (∫ s in Ioc r 1, (s : ℂ)⁻¹ * f s) + ∫ s in Ioi (1 : ℝ), (s : ℂ)⁻¹ * f s := by
    have hu : Ioc r 1 ∪ Ioi (1 : ℝ) = Ioi r := Set.Ioc_union_Ioi_eq_Ioi hr1
    have hdisj : Disjoint (Ioc r 1) (Ioi (1 : ℝ)) :=
      Set.disjoint_left.2 (fun x hx1 hx2 => absurd hx1.2 (not_le.2 hx2))
    rw [← hu, setIntegral_union hdisj measurableSet_Ioi
      ((integrableOn_tail hf hr).mono_set Ioc_subset_Ioi_self)
      ((integrableOn_tail hf hr).mono_set (Ioi_subset_Ioi hr1))]
  have hJ1 : ‖∫ s in Ioc r 1, (s : ℂ)⁻¹ * f s‖ ≤ K := by
    rw [← intervalIntegral.integral_of_le hr1]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := 1) (C := K)
      (f := fun s : ℝ => (s : ℂ)⁻¹ * f s) (by
        intro x hx
        rw [Set.uIoc_of_le hr1] at hx
        have hx0 : 0 < x := lt_trans hr hx.1
        have hx1 : x ≤ 1 := hx.2
        show ‖(x : ℂ)⁻¹ * f x‖ ≤ K
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hx0.le]
        have hfx := hq x hx0 hx1
        calc x⁻¹ * ‖f x‖ ≤ x⁻¹ * (K * x) := mul_le_mul_of_nonneg_left hfx (inv_nonneg.2 hx0.le)
          _ = K := by field_simp)
    beta_reduce at this
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - r)] at this
    nlinarith
  have hJ2 : ‖∫ s in Ioi (1 : ℝ), (s : ℂ)⁻¹ * f s‖ ≤ D := by
    have := norm_tail_le hf (one_pos : (0 : ℝ) < 1)
    rw [div_one] at this
    rw [hD]
    exact this
  have hI2 : ‖∫ s in Ioi r, (s : ℂ)⁻¹ * f s‖ ≤ K + D := by
    rw [hsplit]
    have := norm_add_le (∫ s in Ioc r 1, (s : ℂ)⁻¹ * f s) (∫ s in Ioi (1 : ℝ), (s : ℂ)⁻¹ * f s)
    linarith
  have hG := norm_greenInverse_le_split f hr
  have hI1' : ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s‖ / r ^ 2 ≤ K * r ^ 2 := by
    rw [div_le_iff₀ (pow_pos hr 2)]
    have h5 : K * r ^ 4 * r ≤ K * r ^ 2 * r ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hKnn (pow_nonneg hr.le 4)) (sub_nonneg.2 hr1)]
    linarith [hI1, h5]
  have hI2' : r ^ 2 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * f s‖ ≤ r ^ 2 * (K + D) :=
    mul_le_mul_of_nonneg_left hI2 (pow_pos hr 2).le
  have E : 1 / 4 * (K * r ^ 2 + r ^ 2 * (K + D)) = (2 * K + D) / 4 * r ^ 2 := by
    ring
  have hsum := add_le_add hI1' hI2'
  have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [E] at hmul
  exact le_trans hG hmul

end GreenOrderTwoAux

/-- **Leaf `G4/2/1/a`** (bootstrap at the origin; SP 2347-2352). -/
theorem greenInverseOrderTwo : UnforcedLeray.Short.IIb.GreenInverseOrderTwo := by
  intro lam q h
  exact GreenOrderTwoAux.greenInverse_order_two h.memXG h.re_pos h.eigen

end UnforcedLeray.Short.IIb
