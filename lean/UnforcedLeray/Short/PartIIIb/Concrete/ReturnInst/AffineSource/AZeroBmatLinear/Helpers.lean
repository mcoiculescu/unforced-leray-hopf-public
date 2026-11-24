import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Lam
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AyDiffAt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.BmatLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Helpers for `AZeroBmatLinear` and `AZeroBmatBound` (source 4614-4618, 4757-4760, 4863-4864)

Shared lemmas on the Laplace integrand `t ↦ t^μ e^{-λt}(d(t) - i e(t))` of `aZero`, with
`B = Bmat ν μ χ A`:

* `azInt`, `aZero_eq_azInt` : the integrand and the unfolding of `aZero`;
* `abs_bd_le_frob`, `abs_be_le_frob`, `norm_azQ_le` : `|d|, |e| ≤ |B|`;
* `norm_azInt_le` : pointwise bound on `(0, T]`;
* `azBmat_zero`, `azBmat_aesm` : `B = 0` for `s > 11/10/ν`, measurability on `(0,∞)`;
* `integrableOn_azInt_of` : integrability from measurability, vanishing past `T`, and a bound;
* `azInt_bound_Ioc`, `integrableOn_azInt_Bmat` : the bound and integrability for `Bmat`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Laplace integrand `t^μ e^{-λt}(d(t) - i e(t))` of `aZero` with real `μ`. -/
def azInt (lam : ℂ) (μ : ℝ) (B : ℝ → Mat3) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ (μ : ℂ)) * Complex.exp (-lam * (t : ℂ)) *
    (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))

theorem aZero_eq_azInt (lam ell : ℂ) (μ : ℝ) (B : ℝ → Mat3) :
    aZero lam ell (μ : ℂ) B = -(1 / 2 : ℂ) * ell * ∫ t in Ioi (0 : ℝ), azInt lam μ B t :=
  rfl

/-! ## Frobenius-type bounds on the meridional parts -/

theorem abs_entry_le_frob (M : Mat3) (i j : Fin 3) : |M i j| ≤ frob M := by
  unfold frob
  apply Real.abs_le_sqrt
  have h1 : M i j ^ 2 ≤ ∑ j', M i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', M i j' ^ 2 ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
      (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

theorem abs_bd_le_frob (M : Mat3) : |Bd M| ≤ frob M := by
  have h1 := abs_le.1 (abs_entry_le_frob M 0 0)
  have h2 := abs_le.1 (abs_entry_le_frob M 2 2)
  unfold Bd
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_be_le_frob (M : Mat3) : |Be M| ≤ frob M := by
  have h1 := abs_le.1 (abs_entry_le_frob M 0 2)
  have h2 := abs_le.1 (abs_entry_le_frob M 2 0)
  unfold Be
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem norm_azQ_le (M : Mat3) :
    ‖((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ)‖ ≤ 2 * frob M := by
  have h1 := abs_bd_le_frob M
  have h2 := abs_be_le_frob M
  calc ‖((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ)‖
      ≤ ‖((Bd M : ℝ) : ℂ)‖ + ‖Complex.I * ((Be M : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ = |Bd M| + |Be M| := by
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ frob M + frob M := add_le_add h1 h2
    _ = 2 * frob M := by ring

/-! ## Pointwise bound on `(0, T]` -/

theorem norm_azInt_le (lam : ℂ) (μ : ℝ) (B : ℝ → Mat3) (T t : ℝ) (ht : 0 < t) (htT : t ≤ T)
    (hμ : 0 ≤ μ) :
    ‖azInt lam μ B t‖ ≤ (T ^ μ * Real.exp (|lam.re| * T)) * (2 * frob (B t)) := by
  have hP : ‖(t : ℂ) ^ (μ : ℂ)‖ ≤ T ^ μ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.ofReal_re]
    exact Real.rpow_le_rpow ht.le htT hμ
  have hTμ : 0 ≤ T ^ μ := (norm_nonneg _).trans hP
  have hE : ‖Complex.exp (-lam * (t : ℂ))‖ ≤ Real.exp (|lam.re| * T) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have hre : (-lam * (t : ℂ)).re = -lam.re * t := by simp
    rw [hre]
    have ha : 0 ≤ (|lam.re| + lam.re) * t :=
      mul_nonneg (by linarith [neg_abs_le lam.re]) ht.le
    have hb : 0 ≤ |lam.re| * (T - t) := mul_nonneg (abs_nonneg _) (by linarith)
    nlinarith [ha, hb]
  have hQ := norm_azQ_le (B t)
  have hsplit : ‖azInt lam μ B t‖ = ‖(t : ℂ) ^ (μ : ℂ)‖ * ‖Complex.exp (-lam * (t : ℂ))‖ *
      ‖((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)‖ := by
    unfold azInt
    rw [norm_mul, norm_mul]
  rw [hsplit]
  calc ‖(t : ℂ) ^ (μ : ℂ)‖ * ‖Complex.exp (-lam * (t : ℂ))‖ *
        ‖((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)‖
      ≤ (T ^ μ * Real.exp (|lam.re| * T)) *
          ‖((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul hP hE (norm_nonneg _) hTμ) (norm_nonneg _)
    _ ≤ (T ^ μ * Real.exp (|lam.re| * T)) * (2 * frob (B t)) :=
        mul_le_mul_of_nonneg_left hQ (mul_nonneg hTμ (Real.exp_pos _).le)

/-! ## The matrix `B = Bmat ν μ χ A` on `(0, ∞)` -/

theorem azBmat_zero {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) {ν : ℝ} (μ : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (t : ℝ) (ht : (11 / 10 : ℝ) / ν < t) :
    Bmat ν μ χ A t = 0 := by
  have hev : Ay ν χ A =ᶠ[𝓝 t] fun _ => (0 : Mat3) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs' : (11 / 10 : ℝ) / ν < s := hs
    have h11 : (11 / 10 : ℝ) ≤ ν * s := by
      have := (div_lt_iff₀ hν).1 hs'
      linarith [mul_comm ν s]
    simp only [Ay]
    rw [hχ.zero (ν * s) h11, zero_smul]
  have h0 : Ay ν χ A t = 0 := hev.eq_of_nhds
  show deriv (Ay ν χ A) t + (μ / t) • Ay ν χ A t = 0
  rw [hev.deriv_eq, deriv_const, h0, smul_zero, add_zero]

theorem azInt_zero_of_Bmat_zero (lam : ℂ) (μ : ℝ) (B : ℝ → Mat3) (t : ℝ) (h : B t = 0) :
    azInt lam μ B t = 0 := by
  unfold azInt
  rw [h]
  simp [Bd, Be]

theorem azBmat_aesm {as : ℝ} {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) {ν : ℝ} (μ : ℝ)
    (A : ℝ → Mat3) (hA : IsAffElem as A) :
    AEStronglyMeasurable (Bmat ν μ χ A) (volume.restrict (Ioi (0 : ℝ))) := by
  have hAy : ContinuousOn (Ay ν χ A) (Ioi 0) :=
    ((hχ.smooth.continuous.comp (continuous_const.mul continuous_id)).continuousOn).smul
      hA.smooth.continuousOn
  have hc : ContinuousOn (fun s : ℝ => (μ / s) • Ay ν χ A s) (Ioi 0) :=
    (continuousOn_const.div continuousOn_id (fun s hs => (mem_Ioi.1 hs).ne')).smul hAy
  show AEStronglyMeasurable (fun s => deriv (Ay ν χ A) s + (μ / s) • Ay ν χ A s) _
  exact (measurable_deriv (Ay ν χ A)).aestronglyMeasurable.add
    (hc.aestronglyMeasurable measurableSet_Ioi)

theorem azInt_aesm {as : ℝ} {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) {ν : ℝ} (μ : ℝ) (lam : ℂ)
    (A : ℝ → Mat3) (hA : IsAffElem as A) :
    AEStronglyMeasurable (azInt lam μ (Bmat ν μ χ A)) (volume.restrict (Ioi (0 : ℝ))) := by
  have hP : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) * Complex.exp (-lam * (t : ℂ)))
      (Ioi 0) := by
    apply ContinuousOn.mul
    · exact ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const
        (fun t ht => Complex.ofReal_mem_slitPlane.2 (mem_Ioi.1 ht))
    · exact (continuous_const.mul Complex.continuous_ofReal).cexp.continuousOn
  have hψ : Continuous (fun M : Mat3 => ((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ)) := by
    unfold Bd Be
    fun_prop
  exact (hP.aestronglyMeasurable measurableSet_Ioi).mul
    (hψ.comp_aestronglyMeasurable (azBmat_aesm hχ μ A hA))

/-! ## Integrability -/

theorem integrable_indicator_Ioc_const (T K : ℝ) :
    Integrable (Set.indicator (Ioc 0 T) (fun _ : ℝ => K)) (volume.restrict (Ioi (0 : ℝ))) := by
  have hfin : (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 T) ≠ ⊤ := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_left)
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const hfin

theorem real_restrict_Ioc_eq (T : ℝ) (hT : 0 ≤ T) :
    (volume.restrict (Ioi (0 : ℝ))).real (Ioc 0 T) = T := by
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 Set.Ioc_subset_Ioi_self, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hT]

theorem azInt_ae_le_indicator (lam : ℂ) (μ : ℝ) (B : ℝ → Mat3) (T K : ℝ)
    (hzero : ∀ t, T < t → azInt lam μ B t = 0)
    (hbd : ∀ t, 0 < t → t ≤ T → ‖azInt lam μ B t‖ ≤ K) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖azInt lam μ B t‖ ≤ Set.indicator (Ioc 0 T) (fun _ : ℝ => K) t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  by_cases htT : t ≤ T
  · have hmem : t ∈ Ioc 0 T := ⟨ht0, htT⟩
    rw [Set.indicator_of_mem hmem]
    exact hbd t ht0 htT
  · have hlt : T < t := not_le.1 htT
    have hmem : t ∉ Ioc 0 T := fun h => htT h.2
    rw [hzero t hlt, norm_zero, Set.indicator_apply, if_neg hmem]

theorem integrableOn_azInt_of (lam : ℂ) (μ : ℝ) (B : ℝ → Mat3) (T K : ℝ)
    (hmeas : AEStronglyMeasurable (azInt lam μ B) (volume.restrict (Ioi (0 : ℝ))))
    (hzero : ∀ t, T < t → azInt lam μ B t = 0)
    (hbd : ∀ t, 0 < t → t ≤ T → ‖azInt lam μ B t‖ ≤ K) :
    IntegrableOn (azInt lam μ B) (Ioi 0) :=
  Integrable.mono' (integrable_indicator_Ioc_const T K) hmeas
    (azInt_ae_le_indicator lam μ B T K hzero hbd)

/-! ## The bound on `(0, 11/10ν]` -/

/-- The constant `K` of the pointwise bound on `(0, 11/10ν]`. -/
def azK (lam : ℂ) (μ ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : ℝ :=
  ((11 / 10 : ℝ) / ν) ^ μ * Real.exp (|lam.re| * ((11 / 10 : ℝ) / ν)) *
    (2 * ((1 + μ) * ((11 / 10 : ℝ) / ν) ^ (3 / 2 : ℝ) * affM ν χ A))

theorem azK_nonneg {ν μ : ℝ} (hν : 0 < ν) (hμ : 0 ≤ μ) (lam : ℂ) (χ : ℝ → ℝ)
    (A : ℝ → Mat3) : 0 ≤ azK lam μ ν χ A := by
  have hT : 0 < (11 / 10 : ℝ) / ν := div_pos (by norm_num) hν
  unfold azK
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (Real.exp_pos _).le)
    (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hT.le _)) (affM_nonneg ν χ A)))

theorem azInt_bound_Ioc {as : ℝ} {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) {ν : ℝ} (μ : ℝ)
    (hν : 0 < ν) (hμ : 0 ≤ μ) (lam : ℂ) (A : ℝ → Mat3) (hA : IsAffElem as A) (t : ℝ)
    (ht : 0 < t) (htT : t ≤ (11 / 10 : ℝ) / ν) :
    ‖azInt lam μ (Bmat ν μ χ A) t‖ ≤ azK lam μ ν χ A := by
  have hT : 0 < (11 / 10 : ℝ) / ν := div_pos (by norm_num) hν
  have h1 := norm_azInt_le lam μ (Bmat ν μ χ A) ((11 / 10 : ℝ) / ν) t ht htT hμ
  have hb : frob (Bmat ν μ χ A t) ≤ (1 + μ) * t ^ (3 / 2 : ℝ) * affM ν χ A :=
    bmatBound as χ hχ ν μ hν hμ A hA t ht htT
  have hs : t ^ (3 / 2 : ℝ) ≤ ((11 / 10 : ℝ) / ν) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow ht.le htT (by norm_num)
  have hM := affM_nonneg ν χ A
  have hK0 : 0 ≤ ((11 / 10 : ℝ) / ν) ^ μ * Real.exp (|lam.re| * ((11 / 10 : ℝ) / ν)) :=
    mul_nonneg (Real.rpow_nonneg hT.le _) (Real.exp_pos _).le
  have h2 : (1 + μ) * t ^ (3 / 2 : ℝ) * affM ν χ A ≤
      (1 + μ) * ((11 / 10 : ℝ) / ν) ^ (3 / 2 : ℝ) * affM ν χ A :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by linarith)) hM
  unfold azK
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK0)
  linarith

theorem integrableOn_azInt_Bmat {as : ℝ} {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) {ν : ℝ}
    (μ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ) (lam : ℂ) (A : ℝ → Mat3) (hA : IsAffElem as A) :
    IntegrableOn (azInt lam μ (Bmat ν μ χ A)) (Ioi 0) :=
  integrableOn_azInt_of lam μ (Bmat ν μ χ A) ((11 / 10 : ℝ) / ν) (azK lam μ ν χ A)
    (azInt_aesm hχ μ lam A hA)
    (fun t ht => azInt_zero_of_Bmat_zero lam μ _ t (azBmat_zero hχ μ hν A t ht))
    (fun t ht0 htT => azInt_bound_Ioc hχ μ hν hμ lam A hA t ht0 htT)

end UnforcedLeray.Short.PartIIIb.Concrete
