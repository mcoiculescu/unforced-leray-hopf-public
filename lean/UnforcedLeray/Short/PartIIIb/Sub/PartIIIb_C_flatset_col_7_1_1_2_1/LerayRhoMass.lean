import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRegKerCalc
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Mass of the regularised cylinder density (`RhoMass`)

Source `the November 2 reference manuscript` 1676: `ρ_ε = ΔΓ_ε` has mass one on a cell.
We write `ρ_ε = ∂_q K₀^ε + ∂_η K₁^ε` (`rm_rho_eq_sum`), bound both pieces by an integrable
majorant `M (1 + (a η)²)⁻¹`, and integrate: the `q`-derivative integrates to zero over each
`η`-slice (fundamental theorem of calculus, periodicity of `sin`), and the `η`-derivative
integrates to `a/2π = 1/c` over each `q`-slice (limits `±a/4π` of `K₁^ε`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-! ## Slice derivatives and continuity -/

lemma rm_hasDerivAt_slice0 (g : ℝ × ℝ → ℝ) (hg : Differentiable ℝ g) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => g (t, y.2)) (pd2 0 g y) y.1 := by
  have hl : HasDerivAt (fun t : ℝ => ((t, y.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) y.1 :=
    (hasDerivAt_id' y.1).prodMk (hasDerivAt_const y.1 y.2)
  have hc : HasFDerivAt g (fderiv ℝ g y) (y.1, y.2) := (hg y).hasFDerivAt
  have h2 := hc.comp_hasDerivAt y.1 hl
  have hdir : dir2 0 = ((1 : ℝ), (0 : ℝ)) := by simp [dir2]
  unfold pd2
  rw [hdir]
  exact h2

lemma rm_hasDerivAt_slice1 (g : ℝ × ℝ → ℝ) (hg : Differentiable ℝ g) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => g (y.1, t)) (pd2 1 g y) y.2 := by
  have hl : HasDerivAt (fun t : ℝ => ((y.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id' y.2)
  have hc : HasFDerivAt g (fderiv ℝ g y) (y.1, y.2) := (hg y).hasFDerivAt
  have h2 := hc.comp_hasDerivAt y.2 hl
  have hdir : dir2 1 = ((0 : ℝ), (1 : ℝ)) := by simp [dir2]
  unfold pd2
  rw [hdir]
  exact h2

lemma rm_continuous_pd2 (i : Fin 2) (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    Continuous (pd2 i g) := by
  unfold pd2
  exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const

/-! ## Explicit forms of the two partial derivatives -/

lemma rm_pd2_K0 (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) :
    pd2 0 (cylKerReg c ε 0) y =
      cylFreq c ^ 2 / (4 * Real.pi) *
        (Real.cos (cylFreq c * y.1) * Real.cosh (cylFreq c * y.2) + ε * Real.cos (cylFreq c * y.1) - 1) /
        (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) ^ 2 := by
  rw [(rm_hasDerivAt_slice0 (cylKerReg c ε 0) ((contDiff_cylKerReg_zero c ε hε).differentiable (by simp)) y).unique
    (hasDerivAt_K0_q c ε hε y)]
  have hSC : Real.sin (cylFreq c * y.1) ^ 2 + Real.cos (cylFreq c * y.1) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  congr 1
  linear_combination (-(cylFreq c ^ 2 / (4 * Real.pi))) * hSC

lemma rm_pd2_K1 (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) :
    pd2 1 (cylKerReg c ε 1) y =
      cylFreq c ^ 2 / (4 * Real.pi) *
        (Real.cosh (cylFreq c * y.2) * (ε - Real.cos (cylFreq c * y.1)) + 1) /
        (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) ^ 2 := by
  rw [(rm_hasDerivAt_slice1 (cylKerReg c ε 1) ((contDiff_cylKerReg_one c ε hε).differentiable (by simp)) y).unique
    (hasDerivAt_K1_eta c ε hε y)]
  have hH : Real.cosh (cylFreq c * y.2) ^ 2 = Real.sinh (cylFreq c * y.2) ^ 2 + 1 :=
    Real.cosh_sq _
  congr 1
  linear_combination (cylFreq c ^ 2 / (4 * Real.pi)) * hH

lemma rm_rho_eq_sum (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) :
    cylRho c ε y = pd2 0 (cylKerReg c ε 0) y + pd2 1 (cylKerReg c ε 1) y := by
  rw [rm_pd2_K0 c ε hε y, rm_pd2_K1 c ε hε y, ← add_div]
  unfold cylRho cylDen
  congr 1
  ring

lemma rm_rho_nonneg (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) : 0 ≤ cylRho c ε y := by
  have hs : 0 ≤ Real.cosh (cylFreq c * y.2) + Real.cos (cylFreq c * y.1) := by
    linarith [Real.one_le_cosh (cylFreq c * y.2), Real.neg_one_le_cos (cylFreq c * y.1)]
  unfold cylRho
  exact div_nonneg (mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hε.le) (by positivity)) hs)
    (sq_nonneg _)

/-! ## Elementary bounds -/

lemma rm_cylFreq_pos (c : ℝ) (hc : 0 < c) : 0 < cylFreq c := by
  unfold cylFreq
  exact div_pos (by positivity) hc

lemma rm_one_add_sq_div_four_le_cosh (x : ℝ) : (1 + x ^ 2) / 4 ≤ Real.cosh x := by
  have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have h2 := Real.add_one_le_exp (-|x|)
  have h3 : Real.cosh x = (Real.exp |x| + Real.exp (-|x|)) / 2 := by
    rw [← Real.cosh_eq, Real.cosh_abs]
  have h4 : |x| ^ 2 = x ^ 2 := sq_abs x
  rw [h3]
  rw [h4] at h1
  linarith

lemma rm_abs_core (A e κ C x N D : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e) (hκ : 0 < κ)
    (hC1 : 1 ≤ C) (hCx : (1 + x ^ 2) / 4 ≤ C) (hN : |N| ≤ (e + 2) * C) (hD : κ * C ≤ D) :
    |A * N / D ^ 2| ≤ A * (4 * (e + 2) / κ ^ 2) * (1 + x ^ 2)⁻¹ := by
  have hCpos : 0 < C := by linarith
  have hDpos : 0 < D := lt_of_lt_of_le (mul_pos hκ hCpos) hD
  have hx1 : 0 < 1 + x ^ 2 := by positivity
  have hkC : 0 < κ * C := mul_pos hκ hCpos
  have hAe : 0 ≤ A * (4 * (e + 2) / κ ^ 2) :=
    mul_nonneg hA (div_nonneg (by linarith) (by positivity))
  have h4 : (4 * C)⁻¹ ≤ (1 + x ^ 2)⁻¹ := inv_anti₀ hx1 (by linarith)
  have hstep1 : |A * N / D ^ 2| ≤ A * ((e + 2) * C) / (κ * C) ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hA, abs_of_pos (pow_pos hDpos 2)]
    have hnum : A * |N| ≤ A * ((e + 2) * C) := mul_le_mul_of_nonneg_left hN hA
    have hden : (κ * C) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hkC.le hD 2
    have hA0 : 0 ≤ A * |N| := mul_nonneg hA (abs_nonneg N)
    calc A * |N| / D ^ 2 ≤ A * ((e + 2) * C) / D ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ A * ((e + 2) * C) / (κ * C) ^ 2 :=
          div_le_div_of_nonneg_left (mul_nonneg hA (by positivity)) (by positivity) hden
  have hstep2 : A * ((e + 2) * C) / (κ * C) ^ 2 = A * (4 * (e + 2) / κ ^ 2) * (4 * C)⁻¹ := by
    have hκne : κ ≠ 0 := hκ.ne'
    have hCne : C ≠ 0 := hCpos.ne'
    field_simp
  have hstep3 : A * (4 * (e + 2) / κ ^ 2) * (4 * C)⁻¹ ≤ A * (4 * (e + 2) / κ ^ 2) * (1 + x ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_left h4 hAe
  rw [hstep2] at hstep1
  exact hstep1.trans hstep3

lemma rm_bound_P0 (c ε κ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hκ : 0 < κ) (hκε : κ ≤ ε)
    (hκ1 : κ ≤ 1) (y : ℝ × ℝ) :
    |pd2 0 (cylKerReg c ε 0) y| ≤
      cylFreq c ^ 2 / (4 * Real.pi) * (4 * (ε + 2) / κ ^ 2) * (1 + (cylFreq c * y.2) ^ 2)⁻¹ := by
  rw [rm_pd2_K0 c ε hε y]
  have hc1 := Real.one_le_cosh (cylFreq c * y.2)
  have hcos1 := Real.cos_le_one (cylFreq c * y.1)
  have hcosm := Real.neg_one_le_cos (cylFreq c * y.1)
  have hC0 : 0 ≤ Real.cosh (cylFreq c * y.2) := by linarith
  refine rm_abs_core (cylFreq c ^ 2 / (4 * Real.pi)) ε κ (Real.cosh (cylFreq c * y.2))
    (cylFreq c * y.2) _ _ (by positivity) hε.le hκ hc1 (rm_one_add_sq_div_four_le_cosh _) ?_ ?_
  · rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.cos (cylFreq c * y.1) + 1) hC0,
        mul_nonneg hε.le (by linarith : (0:ℝ) ≤ Real.cos (cylFreq c * y.1) + 1),
        mul_nonneg (by linarith : (0:ℝ) ≤ ε + 1) (by linarith : (0:ℝ) ≤ Real.cosh (cylFreq c * y.2) - 1)]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - Real.cos (cylFreq c * y.1)) hC0,
        mul_nonneg hε.le (by linarith : (0:ℝ) ≤ 1 - Real.cos (cylFreq c * y.1)),
        mul_nonneg hε.le (by linarith : (0:ℝ) ≤ Real.cosh (cylFreq c * y.2) - 1)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - κ) (by linarith : (0:ℝ) ≤ Real.cosh (cylFreq c * y.2) - 1)]

lemma rm_bound_P1 (c ε κ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hκ : 0 < κ) (hκε : κ ≤ ε)
    (hκ1 : κ ≤ 1) (y : ℝ × ℝ) :
    |pd2 1 (cylKerReg c ε 1) y| ≤
      cylFreq c ^ 2 / (4 * Real.pi) * (4 * (ε + 2) / κ ^ 2) * (1 + (cylFreq c * y.2) ^ 2)⁻¹ := by
  rw [rm_pd2_K1 c ε hε y]
  have hc1 := Real.one_le_cosh (cylFreq c * y.2)
  have hcos1 := Real.cos_le_one (cylFreq c * y.1)
  have hcosm := Real.neg_one_le_cos (cylFreq c * y.1)
  have hC0 : 0 ≤ Real.cosh (cylFreq c * y.2) := by linarith
  refine rm_abs_core (cylFreq c ^ 2 / (4 * Real.pi)) ε κ (Real.cosh (cylFreq c * y.2))
    (cylFreq c * y.2) _ _ (by positivity) hε.le hκ hc1 (rm_one_add_sq_div_four_le_cosh _) ?_ ?_
  · rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.cos (cylFreq c * y.1) + 1) hC0,
        mul_nonneg hε.le hC0, mul_nonneg hε.le (by linarith : (0:ℝ) ≤ Real.cosh (cylFreq c * y.2) - 1)]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - Real.cos (cylFreq c * y.1)) hC0,
        mul_nonneg hε.le hC0, mul_nonneg hε.le (by linarith : (0:ℝ) ≤ Real.cosh (cylFreq c * y.2) - 1)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - κ) (by linarith : (0:ℝ) ≤ Real.cosh (cylFreq c * y.2) - 1)]

/-! ## Integrability -/

lemma rm_integrable_majorant (c M : ℝ) (hc : 0 < c) :
    Integrable (fun η : ℝ => M * (1 + (cylFreq c * η) ^ 2)⁻¹) := by
  have h := integrable_inv_one_add_sq.comp_mul_left' (rm_cylFreq_pos c hc).ne'
  exact h.const_mul M

lemma rm_integrableOn_cell_snd (c : ℝ) (g : ℝ → ℝ) (hg : Integrable g) :
    IntegrableOn (fun y : ℝ × ℝ => g y.2) (cellC c) := by
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (-(c / 2)) (c / 2)) := integrableOn_const (by simp)
  have hg' : Integrable g (volume.restrict (univ : Set ℝ)) := by
    rw [Measure.restrict_univ]; exact hg
  have h := Integrable.mul_prod h1 hg'
  simp only [one_mul] at h
  rw [Measure.prod_restrict] at h
  unfold cellC
  exact h

lemma rm_integrableOn_cell_fst (c : ℝ) (g : ℝ → ℝ) (hg : Integrable g) :
    IntegrableOn (fun z : ℝ × ℝ => g z.1) ((univ : Set ℝ) ×ˢ Ioc (-(c / 2)) (c / 2)) := by
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (-(c / 2)) (c / 2)) := integrableOn_const (by simp)
  have hg' : Integrable g (volume.restrict (univ : Set ℝ)) := by
    rw [Measure.restrict_univ]; exact hg
  have h := Integrable.mul_prod hg' h1
  simp only [mul_one] at h
  rw [Measure.prod_restrict] at h
  exact h

lemma rm_integrableOn_P0 (c ε κ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hκ : 0 < κ) (hκε : κ ≤ ε)
    (hκ1 : κ ≤ 1) : IntegrableOn (pd2 0 (cylKerReg c ε 0)) (cellC c) := by
  refine Integrable.mono'
    (rm_integrableOn_cell_snd c _
      (rm_integrable_majorant c (cylFreq c ^ 2 / (4 * Real.pi) * (4 * (ε + 2) / κ ^ 2)) hc)) ?_ ?_
  · exact (rm_continuous_pd2 0 _ (contDiff_cylKerReg_zero c ε hε)).aestronglyMeasurable
  · exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs]
      exact rm_bound_P0 c ε κ hc hε hκ hκε hκ1 y)

lemma rm_integrableOn_P1 (c ε κ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hκ : 0 < κ) (hκε : κ ≤ ε)
    (hκ1 : κ ≤ 1) : IntegrableOn (pd2 1 (cylKerReg c ε 1)) (cellC c) := by
  refine Integrable.mono'
    (rm_integrableOn_cell_snd c _
      (rm_integrable_majorant c (cylFreq c ^ 2 / (4 * Real.pi) * (4 * (ε + 2) / κ ^ 2)) hc)) ?_ ?_
  · exact (rm_continuous_pd2 1 _ (contDiff_cylKerReg_one c ε hε)).aestronglyMeasurable
  · exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs]
      exact rm_bound_P1 c ε κ hc hε hκ hκε hκ1 y)

/-! ## Limits of the ratio `sinh t / (cosh t + m)` -/

lemma rm_tendsto_ratio_atTop (m : ℝ) (hm : ∀ t : ℝ, 0 < Real.cosh t + m) :
    Tendsto (fun t : ℝ => Real.sinh t / (Real.cosh t + m)) atTop (𝓝 1) := by
  have h2 : Tendsto (fun t : ℝ => Real.exp t / 2) atTop atTop :=
    Real.tendsto_exp_atTop.atTop_div_const (by norm_num)
  have hcosh : Tendsto (fun t : ℝ => Real.cosh t) atTop atTop :=
    tendsto_atTop_mono (fun t => by rw [Real.cosh_eq]; linarith [Real.exp_pos (-t)]) h2
  have hD : Tendsto (fun t : ℝ => Real.cosh t + m) atTop atTop :=
    tendsto_atTop_add_const_right _ m hcosh
  have hq : Tendsto (fun t : ℝ => (-Real.exp (-t) - m) / (Real.cosh t + m)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop ((Real.tendsto_exp_neg_atTop_nhds_zero.neg).sub_const m) hD
  have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + (-Real.exp (-t) - m) / (Real.cosh t + m)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hq
    rw [add_zero] at this
    exact this
  refine h1.congr (fun t => ?_)
  show (1 : ℝ) + (-Real.exp (-t) - m) / (Real.cosh t + m) = Real.sinh t / (Real.cosh t + m)
  rw [one_add_div (hm t).ne']
  congr 1
  linarith [Real.sinh_sub_cosh (x := t)]

lemma rm_tendsto_ratio_atBot (m : ℝ) (hm : ∀ t : ℝ, 0 < Real.cosh t + m) :
    Tendsto (fun t : ℝ => Real.sinh t / (Real.cosh t + m)) atBot (𝓝 (-1)) := by
  have h1 : Tendsto (fun t : ℝ => Real.sinh (-t) / (Real.cosh (-t) + m)) atBot (𝓝 1) :=
    (rm_tendsto_ratio_atTop m hm).comp tendsto_neg_atBot_atTop
  have h2 := h1.neg
  refine h2.congr (fun t => ?_)
  show -(Real.sinh (-t) / (Real.cosh (-t) + m)) = Real.sinh t / (Real.cosh t + m)
  rw [Real.sinh_neg, Real.cosh_neg]
  ring

/-! ## The `η`-integral of `∂_η K₁^ε` over one `q`-slice -/

lemma rm_integral_inner (c ε κ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hκ : 0 < κ) (hκε : κ ≤ ε)
    (hκ1 : κ ≤ 1) (q : ℝ) :
    ∫ η, pd2 1 (cylKerReg c ε 1) (q, η) = 1 / c := by
  have hdiff : Differentiable ℝ (cylKerReg c ε 1) :=
    (contDiff_cylKerReg_one c ε hε).differentiable (by simp)
  have hderiv : ∀ η : ℝ, HasDerivAt (fun t : ℝ => cylKerReg c ε 1 (q, t))
      (pd2 1 (cylKerReg c ε 1) (q, η)) η :=
    fun η => rm_hasDerivAt_slice1 (cylKerReg c ε 1) hdiff (q, η)
  have hint : Integrable (fun η : ℝ => pd2 1 (cylKerReg c ε 1) (q, η)) := by
    refine Integrable.mono' (rm_integrable_majorant c (cylFreq c ^ 2 / (4 * Real.pi) * (4 * (ε + 2) / κ ^ 2)) hc)
      ?_ ?_
    · exact ((rm_continuous_pd2 1 _ (contDiff_cylKerReg_one c ε hε)).comp
        (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    · exact ae_of_all _ (fun η => by
        rw [Real.norm_eq_abs]
        exact rm_bound_P1 c ε κ hc hε hκ hκε hκ1 (q, η))
  -- positivity of the denominator in the slice
  have hm : ∀ t : ℝ, 0 < Real.cosh t + (ε - Real.cos (cylFreq c * q)) := fun t => by
    linarith [Real.one_le_cosh t, Real.cos_le_one (cylFreq c * q)]
  have hfun : (fun η : ℝ => cylKerReg c ε 1 (q, η)) = fun η : ℝ =>
      cylFreq c / (4 * Real.pi) *
        (Real.sinh (cylFreq c * η) / (Real.cosh (cylFreq c * η) + (ε - Real.cos (cylFreq c * q)))) := by
    funext η
    simp only [cylKerReg_one_eq]
    rw [mul_div_assoc]
    rw [show Real.cosh (cylFreq c * η) - Real.cos (cylFreq c * q) + ε =
        Real.cosh (cylFreq c * η) + (ε - Real.cos (cylFreq c * q)) by ring]
  have hlim_top : Tendsto (fun η : ℝ => cylKerReg c ε 1 (q, η)) atTop
      (𝓝 (cylFreq c / (4 * Real.pi) * 1)) := by
    rw [hfun]
    exact ((rm_tendsto_ratio_atTop _ hm).comp
      (Filter.Tendsto.const_mul_atTop (rm_cylFreq_pos c hc) tendsto_id)).const_mul _
  have hlim_bot : Tendsto (fun η : ℝ => cylKerReg c ε 1 (q, η)) atBot
      (𝓝 (cylFreq c / (4 * Real.pi) * (-1))) := by
    rw [hfun]
    exact ((rm_tendsto_ratio_atBot _ hm).comp
      (Filter.Tendsto.const_mul_atBot (rm_cylFreq_pos c hc) tendsto_id)).const_mul _
  have hc0 : c ≠ 0 := hc.ne'
  refine (integral_of_hasDerivAt_of_tendsto hderiv hint hlim_bot hlim_top).trans ?_
  unfold cylFreq
  field_simp
  ring

/-! ## The two pieces integrate to `0` and `1` over the cell -/

lemma rm_integral_P0_slice (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (η : ℝ) :
    ∫ q in Ioc (-(c / 2)) (c / 2), pd2 0 (cylKerReg c ε 0) (q, η) = 0 := by
  have hdiff : Differentiable ℝ (cylKerReg c ε 0) :=
    (contDiff_cylKerReg_zero c ε hε).differentiable (by simp)
  have hderiv : ∀ t ∈ uIcc (-(c / 2)) (c / 2),
      HasDerivAt (fun s : ℝ => cylKerReg c ε 0 (s, η)) (pd2 0 (cylKerReg c ε 0) (t, η)) t :=
    fun t _ => rm_hasDerivAt_slice0 (cylKerReg c ε 0) hdiff (t, η)
  have hint : IntervalIntegrable (fun t : ℝ => pd2 0 (cylKerReg c ε 0) (t, η)) volume (-(c / 2)) (c / 2) :=
    ((rm_continuous_pd2 0 _ (contDiff_cylKerReg_zero c ε hε)).comp
      (Continuous.prodMk continuous_id continuous_const)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have e1 : cylFreq c * (c / 2) = Real.pi := by
    unfold cylFreq
    have hc0 : c ≠ 0 := hc.ne'
    field_simp
  have e2 : cylFreq c * (-(c / 2)) = -Real.pi := by rw [mul_neg, e1]
  simp [cylKerReg_zero_eq, e1, e2]

lemma rm_integral_P0_cell (c ε κ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hκ : 0 < κ) (hκε : κ ≤ ε)
    (hκ1 : κ ≤ 1) : ∫ y in cellC c, pd2 0 (cylKerReg c ε 0) y = 0 := by
  have hint : IntegrableOn (fun z : ℝ × ℝ => pd2 0 (cylKerReg c ε 0) z.swap)
      ((univ : Set ℝ) ×ˢ Ioc (-(c / 2)) (c / 2)) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine Integrable.mono'
      (rm_integrableOn_cell_fst c _
        (rm_integrable_majorant c (cylFreq c ^ 2 / (4 * Real.pi) * (4 * (ε + 2) / κ ^ 2)) hc)) ?_ ?_
    · exact ((rm_continuous_pd2 0 _ (contDiff_cylKerReg_zero c ε hε)).comp
        continuous_swap).aestronglyMeasurable
    · exact ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs]
        exact rm_bound_P0 c ε κ hc hε hκ hκε hκ1 z.swap)
  calc ∫ y in cellC c, pd2 0 (cylKerReg c ε 0) y
      = ∫ z in (univ : Set ℝ) ×ˢ Ioc (-(c / 2)) (c / 2), pd2 0 (cylKerReg c ε 0) z.swap :=
        (setIntegral_prod_swap (μ := volume) (ν := volume) (Ioc (-(c / 2)) (c / 2)) (univ : Set ℝ)
          (pd2 0 (cylKerReg c ε 0))).symm
    _ = ∫ η in (univ : Set ℝ), ∫ q in Ioc (-(c / 2)) (c / 2), pd2 0 (cylKerReg c ε 0) (q, η) :=
        setIntegral_prod (μ := volume) (ν := volume)
          (fun z : ℝ × ℝ => pd2 0 (cylKerReg c ε 0) z.swap) hint
    _ = ∫ η in (univ : Set ℝ), (0 : ℝ) :=
        setIntegral_congr_fun MeasurableSet.univ (fun η _ => rm_integral_P0_slice c ε hc hε η)
    _ = 0 := by simp

lemma rm_integral_P1_cell (c ε κ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hκ : 0 < κ) (hκε : κ ≤ ε)
    (hκ1 : κ ≤ 1) : ∫ y in cellC c, pd2 1 (cylKerReg c ε 1) y = 1 := by
  have hc0 : c ≠ 0 := hc.ne'
  have hint : IntegrableOn (fun z : ℝ × ℝ => pd2 1 (cylKerReg c ε 1) z)
      (Ioc (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    rm_integrableOn_P1 c ε κ hc hε hκ hκε hκ1
  calc ∫ y in cellC c, pd2 1 (cylKerReg c ε 1) y
      = ∫ x in Ioc (-(c / 2)) (c / 2), ∫ y in (univ : Set ℝ), pd2 1 (cylKerReg c ε 1) (x, y) :=
        setIntegral_prod (μ := volume) (ν := volume)
          (fun z : ℝ × ℝ => pd2 1 (cylKerReg c ε 1) z) hint
    _ = ∫ x in Ioc (-(c / 2)) (c / 2), (1 / c : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioc (fun x _ => by
          rw [Measure.restrict_univ]
          exact rm_integral_inner c ε κ hc hε hκ hκε hκ1 x)
    _ = 1 := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul]
        field_simp
        ring

/-! ## The mass of `ρ_ε` -/

theorem rhoMass : RhoMass := by
  intro c ε hc hε
  obtain ⟨κ, hκ, hκε, hκ1⟩ : ∃ κ : ℝ, 0 < κ ∧ κ ≤ ε ∧ κ ≤ 1 :=
    ⟨min ε 1, lt_min hε one_pos, min_le_left _ _, min_le_right _ _⟩
  have hP0 := rm_integrableOn_P0 c ε κ hc hε hκ hκε hκ1
  have hP1 := rm_integrableOn_P1 c ε κ hc hε hκ hκε hκ1
  refine ⟨fun y => rm_rho_nonneg c ε hε y, ?_, ?_⟩
  · exact IntegrableOn.congr_fun (Integrable.add hP0 hP1)
      (fun y _ => (rm_rho_eq_sum c ε hε y).symm) (measurableSet_Ioc.prod MeasurableSet.univ)
  · have hsplit : ∫ y in cellC c, cylRho c ε y =
        ∫ y in cellC c, (pd2 0 (cylKerReg c ε 0) y + pd2 1 (cylKerReg c ε 1) y) :=
      setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ)
        (fun y _ => rm_rho_eq_sum c ε hε y)
    rw [hsplit, integral_add hP0 hP1, rm_integral_P0_cell c ε κ hc hε hκ hκε hκ1,
      rm_integral_P1_cell c ε κ hc hε hκ hκε hκ1]
    norm_num

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
