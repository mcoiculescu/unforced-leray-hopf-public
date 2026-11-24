import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# `PartII-b:F8/2` helper: the smooth plane inequality, cutoffs and mollifiers

1. `smooth_lintegral_le`: for a `C¹` compactly supported `u : ℝ × ℝ → ℂ`,
   `∫ |u|^{11/4} ≤ (2C)^{3/4} (‖u‖₂ + ‖∂₁u‖₂ + ‖∂₂u‖₂)^{11/4}`, from the Gagliardo-Nirenberg-Sobolev
   inequality `‖w‖₂ ≤ C ‖Dw‖₁` of Mathlib applied to `w = |u|²` (Ladyzhenskaya) and Hölder between
   `L²` and `L⁴`.
2. `plateau a`: a smooth cutoff equal to `1` on `[-a, a]` and to `0` off `(-(a+1), a+1)`, with
   derivative bounded independently of `a`.
3. `kern n`: normalized smooth bumps on the plane supported in the ball of radius `1/(n+2)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb.FlatKH2

/-! ## 1. The smooth compactly supported bound on the plane -/

/-- Lebesgue measure on the plane `ℝ × ℝ` is an additive Haar measure. -/
instance instIsAddHaarMeasureVolumePlane : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- On `ℝ × ℝ` (sup norm) the operator norm is bounded by the two coordinate images. -/
theorem opNorm_le_coord {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ × ℝ →L[ℝ] F) : ‖A‖ ≤ ‖A (1, 0)‖ + ‖A (0, 1)‖ := by
  refine A.opNorm_le_bound (by positivity) (fun v => ?_)
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have h1 : |v.1| ≤ ‖v‖ := by
    have := norm_fst_le v
    rwa [Real.norm_eq_abs] at this
  have h2 : |v.2| ≤ ‖v‖ := by
    have := norm_snd_le v
    rwa [Real.norm_eq_abs] at this
  calc ‖A v‖ = ‖v.1 • A (1, 0) + v.2 • A (0, 1)‖ := by
        conv_lhs => rw [hv]
        rw [map_add, map_smul, map_smul]
    _ ≤ ‖v.1 • A (1, 0)‖ + ‖v.2 • A (0, 1)‖ := norm_add_le _ _
    _ = |v.1| * ‖A (1, 0)‖ + |v.2| * ‖A (0, 1)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖v‖ * ‖A (1, 0)‖ + ‖v‖ * ‖A (0, 1)‖ := by gcongr
    _ = (‖A (1, 0)‖ + ‖A (0, 1)‖) * ‖v‖ := by ring

/-- The Gagliardo-Nirenberg-Sobolev constant of `ℝ × ℝ` at `p = 2`. -/
def gnsC : ℝ≥0 := eLpNormLESNormFDerivOneConst (volume : Measure (ℝ × ℝ)) ((2 : ℝ≥0) : ℝ)

/-- Hölder's inequality for `‖f‖ ‖g‖` in `L² × L²`. -/
theorem lintegral_enorm_mul_le {f g : ℝ × ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    ∫⁻ y, ‖f y‖ₑ * ‖g y‖ₑ ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hf.enorm hg.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simpa using h

/-- The pointwise power identity `(a²)^{5/8} (a⁴)^{3/8} = a^{11/4}`. -/
theorem rpow_split (a : ℝ≥0∞) :
    (a ^ (2 : ℝ)) ^ (5 / 8 : ℝ) * (a ^ (4 : ℝ)) ^ (3 / 8 : ℝ) = a ^ (11 / 4 : ℝ) := by
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

/-- **Smooth plane inequality** (Ladyzhenskaya + Hölder):
`∫ |u|^{11/4} ≤ (2C)^{3/4} (‖u‖₂ + (‖∂₁u‖₂ + ‖∂₂u‖₂))^{11/4}`. -/
theorem smooth_lintegral_le {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) :
    ∫⁻ y, ‖u y‖ₑ ^ (11 / 4 : ℝ) ≤
      (2 * (gnsC : ℝ≥0∞)) ^ (3 / 4 : ℝ) *
        (eLpNorm u 2 volume + (eLpNorm (fun y => fderiv ℝ u y (1, 0)) 2 volume +
          eLpNorm (fun y => fderiv ℝ u y (0, 1)) 2 volume)) ^ (11 / 4 : ℝ) := by
  set A := eLpNorm u 2 volume with hA
  set D1 := eLpNorm (fun y => fderiv ℝ u y (1, 0)) 2 volume with hD1
  set D2 := eLpNorm (fun y => fderiv ℝ u y (0, 1)) 2 volume with hD2
  set C : ℝ≥0∞ := (gnsC : ℝ≥0∞) with hC
  have hcont : Continuous u := hu.continuous
  have hdiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hcd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hc1 : Continuous (fun y => fderiv ℝ u y (1, 0)) := hcd.clm_apply continuous_const
  have hc2 : Continuous (fun y => fderiv ℝ u y (0, 1)) := hcd.clm_apply continuous_const
  -- (1) the Gagliardo-Nirenberg-Sobolev inequality for `w = ‖u‖²`
  set w : ℝ × ℝ → ℝ := fun y => ‖u y‖ ^ 2 with hw_def
  have hw : ContDiff ℝ 1 w := hu.norm_sq ℝ
  have hwc : HasCompactSupport w :=
    hcs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hp : NNReal.HolderConjugate (Module.finrank ℝ (ℝ × ℝ) : ℝ≥0) 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
    norm_num
    exact NNReal.HolderConjugate.two_two
  have hgns := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure (ℝ × ℝ)) hw hwc hp
  -- (2) the pointwise derivative bound
  have hderiv : ∀ y, ‖fderiv ℝ w y‖ₑ ≤
      2 * (‖u y‖ₑ * ‖fderiv ℝ u y (1, 0)‖ₑ + ‖u y‖ₑ * ‖fderiv ℝ u y (0, 1)‖ₑ) := by
    intro y
    have h1 : HasFDerivAt w (2 • (innerSL ℝ (u y)).comp (fderiv ℝ u y)) y :=
      (hdiff y).hasFDerivAt.norm_sq
    rw [h1.fderiv]
    have e2 : ‖(2 • (innerSL ℝ (u y)).comp (fderiv ℝ u y))‖ ≤
        2 * ‖(innerSL ℝ (u y)).comp (fderiv ℝ u y)‖ := by
      rw [two_nsmul]
      exact (norm_add_le _ _).trans (le_of_eq (by ring))
    have hreal : ‖(2 • (innerSL ℝ (u y)).comp (fderiv ℝ u y))‖ ≤
        2 * (‖u y‖ * ‖fderiv ℝ u y (1, 0)‖ + ‖u y‖ * ‖fderiv ℝ u y (0, 1)‖) := by
      calc _ ≤ 2 * ‖(innerSL ℝ (u y)).comp (fderiv ℝ u y)‖ := e2
        _ ≤ 2 * (‖innerSL ℝ (u y)‖ * ‖fderiv ℝ u y‖) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 2 * (‖u y‖ * (‖fderiv ℝ u y (1, 0)‖ + ‖fderiv ℝ u y (0, 1)‖)) := by
            rw [innerSL_apply_norm]
            gcongr
            exact opNorm_le_coord _
        _ = _ := by ring
    calc ‖_‖ₑ = ENNReal.ofReal ‖(2 • (innerSL ℝ (u y)).comp (fderiv ℝ u y))‖ :=
          (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal
            (2 * (‖u y‖ * ‖fderiv ℝ u y (1, 0)‖ + ‖u y‖ * ‖fderiv ℝ u y (0, 1)‖)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = 2 * (‖u y‖ₑ * ‖fderiv ℝ u y (1, 0)‖ₑ + ‖u y‖ₑ * ‖fderiv ℝ u y (0, 1)‖ₑ) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _),
            ofReal_norm, ofReal_norm, ofReal_norm]
          norm_num
  -- (3) the `L¹` norm of `Dw`
  have hL1 : eLpNorm (fderiv ℝ w) 1 volume ≤ 2 * (A * D1 + A * D2) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hm1 : Measurable (fun y => ‖u y‖ₑ * ‖fderiv ℝ u y (1, 0)‖ₑ) :=
      hcont.enorm.measurable.mul hc1.enorm.measurable
    have hm2 : Measurable (fun y => ‖u y‖ₑ * ‖fderiv ℝ u y (0, 1)‖ₑ) :=
      hcont.enorm.measurable.mul hc2.enorm.measurable
    calc ∫⁻ y, ‖fderiv ℝ w y‖ₑ
        ≤ ∫⁻ y, 2 * (‖u y‖ₑ * ‖fderiv ℝ u y (1, 0)‖ₑ + ‖u y‖ₑ * ‖fderiv ℝ u y (0, 1)‖ₑ) :=
          lintegral_mono hderiv
      _ = 2 * ((∫⁻ y, ‖u y‖ₑ * ‖fderiv ℝ u y (1, 0)‖ₑ) +
            ∫⁻ y, ‖u y‖ₑ * ‖fderiv ℝ u y (0, 1)‖ₑ) := by
          rw [lintegral_const_mul _ (show Measurable (fun y => ‖u y‖ₑ * ‖fderiv ℝ u y (1, 0)‖ₑ +
            ‖u y‖ₑ * ‖fderiv ℝ u y (0, 1)‖ₑ) from hm1.add hm2), lintegral_add_left hm1]
      _ ≤ 2 * (A * D1 + A * D2) := by
          gcongr
          · exact lintegral_enorm_mul_le hcont.aestronglyMeasurable hc1.aestronglyMeasurable
          · exact lintegral_enorm_mul_le hcont.aestronglyMeasurable hc2.aestronglyMeasurable
  -- (4) the `L²` norm of `w` is `(∫ |u|⁴)^{1/2}`
  set I2 : ℝ≥0∞ := ∫⁻ y, ‖u y‖ₑ ^ (2 : ℝ) with hI2
  set I4 : ℝ≥0∞ := ∫⁻ y, ‖u y‖ₑ ^ (4 : ℝ) with hI4
  have hwpt : ∀ y, ‖w y‖ₑ = ‖u y‖ₑ ^ (2 : ℝ) := by
    intro y
    rw [hw_def, Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
    norm_cast
  have hw2 : eLpNorm w 2 volume = I4 ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), hI4]
    have : (fun y => ‖w y‖ₑ ^ (2 : ℝ≥0∞).toReal) = fun y => ‖u y‖ₑ ^ (4 : ℝ) := by
      funext y
      rw [hwpt y, ← ENNReal.rpow_mul]
      norm_num
    rw [this]
    norm_num
  have hA2 : A = I2 ^ (1 / 2 : ℝ) := by
    rw [hA, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), hI2]
    norm_num
  have h4 : I4 ^ (1 / 2 : ℝ) ≤ 2 * C * A * (D1 + D2) := by
    rw [← hw2]
    have hcoe : (((2 : ℝ≥0) : ℝ≥0∞)) = 2 := by norm_num
    rw [hcoe] at hgns
    calc eLpNorm w 2 volume ≤ C * eLpNorm (fderiv ℝ w) 1 volume := hgns
      _ ≤ C * (2 * (A * D1 + A * D2)) := by gcongr
      _ = 2 * C * A * (D1 + D2) := by ring
  -- (5) Hölder between `L²` and `L⁴`
  have hhol : ∫⁻ y, ‖u y‖ₑ ^ (11 / 4 : ℝ) ≤ I2 ^ (5 / 8 : ℝ) * I4 ^ (3 / 8 : ℝ) := by
    have h := ENNReal.lintegral_mul_norm_pow_le (μ := (volume : Measure (ℝ × ℝ)))
      (f := fun y => ‖u y‖ₑ ^ (2 : ℝ)) (g := fun y => ‖u y‖ₑ ^ (4 : ℝ))
      (hcont.enorm.measurable.pow_const _).aemeasurable
      (hcont.enorm.measurable.pow_const _).aemeasurable
      (p := 5 / 8) (q := 3 / 8) (by norm_num) (by norm_num) (by norm_num)
    simp only [rpow_split] at h
    exact h
  have hI2' : I2 ^ (5 / 8 : ℝ) = A ^ (5 / 4 : ℝ) := by
    rw [hA2, ← ENNReal.rpow_mul]
    norm_num
  have hI4' : I4 ^ (3 / 8 : ℝ) = (I4 ^ (1 / 2 : ℝ)) ^ (3 / 4 : ℝ) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  calc ∫⁻ y, ‖u y‖ₑ ^ (11 / 4 : ℝ)
      ≤ A ^ (5 / 4 : ℝ) * (2 * C * A * (D1 + D2)) ^ (3 / 4 : ℝ) := by
        rw [← hI2']
        refine hhol.trans ?_
        rw [hI4']
        gcongr
    _ = (2 * C) ^ (3 / 4 : ℝ) * (A ^ (5 / 4 : ℝ) * A ^ (3 / 4 : ℝ)) * (D1 + D2) ^ (3 / 4 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        ring
    _ = (2 * C) ^ (3 / 4 : ℝ) * A ^ (2 : ℝ) * (D1 + D2) ^ (3 / 4 : ℝ) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
        norm_num
    _ ≤ (2 * C) ^ (3 / 4 : ℝ) * (A + (D1 + D2)) ^ (2 : ℝ) *
          (A + (D1 + D2)) ^ (3 / 4 : ℝ) := by
        have hA' : A ^ (2 : ℝ) ≤ (A + (D1 + D2)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow le_self_add (by norm_num)
        have hD' : (D1 + D2) ^ (3 / 4 : ℝ) ≤ (A + (D1 + D2)) ^ (3 / 4 : ℝ) :=
          ENNReal.rpow_le_rpow le_add_self (by norm_num)
        exact mul_le_mul' (mul_le_mul' le_rfl hA') hD'
    _ = (2 * C) ^ (3 / 4 : ℝ) * (A + (D1 + D2)) ^ (11 / 4 : ℝ) := by
        rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
        norm_num

/-! ## 2. Smooth plateau cutoffs -/

/-- `|smoothTransition'|` is bounded. -/
theorem exists_deriv_smoothTransition_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv Real.smoothTransition x| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc (fun x hx => ?_)
    rcases not_and_or.mp (show ¬(0 ≤ x ∧ x ≤ 1) from hx) with h | h
    · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds (not_le.mp h)] with y hy
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [hev.deriv_eq]
      simp
    · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds (not_le.mp h)] with y hy
        exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
      rw [hev.deriv_eq]
      simp
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have := hC x
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- A fixed bound for `|smoothTransition'|`. -/
def stM : ℝ := Classical.choose exists_deriv_smoothTransition_bound

theorem stM_nonneg : 0 ≤ stM := (Classical.choose_spec exists_deriv_smoothTransition_bound).1

theorem abs_deriv_st_le (x : ℝ) : |deriv Real.smoothTransition x| ≤ stM :=
  (Classical.choose_spec exists_deriv_smoothTransition_bound).2 x

/-- The plateau `t ↦ st(1 + a - t) st(1 + a + t)`. -/
def plateau (a t : ℝ) : ℝ :=
  Real.smoothTransition (1 + a - t) * Real.smoothTransition (1 + a + t)

theorem contDiff_plateau (a : ℝ) : ContDiff ℝ ∞ (plateau a) := by
  unfold plateau
  exact ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id)).mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.add contDiff_id))

theorem plateau_nonneg (a t : ℝ) : 0 ≤ plateau a t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem plateau_le_one (a t : ℝ) : plateau a t ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem abs_plateau_le_one (a t : ℝ) : |plateau a t| ≤ 1 := by
  rw [abs_of_nonneg (plateau_nonneg a t)]
  exact plateau_le_one a t

theorem plateau_eq_one {a t : ℝ} (h : |t| ≤ a) : plateau a t = 1 := by
  have h1 := neg_abs_le t
  have h2 := le_abs_self t
  unfold plateau
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem plateau_eq_zero {a t : ℝ} (h : a + 1 ≤ |t|) : plateau a t = 0 := by
  unfold plateau
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht] at h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [abs_of_neg ht] at h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 1 + a + t ≤ 0), mul_zero]

theorem hasDerivAt_plateau (a t : ℝ) :
    HasDerivAt (plateau a)
      (-(deriv Real.smoothTransition (1 + a - t)) * Real.smoothTransition (1 + a + t) +
        Real.smoothTransition (1 + a - t) * deriv Real.smoothTransition (1 + a + t)) t := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun t => Real.smoothTransition (1 + a - t))
      (deriv Real.smoothTransition (1 + a - t) * (-1)) t :=
    (hd _).hasDerivAt.comp t ((hasDerivAt_id t).const_sub (1 + a))
  have h2 : HasDerivAt (fun t => Real.smoothTransition (1 + a + t))
      (deriv Real.smoothTransition (1 + a + t) * 1) t :=
    (hd _).hasDerivAt.comp t ((hasDerivAt_id t).const_add (1 + a))
  have h12 := h1.mul h2
  rw [show -(deriv Real.smoothTransition (1 + a - t)) * Real.smoothTransition (1 + a + t) +
      Real.smoothTransition (1 + a - t) * deriv Real.smoothTransition (1 + a + t) =
      deriv Real.smoothTransition (1 + a - t) * (-1) * Real.smoothTransition (1 + a + t) +
      Real.smoothTransition (1 + a - t) * (deriv Real.smoothTransition (1 + a + t) * 1) by ring]
  exact h12

theorem abs_deriv_plateau_le (a t : ℝ) : |deriv (plateau a) t| ≤ 2 * stM := by
  rw [(hasDerivAt_plateau a t).deriv]
  have e1 := abs_deriv_st_le (1 + a - t)
  have e2 := abs_deriv_st_le (1 + a + t)
  have s1 : |Real.smoothTransition (1 + a - t)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have s2 : |Real.smoothTransition (1 + a + t)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  calc _ ≤ |-(deriv Real.smoothTransition (1 + a - t)) * Real.smoothTransition (1 + a + t)| +
        |Real.smoothTransition (1 + a - t) * deriv Real.smoothTransition (1 + a + t)| :=
        abs_add_le _ _
    _ = |deriv Real.smoothTransition (1 + a - t)| * |Real.smoothTransition (1 + a + t)| +
        |Real.smoothTransition (1 + a - t)| * |deriv Real.smoothTransition (1 + a + t)| := by
        rw [abs_mul, abs_mul, abs_neg]
    _ ≤ stM * 1 + 1 * stM := by
        have hM := stM_nonneg
        gcongr
    _ = 2 * stM := by ring

/-- The plane cutoff `ζ(y) = plateau a y₁ · plateau b y₂`. -/
def cut2 (a b : ℝ) (y : ℝ × ℝ) : ℝ := plateau a y.1 * plateau b y.2

theorem contDiff_cut2 (a b : ℝ) : ContDiff ℝ ∞ (cut2 a b) := by
  unfold cut2
  exact ((contDiff_plateau a).comp contDiff_fst).mul ((contDiff_plateau b).comp contDiff_snd)

theorem abs_cut2_le_one (a b : ℝ) (y : ℝ × ℝ) : |cut2 a b y| ≤ 1 := by
  unfold cut2
  rw [abs_mul]
  exact mul_le_one₀ (abs_plateau_le_one _ _) (abs_nonneg _) (abs_plateau_le_one _ _)

theorem cut2_eq_zero {a b : ℝ} {y : ℝ × ℝ} (h : a + 1 ≤ |y.1|) : cut2 a b y = 0 := by
  unfold cut2
  rw [plateau_eq_zero h, zero_mul]

theorem hasCompactSupport_cut2 (a b : ℝ) : HasCompactSupport (cut2 a b) := by
  refine HasCompactSupport.intro (K := Icc (-(a + 1)) (a + 1) ×ˢ Icc (-(b + 1)) (b + 1))
    (isCompact_Icc.prod isCompact_Icc) (fun y hy => ?_)
  unfold cut2
  rw [Set.mem_prod, not_and_or] at hy
  rcases hy with h | h
  · rw [plateau_eq_zero (a := a) (t := y.1) ?_, zero_mul]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl h.le)
  · rw [plateau_eq_zero (a := b) (t := y.2) ?_, mul_zero]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl h.le)

theorem norm_fderiv_cut2_le (a b : ℝ) (y : ℝ × ℝ) : ‖fderiv ℝ (cut2 a b) y‖ ≤ 4 * stM := by
  have hA : HasFDerivAt (fun y : ℝ × ℝ => plateau a y.1)
      ((deriv (plateau a) y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) y :=
    ((contDiff_plateau a).differentiable (by simp) y.1).hasDerivAt.comp_hasFDerivAt y
      (hasFDerivAt_fst)
  have hB : HasFDerivAt (fun y : ℝ × ℝ => plateau b y.2)
      ((deriv (plateau b) y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
    ((contDiff_plateau b).differentiable (by simp) y.2).hasDerivAt.comp_hasFDerivAt y
      (hasFDerivAt_snd)
  have hAB : HasFDerivAt (cut2 a b)
      (plateau a y.1 • (deriv (plateau b) y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) +
        plateau b y.2 • (deriv (plateau a) y.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)) y :=
    hA.mul hB
  rw [hAB.fderiv]
  have hfst : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have hsnd : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  have d1 := abs_deriv_plateau_le a y.1
  have d2 := abs_deriv_plateau_le b y.2
  have p1 := abs_plateau_le_one a y.1
  have p2 := abs_plateau_le_one b y.2
  have hM := stM_nonneg
  calc ‖plateau a y.1 • (deriv (plateau b) y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) +
        plateau b y.2 • (deriv (plateau a) y.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)‖
      ≤ ‖plateau a y.1 • (deriv (plateau b) y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)‖ +
        ‖plateau b y.2 • (deriv (plateau a) y.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)‖ :=
        norm_add_le _ _
    _ = |plateau a y.1| * (|deriv (plateau b) y.2| * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖) +
        |plateau b y.2| * (|deriv (plateau a) y.1| * ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖) := by
        rw [norm_smul, norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * (2 * stM * 1) + 1 * (2 * stM * 1) := by
        gcongr
    _ = 4 * stM := by ring

theorem abs_fderiv_cut2_apply_le (a b : ℝ) (y v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) :
    |fderiv ℝ (cut2 a b) y v| ≤ 4 * stM := by
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ (cut2 a b) y v‖ ≤ ‖fderiv ℝ (cut2 a b) y‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (4 * stM) * 1 := by
        gcongr
        · exact mul_nonneg (by norm_num) stM_nonneg
        · exact norm_fderiv_cut2_le a b y
    _ = 4 * stM := by ring

/-! ## 3. Mollifiers on the plane -/

/-- The bump of radii `1/(2(n+2)) < 1/(n+2)` centered at `0`. -/
def bump (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := 1 / (2 * ((n : ℝ) + 2))
  rOut := 1 / ((n : ℝ) + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    apply one_div_lt_one_div_of_lt h
    linarith

/-- The normalized mollifier `K_n`. -/
def kern (n : ℕ) : ℝ × ℝ → ℝ := (bump n).normed volume

theorem kern_contDiff (n : ℕ) : ContDiff ℝ ∞ (kern n) := (bump n).contDiff_normed

theorem kern_hasCompactSupport (n : ℕ) : HasCompactSupport (kern n) :=
  (bump n).hasCompactSupport_normed

theorem kern_nonneg (n : ℕ) (y : ℝ × ℝ) : 0 ≤ kern n y := (bump n).nonneg_normed y

theorem kern_integral (n : ℕ) : ∫ y, kern n y = 1 := (bump n).integral_normed

theorem kern_integrable (n : ℕ) : Integrable (kern n) volume := (bump n).integrable_normed

theorem bump_rOut_tendsto : Tendsto (fun n => (bump n).rOut) atTop (𝓝 (0 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have he : (fun n => (bump n).rOut) = fun n : ℕ => ((n : ℝ) + 2)⁻¹ := by
    funext n
    simp [bump]
  rw [he]
  exact h.inv_tendsto_atTop

theorem bump_shape (n : ℕ) : (bump n).rOut ≤ 2 * (bump n).rIn := by
  simp only [bump]
  have h : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [mul_one_div, ← div_div, div_self (by norm_num : (2 : ℝ) ≠ 0)]

/-- `K_n` vanishes off the ball of radius `1/2`. -/
theorem kern_eq_zero {n : ℕ} {y : ℝ × ℝ} (hy : 1 / 2 ≤ ‖y‖) : kern n y = 0 := by
  have hs : y ∉ Function.support (kern n) := by
    rw [kern, (bump n).support_normed_eq, Metric.mem_ball, dist_zero_right, not_lt]
    refine le_trans ?_ hy
    simp only [bump]
    have h : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [one_div_le_one_div (by positivity) (by norm_num)]
    exact h
  simpa [Function.mem_support] using hs

end UnforcedLeray.Short.IIb.FlatKH2
