import UnforcedLeray.Units.B0306.Conv
import UnforcedLeray.Units.B0306.Gauss
import UnforcedLeray.Units.B0306.Cutoff
import UnforcedLeray.Units.B0306.Taylor

/-!
# B0306: heat smoothing of `|x|^{-1}`-type fields (`background:eq:2.48`)

Blueprint unit B0306, `paper/main.tex` lines 5909--5921 (infrastructure INF29, old ledger C21):

> If `b` is smooth off zero and `|D^j b(x)| ≤ C_j |x|^{-1-j}`, Gaussian convolution gives
> `|D^j(e^{νΔ}b - b)(y)| ≤ C_{j,ν} |y|^{-3-j}` for `|y| ≥ 1`.

Conventions.
* `e^{νΔ}b` is the compiled heat integral `UnforcedLeray.Heat.average ν b`,
  `y ↦ ∫ x, K_ν(x) • b(y - x)`, with `K_ν = UnforcedLeray.Heat.kernel ν` the Gaussian
  `(4πν)^{-3/2} e^{-|x|²/(4ν)}`. The heat integral is a Bochner integral, so we also prove that
  its integrand is integrable at every point (`heat_integrable`): the value is not a junk `0`.
* `D^j` is `iteratedFDeriv ℝ j`. The datum `b` is only assumed smooth on `{0}ᶜ`; its value at
  `0` is irrelevant (a null set for the integral, and `D^j b(y)` for `|y| ≥ 1` only sees `b` near
  `y`). We prove `e^{νΔ}b` is `C^∞` on all of space (`heat_contDiff`), so `D^j(e^{νΔ}b - b)(y)` is
  an honest derivative at `|y| ≥ 1`, not a junk value.
* The hypothesis `IsInverseDistanceField b` is exactly the manuscript's: smooth off zero and
  `|D^j b(x)| ≤ C_j |x|^{-1-j}` for every `j` and every `x ≠ 0`. The datum takes values in any
  real Banach space `F` (the manuscript applies it to vector fields).

Proof (tex lines 5915--5921). With a fixed smooth cutoff, `b = nearPart b + farPart b`
(`Units/B0306/Cutoff.lean`). The near part is integrable and supported in `|x| < 1/2`; its
smoothing is differentiated through the Gaussian (`Units/B0306/Conv.lean`), and since
`|y - x| ≥ |y|/2` on its support the result is `O(e^{-|y|²/(32ν)})` ("the off-ball convolution is
exponentially small ... differentiating the Gaussian, without differentiating the singular datum
at zero"). The far part is smooth with bounded derivatives and equals `b` near `y`; with
`g = D^j(farPart b)`, `D^j(e^{νΔ}farPart b) - g = ∫ K_ν(x)(g(y - x) - g(y)) dx`. Subtracting the
first-order Taylor term, whose Gaussian integral vanishes (`integral_kernel_smul_odd`), leaves the
remainder `T(x)`; for `|x| ≤ |y|/4` it is `≤ C_{j+2}(4/3)^{j+3}|y|^{-3-j}|x|²` by the quadratic
Taylor bound on `B̄(y, |y|/4)` (`Units/B0306/Taylor.lean`), and for `|x| > |y|/4` it is
`≤ (2M₀ + M₁|x|)(4|x|/|y|)^{j+3}`. Gaussian moments of every order are finite
(`Units/B0306/Gauss.lean`), which gives `C|y|^{-3-j}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology

namespace UnforcedLeray.B0306

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The hypothesis of `background:eq:2.48` (tex lines 5909--5910): `b` is smooth off zero and
`|D^j b(x)| ≤ C_j |x|^{-1-j}` for every order `j` and every `x ≠ 0`. -/
structure IsInverseDistanceField (b : Space → F) : Prop where
  smooth : ContDiffOn ℝ ∞ b {0}ᶜ
  bound : ∃ C : ℕ → ℝ, ∀ j x, x ≠ 0 → ‖iteratedFDeriv ℝ j b x‖ ≤ C j / ‖x‖ ^ (j + 1)

variable [CompleteSpace F]

set_option linter.unusedSectionVars false

/-! ### The two pieces of the heat integral -/

theorem average_farPart_eq (ν : ℝ) (b : Space → F) :
    Heat.average ν (farPart b) =
      bconv (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F) (Heat.kernel ν) (farPart b) := by
  funext y
  simp only [Heat.average, bconv, ContinuousLinearMap.lsmul_apply]

theorem average_nearPart_eq (ν : ℝ) (b : Space → F) :
    Heat.average ν (nearPart b) =
      bconv (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip (nearPart b)
        (Heat.kernel ν) := by
  funext y
  simp only [Heat.average, bconv, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]
  have h := integral_sub_left_eq_self (fun x => Heat.kernel ν (y - x) • nearPart b x)
    (volume : Measure Space) y
  simp only [sub_sub_cancel] at h
  exact h

theorem integrable_near_integrand {ν : ℝ} (hν : 0 < ν) {b : Space → F}
    (hnear : Integrable (nearPart b)) (y : Space) :
    Integrable (fun x => Heat.kernel ν x • nearPart b (y - x)) := by
  have hf : Integrable (fun x => nearPart b (y - x)) := hnear.comp_sub_left y
  refine hf.bdd_smul (Heat.Gaussian.normalization (4 * ν))
    (Kernels.heatKernel_smooth ν).continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Heat.kernel_nonneg hν x)]
  exact Heat.Gaussian.kernel_le_normalization (by positivity) x

theorem integrable_far_integrand {ν : ℝ} (hν : 0 < ν) {b : Space → F}
    (hfs : ContDiff ℝ ∞ (farPart b)) (hfb : BddDerivs (farPart b)) (y : Space) :
    Integrable (fun x => Heat.kernel ν x • farPart b (y - x)) := by
  obtain ⟨M, hM⟩ := hfb 0
  refine (Heat.kernel_integrable hν).smul_bdd M
    (hfs.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  simpa using hM (y - x)

theorem average_eq_add {ν : ℝ} (hν : 0 < ν) {b : Space → F} (hnear : Integrable (nearPart b))
    (hfs : ContDiff ℝ ∞ (farPart b)) (hfb : BddDerivs (farPart b)) :
    Heat.average ν b = Heat.average ν (nearPart b) + Heat.average ν (farPart b) := by
  funext y
  simp only [Heat.average, Pi.add_apply]
  rw [← integral_add (integrable_near_integrand hν hnear y)
    (integrable_far_integrand hν hfs hfb y)]
  congr 1
  funext x
  rw [← smul_add, nearPart_add_farPart]

/-- The near piece: derivatives fall on the Gaussian. -/
theorem average_nearPart_contDiff {ν : ℝ} (hν : 0 < ν) {b : Space → F}
    (hnear : Integrable (nearPart b)) (n : ℕ) :
    ContDiff ℝ n (Heat.average ν (nearPart b)) ∧
      iteratedFDeriv ℝ n (Heat.average ν (nearPart b)) = fun y => ∫ x,
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip
          (nearPart b x)).compContinuousMultilinearMap
            (iteratedFDeriv ℝ n (Heat.kernel ν) (y - x)) := by
  rw [average_nearPart_eq]
  exact iteratedFDeriv_bconv hnear n _ _ (Kernels.heatKernel_smooth ν) (kernel_bddDerivs hν)

/-- The far piece: derivatives fall on the (smooth, bounded) far part of the datum. -/
theorem average_farPart_contDiff {ν : ℝ} (hν : 0 < ν) {b : Space → F}
    (hfs : ContDiff ℝ ∞ (farPart b)) (hfb : BddDerivs (farPart b)) (n : ℕ) :
    ContDiff ℝ n (Heat.average ν (farPart b)) ∧
      iteratedFDeriv ℝ n (Heat.average ν (farPart b)) =
        fun y => ∫ x, Heat.kernel ν x • iteratedFDeriv ℝ n (farPart b) (y - x) := by
  rw [average_farPart_eq]
  obtain ⟨h1, h2⟩ := iteratedFDeriv_bconv (Heat.kernel_integrable hν) n
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F) (farPart b) hfs hfb
  refine ⟨h1, ?_⟩
  rw [h2]
  funext y
  congr 1

/-! ### The near term: exponentially small -/

theorem near_term_bound {ν : ℝ} (hν : 0 < ν) {b : Space → F} (hnear : Integrable (nearPart b))
    (j : ℕ) : ∃ CI : ℝ, 0 ≤ CI ∧ ∀ y : Space, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ j (Heat.average ν (nearPart b)) y‖ ≤
        CI * Real.exp (-((32 * ν)⁻¹ * ‖y‖ ^ 2)) := by
  have hE0n : 0 ≤ Kernels.heatDerivConst j * ν ^ (-((3 + j : ℝ) / 2)) :=
    mul_nonneg (Kernels.heatDerivConst_pos j).le (Real.rpow_nonneg hν.le _)
  have hN1n : 0 ≤ ∫ x, ‖nearPart b x‖ := integral_nonneg fun x => norm_nonneg _
  refine ⟨‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip‖ * (∫ x, ‖nearPart b x‖) *
    (Kernels.heatDerivConst j * ν ^ (-((3 + j : ℝ) / 2))),
    mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hN1n) hE0n, fun y hy => ?_⟩
  rw [(average_nearPart_contDiff hν hnear j).2]
  have hpt : ∀ x, ‖((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip
        (nearPart b x)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j (Heat.kernel ν) (y - x))‖ ≤
      ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip‖ * ‖nearPart b x‖ *
        ((Kernels.heatDerivConst j * ν ^ (-((3 + j : ℝ) / 2))) *
          Real.exp (-((32 * ν)⁻¹ * ‖y‖ ^ 2))) := by
    intro x
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    by_cases hx : ‖x‖ < 1 / 2
    · have hyx : ‖y‖ / 2 ≤ ‖y - x‖ := by
        have := norm_sub_norm_le y x
        linarith
      have h3 : (‖y‖ / 2) ^ 2 ≤ ‖y - x‖ ^ 2 := pow_le_pow_left₀ (by positivity) hyx 2
      have h4 : (32 * ν)⁻¹ * ‖y‖ ^ 2 ≤ ‖y - x‖ ^ 2 / (8 * ν) := by
        rw [show (32 * ν)⁻¹ * ‖y‖ ^ 2 = (‖y‖ / 2) ^ 2 / (8 * ν) by field_simp; ring]
        exact div_le_div_of_nonneg_right h3 (by positivity)
      have h5 : Real.exp (-‖y - x‖ ^ 2 / (8 * ν)) ≤ Real.exp (-((32 * ν)⁻¹ * ‖y‖ ^ 2)) := by
        apply Real.exp_le_exp.2
        rw [neg_div]
        linarith
      have h6 : ‖iteratedFDeriv ℝ j (Heat.kernel ν) (y - x)‖ ≤
          (Kernels.heatDerivConst j * ν ^ (-((3 + j : ℝ) / 2))) *
            Real.exp (-((32 * ν)⁻¹ * ‖y‖ ^ 2)) :=
        (Kernels.norm_iteratedFDeriv_heatKernel_le j hν (y - x)).trans
          (mul_le_mul_of_nonneg_left h5 hE0n)
      exact mul_le_mul (ContinuousLinearMap.le_opNorm _ _) h6 (norm_nonneg _)
        (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _))
    · simp [nearPart_eq_zero b (not_lt.1 hx)]
  have hint : Integrable (fun x =>
      ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip‖ * ‖nearPart b x‖ *
        ((Kernels.heatDerivConst j * ν ^ (-((3 + j : ℝ) / 2))) *
          Real.exp (-((32 * ν)⁻¹ * ‖y‖ ^ 2)))) :=
    (hnear.norm.const_mul _).mul_const _
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_const_mul]
  ring

/-! ### The far term: Taylor expansion and the vanishing first moment -/

/-- Pointwise bound on the first-order Taylor remainder of `g = D^j(farPart b)` about `y`. -/
theorem far_remainder_pointwise {b : Space → F} (hb : ContDiffOn ℝ ∞ b {0}ᶜ) {C : ℕ → ℝ}
    (hC : ∀ j x, x ≠ 0 → ‖iteratedFDeriv ℝ j b x‖ ≤ C j / ‖x‖ ^ (j + 1)) (j : ℕ) {M0 M1 : ℝ}
    (hM0 : ∀ x, ‖iteratedFDeriv ℝ j (farPart b) x‖ ≤ M0)
    (hM1 : ∀ x, ‖iteratedFDeriv ℝ (j + 1) (farPart b) x‖ ≤ M1) {y : Space} (hy : 1 ≤ ‖y‖)
    (x : Space) :
    ‖iteratedFDeriv ℝ j (farPart b) (y - x) - iteratedFDeriv ℝ j (farPart b) y -
        fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x)‖ ≤
      (‖y‖ ^ (j + 3))⁻¹ * (C (j + 2) / (3 / 4) ^ (j + 3) * ‖x‖ ^ 2 +
        4 ^ (j + 3) * (2 * M0 * ‖x‖ ^ (j + 3) + M1 * ‖x‖ ^ (j + 4))) := by
  have hfs := farPart_smooth hb
  have hR0 : 0 < ‖y‖ := by linarith
  have hM0n : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hA : 0 ≤ C (j + 2) / (3 / 4) ^ (j + 3) := div_nonneg (bound_nonneg hC _) (by positivity)
  have hRp : 0 < ‖y‖ ^ (j + 3) := pow_pos hR0 _
  have htail : 0 ≤ 4 ^ (j + 3) * (2 * M0 * ‖x‖ ^ (j + 3) + M1 * ‖x‖ ^ (j + 4)) :=
    mul_nonneg (by positivity) (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hM0n) (by positivity))
      (mul_nonneg hM1n (by positivity)))
  by_cases hx : ‖x‖ ≤ ‖y‖ / 4
  · have hMball : ∀ z ∈ closedBall y (‖y‖ / 4), ‖iteratedFDeriv ℝ (j + 2) (farPart b) z‖ ≤
        C (j + 2) / (3 / 4) ^ (j + 3) / ‖y‖ ^ (j + 3) := by
      intro z hz
      have hz' : 3 / 4 * ‖y‖ ≤ ‖z‖ := by
        have h1 := mem_closedBall.1 hz
        rw [dist_eq_norm] at h1
        have h2 := norm_sub_norm_le y z
        rw [norm_sub_rev] at h2
        linarith
      have hz0 : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz'
        linarith
      have hzbig : 1 / 2 < ‖z‖ := by linarith
      rw [((farPart_eventuallyEq b hzbig).iteratedFDeriv ℝ (j + 2)).eq_of_nhds]
      calc ‖iteratedFDeriv ℝ (j + 2) b z‖ ≤ C (j + 2) / ‖z‖ ^ (j + 2 + 1) := hC _ z hz0
        _ ≤ C (j + 2) / (3 / 4 * ‖y‖) ^ (j + 3) :=
          div_le_div_of_nonneg_left (bound_nonneg hC _) (by positivity)
            (pow_le_pow_left₀ (by positivity) hz' _)
        _ = C (j + 2) / (3 / 4) ^ (j + 3) / ‖y‖ ^ (j + 3) := by
          rw [mul_pow, div_mul_eq_div_div]
    have ht := taylor_two hfs j hMball hx
    calc _ ≤ C (j + 2) / (3 / 4) ^ (j + 3) / ‖y‖ ^ (j + 3) * ‖x‖ ^ 2 := ht
      _ = (‖y‖ ^ (j + 3))⁻¹ * (C (j + 2) / (3 / 4) ^ (j + 3) * ‖x‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right htail) (inv_nonneg.2 hRp.le)
  · push Not at hx
    have hφ : ‖fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y‖ ≤ M1 := by
      rw [norm_fderiv_iteratedFDeriv]; exact hM1 y
    have h1 : ‖iteratedFDeriv ℝ j (farPart b) (y - x) - iteratedFDeriv ℝ j (farPart b) y -
        fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x)‖ ≤ 2 * M0 + M1 * ‖x‖ := by
      calc _ ≤ ‖iteratedFDeriv ℝ j (farPart b) (y - x) - iteratedFDeriv ℝ j (farPart b) y‖ +
            ‖fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x)‖ := norm_sub_le _ _
        _ ≤ (‖iteratedFDeriv ℝ j (farPart b) (y - x)‖ + ‖iteratedFDeriv ℝ j (farPart b) y‖) +
            ‖fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y‖ * ‖-x‖ :=
          add_le_add (norm_sub_le _ _) (ContinuousLinearMap.le_opNorm _ _)
        _ ≤ (M0 + M0) + M1 * ‖x‖ := by
          rw [norm_neg]
          exact add_le_add (add_le_add (hM0 _) (hM0 _))
            (mul_le_mul hφ le_rfl (norm_nonneg _) hM1n)
        _ = 2 * M0 + M1 * ‖x‖ := by ring
    have h4 : 1 ≤ 4 * ‖x‖ / ‖y‖ := by rw [le_div_iff₀ hR0]; linarith
    have h5 : 1 ≤ (4 * ‖x‖ / ‖y‖) ^ (j + 3) := one_le_pow₀ h4
    have h6 : 2 * M0 + M1 * ‖x‖ ≤ (2 * M0 + M1 * ‖x‖) * (4 * ‖x‖ / ‖y‖) ^ (j + 3) :=
      le_mul_of_one_le_right (add_nonneg (mul_nonneg (by norm_num) hM0n)
        (mul_nonneg hM1n (norm_nonneg _))) h5
    have h7 : (2 * M0 + M1 * ‖x‖) * (4 * ‖x‖ / ‖y‖) ^ (j + 3) =
        (‖y‖ ^ (j + 3))⁻¹ * (4 ^ (j + 3) * (2 * M0 * ‖x‖ ^ (j + 3) + M1 * ‖x‖ ^ (j + 4))) := by
      rw [div_pow, mul_pow, div_eq_mul_inv]
      ring
    calc _ ≤ 2 * M0 + M1 * ‖x‖ := h1
      _ ≤ _ := h6
      _ = _ := h7
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (mul_nonneg hA (by positivity))) (inv_nonneg.2 hRp.le)

/-- The far term `D^j(e^{νΔ} farPart b) - D^j farPart b` is `O(|y|^{-3-j})`. -/
theorem far_term_bound {ν : ℝ} (hν : 0 < ν) {b : Space → F} (hb : ContDiffOn ℝ ∞ b {0}ᶜ)
    {C : ℕ → ℝ} (hC : ∀ j x, x ≠ 0 → ‖iteratedFDeriv ℝ j b x‖ ≤ C j / ‖x‖ ^ (j + 1)) (j : ℕ) :
    ∃ CII : ℝ, ∀ y : Space, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ j (Heat.average ν (farPart b)) y -
          iteratedFDeriv ℝ j (farPart b) y‖ ≤ CII / ‖y‖ ^ (j + 3) := by
  have hfs := farPart_smooth hb
  have hfb := farPart_bddDerivs hb hC
  obtain ⟨M0, hM0⟩ := hfb j
  obtain ⟨M1, hM1⟩ := hfb (j + 1)
  have hK := Heat.kernel_integrable hν
  have hKn : ∀ x, 0 ≤ Heat.kernel ν x := Heat.kernel_nonneg hν
  have hQ : Integrable (fun x => Heat.kernel ν x * (C (j + 2) / (3 / 4) ^ (j + 3) * ‖x‖ ^ 2 +
        4 ^ (j + 3) * (2 * M0 * ‖x‖ ^ (j + 3) + M1 * ‖x‖ ^ (j + 4)))) := by
    have e : (fun x => Heat.kernel ν x * (C (j + 2) / (3 / 4) ^ (j + 3) * ‖x‖ ^ 2 +
        4 ^ (j + 3) * (2 * M0 * ‖x‖ ^ (j + 3) + M1 * ‖x‖ ^ (j + 4)))) =
        fun x => C (j + 2) / (3 / 4) ^ (j + 3) * (‖x‖ ^ 2 * Heat.kernel ν x) +
          4 ^ (j + 3) * (2 * M0 * (‖x‖ ^ (j + 3) * Heat.kernel ν x) +
            M1 * (‖x‖ ^ (j + 4) * Heat.kernel ν x)) := by
      funext x; ring
    rw [e]
    exact ((integrable_pow_mul_kernel hν 2).const_mul _).add
      ((((integrable_pow_mul_kernel hν (j + 3)).const_mul _).add
        ((integrable_pow_mul_kernel hν (j + 4)).const_mul _)).const_mul _)
  refine ⟨∫ x, Heat.kernel ν x * (C (j + 2) / (3 / 4) ^ (j + 3) * ‖x‖ ^ 2 +
        4 ^ (j + 3) * (2 * M0 * ‖x‖ ^ (j + 3) + M1 * ‖x‖ ^ (j + 4))), fun y hy => ?_⟩
  rw [(average_farPart_contDiff hν hfs hfb j).2]
  have hg : Continuous (iteratedFDeriv ℝ j (farPart b)) :=
    hfs.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have i1 : Integrable (fun x => Heat.kernel ν x • iteratedFDeriv ℝ j (farPart b) (y - x)) :=
    hK.smul_bdd M0 (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun x => hM0 (y - x))
  have i2 : Integrable (fun x => Heat.kernel ν x • iteratedFDeriv ℝ j (farPart b) y) :=
    hK.smul_const _
  have i3 : Integrable (fun x => Heat.kernel ν x •
      fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x)) := by
    refine ((integrable_pow_mul_kernel hν 1).const_mul
      ‖fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y‖).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((Kernels.heatKernel_smooth ν).continuous.smul
        ((fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y).continuous.comp
          continuous_neg)).aestronglyMeasurable
    · rw [norm_smul, Real.norm_of_nonneg (hKn x), pow_one]
      calc Heat.kernel ν x * ‖fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x)‖
          ≤ Heat.kernel ν x * (‖fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y‖ * ‖x‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (hKn x)
            simpa [norm_neg] using
              (fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y).le_opNorm (-x)
        _ = ‖fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y‖ * (‖x‖ * Heat.kernel ν x) := by ring
  have i4 : Integrable (fun x => Heat.kernel ν x •
      (iteratedFDeriv ℝ j (farPart b) (y - x) - iteratedFDeriv ℝ j (farPart b) y -
        fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x))) := by
    refine ((i1.sub i2).sub i3).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, smul_sub]
  have hgy : (∫ x, Heat.kernel ν x • iteratedFDeriv ℝ j (farPart b) y) =
      iteratedFDeriv ℝ j (farPart b) y := by
    rw [integral_smul_const, Heat.integral_kernel hν, one_smul]
  have hodd : ∫ x, Heat.kernel ν x • fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x) = 0 :=
    integral_kernel_smul_odd ν (fun x => fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x))
      (fun x => by simp only [neg_neg, ContinuousLinearMap.map_neg])
  have hsplit : (∫ x, Heat.kernel ν x • iteratedFDeriv ℝ j (farPart b) (y - x)) -
      iteratedFDeriv ℝ j (farPart b) y =
      ∫ x, Heat.kernel ν x • (iteratedFDeriv ℝ j (farPart b) (y - x) -
        iteratedFDeriv ℝ j (farPart b) y - fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x)) := by
    calc (∫ x, Heat.kernel ν x • iteratedFDeriv ℝ j (farPart b) (y - x)) -
          iteratedFDeriv ℝ j (farPart b) y
        = (∫ x, Heat.kernel ν x • iteratedFDeriv ℝ j (farPart b) (y - x)) -
          ∫ x, Heat.kernel ν x • iteratedFDeriv ℝ j (farPart b) y := by rw [hgy]
      _ = ∫ x, (Heat.kernel ν x • iteratedFDeriv ℝ j (farPart b) (y - x) -
          Heat.kernel ν x • iteratedFDeriv ℝ j (farPart b) y) := (integral_sub i1 i2).symm
      _ = ∫ x, (Heat.kernel ν x • (iteratedFDeriv ℝ j (farPart b) (y - x) -
          iteratedFDeriv ℝ j (farPart b) y - fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x)) +
          Heat.kernel ν x • fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x)) := by
        congr 1
        funext x
        rw [← smul_add, sub_add_cancel, smul_sub]
      _ = (∫ x, Heat.kernel ν x • (iteratedFDeriv ℝ j (farPart b) (y - x) -
          iteratedFDeriv ℝ j (farPart b) y - fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x))) +
          ∫ x, Heat.kernel ν x • fderiv ℝ (iteratedFDeriv ℝ j (farPart b)) y (-x) :=
        integral_add i4 i3
      _ = _ := by rw [hodd, add_zero]
  rw [hsplit]
  refine (norm_integral_le_of_norm_le (hQ.const_mul (‖y‖ ^ (j + 3))⁻¹)
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
  · rw [norm_smul, Real.norm_of_nonneg (hKn x)]
    calc _ ≤ Heat.kernel ν x * ((‖y‖ ^ (j + 3))⁻¹ * (C (j + 2) / (3 / 4) ^ (j + 3) * ‖x‖ ^ 2 +
          4 ^ (j + 3) * (2 * M0 * ‖x‖ ^ (j + 3) + M1 * ‖x‖ ^ (j + 4)))) :=
        mul_le_mul_of_nonneg_left (far_remainder_pointwise hb hC j hM0 hM1 hy x) (hKn x)
      _ = _ := by ring
  · rw [integral_const_mul, inv_mul_eq_div]

/-! ### The unit -/

/-- The heat integral of an inverse-distance field converges absolutely at every point. -/
theorem heat_integrable {b : Space → F} (hb : IsInverseDistanceField b) {ν : ℝ} (hν : 0 < ν)
    (y : Space) : Integrable (fun x => Heat.kernel ν x • b (y - x)) := by
  obtain ⟨C, hC⟩ := hb.bound
  have h := (integrable_near_integrand hν (nearPart_integrable hb.smooth hC) y).add
    (integrable_far_integrand hν (farPart_smooth hb.smooth) (farPart_bddDerivs hb.smooth hC) y)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, ← smul_add, nearPart_add_farPart]

/-- `e^{νΔ}b` is smooth on all of space. -/
theorem heat_contDiff {b : Space → F} (hb : IsInverseDistanceField b) {ν : ℝ} (hν : 0 < ν) :
    ContDiff ℝ ∞ (Heat.average ν b) := by
  obtain ⟨C, hC⟩ := hb.bound
  have hnear := nearPart_integrable hb.smooth hC
  have hfs := farPart_smooth hb.smooth
  have hfb := farPart_bddDerivs hb.smooth hC
  rw [average_eq_add hν hnear hfs hfb]
  exact (contDiff_infty.2 fun n => (average_nearPart_contDiff hν hnear n).1).add
    (contDiff_infty.2 fun n => (average_farPart_contDiff hν hfs hfb n).1)

/-- The heat remainder `e^{νΔ}b - b` is smooth off zero. -/
theorem heat_remainder_contDiffOn {b : Space → F} (hb : IsInverseDistanceField b) {ν : ℝ}
    (hν : 0 < ν) : ContDiffOn ℝ ∞ (fun x => Heat.average ν b x - b x) {0}ᶜ :=
  (heat_contDiff hb hν).contDiffOn.sub hb.smooth

/-- **`background:eq:2.48`** (tex lines 5909--5914): if `b` is smooth off zero with
`|D^j b(x)| ≤ C_j |x|^{-1-j}`, then `|D^j(e^{νΔ}b - b)(y)| ≤ C_{j,ν} |y|^{-3-j}` for `|y| ≥ 1`. -/
theorem heat_remainder_bound {b : Space → F} (hb : IsInverseDistanceField b) {ν : ℝ}
    (hν : 0 < ν) (j : ℕ) : ∃ C : ℝ, ∀ y : Space, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ j (fun x => Heat.average ν b x - b x) y‖ ≤ C / ‖y‖ ^ (j + 3) := by
  obtain ⟨C, hC⟩ := hb.bound
  have hnear := nearPart_integrable hb.smooth hC
  have hfs := farPart_smooth hb.smooth
  have hfb := farPart_bddDerivs hb.smooth hC
  obtain ⟨CI, hCI0, hCI⟩ := near_term_bound hν hnear j
  obtain ⟨CII, hCII⟩ := far_term_bound hν hb.smooth hC j
  obtain ⟨D, -, hD⟩ := exp_le_div_pow (a := (32 * ν)⁻¹) (by positivity) (j + 3)
  refine ⟨CI * D + CII, fun y hy => ?_⟩
  have hy0 : 0 < ‖y‖ := by linarith
  have hA : ContDiff ℝ ∞ (Heat.average ν (nearPart b)) :=
    contDiff_infty.2 fun n => (average_nearPart_contDiff hν hnear n).1
  have hB : ContDiff ℝ ∞ (Heat.average ν (farPart b)) :=
    contDiff_infty.2 fun n => (average_farPart_contDiff hν hfs hfb n).1
  have hBO : ContDiff ℝ ∞ (Heat.average ν (farPart b) - farPart b) := hB.sub hfs
  have hev : (fun x => Heat.average ν b x - b x) =ᶠ[𝓝 y]
      Heat.average ν (nearPart b) + (Heat.average ν (farPart b) - farPart b) := by
    filter_upwards [farPart_eventuallyEq b (by linarith : (1 : ℝ) / 2 < ‖y‖)] with z hz
    rw [average_eq_add hν hnear hfs hfb]
    simp only [Pi.add_apply, Pi.sub_apply, hz]
    abel
  have hj : ((j : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds,
    iteratedFDeriv_add_apply (hA.of_le hj).contDiffAt (hBO.of_le hj).contDiffAt,
    iteratedFDeriv_sub_apply (hB.of_le hj).contDiffAt (hfs.of_le hj).contDiffAt]
  calc _ ≤ ‖iteratedFDeriv ℝ j (Heat.average ν (nearPart b)) y‖ +
        ‖iteratedFDeriv ℝ j (Heat.average ν (farPart b)) y -
          iteratedFDeriv ℝ j (farPart b) y‖ := norm_add_le _ _
    _ ≤ CI * (D / ‖y‖ ^ (j + 3)) + CII / ‖y‖ ^ (j + 3) :=
      add_le_add ((hCI y hy).trans (mul_le_mul_of_nonneg_left (hD ‖y‖ hy0) hCI0)) (hCII y hy)
    _ = (CI * D + CII) / ‖y‖ ^ (j + 3) := by ring

/-- **B0306, the whole unit.** For an inverse-distance field `b` and `ν > 0`: the heat integral
`e^{νΔ}b` converges absolutely at every point, is `C^∞`, and
`|D^j(e^{νΔ}b - b)(y)| ≤ C_{j,ν} |y|^{-3-j}` for `|y| ≥ 1` and every `j`
(`background:eq:2.48`, tex lines 5909--5921). -/
theorem eq_2_48 {b : Space → F} (hb : IsInverseDistanceField b) {ν : ℝ} (hν : 0 < ν) :
    (∀ y : Space, Integrable (fun x => Heat.kernel ν x • b (y - x))) ∧
    ContDiff ℝ ∞ (Heat.average ν b) ∧
    ∀ j : ℕ, ∃ C : ℝ, ∀ y : Space, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ j (fun x => Heat.average ν b x - b x) y‖ ≤ C / ‖y‖ ^ (j + 3) :=
  ⟨heat_integrable hb hν, heat_contDiff hb hν, heat_remainder_bound hb hν⟩

end UnforcedLeray.B0306
