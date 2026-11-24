import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# One-dimensional Liouville lemmas for `L²(ℝ)` (helpers of CY12 and CY13)

Helpers for target CY13 (`eq_zero_of_curl_div`, bypass BP7) and CY12 (`qAvg_P0`) of

`q`-mode the cylinder Liouville theorem B0935 (`paper/main.tex` line 14360: `D ∈ H^{-1}(C_c)`,
`curl D = 0`, `div D = 0` ⇒ `D = 0`) reduces to one of the following statements about a single
`v ∈ L²(ℝ; ℂ)` tested against smooth compactly supported real `ψ`:

* `eq_zero_of_deriv`: `∫ ψ' v = 0` for all `ψ` ⇒ `v = 0` (a constant in `L²(ℝ)` vanishes);
* `eq_zero_of_first_order`: `b ≠ 0`, `∫ (ψ' + bψ) v = 0` for all `ψ` ⇒ `v = 0`;
* `eq_zero_of_helmholtz`: `a ≠ 0`, `∫ (a²ψ − ψ'') v = 0` for all `ψ` ⇒ `v = 0`.

Proofs use no distribution theory. For a test `θ` and a fixed bump `β₀` with `∫ β₀ = 1`, the
function `θ − (∫ e^{bx} θ) β_s`, `β_s(x) = e^{-bx} β₀(x − s)`, has a compactly supported
solution `ψ` of `ψ' + bψ = ·` (`exists_first_order`), so `∫ θ v = (∫ e^{bx} θ) ∫ β_s v`, and
`‖β_s‖₂ = e^{-bs} ‖e^{-b·} β₀‖₂` tends to `0` along `bs → ∞`. For `b = 0` the bump is dilated
instead (`‖R⁻¹ β₀(·/R)‖₂ = R^{-1/2} ‖β₀‖₂`). The second-order case factors
`a² − ∂² = (a − ∂)(a + ∂)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Cyl.OneD

/-- A smooth compactly supported real test function on `ℝ`. -/
structure Test (ψ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ψ
  compact : HasCompactSupport ψ

namespace Test

variable {ψ φ : ℝ → ℝ}

theorem continuous (h : Test ψ) : Continuous ψ := h.smooth.continuous

theorem deriv (h : Test ψ) : Test (_root_.deriv ψ) :=
  ⟨(contDiff_infty_iff_deriv.1 h.smooth).2, h.compact.deriv⟩

theorem hasDerivAt (h : Test ψ) (x : ℝ) : HasDerivAt ψ (_root_.deriv ψ x) x :=
  ((h.smooth.differentiable (by simp)) x).hasDerivAt

theorem sub (h : Test ψ) (h' : Test φ) : Test (fun x => ψ x - φ x) :=
  ⟨h.smooth.sub h'.smooth, h.compact.sub h'.compact⟩

theorem add (h : Test ψ) (h' : Test φ) : Test (fun x => ψ x + φ x) :=
  ⟨h.smooth.add h'.smooth, h.compact.add h'.compact⟩

theorem const_mul (h : Test ψ) (a : ℝ) : Test (fun x => a * ψ x) :=
  ⟨contDiff_const.mul h.smooth, h.compact.mul_left⟩

theorem mul_left (h : Test ψ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) : Test (fun x => g x * ψ x) :=
  ⟨hg.mul h.smooth, h.compact.mul_left⟩

theorem comp_sub (h : Test ψ) (s : ℝ) : Test (fun x => ψ (x - s)) :=
  ⟨h.smooth.comp (contDiff_id.sub contDiff_const),
    h.compact.comp_homeomorph (Homeomorph.subRight s)⟩

theorem comp_div (h : Test ψ) {R : ℝ} (hR : R ≠ 0) : Test (fun x => ψ (x / R)) :=
  ⟨h.smooth.comp (contDiff_id.div_const R),
    h.compact.comp_homeomorph (Homeomorph.mulRight₀ R⁻¹ (inv_ne_zero hR))⟩

theorem memLp (h : Test ψ) (p : ℝ≥0∞) : MemLp ψ p volume :=
  h.continuous.memLp_of_hasCompactSupport (μ := volume) h.compact

theorem integrable (h : Test ψ) : Integrable ψ volume :=
  memLp_one_iff_integrable.1 (h.memLp 1)

/-- A test vanishes outside a symmetric interval. -/
theorem exists_bound (h : Test ψ) : ∃ M : ℝ, 0 < M ∧ ∀ x, M ≤ |x| → ψ x = 0 := by
  obtain ⟨r, hr⟩ := h.compact.isCompact.isBounded.subset_closedBall 0
  refine ⟨|r| + 1, by positivity, fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hr hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have := le_abs_self r
  linarith

end Test

/-- The fixed bump `β₀` with `∫ β₀ = 1`. -/
def bump0 : ℝ → ℝ :=
  (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)).normed volume

theorem test_bump0 : Test bump0 :=
  ⟨ContDiffBump.contDiff_normed _, ContDiffBump.hasCompactSupport_normed _⟩

theorem integral_bump0 : ∫ x, bump0 x = 1 := ContDiffBump.integral_normed _

/-! ### Primitives and first-order solutions with compact support -/

/-- **Primitive of a zero-mean test.** -/
theorem exists_primitive {g : ℝ → ℝ} (hg : Test g) (h0 : ∫ x, g x = 0) :
    ∃ G : ℝ → ℝ, Test G ∧ ∀ x, HasDerivAt G (g x) x := by
  obtain ⟨M, hM, hgM⟩ := hg.exists_bound
  set G : ℝ → ℝ := fun x => ∫ t in (-M)..x, g t with hG
  have hd : ∀ x, HasDerivAt G (g x) x := fun x =>
    (hg.continuous.integral_hasStrictDerivAt (-M) x).hasDerivAt
  have hderiv : _root_.deriv G = g := funext fun x => (hd x).deriv
  have hsmooth : ContDiff ℝ ∞ G := by
    rw [contDiff_infty_iff_deriv, hderiv]
    exact ⟨fun x => (hd x).differentiableAt, hg.smooth⟩
  have hleft : ∀ x, x ≤ -M → G x = 0 := by
    intro x hx
    simp only [hG]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
    · simp
    · apply hgM
      rw [uIcc_of_ge hx] at ht
      rw [abs_of_neg (by linarith [ht.2])]
      linarith [ht.2]
  have hright : ∀ x, M ≤ x → G x = 0 := by
    intro x hx
    simp only [hG]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hg.continuous.intervalIntegrable (μ := volume) (-M) M)
      (hg.continuous.intervalIntegrable (μ := volume) M x)
    rw [← hsplit]
    have h1 : ∫ t in (-M)..M, g t = ∫ t, g t := by
      rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => hgM t ?_
      simp only [mem_Ioo, not_and_or, not_lt] at ht
      rcases ht with ht | ht
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have h2 : ∫ t in M..x, g t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
      · simp
      · apply hgM
        rw [uIcc_of_le hx] at ht
        rw [abs_of_pos (by linarith [ht.1])]
        exact ht.1
    rw [h1, h2, h0, add_zero]
  refine ⟨G, ⟨hsmooth, HasCompactSupport.intro isCompact_Icc (K := Icc (-M) M) fun x hx => ?_⟩,
    hd⟩
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact hleft x hx.le
  · exact hright x hx.le

/-- **First-order solution with compact support**: if `∫ e^{bx} θ = 0`, then
`ψ' + bψ = θ` has a test solution `ψ = e^{-bx} ∫_{-∞}^x e^{by} θ(y) dy`. -/
theorem exists_first_order (b : ℝ) {θ : ℝ → ℝ} (hθ : Test θ)
    (h0 : ∫ x, Real.exp (b * x) * θ x = 0) :
    ∃ ψ : ℝ → ℝ, Test ψ ∧ ∀ x, _root_.deriv ψ x + b * ψ x = θ x := by
  have hexp : ContDiff ℝ ∞ fun x : ℝ => Real.exp (b * x) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hexp' : ContDiff ℝ ∞ fun x : ℝ => Real.exp (-b * x) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  obtain ⟨G, hG, hGd⟩ := exists_primitive (hθ.mul_left hexp) h0
  refine ⟨fun x => Real.exp (-b * x) * G x, hG.mul_left hexp', fun x => ?_⟩
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-b * x)) (Real.exp (-b * x) * (-b * 1)) x :=
    (Real.hasDerivAt_exp _).comp x ((hasDerivAt_id x).const_mul (-b))
  have h2 : HasDerivAt (fun x => Real.exp (-b * x) * G x)
      (Real.exp (-b * x) * (-b * 1) * G x + Real.exp (-b * x) * (Real.exp (b * x) * θ x)) x :=
    h1.mul (hGd x)
  rw [h2.deriv]
  have he : Real.exp (-b * x) * Real.exp (b * x) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination θ x * he

/-! ### Cauchy–Schwarz and the two scalings -/

variable {v : ℝ → ℂ}

/-- Cauchy–Schwarz for `∫ u v`, `u` real. -/
theorem norm_integral_smul_le {u : ℝ → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    ‖∫ x, u x • v x‖ ≤ (eLpNorm u 2 volume).toReal * (eLpNorm v 2 volume).toReal := by
  have h1 : eLpNorm (u • v) 1 volume ≤ eLpNorm u 2 volume * eLpNorm v 2 volume :=
    eLpNorm_smul_le_mul_eLpNorm hv.1 hu.1
  have hm : AEStronglyMeasurable (u • v) volume := hu.1.smul hv.1
  calc ‖∫ x, u x • v x‖ ≤ ∫ x, ‖u x • v x‖ := norm_integral_le_integral_norm _
    _ = (eLpNorm (u • v) 1 volume).toReal := by
        show ∫ x, ‖(u • v) x‖ = _
        rw [integral_norm_eq_lintegral_enorm hm, eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (eLpNorm u 2 volume * eLpNorm v 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hu.2.ne hv.2.ne) h1
    _ = _ := ENNReal.toReal_mul

/-- `‖e^{-bx} h(x − s)‖₂ = e^{-bs} ‖e^{-by} h(y)‖₂`. -/
theorem eLpNorm_exp_shift (b s : ℝ) {h : ℝ → ℝ} (hh : Continuous h) :
    eLpNorm (fun x => Real.exp (-b * x) * h (x - s)) 2 volume =
      ENNReal.ofReal (Real.exp (-b * s)) *
        eLpNorm (fun y => Real.exp (-b * y) * h y) 2 volume := by
  have hfun : (fun x => Real.exp (-b * x) * h (x - s)) =
      Real.exp (-b * s) • ((fun y => Real.exp (-b * y) * h y) ∘ fun x => x - s) := by
    funext x
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hc : Continuous fun y => Real.exp (-b * y) * h y :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hh
  rw [hfun, eLpNorm_const_smul, eLpNorm_comp_measurePreserving (g := fun y => Real.exp (-b * y) * h y)
    hc.aestronglyMeasurable (measurePreserving_sub_right volume s),
    Real.enorm_eq_ofReal (Real.exp_pos _).le]

/-- `‖β(·/R)‖₂ = √R ‖β‖₂` for `R > 0` and a test `β`. -/
theorem eLpNorm_comp_div {β : ℝ → ℝ} (hβ : Test β) {R : ℝ} (hR : 0 < R) :
    eLpNorm (fun x => β (x / R)) 2 volume =
      ENNReal.ofReal (R ^ (1 / 2 : ℝ)) * eLpNorm β 2 volume := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  rw [MemLp.eLpNorm_eq_integral_rpow_norm h2 ENNReal.ofNat_ne_top ((hβ.comp_div hR.ne').memLp 2),
    MemLp.eLpNorm_eq_integral_rpow_norm h2 ENNReal.ofNat_ne_top (hβ.memLp 2)]
  rw [Measure.integral_comp_div (fun y => ‖β y‖ ^ (2 : ℝ≥0∞).toReal) R, abs_of_pos hR, smul_eq_mul,
    Real.mul_rpow hR.le (integral_nonneg fun _ => by positivity), ENNReal.ofReal_mul (by positivity)]
  norm_num

/-- If `0 ≤ x ≤ f n` for all `n` and `f n → 0`, then `x = 0`. -/
theorem eq_zero_of_le_tendsto {x : ℝ} (hx : 0 ≤ x) {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0))
    (h : ∀ n, x ≤ f n) : x = 0 :=
  le_antisymm (ge_of_tendsto' hf h) hx

theorem integrable_smul_of_test {ψ : ℝ → ℝ} (hψ : Test ψ) (hv : MemLp v 2 volume) :
    Integrable (fun x => ψ x • v x) volume :=
  (hv.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hψ.continuous
    hψ.compact

/-! ### The three Liouville lemmas -/

/-- **A function of `L²(ℝ)` with zero weak derivative vanishes.** -/
theorem eq_zero_of_deriv (hv : MemLp v 2 volume)
    (h : ∀ ψ : ℝ → ℝ, Test ψ → ∫ x, _root_.deriv ψ x • v x = 0) : v =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (hv.locallyIntegrable (by norm_num))
    fun θ hθs hθc => ?_
  have hθ : Test θ := ⟨hθs, hθc⟩
  set A : ℝ := (eLpNorm v 2 volume).toReal
  set B : ℝ := (eLpNorm bump0 2 volume).toReal
  have key : ∀ R : ℝ, 0 < R →
      ‖∫ x, θ x • v x‖ ≤ ‖∫ x, θ x‖ * (R⁻¹ * R ^ (1 / 2 : ℝ) * B) * A := by
    intro R hR
    set βR : ℝ → ℝ := fun x => R⁻¹ * bump0 (x / R) with hβR
    have hβ : Test βR := (test_bump0.comp_div hR.ne').const_mul R⁻¹
    have hint : ∫ x, βR x = 1 := by
      simp only [hβR]
      rw [integral_const_mul, Measure.integral_comp_div bump0 R, integral_bump0, abs_of_pos hR,
        smul_eq_mul, mul_one, inv_mul_cancel₀ hR.ne']
    set g : ℝ → ℝ := fun x => θ x - (∫ y, θ y) * βR x with hg
    have hgt : Test g := hθ.sub (hβ.const_mul _)
    have hg0 : ∫ x, g x = 0 := by
      simp only [hg]
      rw [integral_sub hθ.integrable (hβ.const_mul _).integrable, integral_const_mul, hint]
      ring
    obtain ⟨G, hG, hGd⟩ := exists_primitive hgt hg0
    have hzero := h G hG
    have hdG : _root_.deriv G = g := funext fun x => (hGd x).deriv
    rw [hdG] at hzero
    have hsplit : ∫ x, θ x • v x = (∫ y, θ y) • ∫ x, βR x • v x := by
      have e : (fun x => g x • v x) = fun x => θ x • v x - (∫ y, θ y) • (βR x • v x) := by
        funext x; simp only [hg, sub_smul, mul_smul]
      have hi2 : Integrable (fun x => (∫ y, θ y) • (βR x • v x)) volume :=
        (integrable_smul_of_test hβ hv).smul (∫ y, θ y)
      rw [e, integral_sub (integrable_smul_of_test hθ hv) hi2, integral_smul] at hzero
      exact sub_eq_zero.1 hzero
    have hnβ : (eLpNorm βR 2 volume).toReal = R⁻¹ * R ^ (1 / 2 : ℝ) * B := by
      have e : βR = R⁻¹ • fun x => bump0 (x / R) := rfl
      rw [e, eLpNorm_const_smul, eLpNorm_comp_div test_bump0 hR, ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), toReal_enorm,
        Real.norm_of_nonneg (inv_nonneg.2 hR.le), mul_assoc]
    rw [hsplit, norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← hnβ]
    exact norm_integral_smul_le (hβ.memLp 2) hv
  have hlim : Tendsto (fun n : ℕ => ‖∫ x, θ x‖ * (((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) *
      B) * A) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h2 : (fun n : ℕ => ‖∫ x, θ x‖ * (((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) * B) * A) =
        fun n : ℕ => (‖∫ x, θ x‖ * B * A) * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
      funext n
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) = ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hn]; norm_num
      rw [this]; ring
    rw [h2]
    simpa using h1.const_mul (‖∫ x, θ x‖ * B * A)
  have := eq_zero_of_le_tendsto (norm_nonneg _) hlim fun n => key _ (by positivity)
  exact norm_eq_zero.1 this

/-- The shifted weighted bump `β_s(x) = e^{-bx} β₀(x − s)`, with `∫ e^{bx} β_s = 1`. -/
theorem integral_exp_mul_shiftBump (b s : ℝ) :
    ∫ x, Real.exp (b * x) * (Real.exp (-b * x) * bump0 (x - s)) = 1 := by
  have e : (fun x => Real.exp (b * x) * (Real.exp (-b * x) * bump0 (x - s))) =
      fun x => bump0 (x - s) := by
    funext x
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [e, integral_sub_right_eq_self (fun x => bump0 x) s, integral_bump0]

theorem test_shiftBump (b s : ℝ) : Test fun x => Real.exp (-b * x) * bump0 (x - s) :=
  (test_bump0.comp_sub s).mul_left (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

/-- The decay `e^{-bs} → 0` along `s = (n + 1)/b`. -/
theorem tendsto_exp_shift {b : ℝ} (hb : b ≠ 0) (K : ℝ) :
    Tendsto (fun n : ℕ => K * Real.exp (-b * (((n : ℝ) + 1) / b))) atTop (𝓝 0) := by
  have e : (fun n : ℕ => K * Real.exp (-b * (((n : ℝ) + 1) / b))) =
      fun n : ℕ => K * Real.exp (-((n : ℝ) + 1)) := by
    funext n; congr 2; field_simp
  rw [e]
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  simpa using h.const_mul K

/-- **First-order Liouville**: if `b ≠ 0` and `∫ (ψ' + bψ) v = 0` for all tests, then `v = 0`. -/
theorem eq_zero_of_first_order {b : ℝ} (hb : b ≠ 0) (hv : MemLp v 2 volume)
    (h : ∀ ψ : ℝ → ℝ, Test ψ → ∫ x, (_root_.deriv ψ x + b * ψ x) • v x = 0) :
    v =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (hv.locallyIntegrable (by norm_num))
    fun θ hθs hθc => ?_
  have hθ : Test θ := ⟨hθs, hθc⟩
  set A : ℝ := (eLpNorm v 2 volume).toReal
  set B : ℝ := (eLpNorm (fun y => Real.exp (-b * y) * bump0 y) 2 volume).toReal
  set m : ℝ := ∫ x, Real.exp (b * x) * θ x
  have key : ∀ s : ℝ, ‖∫ x, θ x • v x‖ ≤ (|m| * B * A) * Real.exp (-b * s) := by
    intro s
    set βs : ℝ → ℝ := fun x => Real.exp (-b * x) * bump0 (x - s) with hβs
    have hβ : Test βs := test_shiftBump b s
    set g : ℝ → ℝ := fun x => θ x - m * βs x with hg
    have hgt : Test g := hθ.sub (hβ.const_mul _)
    have hexp : ContDiff ℝ ∞ fun x : ℝ => Real.exp (b * x) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    have hg0 : ∫ x, Real.exp (b * x) * g x = 0 := by
      have e : (fun x => Real.exp (b * x) * g x) =
          fun x => Real.exp (b * x) * θ x - m * (Real.exp (b * x) * βs x) := by
        funext x; simp only [hg]; ring
      rw [e, integral_sub (hθ.mul_left hexp).integrable ((hβ.mul_left hexp).integrable.const_mul _),
        integral_const_mul, integral_exp_mul_shiftBump]
      ring
    obtain ⟨ψ, hψ, hψd⟩ := exists_first_order b hgt hg0
    have hzero := h ψ hψ
    have hfun : (fun x => (_root_.deriv ψ x + b * ψ x) • v x) = fun x => g x • v x := by
      funext x; rw [hψd x]
    rw [hfun] at hzero
    have hsplit : ∫ x, θ x • v x = m • ∫ x, βs x • v x := by
      have e : (fun x => g x • v x) = fun x => θ x • v x - m • (βs x • v x) := by
        funext x; simp only [hg, sub_smul, mul_smul]
      have hi2 : Integrable (fun x => m • (βs x • v x)) volume :=
        (integrable_smul_of_test hβ hv).smul m
      rw [e, integral_sub (integrable_smul_of_test hθ hv) hi2, integral_smul] at hzero
      exact sub_eq_zero.1 hzero
    have hnβ : (eLpNorm βs 2 volume).toReal = Real.exp (-b * s) * B := by
      rw [hβs, eLpNorm_exp_shift b s test_bump0.continuous, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [hsplit, norm_smul, Real.norm_eq_abs]
    calc |m| * ‖∫ x, βs x • v x‖ ≤ |m| * ((eLpNorm βs 2 volume).toReal * A) :=
          mul_le_mul_of_nonneg_left (norm_integral_smul_le (hβ.memLp 2) hv) (abs_nonneg _)
      _ = (|m| * B * A) * Real.exp (-b * s) := by rw [hnβ]; ring
  exact norm_eq_zero.1 (eq_zero_of_le_tendsto (norm_nonneg _) (tendsto_exp_shift hb _)
    fun n => key _)

/-- **Helmholtz Liouville**: if `a ≠ 0` and `∫ (a²ψ − ψ'') v = 0` for all tests, then `v = 0`. -/
theorem eq_zero_of_helmholtz {a : ℝ} (ha : a ≠ 0) (hv : MemLp v 2 volume)
    (h : ∀ ψ : ℝ → ℝ, Test ψ →
      ∫ x, (a ^ 2 * ψ x - _root_.deriv (_root_.deriv ψ) x) • v x = 0) :
    v =ᵐ[volume] 0 := by
  -- first show the first-order identity for `b = -a`
  refine eq_zero_of_first_order (b := -a) (neg_ne_zero.2 ha) hv fun χ hχ => ?_
  set A : ℝ := (eLpNorm v 2 volume).toReal
  set hb : ℝ → ℝ := fun y => _root_.deriv bump0 y - 2 * a * bump0 y with hhb
  have hbt : Test hb := test_bump0.deriv.sub (test_bump0.const_mul _)
  set B : ℝ := (eLpNorm (fun y => Real.exp (-a * y) * hb y) 2 volume).toReal
  set m : ℝ := ∫ x, Real.exp (a * x) * χ x
  have hexp : ContDiff ℝ ∞ fun x : ℝ => Real.exp (a * x) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hexp' : ContDiff ℝ ∞ fun x : ℝ => Real.exp (-a * x) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  -- the operator `χ ↦ χ' - aχ`
  have key : ∀ s : ℝ, ‖∫ x, (_root_.deriv χ x + -a * χ x) • v x‖ ≤
      (|m| * B * A) * Real.exp (-a * s) := by
    intro s
    set βs : ℝ → ℝ := fun x => Real.exp (-a * x) * bump0 (x - s) with hβs
    have hβ : Test βs := test_shiftBump a s
    set g : ℝ → ℝ := fun x => χ x - m * βs x with hg
    have hgt : Test g := hχ.sub (hβ.const_mul _)
    have hg0 : ∫ x, Real.exp (a * x) * g x = 0 := by
      have e : (fun x => Real.exp (a * x) * g x) =
          fun x => Real.exp (a * x) * χ x - m * (Real.exp (a * x) * βs x) := by
        funext x; simp only [hg]; ring
      rw [e, integral_sub (hχ.mul_left hexp).integrable ((hβ.mul_left hexp).integrable.const_mul _),
        integral_const_mul, integral_exp_mul_shiftBump]
      ring
    obtain ⟨ψ, hψ, hψd⟩ := exists_first_order a hgt hg0
    -- `g' - a g = ψ'' - a² ψ`
    have hgd : ∀ x, _root_.deriv g x + -a * g x =
        -(a ^ 2 * ψ x - _root_.deriv (_root_.deriv ψ) x) := by
      intro x
      have hg_eq : g = fun x => _root_.deriv ψ x + a * ψ x := funext fun x => (hψd x).symm
      have hd1 : HasDerivAt (fun x => _root_.deriv ψ x + a * ψ x)
          (_root_.deriv (_root_.deriv ψ) x + a * _root_.deriv ψ x) x :=
        (hψ.deriv.hasDerivAt x).add ((hψ.hasDerivAt x).const_mul a)
      rw [hg_eq, hd1.deriv]
      ring
    have hzero := h ψ hψ
    have hfun : (fun x => (_root_.deriv g x + -a * g x) • v x) =
        fun x => -((a ^ 2 * ψ x - _root_.deriv (_root_.deriv ψ) x) • v x) := by
      funext x; rw [hgd x, neg_smul]
    have hzero' : ∫ x, (_root_.deriv g x + -a * g x) • v x = 0 := by
      rw [hfun, integral_neg, hzero, neg_zero]
    -- expand `g = χ - m βs`
    have hdg : ∀ x, _root_.deriv g x + -a * g x =
        (_root_.deriv χ x + -a * χ x) - m * (_root_.deriv βs x + -a * βs x) := by
      intro x
      have hd : HasDerivAt g (_root_.deriv χ x - m * _root_.deriv βs x) x :=
        (hχ.hasDerivAt x).sub ((hβ.hasDerivAt x).const_mul m)
      rw [hd.deriv]
      simp only [hg]
      ring
    have hT1 : Test fun x => _root_.deriv χ x + -a * χ x := hχ.deriv.add (hχ.const_mul _)
    have hT2 : Test fun x => _root_.deriv βs x + -a * βs x := hβ.deriv.add (hβ.const_mul _)
    have hsplit : ∫ x, (_root_.deriv χ x + -a * χ x) • v x =
        m • ∫ x, (_root_.deriv βs x + -a * βs x) • v x := by
      have e : (fun x => (_root_.deriv g x + -a * g x) • v x) = fun x =>
          (_root_.deriv χ x + -a * χ x) • v x - m • ((_root_.deriv βs x + -a * βs x) • v x) := by
        funext x; rw [hdg x, sub_smul, mul_smul]
      have hi2 : Integrable (fun x => m • ((_root_.deriv βs x + -a * βs x) • v x)) volume :=
        (integrable_smul_of_test hT2 hv).smul m
      rw [e, integral_sub (integrable_smul_of_test hT1 hv) hi2, integral_smul] at hzero'
      exact sub_eq_zero.1 hzero'
    -- `βs' - a βs = e^{-ax} (β₀' - 2a β₀)(x - s)`
    have hβd : (fun x => _root_.deriv βs x + -a * βs x) =
        fun x => Real.exp (-a * x) * hb (x - s) := by
      funext x
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (-a * x)) (Real.exp (-a * x) * (-a * 1)) x :=
        (Real.hasDerivAt_exp _).comp x ((hasDerivAt_id x).const_mul (-a))
      have h2 : HasDerivAt (fun x => bump0 (x - s)) (_root_.deriv bump0 (x - s)) x :=
        HasDerivAt.comp_sub_const x s (test_bump0.hasDerivAt (x - s))
      have h3 : HasDerivAt βs (Real.exp (-a * x) * (-a * 1) * bump0 (x - s) +
          Real.exp (-a * x) * _root_.deriv bump0 (x - s)) x := h1.mul h2
      rw [h3.deriv]
      simp only [hβs, hhb]
      ring
    have hnβ : (eLpNorm (fun x => _root_.deriv βs x + -a * βs x) 2 volume).toReal =
        Real.exp (-a * s) * B := by
      rw [hβd, eLpNorm_exp_shift a s hbt.continuous, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [hsplit, norm_smul, Real.norm_eq_abs]
    calc |m| * ‖∫ x, (_root_.deriv βs x + -a * βs x) • v x‖
        ≤ |m| * ((eLpNorm (fun x => _root_.deriv βs x + -a * βs x) 2 volume).toReal * A) :=
          mul_le_mul_of_nonneg_left (norm_integral_smul_le (hT2.memLp 2) hv) (abs_nonneg _)
      _ = (|m| * B * A) * Real.exp (-a * s) := by rw [hnβ]; ring
  exact norm_eq_zero.1 (eq_zero_of_le_tendsto (norm_nonneg _) (tendsto_exp_shift ha _)
    fun n => key _)

end UnforcedLeray.Cyl.OneD
