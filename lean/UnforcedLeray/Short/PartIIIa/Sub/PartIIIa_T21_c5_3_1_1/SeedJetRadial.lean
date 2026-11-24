import UnforcedLeray.Lib.ComplexODEC.Velocity
import UnforcedLeray.Lib.ComplexODEC.Bounds

/-!
# Radial profile bounds for the seed dual kernels (helper for `PartIII-a:T21/c5/3/1/1/1`)

Source `the November 2 reference manuscript`
lines 593-610 (`eq:short-seed-functional`) and 2891-2897.  In the variable `s = r²` the seed dual
kernel has the radial profile `β(s) = K b(s) / (e^{-s/4} - a₀)`, where `b = regB c` is the regular
solution of `4(s b'' + 3 b') = κ_c b` (the Cartesian form `ψ(y) = β₀ y² b(|y|²)` of the stream
function of the growing mode) and `a₀ = iλ/2` has nonzero imaginary part.  This file proves
`‖β(s)‖(1+s)² ≤ B`, `‖β'(s)‖(1+s)³ ≤ B`, `‖β''(s)‖(1+s)³ ≤ B` on `s ≥ 0`.

Inputs: `exists_decay_regB` (`b = O((1+s)^{-2})`), `exists_decay_deriv_regB`
(`b' = O((1+s)^{-3})`), the ODE `regB_ode` (which gives `b'' = O((1+s)^{-3})` for `s ≥ 1`) and
`kappa_norm_le_three`; the denominator `m(s) = (e^{-s/4} - a₀)⁻¹` is bounded by `1/|Im a₀|`, and
`m' = ¼ e^{-s/4} m²`, `m''` carry the factor `e^{-s/4} ≤ 4/(1+s)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.SeedJet2Aux

open UnforcedLeray.ComplexODEC

/-- `E(s) = e^{-s/4}`, complex valued. -/
def gaussE4 (s : ℝ) : ℂ := ((Real.exp (-(s / 4)) : ℝ) : ℂ)

theorem hasDerivAt_gaussE4 (s : ℝ) : HasDerivAt gaussE4 (-(1 / 4) * gaussE4 s) s := by
  have h1 : HasDerivAt (fun t : ℝ => -(t / 4)) (-(1 / 4)) s :=
    ((hasDerivAt_id s).div_const 4).neg
  have h3 := h1.exp.ofReal_comp
  have hv : (((Real.exp (-(s / 4)) * -(1 / 4) : ℝ)) : ℂ) = -(1 / 4) * gaussE4 s := by
    unfold gaussE4
    push_cast
    ring
  rw [hv] at h3
  exact h3

theorem norm_gaussE4 (s : ℝ) : ‖gaussE4 s‖ = Real.exp (-(s / 4)) := by
  rw [gaussE4, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem norm_gaussE4_le_one {s : ℝ} (hs : 0 ≤ s) : ‖gaussE4 s‖ ≤ 1 := by
  have _hs := hs
  rw [norm_gaussE4]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem norm_gaussE4_mul_le {s : ℝ} (hs : 0 ≤ s) : ‖gaussE4 s‖ * (1 + s) ≤ 4 := by
  rw [norm_gaussE4]
  have h1 : s / 4 + 1 ≤ Real.exp (s / 4) := Real.add_one_le_exp _
  have h2 : Real.exp (-(s / 4)) * Real.exp (s / 4) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-(s / 4))
  nlinarith

theorem gaussE4_sub_ne {a₀ : ℂ} (ha : a₀.im ≠ 0) (s : ℝ) : gaussE4 s - a₀ ≠ 0 := by
  intro h
  apply ha
  have := congrArg Complex.im h
  rw [Complex.sub_im, gaussE4, Complex.ofReal_im, Complex.zero_im] at this
  linarith

theorem norm_inv_gaussE4_sub_le {a₀ : ℂ} (ha : a₀.im ≠ 0) (s : ℝ) :
    ‖(gaussE4 s - a₀)⁻¹‖ ≤ 1 / |a₀.im| := by
  have hpos : 0 < |a₀.im| := abs_pos.mpr ha
  have hle : |a₀.im| ≤ ‖gaussE4 s - a₀‖ := by
    have h := Complex.abs_im_le_norm (gaussE4 s - a₀)
    have him : (gaussE4 s - a₀).im = -a₀.im := by
      rw [Complex.sub_im, gaussE4, Complex.ofReal_im, zero_sub]
    rw [him, abs_neg] at h
    exact h
  rw [norm_inv, one_div]
  exact inv_anti₀ hpos hle

/-- `m(s) = (e^{-s/4} - a₀)⁻¹`. -/
def denM (a₀ : ℂ) (s : ℝ) : ℂ := (gaussE4 s - a₀)⁻¹

/-- `m'(s) = ¼ e^{-s/4} m(s)²`. -/
def denM1 (a₀ : ℂ) (s : ℝ) : ℂ := 1 / 4 * gaussE4 s * denM a₀ s ^ 2

/-- `m''(s)`. -/
def denM2 (a₀ : ℂ) (s : ℝ) : ℂ :=
  1 / 4 * ((-(1 / 4) * gaussE4 s) * denM a₀ s ^ 2 + gaussE4 s * (2 * denM a₀ s * denM1 a₀ s))

theorem hasDerivAt_denM {a₀ : ℂ} (ha : a₀.im ≠ 0) (s : ℝ) :
    HasDerivAt (denM a₀) (denM1 a₀ s) s := by
  have h1 : HasDerivAt (fun t => gaussE4 t - a₀) (-(1 / 4) * gaussE4 s) s :=
    (hasDerivAt_gaussE4 s).sub_const a₀
  have h2 := h1.fun_inv (gaussE4_sub_ne ha s)
  have hne := gaussE4_sub_ne ha s
  have hv : -(-(1 / 4) * gaussE4 s) / (gaussE4 s - a₀) ^ 2 = denM1 a₀ s := by
    unfold denM1 denM
    field_simp
  rw [hv] at h2
  exact h2

theorem hasDerivAt_denM1 {a₀ : ℂ} (ha : a₀.im ≠ 0) (s : ℝ) :
    HasDerivAt (denM1 a₀) (denM2 a₀ s) s := by
  have h1 := ((hasDerivAt_gaussE4 s).const_mul (1 / 4 : ℂ)).fun_mul
    ((hasDerivAt_denM ha s).fun_pow 2)
  have hv : 1 / 4 * (-(1 / 4) * gaussE4 s) * denM a₀ s ^ 2 +
      1 / 4 * gaussE4 s * (((2 : ℕ) : ℂ) * denM a₀ s ^ (2 - 1) * denM1 a₀ s) = denM2 a₀ s := by
    unfold denM2
    push_cast
    ring
  rw [hv] at h1
  exact h1

theorem deriv_denM {a₀ : ℂ} (ha : a₀.im ≠ 0) : deriv (denM a₀) = denM1 a₀ :=
  funext fun s => (hasDerivAt_denM ha s).deriv

theorem deriv_denM1 {a₀ : ℂ} (ha : a₀.im ≠ 0) : deriv (denM1 a₀) = denM2 a₀ :=
  funext fun s => (hasDerivAt_denM1 ha s).deriv

theorem norm_denM_le {a₀ : ℂ} (ha : a₀.im ≠ 0) (s : ℝ) : ‖denM a₀ s‖ ≤ 1 / |a₀.im| :=
  norm_inv_gaussE4_sub_le ha s

theorem norm_denM1_mul_le {a₀ : ℂ} (ha : a₀.im ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ‖denM1 a₀ s‖ * (1 + s) ≤ (1 / |a₀.im|) ^ 2 := by
  have hm := norm_denM_le ha s
  have hE := norm_gaussE4_mul_le hs
  have hm0 := norm_nonneg (denM a₀ s)
  unfold denM1
  rw [norm_mul, norm_mul, norm_pow]
  have h14 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [h14]
  calc 1 / 4 * ‖gaussE4 s‖ * ‖denM a₀ s‖ ^ 2 * (1 + s)
      = 1 / 4 * (‖gaussE4 s‖ * (1 + s)) * ‖denM a₀ s‖ ^ 2 := by ring
    _ ≤ 1 / 4 * 4 * (1 / |a₀.im|) ^ 2 := by gcongr
    _ = (1 / |a₀.im|) ^ 2 := by ring

theorem norm_denM1_le {a₀ : ℂ} (ha : a₀.im ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ‖denM1 a₀ s‖ ≤ (1 / |a₀.im|) ^ 2 := by
  have h := norm_denM1_mul_le ha hs
  have h1 : ‖denM1 a₀ s‖ ≤ ‖denM1 a₀ s‖ * (1 + s) :=
    le_mul_of_one_le_right (norm_nonneg _) (by linarith)
  exact h1.trans h

theorem norm_denM2_mul_le {a₀ : ℂ} (ha : a₀.im ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ‖denM2 a₀ s‖ * (1 + s) ≤ (1 / |a₀.im|) ^ 2 + 2 * (1 / |a₀.im|) ^ 3 := by
  set M := 1 / |a₀.im| with hM
  have hM0 : 0 ≤ M := by positivity
  have hm := norm_denM_le ha s
  have hm1 := norm_denM1_le ha hs
  have hE := norm_gaussE4_mul_le hs
  have hE1 := norm_gaussE4_le_one hs
  rw [← hM] at hm hm1
  have hm0 := norm_nonneg (denM a₀ s)
  have hm10 := norm_nonneg (denM1 a₀ s)
  have hE0 := norm_nonneg (gaussE4 s)
  have hs1 : 0 ≤ 1 + s := by linarith
  unfold denM2
  have hA : ‖(1 / 4 : ℂ) * ((-(1 / 4) * gaussE4 s) * denM a₀ s ^ 2 +
      gaussE4 s * (2 * denM a₀ s * denM1 a₀ s))‖ ≤
      1 / 4 * (1 / 4 * ‖gaussE4 s‖ * ‖denM a₀ s‖ ^ 2 +
        ‖gaussE4 s‖ * (2 * ‖denM a₀ s‖ * ‖denM1 a₀ s‖)) := by
    rw [norm_mul]
    have h14 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    rw [h14]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_mul, norm_mul, norm_mul, h14]
    norm_num
  calc ‖(1 / 4 : ℂ) * ((-(1 / 4) * gaussE4 s) * denM a₀ s ^ 2 +
        gaussE4 s * (2 * denM a₀ s * denM1 a₀ s))‖ * (1 + s)
      ≤ 1 / 4 * (1 / 4 * ‖gaussE4 s‖ * ‖denM a₀ s‖ ^ 2 +
          ‖gaussE4 s‖ * (2 * ‖denM a₀ s‖ * ‖denM1 a₀ s‖)) * (1 + s) := by gcongr
    _ = 1 / 4 * (1 / 4 * (‖gaussE4 s‖ * (1 + s)) * ‖denM a₀ s‖ ^ 2 +
          (‖gaussE4 s‖ * (1 + s)) * (2 * ‖denM a₀ s‖ * ‖denM1 a₀ s‖)) := by ring
    _ ≤ 1 / 4 * (1 / 4 * 4 * M ^ 2 + 4 * (2 * M * M ^ 2)) := by gcongr
    _ = M ^ 2 / 4 + 2 * M ^ 3 := by ring
    _ ≤ M ^ 2 + 2 * M ^ 3 := by nlinarith [sq_nonneg M]

/-- `b'' = O((1+s)^{-3})` on `s ≥ 0`, from the ODE `4(s b'' + 3 b') = κ b`. -/
theorem exists_decay_deriv2_regB {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 ≤ s → ‖deriv (deriv (regB c)) s‖ * (1 + s) ^ 3 ≤ C := by
  have hc := hF.im_ne_zero
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_decay_regB hF
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_decay_deriv_regB hF
  have hb := contDiff_regB hc
  have hb2 : Continuous (deriv (deriv (regB c))) := by
    have h1 := (contDiff_infty_iff_deriv.mp hb).2
    exact (contDiff_infty_iff_deriv.mp h1).2.continuous
  obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hb2.continuousOn (s := Icc (0 : ℝ) 1))
  have hci : 0 < |c.im| := abs_pos.mpr hc
  refine ⟨max (8 * |K₁|) (2 * (3 / |c.im| * C₀ / 4 + 3 * C₁)),
    le_trans (by positivity) (le_max_left _ _), fun s hs => ?_⟩
  rcases le_total s 1 with h1 | h1
  · refine le_trans ?_ (le_max_left _ _)
    have hb' := hK₁ s ⟨hs, h1⟩
    have h8 : (1 + s) ^ 3 ≤ 8 := by
      have : 1 + s ≤ 2 := by linarith
      calc (1 + s) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) this 3
        _ = 8 := by norm_num
    calc ‖deriv (deriv (regB c)) s‖ * (1 + s) ^ 3 ≤ |K₁| * 8 :=
          mul_le_mul (hb'.trans (le_abs_self _)) h8 (by positivity) (abs_nonneg _)
      _ = 8 * |K₁| := by ring
  · refine le_trans ?_ (le_max_right _ _)
    have hode := regB_ode hc s
    have hs0 : (0 : ℝ) < s := by linarith
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have heq : deriv (deriv (regB c)) s =
        (kappa c s * regB c s / 4 - 3 * deriv (regB c) s) / (s : ℂ) := by
      rw [eq_div_iff hsC]
      linear_combination hode / 4
    have hk := kappa_norm_le_three hc hs
    have hb0 := hC₀ s hs
    have hb1 := hC₁ s hs
    have hX : ‖kappa c s * regB c s / 4 - 3 * deriv (regB c) s‖ ≤
        3 / |c.im| * ‖regB c s‖ / 4 + 3 * ‖deriv (regB c) s‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_div, norm_mul, norm_mul]
      have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
      have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      rw [h4, h3]
      gcongr
    have hsq : (1 + s) ^ 3 ≤ 2 * s * (1 + s) ^ 2 := by
      have : (1 + s) ^ 3 = (1 + s) * (1 + s) ^ 2 := by ring
      rw [this]
      have h2 : 0 ≤ (1 + s) ^ 2 := by positivity
      nlinarith
    rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have hb1' : ‖deriv (regB c) s‖ * (1 + s) ^ 2 ≤ C₁ := by
      refine le_trans ?_ hb1
      have : (1 + s) ^ 2 ≤ (1 + s) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
    calc ‖kappa c s * regB c s / 4 - 3 * deriv (regB c) s‖ / s * (1 + s) ^ 3
        ≤ ‖kappa c s * regB c s / 4 - 3 * deriv (regB c) s‖ / s * (2 * s * (1 + s) ^ 2) := by
          gcongr
      _ = 2 * (‖kappa c s * regB c s / 4 - 3 * deriv (regB c) s‖ * (1 + s) ^ 2) := by
          field_simp
      _ ≤ 2 * ((3 / |c.im| * ‖regB c s‖ / 4 + 3 * ‖deriv (regB c) s‖) * (1 + s) ^ 2) := by
          gcongr
      _ = 2 * (3 / |c.im| * (‖regB c s‖ * (1 + s) ^ 2) / 4 +
            3 * (‖deriv (regB c) s‖ * (1 + s) ^ 2)) := by ring
      _ ≤ 2 * (3 / |c.im| * C₀ / 4 + 3 * C₁) := by gcongr

/-- The radial profile `β(s) = K b(s) m(s)` of the seed dual kernel. -/
def betaFun (c a₀ K : ℂ) (s : ℝ) : ℂ := K * (regB c s * denM a₀ s)

/-- **Radial jet bounds**: `β` is smooth and `‖β‖(1+s)²`, `‖β'‖(1+s)³`, `‖β''‖(1+s)³` are bounded
on `s ≥ 0`. -/
theorem betaFun_bounds {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) {a₀ : ℂ} (ha : a₀.im ≠ 0)
    (K : ℂ) :
    ContDiff ℝ ∞ (betaFun c a₀ K) ∧ ∃ B : ℝ,
      (∀ s, 0 ≤ s → ‖betaFun c a₀ K s‖ * (1 + s) ^ 2 ≤ B) ∧
      (∀ s, 0 ≤ s → ‖deriv (betaFun c a₀ K) s‖ * (1 + s) ^ 3 ≤ B) ∧
      (∀ s, 0 ≤ s → ‖deriv (deriv (betaFun c a₀ K)) s‖ * (1 + s) ^ 3 ≤ B) := by
  have hc := hF.im_ne_zero
  have hb := contDiff_regB hc
  set b := regB c with hbdef
  have hbd : Differentiable ℝ b := hb.differentiable (by simp)
  have hb1c : ContDiff ℝ ∞ (deriv b) := (contDiff_infty_iff_deriv.mp hb).2
  have hbd1 : Differentiable ℝ (deriv b) := hb1c.differentiable (by simp)
  -- smoothness of `m`
  have hmc : ContDiff ℝ ∞ (denM a₀) := by
    have hE : ContDiff ℝ ∞ gaussE4 := by
      unfold gaussE4
      exact Complex.ofRealCLM.contDiff.comp
        (Real.contDiff_exp.comp ((contDiff_id.div_const 4).neg))
    exact (hE.sub contDiff_const).inv fun s => gaussE4_sub_ne ha s
  refine ⟨contDiff_const.mul (hb.mul hmc), ?_⟩
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_decay_regB hF
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_decay_deriv_regB hF
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_decay_deriv2_regB hF
  set M := 1 / |a₀.im| with hM
  have hM0 : 0 ≤ M := by positivity
  -- derivatives of `β`
  have hd1 : ∀ s, HasDerivAt (betaFun c a₀ K)
      (K * (deriv b s * denM a₀ s + b s * denM1 a₀ s)) s := fun s =>
    ((hbd s).hasDerivAt.fun_mul (hasDerivAt_denM ha s)).const_mul K
  have hD1 : deriv (betaFun c a₀ K) =
      fun s => K * (deriv b s * denM a₀ s + b s * denM1 a₀ s) :=
    funext fun s => (hd1 s).deriv
  have hd2 : ∀ s, HasDerivAt (fun s => K * (deriv b s * denM a₀ s + b s * denM1 a₀ s))
      (K * ((deriv (deriv b) s * denM a₀ s + deriv b s * denM1 a₀ s) +
        (deriv b s * denM1 a₀ s + b s * denM2 a₀ s))) s := fun s =>
    ((((hbd1 s).hasDerivAt.fun_mul (hasDerivAt_denM ha s))).fun_add
      ((hbd s).hasDerivAt.fun_mul (hasDerivAt_denM1 ha s))).const_mul K
  have hD2 : deriv (deriv (betaFun c a₀ K)) = fun s =>
      K * ((deriv (deriv b) s * denM a₀ s + deriv b s * denM1 a₀ s) +
        (deriv b s * denM1 a₀ s + b s * denM2 a₀ s)) := by
    rw [hD1]
    exact funext fun s => (hd2 s).deriv
  refine ⟨‖K‖ * (C₀ * M + (C₁ * M + C₀ * M ^ 2) +
      (C₂ * M + 2 * C₁ * M ^ 2 + C₀ * (M ^ 2 + 2 * M ^ 3))), ?_, ?_, ?_⟩
  · intro s hs
    have hb0 := hC₀ s hs
    have hm := norm_denM_le ha s
    rw [← hM] at hm
    unfold betaFun
    rw [norm_mul, norm_mul]
    calc ‖K‖ * (‖b s‖ * ‖denM a₀ s‖) * (1 + s) ^ 2 =
        ‖K‖ * ((‖b s‖ * (1 + s) ^ 2) * ‖denM a₀ s‖) := by ring
      _ ≤ ‖K‖ * (C₀ * M) := by gcongr
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg K)
        have : 0 ≤ C₁ * M + C₀ * M ^ 2 := by positivity
        have : 0 ≤ C₂ * M + 2 * C₁ * M ^ 2 + C₀ * (M ^ 2 + 2 * M ^ 3) := by positivity
        linarith
  · intro s hs
    have hb0 := hC₀ s hs
    have hb1 := hC₁ s hs
    have hm := norm_denM_le ha s
    have hm1 := norm_denM1_mul_le ha hs
    rw [← hM] at hm hm1
    rw [hD1]
    simp only
    rw [norm_mul]
    have hs1 : 0 ≤ 1 + s := by linarith
    calc ‖K‖ * ‖deriv b s * denM a₀ s + b s * denM1 a₀ s‖ * (1 + s) ^ 3
        ≤ ‖K‖ * (‖deriv b s‖ * ‖denM a₀ s‖ + ‖b s‖ * ‖denM1 a₀ s‖) * (1 + s) ^ 3 := by
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ = ‖K‖ * ((‖deriv b s‖ * (1 + s) ^ 3) * ‖denM a₀ s‖ +
          (‖b s‖ * (1 + s) ^ 2) * (‖denM1 a₀ s‖ * (1 + s))) := by ring
      _ ≤ ‖K‖ * (C₁ * M + C₀ * M ^ 2) := by gcongr
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg K)
        have : 0 ≤ C₀ * M := by positivity
        have : 0 ≤ C₂ * M + 2 * C₁ * M ^ 2 + C₀ * (M ^ 2 + 2 * M ^ 3) := by positivity
        linarith
  · intro s hs
    have hb0 := hC₀ s hs
    have hb1 := hC₁ s hs
    have hb2 := hC₂ s hs
    have hm := norm_denM_le ha s
    have hm1 := norm_denM1_mul_le ha hs
    have hm1' := norm_denM1_le ha hs
    have hm2 := norm_denM2_mul_le ha hs
    rw [← hM] at hm hm1 hm1' hm2
    rw [hD2]
    simp only
    rw [norm_mul]
    have hs1 : 0 ≤ 1 + s := by linarith
    calc ‖K‖ * ‖(deriv (deriv b) s * denM a₀ s + deriv b s * denM1 a₀ s) +
          (deriv b s * denM1 a₀ s + b s * denM2 a₀ s)‖ * (1 + s) ^ 3
        ≤ ‖K‖ * ((‖deriv (deriv b) s‖ * ‖denM a₀ s‖ + ‖deriv b s‖ * ‖denM1 a₀ s‖) +
          (‖deriv b s‖ * ‖denM1 a₀ s‖ + ‖b s‖ * ‖denM2 a₀ s‖)) * (1 + s) ^ 3 := by
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          · refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
          · refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
      _ = ‖K‖ * ((‖deriv (deriv b) s‖ * (1 + s) ^ 3) * ‖denM a₀ s‖ +
          2 * ((‖deriv b s‖ * (1 + s) ^ 3) * ‖denM1 a₀ s‖) +
          (‖b s‖ * (1 + s) ^ 2) * (‖denM2 a₀ s‖ * (1 + s))) := by ring
      _ ≤ ‖K‖ * (C₂ * M + 2 * (C₁ * M ^ 2) + C₀ * (M ^ 2 + 2 * M ^ 3)) := by gcongr
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg K)
        have : 0 ≤ C₀ * M := by positivity
        have : 0 ≤ C₁ * M + C₀ * M ^ 2 := by positivity
        linarith

end UnforcedLeray.Short.IIIa.SeedJet2Aux
