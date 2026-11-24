import UnforcedLeray.Lib.ComplexODEC.Regular
import UnforcedLeray.Lib.ComplexODEB
import UnforcedLeray.Lib.PlanarSectors
import UnforcedLeray.Units.B0034.Radial
import NonUniqueEuler.P.Infra.ODE.Uniqueness

/-!
# The radial mode: matching with the regular solution and the Green representation
(INF18 O12 matching, O9)

Scoping note `scoping/INF10-INF12-INF18-Planar.md` §4 bypasses B3, B4 and §5 targets O9, O12.
Manuscript `paper/main.tex` lines 1128--1192 (§`sec:st18-1294`, units B0051--B0057).

Input: a whole-line Gaussian Rayleigh mode `F` in logarithmic radius, as produced by O8
(`Rayleigh.Evans.exists_wholeLine_growing_mode`, `Lib/ComplexODEB`), bundled as
`WholeLineData c F`. In `s = r²` the coefficient is `kappa c s = k(√s)/(Ω(√s) - c)`
(tex line 1163), and in log radius the equation is `F'' = (4 + e^{2t} κ(e^{2t})) F`
(tex eq. `st18-t00043`, `B = A/(Ω - c)`).

Main results.
* `exists_mode_eq_regLog` (O12 matching, tex lines 1163--1166): `F(t) = β₀ e^{2t} b(e^{2t})`
  for all `t`, with `b = regSol (kappa c)` the smooth regular solution of
  `4(s b'' + 3 b') = κ b` and `β₀ ≠ 0`. The manuscript identifies the Frobenius solution with
  the selected solution; here a Wronskian argument at `t → -∞` does it (bypass B4).
* `modeRadial_eq` : `φ(r) = F(log r) = β₀ r² b(r²)` for `r > 0`.
* `mode_eq_green` (O9, tex lines 1181--1183, eq. `st18-t00007`): `φ = greenN 2 h` on
  `(0, ∞)`, `h = kφ/(Ω - c)` (tex eq. `st18-t00046`).
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.ComplexODEC

open UnforcedLeray.GaussianVortex UnforcedLeray.Rayleigh UnforcedLeray.Sturm
open NonUniqueEuler.LinODE

/-! ### The coefficient in `s = r²` -/

/-- `κ_c(s) = k(√s)/(Ω(√s) - c) = (s/4 - 2) e^{-s/4}/(e^{-s/4} - c)` (tex line 1163). -/
def kappa (c : ℂ) (s : ℝ) : ℂ :=
  (((s / 4 - 2) * Real.exp (-(s / 4)) : ℝ) : ℂ) / ((Real.exp (-(s / 4)) : ℂ) - c)

theorem ofReal_sub_ne_zero {c : ℂ} (hc : c.im ≠ 0) (x : ℝ) : (x : ℂ) - c ≠ 0 := by
  intro h
  apply hc
  have := congrArg Complex.im h
  simpa using this

theorem abs_im_le_norm_ofReal_sub (c : ℂ) (x : ℝ) : |c.im| ≤ ‖(x : ℂ) - c‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) - c)
  simpa using this

theorem contDiff_kappa {c : ℂ} (hc : c.im ≠ 0) : ContDiff ℝ ∞ (kappa c) := by
  have h1r : ContDiff ℝ ∞ fun s : ℝ => (s / 4 - 2) * Real.exp (-(s / 4)) := by fun_prop
  have h2r : ContDiff ℝ ∞ fun s : ℝ => Real.exp (-(s / 4)) := by fun_prop
  have h1 : ContDiff ℝ ∞ fun s : ℝ => (((s / 4 - 2) * Real.exp (-(s / 4)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp h1r
  have h2 : ContDiff ℝ ∞ fun s : ℝ => (Real.exp (-(s / 4)) : ℂ) - c :=
    (Complex.ofRealCLM.contDiff.comp h2r).sub contDiff_const
  have h3 := h2.inv (fun s => ofReal_sub_ne_zero hc _)
  have e : kappa c = fun s => (((s / 4 - 2) * Real.exp (-(s / 4)) : ℝ) : ℂ) *
      ((Real.exp (-(s / 4)) : ℂ) - c)⁻¹ := by
    funext s
    simp only [kappa, div_eq_mul_inv]
  rw [e]
  exact h1.mul h3

/-- `‖κ_c(s)‖ ≤ |s/4 - 2| e^{-s/4} / |Im c|` (tex line 1176, `|Ω - c| ≥ Im c`). -/
theorem norm_kappa_le {c : ℂ} (hc : c.im ≠ 0) (s : ℝ) :
    ‖kappa c s‖ ≤ |s / 4 - 2| * Real.exp (-(s / 4)) / |c.im| := by
  have hpos : 0 < |c.im| := abs_pos.mpr hc
  rw [kappa, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  exact div_le_div_of_nonneg_left (by positivity) hpos (abs_im_le_norm_ofReal_sub c _)

/-- `k(r)/(Ω(r) - c) = κ_c(r²)`. -/
theorem radialK_div_eq_kappa (c : ℂ) (r : ℝ) :
    (radialK r : ℂ) / ((radialOmega r : ℂ) - c) = kappa c (r ^ 2) := by
  simp only [kappa, radialK, radialOmega]

/-- In log radius, `A/(Ω - c) = e^{2t} κ_c(e^{2t})` (tex eq. `st18-t00043`). -/
theorem coeff_div_eq_kappa (c : ℂ) (t : ℝ) :
    (gaussianRayleighCoefficient t : ℂ) / ((neutralOmega t : ℂ) - c) =
      ((Real.exp t ^ 2 : ℝ) : ℂ) * kappa c (Real.exp t ^ 2) := by
  rw [B0034.gaussianRayleighCoefficient_eq_radialK, ← radialOmega_exp]
  simp only [kappa, radialK, radialOmega]
  push_cast
  ring

/-- The log-radius potential `V = 4 + A/(Ω - c)` of `F'' = V F`. -/
def logPot (c : ℂ) (t : ℝ) : ℂ :=
  4 + (gaussianRayleighCoefficient t : ℂ) / ((neutralOmega t : ℂ) - c)

theorem logPot_eq (c : ℂ) (t : ℝ) :
    logPot c t = 4 + ((Real.exp t ^ 2 : ℝ) : ℂ) * kappa c (Real.exp t ^ 2) := by
  rw [logPot, coeff_div_eq_kappa]

theorem continuous_logPot {c : ℂ} (hc : c.im ≠ 0) : Continuous (logPot c) := by
  have e : logPot c = fun t => 4 + ((Real.exp t ^ 2 : ℝ) : ℂ) * kappa c (Real.exp t ^ 2) :=
    funext (logPot_eq c)
  rw [e]
  have hk := (contDiff_kappa hc).continuous
  fun_prop

/-! ### The whole-line mode (output of O8) -/

/-- The output of O8 (`Rayleigh.Evans.exists_wholeLine_growing_mode`): a classical whole-line
Gaussian Rayleigh mode at angular index two (tex eq. `st18-t00039`, lines 1122--1127), smooth,
with `F, F' → 0` at both ends. -/
structure WholeLineData (c : ℂ) (F : ℝ → ℂ) : Prop where
  mode : GaussianWholeLineMode c F
  smooth : ContDiff ℝ ∞ F
  tendsto_atTop : Tendsto F atTop (𝓝 0)
  tendsto_atBot : Tendsto F atBot (𝓝 0)
  deriv_tendsto_atTop : Tendsto (deriv F) atTop (𝓝 0)
  deriv_tendsto_atBot : Tendsto (deriv F) atBot (𝓝 0)

namespace WholeLineData

variable {c : ℂ} {F : ℝ → ℂ}

theorem im_ne_zero (hF : WholeLineData c F) : c.im ≠ 0 := hF.mode.upper_half_plane.ne'

theorem differentiable (hF : WholeLineData c F) : Differentiable ℝ F :=
  hF.smooth.differentiable (by simp)

theorem differentiable_deriv (hF : WholeLineData c F) : Differentiable ℝ (deriv F) :=
  (contDiff_infty_iff_deriv.mp hF.smooth).2.differentiable (by simp)

theorem continuous_deriv (hF : WholeLineData c F) : Continuous (deriv F) :=
  hF.differentiable_deriv.continuous

/-- `F'' = V F` (tex eq. `st18-t00043`). -/
theorem deriv_deriv_eq (hF : WholeLineData c F) (t : ℝ) :
    deriv (deriv F) t = logPot c t * F t := by
  have heq := hF.mode.equation t
  have hne := gaussianSpeed_denominator_ne_zero hF.mode.upper_half_plane t
  rw [logPot]
  field_simp
  linear_combination heq

theorem isSolOn (hF : WholeLineData c F) : IsSolOn (logPot c) univ F (deriv F) :=
  ⟨fun t _ => (hF.differentiable t).hasDerivAt.hasDerivWithinAt,
    fun t _ => by
      rw [← hF.deriv_deriv_eq t]
      exact (hF.differentiable_deriv t).hasDerivAt.hasDerivWithinAt⟩

/-- A continuous function with zero limits at both ends is bounded. -/
theorem exists_bound_of_tendsto {f : ℝ → ℂ} (hf : Continuous f)
    (h1 : Tendsto f atTop (𝓝 0)) (h2 : Tendsto f atBot (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M := by
  have e1 : ∀ᶠ t in atTop, ‖f t‖ ≤ 1 := by
    have := h1.norm
    rw [norm_zero] at this
    exact this.eventually (ge_mem_nhds one_pos)
  have e2 : ∀ᶠ t in atBot, ‖f t‖ ≤ 1 := by
    have := h2.norm
    rw [norm_zero] at this
    exact this.eventually (ge_mem_nhds one_pos)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp e1
  obtain ⟨T₀, hT₀⟩ := eventually_atBot.mp e2
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := T₀) (b := T₁)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), fun t => ?_⟩
  rcases le_or_gt t T₀ with h | h
  · exact (hT₀ t h).trans (le_max_right _ _)
  rcases le_or_gt T₁ t with h' | h'
  · exact (hT₁ t h').trans (le_max_right _ _)
  exact (hC t ⟨h.le, h'.le⟩).trans (le_max_left _ _)

theorem exists_bound (hF : WholeLineData c F) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖F t‖ ≤ M :=
  exists_bound_of_tendsto hF.smooth.continuous hF.tendsto_atTop hF.tendsto_atBot

theorem exists_bound_deriv (hF : WholeLineData c F) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖deriv F t‖ ≤ M :=
  exists_bound_of_tendsto hF.continuous_deriv hF.deriv_tendsto_atTop hF.deriv_tendsto_atBot

end WholeLineData

/-! ### The regular solution in log radius -/

/-- The regular solution `b = regSol (kappa c)` of `4(s b'' + 3 b') = κ_c b`, `b(0) = 1`. -/
def regB (c : ℂ) : ℝ → ℂ := regSol (kappa c)

theorem contDiff_regB {c : ℂ} (hc : c.im ≠ 0) : ContDiff ℝ ∞ (regB c) :=
  contDiff_regSol (contDiff_kappa hc)

theorem regB_zero {c : ℂ} (hc : c.im ≠ 0) : regB c 0 = 1 :=
  regSol_zero (contDiff_kappa hc).continuous

theorem regB_ode {c : ℂ} (hc : c.im ≠ 0) (s : ℝ) :
    4 * ((s : ℂ) * deriv (deriv (regB c)) s + 3 * deriv (regB c) s) = kappa c s * regB c s :=
  regSol_ode (contDiff_kappa hc) s

/-- The regular solution in log radius, `G(t) = e^{2t} b(e^{2t})`. -/
def regLog (c : ℂ) (t : ℝ) : ℂ := ((Real.exp t ^ 2 : ℝ) : ℂ) * regB c (Real.exp t ^ 2)

/-- Its derivative `G'(t) = 2 e^{2t} b(e^{2t}) + 2 e^{4t} b'(e^{2t})`. -/
def regLog' (c : ℂ) (t : ℝ) : ℂ :=
  2 * ((Real.exp t ^ 2 : ℝ) : ℂ) * regB c (Real.exp t ^ 2) +
    2 * ((Real.exp t ^ 2 : ℝ) : ℂ) ^ 2 * deriv (regB c) (Real.exp t ^ 2)

theorem hasDerivAt_exp_sq (t : ℝ) :
    HasDerivAt (fun t => Real.exp t ^ 2) (2 * Real.exp t ^ 2) t := by
  have := (Real.hasDerivAt_exp t).pow 2
  norm_num at this
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_regLog {c : ℂ} (hc : c.im ≠ 0) (t : ℝ) :
    HasDerivAt (regLog c) (regLog' c t) t := by
  have hbd : Differentiable ℝ (regB c) := (contDiff_regB hc).differentiable (by simp)
  have hE := hasDerivAt_exp_sq t
  have hb := (hbd (Real.exp t ^ 2)).hasDerivAt.scomp t hE
  have hEc := hE.ofReal_comp
  have h := hEc.mul hb
  refine h.congr_deriv ?_
  simp only [regLog', Complex.real_smul, Function.comp_apply]
  push_cast
  ring

theorem hasDerivAt_regLog' {c : ℂ} (hc : c.im ≠ 0) (t : ℝ) :
    HasDerivAt (regLog' c) (logPot c t * regLog c t) t := by
  have hbd : Differentiable ℝ (regB c) := (contDiff_regB hc).differentiable (by simp)
  have hb'd : Differentiable ℝ (deriv (regB c)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_regB hc)).2.differentiable (by simp)
  have hE := hasDerivAt_exp_sq t
  have hb := (hbd (Real.exp t ^ 2)).hasDerivAt.scomp t hE
  have hb' := (hb'd (Real.exp t ^ 2)).hasDerivAt.scomp t hE
  have hEc := hE.ofReal_comp
  have h := ((hEc.const_mul 2).mul hb).add (((hEc.pow 2).const_mul 2).mul hb')
  have hode := regB_ode hc (Real.exp t ^ 2)
  refine h.congr_deriv ?_
  rw [logPot_eq]
  simp only [regLog, Complex.real_smul, Function.comp_apply, Pi.pow_apply]
  push_cast at hode ⊢
  linear_combination (Complex.exp (t : ℂ) ^ 2) ^ 2 * hode

theorem isSolOn_regLog {c : ℂ} (hc : c.im ≠ 0) : IsSolOn (logPot c) univ (regLog c) (regLog' c) :=
  ⟨fun t _ => (hasDerivAt_regLog hc t).hasDerivWithinAt,
    fun t _ => (hasDerivAt_regLog' hc t).hasDerivWithinAt⟩

/-- The Wronskian of two solutions of `ψ'' = V ψ` on `ℝ` is constant. -/
theorem wronskian_const {V ψ ψ' φ φ' : ℝ → ℂ} (h₁ : IsSolOn V univ ψ ψ')
    (h₂ : IsSolOn V univ φ φ') (x y : ℝ) :
    ψ x * φ' x - ψ' x * φ x = ψ y * φ' y - ψ' y * φ y := by
  have hd : ∀ t, HasDerivAt (fun t => ψ t * φ' t - ψ' t * φ t) 0 t := by
    intro t
    have a1 := hasDerivWithinAt_univ.mp (h₁.hasDerivWithinAt t (mem_univ t))
    have a2 := hasDerivWithinAt_univ.mp (h₁.hasDerivWithinAt' t (mem_univ t))
    have b1 := hasDerivWithinAt_univ.mp (h₂.hasDerivWithinAt t (mem_univ t))
    have b2 := hasDerivWithinAt_univ.mp (h₂.hasDerivWithinAt' t (mem_univ t))
    refine ((a1.mul b2).sub (a2.mul b1)).congr_deriv ?_
    ring
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) x y

theorem tendsto_exp_sq_atBot : Tendsto (fun t : ℝ => Real.exp t ^ 2) atBot (𝓝 0) := by
  have := Real.tendsto_exp_atBot.pow 2
  simpa using this

theorem tendsto_regLog_atBot {c : ℂ} (hc : c.im ≠ 0) : Tendsto (regLog c) atBot (𝓝 0) := by
  have hE := tendsto_exp_sq_atBot
  have hEc : Tendsto (fun t : ℝ => ((Real.exp t ^ 2 : ℝ) : ℂ)) atBot (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hE
    rw [Complex.ofReal_zero] at this
    exact this
  have hb : Tendsto (fun t => regB c (Real.exp t ^ 2)) atBot (𝓝 (regB c 0)) :=
    ((contDiff_regB hc).continuous.tendsto 0).comp hE
  have := hEc.mul hb
  rw [zero_mul] at this
  exact this

theorem tendsto_regLog'_atBot {c : ℂ} (hc : c.im ≠ 0) : Tendsto (regLog' c) atBot (𝓝 0) := by
  have hE := tendsto_exp_sq_atBot
  have hEc : Tendsto (fun t : ℝ => ((Real.exp t ^ 2 : ℝ) : ℂ)) atBot (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hE
    rw [Complex.ofReal_zero] at this
    exact this
  have hb : Tendsto (fun t => regB c (Real.exp t ^ 2)) atBot (𝓝 (regB c 0)) :=
    ((contDiff_regB hc).continuous.tendsto 0).comp hE
  have hb' : Tendsto (fun t => deriv (regB c) (Real.exp t ^ 2)) atBot
      (𝓝 (deriv (regB c) 0)) :=
    (((contDiff_regB hc).continuous_deriv (by simp)).tendsto 0).comp hE
  have := ((hEc.const_mul 2).mul hb).add (((hEc.pow 2).const_mul 2).mul hb')
  simp only [mul_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at this
  exact this

/-- **Matching** (tex lines 1163--1166; bypass B4): the whole-line mode is a nonzero
multiple of the regular solution, `F(t) = β₀ e^{2t} b(e^{2t})`. -/
theorem exists_mode_eq_regLog {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∃ β₀ : ℂ, β₀ ≠ 0 ∧ ∀ t, F t = β₀ * regLog c t ∧ deriv F t = β₀ * regLog' c t := by
  have hc := hF.im_ne_zero
  have hsolF := hF.isSolOn
  have hsolG := isSolOn_regLog hc
  set W : ℝ → ℂ := fun t => F t * regLog' c t - deriv F t * regLog c t with hW
  have hWconst : ∀ t, W t = W 0 := fun t => wronskian_const hsolF hsolG t 0
  have hWlim : Tendsto W atBot (𝓝 0) := by
    have := (hF.tendsto_atBot.mul (tendsto_regLog'_atBot hc)).sub
      (hF.deriv_tendsto_atBot.mul (tendsto_regLog_atBot hc))
    simpa using this
  have hW0 : W 0 = 0 := by
    have hconst : Tendsto W atBot (𝓝 (W 0)) :=
      tendsto_const_nhds.congr fun t => (hWconst t).symm
    exact tendsto_nhds_unique hconst hWlim
  -- a point where the regular solution does not vanish
  have hbne : ∀ᶠ t in atBot, regB c (Real.exp t ^ 2) ≠ 0 := by
    have hb : Tendsto (fun t => regB c (Real.exp t ^ 2)) atBot (𝓝 (regB c 0)) :=
      ((contDiff_regB hc).continuous.tendsto 0).comp tendsto_exp_sq_atBot
    rw [regB_zero hc] at hb
    exact hb.eventually_ne one_ne_zero
  obtain ⟨t₀, ht₀⟩ := hbne.exists
  have hG0 : regLog c t₀ ≠ 0 := by
    refine mul_ne_zero ?_ ht₀
    exact_mod_cast (pow_pos (Real.exp_pos t₀) 2).ne'
  set β₀ : ℂ := F t₀ / regLog c t₀ with hβ₀
  have h0 : F t₀ = β₀ * regLog c t₀ := by rw [hβ₀]; field_simp
  have h0' : deriv F t₀ = β₀ * regLog' c t₀ := by
    have hw : F t₀ * regLog' c t₀ - deriv F t₀ * regLog c t₀ = 0 := by
      have := hWconst t₀
      rw [hW0] at this
      exact this
    rw [hβ₀]
    field_simp
    linear_combination -hw
  have heq := IsSolOn.eqOn ordConnected_univ (continuous_logPot hc).continuousOn hsolF
    (hsolG.const_mul β₀) (mem_univ t₀) h0 h0'
  have hβne : β₀ ≠ 0 := by
    intro hβ
    obtain ⟨t, ht⟩ := hF.mode.nonzero
    apply ht
    simpa [hβ] using heq.1 (mem_univ t)
  exact ⟨β₀, hβne, fun t => ⟨heq.1 (mem_univ t), heq.2 (mem_univ t)⟩⟩

/-! ### The radial mode and its vorticity -/

/-- The radial streamfunction `φ(r) = F(log r)` (tex line 1124). -/
def modeRadial (F : ℝ → ℂ) (r : ℝ) : ℂ := F (Real.log r)

/-- The vorticity profile `h = kφ/(Ω - c) = κ_c(r²) φ(r)` (tex eq. `st18-t00046`). -/
def modeVort (c : ℂ) (F : ℝ → ℂ) (r : ℝ) : ℂ := kappa c (r ^ 2) * modeRadial F r

theorem modeVort_eq (c : ℂ) (F : ℝ → ℂ) (r : ℝ) :
    modeVort c F r = (radialK r : ℂ) * modeRadial F r / ((radialOmega r : ℂ) - c) := by
  rw [modeVort, ← radialK_div_eq_kappa]
  ring

/-- `φ(r) = β₀ r² b(r²)` for `r > 0` (tex line 1162). -/
theorem modeRadial_eq {c : ℂ} {F : ℝ → ℂ} {β₀ : ℂ}
    (hβ : ∀ t, F t = β₀ * regLog c t) {r : ℝ} (hr : 0 < r) :
    modeRadial F r = β₀ * ((r ^ 2 : ℝ) : ℂ) * regB c (r ^ 2) := by
  rw [modeRadial, hβ, regLog, Real.exp_log hr]
  ring

/-! ### O9: the Green representation -/

/-- `x^k e^{-x²/4}` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_gauss (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2 / 4))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := (k : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast]
  congr 2
  ring

/-- `‖h(ρ)‖ ≤ M (ρ²/4 + 2) e^{-ρ²/4} / |Im c|` for `‖F‖ ≤ M`. -/
theorem norm_modeVort_le {c : ℂ} {F : ℝ → ℂ} (hc : c.im ≠ 0) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ‖F t‖ ≤ M) (ρ : ℝ) :
    ‖modeVort c F ρ‖ ≤ M / |c.im| * ((ρ ^ 2 / 4 + 2) * Real.exp (-(ρ ^ 2 / 4))) := by
  have hpos : 0 < |c.im| := abs_pos.mpr hc
  rw [modeVort, norm_mul]
  have h1 := norm_kappa_le hc (ρ ^ 2)
  have h2 : |ρ ^ 2 / 4 - 2| ≤ ρ ^ 2 / 4 + 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg ρ]
  have h3 : ‖kappa c (ρ ^ 2)‖ ≤ (ρ ^ 2 / 4 + 2) * Real.exp (-(ρ ^ 2 / 4)) / |c.im| :=
    h1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le) hpos.le)
  calc ‖kappa c (ρ ^ 2)‖ * ‖modeRadial F ρ‖
      ≤ (ρ ^ 2 / 4 + 2) * Real.exp (-(ρ ^ 2 / 4)) / |c.im| * M :=
        mul_le_mul h3 (hM _) (norm_nonneg _) (by positivity)
    _ = M / |c.im| * ((ρ ^ 2 / 4 + 2) * Real.exp (-(ρ ^ 2 / 4))) := by ring

theorem continuousOn_modeRadial {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ContinuousOn (modeRadial F) (Ioi 0) := fun r hr =>
  (hF.smooth.continuous.continuousAt.comp
    (Real.continuousAt_log (ne_of_gt hr))).continuousWithinAt

theorem continuousOn_modeVort {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ContinuousOn (modeVort c F) (Ioi 0) := by
  have hk : Continuous fun r : ℝ => kappa c (r ^ 2) :=
    (contDiff_kappa hF.im_ne_zero).continuous.comp (continuous_pow 2)
  exact hk.continuousOn.mul (continuousOn_modeRadial hF)

/-- `r^k h(r)` is integrable on `(0, ∞)` for every `k`. -/
theorem integrableOn_pow_mul_modeVort {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (k : ℕ) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ k * modeVort c F r) (Ioi 0) := by
  obtain ⟨M, hM0, hM⟩ := hF.exists_bound
  have hc := hF.im_ne_zero
  have hint : IntegrableOn (fun r : ℝ => M / |c.im| * ((r ^ (k + 2) / 4 + 2 * r ^ k) *
      Real.exp (-(r ^ 2 / 4)))) (Ioi 0) := by
    have := ((integrableOn_pow_mul_gauss (k + 2)).div_const 4).add
      ((integrableOn_pow_mul_gauss k).const_mul 2)
    refine IntegrableOn.congr_fun (this.const_mul (M / |c.im|)) (fun r _ => ?_)
      measurableSet_Ioi
    simp only [Pi.add_apply]
    ring
  refine hint.mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.pow k).continuousOn.mul
      (continuousOn_modeVort hF)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    calc r ^ k * ‖modeVort c F r‖
        ≤ r ^ k * (M / |c.im| * ((r ^ 2 / 4 + 2) * Real.exp (-(r ^ 2 / 4)))) :=
          mul_le_mul_of_nonneg_left (norm_modeVort_le hc hM0 hM r) (by positivity)
      _ = M / |c.im| * ((r ^ (k + 2) / 4 + 2 * r ^ k) * Real.exp (-(r ^ 2 / 4))) := by ring

/-- The vorticity profile is an admissible Green datum (`r h ∈ L¹(0, ∞)`). -/
theorem wprof_modeVort {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    B0011.WProf (modeVort c F) := by
  refine ⟨(continuousOn_modeVort hF).aestronglyMeasurable measurableSet_Ioi, ?_⟩
  have h := (integrableOn_pow_mul_modeVort hF 1).norm
  refine IntegrableOn.congr_fun h (fun r hr => ?_) measurableSet_Ioi
  have hr0 : (0 : ℝ) < r := hr
  simp only [pow_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]

/-- `Δ₂ φ = h` on `(0, ∞)` in the integrated form of the Green layer (tex lines 1168--1170,
eq. `st18-t00046`). -/
theorem isRadialPoissonSol_modeRadial {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    Planar.IsRadialPoissonSol 2 (modeVort c F) (modeRadial F) := by
  set ψ' : ℝ → ℂ := fun r => r⁻¹ • deriv F (Real.log r) with hψ'
  have h1 : ∀ r : ℝ, 0 < r → HasDerivAt (modeRadial F) (ψ' r) r := fun r hr =>
    (hF.differentiable (Real.log r)).hasDerivAt.scomp r (Real.hasDerivAt_log hr.ne')
  have h2 : ∀ r : ℝ, 0 < r → HasDerivAt ψ'
      (r⁻¹ • (r⁻¹ • deriv (deriv F) (Real.log r)) + (-(r ^ 2)⁻¹) • deriv F (Real.log r)) r :=
    fun r hr => (hasDerivAt_inv hr.ne').smul
      ((hF.differentiable_deriv (Real.log r)).hasDerivAt.scomp r (Real.hasDerivAt_log hr.ne'))
  have hcont' : ContinuousOn ψ' (Ioi 0) := fun r hr =>
    (h2 r hr).continuousAt.continuousWithinAt
  refine ⟨ψ', h1, hcont', fun a b ha hb => ?_⟩
  have hsub : ∀ x ∈ uIcc a b, 0 < x := fun x hx => by
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [uIcc_of_ge h] at hx; exact lt_of_lt_of_le hb hx.1
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt ψ' (modeVort c F x - ψ' x / (x : ℂ) +
      ((2 : ℕ) : ℂ) ^ 2 * modeRadial F x / (x : ℂ) ^ 2) x := by
    intro x hx
    have hx0 := hsub x hx
    convert h2 x hx0 using 1
    have hpot := hF.deriv_deriv_eq (Real.log x)
    rw [logPot_eq, Real.exp_log hx0] at hpot
    rw [hpot, hψ', modeVort, modeRadial]
    simp only [Complex.real_smul]
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    push_cast
    field_simp
    ring
  have hcont : ContinuousOn (fun x => modeVort c F x - ψ' x / (x : ℂ) +
      ((2 : ℕ) : ℂ) ^ 2 * modeRadial F x / (x : ℂ) ^ 2) (uIcc a b) := by
    intro x hx
    have hx0 := hsub x hx
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    refine ContinuousAt.continuousWithinAt ?_
    have c1 : ContinuousAt (modeVort c F) x :=
      (continuousOn_modeVort hF).continuousAt (Ioi_mem_nhds hx0)
    have c2 : ContinuousAt ψ' x := (h2 x hx0).continuousAt
    have c3 : ContinuousAt (modeRadial F) x :=
      (continuousOn_modeRadial hF).continuousAt (Ioi_mem_nhds hx0)
    have c4 : ContinuousAt (fun x : ℝ => (x : ℂ)) x := Complex.continuous_ofReal.continuousAt
    exact (c1.sub (c2.div c4 hxne)).add ((continuousAt_const.mul c3).div (c4.pow 2)
      (pow_ne_zero 2 hxne))
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable)).symm

theorem tendsto_modeRadial_nhdsGT_zero {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    Tendsto (modeRadial F) (𝓝[>] 0) (𝓝 0) :=
  hF.tendsto_atBot.comp Real.tendsto_log_nhdsGT_zero

theorem tendsto_modeRadial_atTop {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    Tendsto (modeRadial F) atTop (𝓝 0) :=
  hF.tendsto_atTop.comp Real.tendsto_log_atTop

/-- **O9** (scoping `mode_eq_green`; tex lines 1181--1183): the radial streamfunction is the
Green inverse of its vorticity, `φ = R h = greenN 2 h` on `(0, ∞)`. -/
theorem mode_eq_green {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∀ r > 0, modeRadial F r = Planar.greenN 2 (modeVort c F) r := fun r hr =>
  Planar.eqOn_greenN_of_tendsto (by norm_num) (wprof_modeVort hF)
    (isRadialPoissonSol_modeRadial hF) (tendsto_modeRadial_nhdsGT_zero hF)
    (tendsto_modeRadial_atTop hF) hr

end UnforcedLeray.ComplexODEC
