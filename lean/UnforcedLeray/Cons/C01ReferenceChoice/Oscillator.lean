import UnforcedLeray.Cons.C01ReferenceChoice.Eigenpair

/-!
# Step C1, part G3a: the eigenvorticity lies in the domain of the oscillator `D`

`paper/main.tex`, Theorem G3a (`thm:ref-gaussian-domains`, lines 719–733): `q` belongs to the
power domains of `D = Δ + ½y·∇ + 2` on `X_G` (`eq:st18-t00011`; line 1516, blueprint unit
B0095, within B0099), using "the Gaussian derivative bounds" of the eigenvorticity. Only the
first power is needed by the blueprint (`IsPlanarReference.oscillator_memXG`): the classical
`Dq` of the smooth profile is in `X_G`.

For the whole-line mode `F` (O8) with `φ(r) = F(log r)` and `h(r) = κ_c(r²)φ(r)`
(`ComplexODEC.modeVort`), write `s = r²`, `t = log r`. Then for `r > 0`
`Dh = F(t)(4κ' + 4sκ'' + sκ' + 2κ + κ²) + F'(t)(4κ' + κ/2)` (`oscillatorD_modeVort`), where the
singular terms cancel because `F'' - 4F = sκF` (the Rayleigh equation, tex eq. `st18-t00043`).
With `|F|, |F'|` bounded (O8) and `|κ|, |κ'|, |κ''| ≤ C(1 + s)e^{-s/4}` (explicit quotient
rule, `|e^{-s/4} - c| ≥ |Im c|`), `|Dh| ≤ C(1 + r²)²e^{-r²/4}`, so `|Dh|²G⁻¹r` is integrable.

Main declarations (namespace `UnforcedLeray.Cons.C01.Osc`): `kappa1`, `kappa2` (the first two
derivatives of `κ_c`), `hasDerivAt_kappa`, `hasDerivAt_kappa1`, `hasDerivAt_modeVort`,
`oscillatorD_modeVort`, `norm_Dform_le`, **`memXG_oscillatorD_modeVort`**.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Cons.C01.Osc

open UnforcedLeray.ComplexODEC Blueprint.Planar

/-! ## The pieces of `κ_c = N/D` and their derivatives -/

/-- Numerator `N(s) = (s/4 - 2)e^{-s/4}` of `κ_c`. -/
def Nk (s : ℝ) : ℂ := (((s / 4 - 2) * Real.exp (-(s / 4)) : ℝ) : ℂ)
/-- `N'(s)`. -/
def Nk1 (s : ℝ) : ℂ := (((3 - s / 4) / 4 * Real.exp (-(s / 4)) : ℝ) : ℂ)
/-- `N''(s)`. -/
def Nk2 (s : ℝ) : ℂ := ((-(4 - s / 4) / 16 * Real.exp (-(s / 4)) : ℝ) : ℂ)
/-- Denominator `D(s) = e^{-s/4} - c` of `κ_c`. -/
def Dk (c : ℂ) (s : ℝ) : ℂ := (Real.exp (-(s / 4)) : ℂ) - c
/-- `D'(s)`. -/
def Dk1 (s : ℝ) : ℂ := ((-(1 / 4) * Real.exp (-(s / 4)) : ℝ) : ℂ)
/-- `D''(s)`. -/
def Dk2 (s : ℝ) : ℂ := ((1 / 16 * Real.exp (-(s / 4)) : ℝ) : ℂ)

/-- `P = N'D - ND'`, the numerator of `κ' = P/D²`. -/
def Pk (c : ℂ) (s : ℝ) : ℂ := Nk1 s * Dk c s - Nk s * Dk1 s
/-- `P'`. -/
def Pk1 (c : ℂ) (s : ℝ) : ℂ :=
  Nk2 s * Dk c s + Nk1 s * Dk1 s - (Nk1 s * Dk1 s + Nk s * Dk2 s)
/-- `(D²)' = 2DD'`. -/
def Qk1 (c : ℂ) (s : ℝ) : ℂ := 2 * Dk c s * Dk1 s

/-- `κ_c'`. -/
def kappa1 (c : ℂ) (s : ℝ) : ℂ := Pk c s / Dk c s ^ 2
/-- `κ_c''`. -/
def kappa2 (c : ℂ) (s : ℝ) : ℂ :=
  (Pk1 c s * Dk c s ^ 2 - Pk c s * Qk1 c s) / (Dk c s ^ 2) ^ 2

theorem Dk_ne {c : ℂ} (hc : c.im ≠ 0) (s : ℝ) : Dk c s ≠ 0 := ofReal_sub_ne_zero hc _

theorem hasDerivAt_exp_quarter (s : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(s / 4))) (Real.exp (-(s / 4)) * (-(1 / 4))) s := by
  have h1 : HasDerivAt (fun x : ℝ => -(x / 4)) (-(1 / 4)) s :=
    ((hasDerivAt_id' (x := s)).div_const 4).fun_neg
  exact h1.exp

theorem hasDerivAt_Nk (s : ℝ) : HasDerivAt Nk (Nk1 s) s := by
  have h1 : HasDerivAt (fun s : ℝ => s / 4 - 2) (1 / 4) s :=
    ((hasDerivAt_id' (x := s)).div_const 4).sub_const 2
  have h : HasDerivAt (fun s : ℝ => (s / 4 - 2) * Real.exp (-(s / 4)))
      ((3 - s / 4) / 4 * Real.exp (-(s / 4))) s :=
    (h1.fun_mul (hasDerivAt_exp_quarter s)).congr_deriv (by ring)
  exact h.ofReal_comp

theorem hasDerivAt_Nk1 (s : ℝ) : HasDerivAt Nk1 (Nk2 s) s := by
  have h1 : HasDerivAt (fun s : ℝ => (3 - s / 4) / 4) (-(1 / 4) / 4) s :=
    (((hasDerivAt_id' (x := s)).div_const 4).const_sub 3).div_const 4
  have h : HasDerivAt (fun s : ℝ => (3 - s / 4) / 4 * Real.exp (-(s / 4)))
      (-(4 - s / 4) / 16 * Real.exp (-(s / 4))) s :=
    (h1.fun_mul (hasDerivAt_exp_quarter s)).congr_deriv (by ring)
  exact h.ofReal_comp

theorem hasDerivAt_Dk (c : ℂ) (s : ℝ) : HasDerivAt (Dk c) (Dk1 s) s := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (-(s / 4))) (-(1 / 4) * Real.exp (-(s / 4))) s :=
    (hasDerivAt_exp_quarter s).congr_deriv (by ring)
  exact h.ofReal_comp.sub_const c

theorem hasDerivAt_Dk1 (s : ℝ) : HasDerivAt Dk1 (Dk2 s) s := by
  have h : HasDerivAt (fun s : ℝ => -(1 / 4) * Real.exp (-(s / 4)))
      (1 / 16 * Real.exp (-(s / 4))) s :=
    ((hasDerivAt_exp_quarter s).const_mul (-(1 / 4))).congr_deriv (by ring)
  exact h.ofReal_comp

theorem hasDerivAt_Pk (c : ℂ) (s : ℝ) : HasDerivAt (Pk c) (Pk1 c s) s :=
  ((hasDerivAt_Nk1 s).fun_mul (hasDerivAt_Dk c s)).fun_sub
    ((hasDerivAt_Nk s).fun_mul (hasDerivAt_Dk1 s))

theorem hasDerivAt_Dk_sq (c : ℂ) (s : ℝ) :
    HasDerivAt (fun s => Dk c s ^ 2) (Qk1 c s) s := by
  have h := (hasDerivAt_Dk c s).fun_mul (hasDerivAt_Dk c s)
  have e : (fun s => Dk c s ^ 2) = fun s => Dk c s * Dk c s := funext fun s => sq _
  rw [e]
  refine h.congr_deriv ?_
  rw [Qk1]
  ring

/-- `κ_c = N/D`. -/
theorem kappa_eq (c : ℂ) : kappa c = fun s => Nk s / Dk c s := rfl

/-- `κ_c' = kappa1`. -/
theorem hasDerivAt_kappa {c : ℂ} (hc : c.im ≠ 0) (s : ℝ) :
    HasDerivAt (kappa c) (kappa1 c s) s := by
  rw [kappa_eq]
  exact (hasDerivAt_Nk s).fun_div (hasDerivAt_Dk c s) (Dk_ne hc s)

/-- `κ_c'' = kappa2`. -/
theorem hasDerivAt_kappa1 {c : ℂ} (hc : c.im ≠ 0) (s : ℝ) :
    HasDerivAt (kappa1 c) (kappa2 c s) s :=
  (hasDerivAt_Pk c s).fun_div (hasDerivAt_Dk_sq c s) (pow_ne_zero 2 (Dk_ne hc s))

theorem continuous_Nk : Continuous Nk := by unfold Nk; fun_prop
theorem continuous_Nk1 : Continuous Nk1 := by unfold Nk1; fun_prop
theorem continuous_Nk2 : Continuous Nk2 := by unfold Nk2; fun_prop
theorem continuous_Dk (c : ℂ) : Continuous (Dk c) := by unfold Dk; fun_prop
theorem continuous_Dk1 : Continuous Dk1 := by unfold Dk1; fun_prop
theorem continuous_Dk2 : Continuous Dk2 := by unfold Dk2; fun_prop

theorem continuous_kappa1 {c : ℂ} (hc : c.im ≠ 0) : Continuous (kappa1 c) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_kappa1 hc s).continuousAt

theorem continuous_kappa {c : ℂ} (hc : c.im ≠ 0) : Continuous (kappa c) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_kappa hc s).continuousAt

theorem continuous_kappa2 {c : ℂ} (hc : c.im ≠ 0) : Continuous (kappa2 c) := by
  have hP : Continuous (Pk c) := (continuous_Nk1.mul (continuous_Dk c)).sub
    (continuous_Nk.mul continuous_Dk1)
  have hP1 : Continuous (Pk1 c) := ((continuous_Nk2.mul (continuous_Dk c)).add
    (continuous_Nk1.mul continuous_Dk1)).sub ((continuous_Nk1.mul continuous_Dk1).add
    (continuous_Nk.mul continuous_Dk2))
  have hQ1 : Continuous (Qk1 c) := (continuous_const.mul (continuous_Dk c)).mul continuous_Dk1
  have hD := continuous_Dk c
  exact ((hP1.mul (hD.pow 2)).sub (hP.mul hQ1)).div ((hD.pow 2).pow 2)
    fun s => pow_ne_zero 2 (pow_ne_zero 2 (Dk_ne hc s))

/-! ## Bounds for `s ≥ 0` -/

section Bounds

variable {s : ℝ}

theorem exp_quarter_le_one (hs : 0 ≤ s) : Real.exp (-(s / 4)) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by linarith)

/-- The common Gaussian bound `B(s) = 4(1 + s)e^{-s/4}`. -/
def gB (s : ℝ) : ℝ := 4 * (1 + s) * Real.exp (-(s / 4))

theorem gB_nonneg (hs : 0 ≤ s) : 0 ≤ gB s := by unfold gB; positivity

theorem norm_Nk_le (hs : 0 ≤ s) : ‖Nk s‖ ≤ gB s := by
  rw [Nk, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), gB]
  gcongr
  rw [abs_le]; constructor <;> linarith

theorem norm_Nk1_le (hs : 0 ≤ s) : ‖Nk1 s‖ ≤ gB s := by
  rw [Nk1, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), gB]
  gcongr
  rw [abs_le]; constructor <;> linarith

theorem norm_Nk2_le (hs : 0 ≤ s) : ‖Nk2 s‖ ≤ gB s := by
  rw [Nk2, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), gB]
  gcongr
  rw [abs_le]; constructor <;> linarith

theorem norm_Dk1_le (hs : 0 ≤ s) : ‖Dk1 s‖ ≤ 1 := by
  rw [Dk1, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := exp_quarter_le_one hs
  norm_num
  linarith

theorem norm_Dk2_le (hs : 0 ≤ s) : ‖Dk2 s‖ ≤ 1 := by
  rw [Dk2, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := exp_quarter_le_one hs
  norm_num
  linarith

theorem norm_Dk_le (c : ℂ) (hs : 0 ≤ s) : ‖Dk c s‖ ≤ 1 + ‖c‖ := by
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  linarith [exp_quarter_le_one hs]

theorem le_norm_Dk (c : ℂ) (s : ℝ) : |c.im| ≤ ‖Dk c s‖ := abs_im_le_norm_ofReal_sub c _

variable {c : ℂ}

theorem norm_kappa_le_gB (hc : c.im ≠ 0) (hs : 0 ≤ s) :
    ‖kappa c s‖ ≤ 1 / |c.im| * gB s := by
  have hm : 0 < |c.im| := abs_pos.mpr hc
  rw [kappa_eq, norm_div, one_div_mul_eq_div]
  exact div_le_div₀ (gB_nonneg hs) (norm_Nk_le hs) hm (le_norm_Dk c s)

theorem norm_Pk_le (hs : 0 ≤ s) : ‖Pk c s‖ ≤ (1 + ‖c‖ + 1) * gB s := by
  have hB := gB_nonneg hs
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖Nk1 s‖ * ‖Dk c s‖ ≤ gB s * (1 + ‖c‖) :=
    mul_le_mul (norm_Nk1_le hs) (norm_Dk_le c hs) (norm_nonneg _) hB
  have h2 : ‖Nk s‖ * ‖Dk1 s‖ ≤ gB s * 1 :=
    mul_le_mul (norm_Nk_le hs) (norm_Dk1_le hs) (norm_nonneg _) hB
  nlinarith

theorem norm_Pk1_le (hs : 0 ≤ s) : ‖Pk1 c s‖ ≤ (1 + ‖c‖ + 3) * gB s := by
  have hB := gB_nonneg hs
  have h1 : ‖Nk2 s * Dk c s‖ ≤ gB s * (1 + ‖c‖) := by
    rw [norm_mul]; exact mul_le_mul (norm_Nk2_le hs) (norm_Dk_le c hs) (norm_nonneg _) hB
  have h2 : ‖Nk1 s * Dk1 s‖ ≤ gB s * 1 := by
    rw [norm_mul]; exact mul_le_mul (norm_Nk1_le hs) (norm_Dk1_le hs) (norm_nonneg _) hB
  have h3 : ‖Nk s * Dk2 s‖ ≤ gB s * 1 := by
    rw [norm_mul]; exact mul_le_mul (norm_Nk_le hs) (norm_Dk2_le hs) (norm_nonneg _) hB
  have e1 := norm_sub_le (Nk2 s * Dk c s + Nk1 s * Dk1 s) (Nk1 s * Dk1 s + Nk s * Dk2 s)
  have e2 := norm_add_le (Nk2 s * Dk c s) (Nk1 s * Dk1 s)
  have e3 := norm_add_le (Nk1 s * Dk1 s) (Nk s * Dk2 s)
  rw [Pk1]
  nlinarith

theorem norm_kappa1_le_gB (hc : c.im ≠ 0) (hs : 0 ≤ s) :
    ‖kappa1 c s‖ ≤ (1 + ‖c‖ + 1) / |c.im| ^ 2 * gB s := by
  have hm : 0 < |c.im| := abs_pos.mpr hc
  rw [kappa1, norm_div, norm_pow, div_mul_eq_mul_div]
  refine div_le_div₀ (by have := gB_nonneg hs; positivity) ?_ (by positivity)
    (pow_le_pow_left₀ hm.le (le_norm_Dk c s) 2)
  linarith [norm_Pk_le (c := c) hs]

theorem norm_kappa2_le_gB (hc : c.im ≠ 0) (hs : 0 ≤ s) :
    ‖kappa2 c s‖ ≤ ((1 + ‖c‖ + 3) * (1 + ‖c‖) ^ 2 + (1 + ‖c‖ + 1) * (2 * (1 + ‖c‖))) /
      |c.im| ^ 4 * gB s := by
  have hm : 0 < |c.im| := abs_pos.mpr hc
  have hB := gB_nonneg hs
  set L : ℝ := 1 + ‖c‖ with hL
  have hL0 : 0 ≤ L := by positivity
  have hD := norm_Dk_le c hs
  have hQ : ‖Dk c s ^ 2‖ ≤ L ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hQ1 : ‖Qk1 c s‖ ≤ 2 * L := by
    rw [Qk1, norm_mul, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    have := norm_Dk1_le hs
    have := norm_nonneg (Dk c s)
    have := norm_nonneg (Dk1 s)
    nlinarith
  have hnum : ‖Pk1 c s * Dk c s ^ 2 - Pk c s * Qk1 c s‖ ≤
      ((L + 3) * L ^ 2 + (L + 1) * (2 * L)) * gB s := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖Pk1 c s‖ * ‖Dk c s ^ 2‖ ≤ (L + 3) * gB s * L ^ 2 :=
      mul_le_mul (norm_Pk1_le hs) hQ (norm_nonneg _) (by positivity)
    have h2 : ‖Pk c s‖ * ‖Qk1 c s‖ ≤ (L + 1) * gB s * (2 * L) :=
      mul_le_mul (norm_Pk_le hs) hQ1 (norm_nonneg _) (by positivity)
    nlinarith
  rw [kappa2, norm_div, norm_pow, norm_pow, div_mul_eq_mul_div]
  have hden : |c.im| ^ 4 ≤ (‖Dk c s‖ ^ 2) ^ 2 := by
    rw [← pow_mul]
    exact pow_le_pow_left₀ hm.le (le_norm_Dk c s) 4
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

end Bounds

/-! ## Derivatives of the eigenvorticity -/

variable {c : ℂ} {F : ℝ → ℂ}

/-- `h'(r) = 2rκ'(r²)F(log r) + κ(r²)F'(log r)/r`. -/
def h1 (c : ℂ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  2 * (r : ℂ) * kappa1 c (r ^ 2) * F (Real.log r) + kappa c (r ^ 2) * deriv F (Real.log r) / (r : ℂ)

/-- `h''(r)`. -/
def h2 (c : ℂ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  2 * kappa1 c (r ^ 2) * F (Real.log r) + 4 * (r : ℂ) ^ 2 * kappa2 c (r ^ 2) * F (Real.log r) +
    4 * kappa1 c (r ^ 2) * deriv F (Real.log r) +
    kappa c (r ^ 2) * deriv (deriv F) (Real.log r) / (r : ℂ) ^ 2 -
    kappa c (r ^ 2) * deriv F (Real.log r) / (r : ℂ) ^ 2

theorem hasDerivAt_comp_sq {g g' : ℝ → ℂ} (hg : ∀ s, HasDerivAt g (g' s) s) (r : ℝ) :
    HasDerivAt (fun r : ℝ => g (r ^ 2)) (g' (r ^ 2) * (2 * (r : ℂ))) r := by
  have h := (hg (r ^ 2)).scomp r (hasDerivAt_pow 2 r)
  refine h.congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

theorem hasDerivAt_comp_log {g : ℝ → ℂ} (hg : Differentiable ℝ g) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => g (Real.log r)) (deriv g (Real.log r) / (r : ℂ)) r := by
  have h := (hg (Real.log r)).hasDerivAt.scomp r (Real.hasDerivAt_log hr.ne')
  refine h.congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

theorem hasDerivAt_ofReal' (r : ℝ) : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := by
  have h := (hasDerivAt_id' (x := r)).ofReal_comp
  simpa using h

theorem hasDerivAt_modeVort (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (modeVort c F) (h1 c F r) r := by
  have hc := hF.im_ne_zero
  have hK := hasDerivAt_comp_sq (hasDerivAt_kappa hc) r
  have hΦ := hasDerivAt_comp_log hF.differentiable hr
  have h := hK.fun_mul hΦ
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine h.congr_deriv ?_
  rw [h1]
  field_simp

theorem hasDerivAt_h1 (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (h1 c F) (h2 c F r) r := by
  have hc := hF.im_ne_zero
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hR := hasDerivAt_ofReal' r
  have hK := hasDerivAt_comp_sq (hasDerivAt_kappa hc) r
  have hK1 := hasDerivAt_comp_sq (hasDerivAt_kappa1 hc) r
  have hΦ := hasDerivAt_comp_log hF.differentiable hr
  have hΦ' := hasDerivAt_comp_log hF.differentiable_deriv hr
  have hA := ((hR.const_mul 2).fun_mul hK1).fun_mul hΦ
  have hB := (hK.fun_mul hΦ').fun_div hR hr'
  have h := hA.fun_add hB
  refine h.congr_deriv ?_
  rw [h2]
  field_simp
  ring

theorem deriv_modeVort (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    deriv (modeVort c F) r = h1 c F r := (hasDerivAt_modeVort hF hr).deriv

theorem deriv_deriv_modeVort (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (modeVort c F)) r = h2 c F r := by
  have heq : deriv (modeVort c F) =ᶠ[𝓝 r] h1 c F :=
    Filter.eventually_of_mem (Ioi_mem_nhds hr) fun y hy => deriv_modeVort hF hy
  rw [heq.deriv_eq]
  exact (hasDerivAt_h1 hF hr).deriv

/-- The closed form of `Dh` (no singular terms). -/
def Dform (c : ℂ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  F (Real.log r) * (4 * kappa1 c (r ^ 2) + 4 * (r : ℂ) ^ 2 * kappa2 c (r ^ 2) +
      (r : ℂ) ^ 2 * kappa1 c (r ^ 2) + 2 * kappa c (r ^ 2) + kappa c (r ^ 2) ^ 2) +
    deriv F (Real.log r) * (4 * kappa1 c (r ^ 2) + kappa c (r ^ 2) / 2)

/-- **`Dh` in closed form** for `r > 0`, from the Rayleigh equation `F'' = (4 + sκ)F`. -/
theorem oscillatorD_modeVort (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    oscillatorD (modeVort c F) r = Dform c F r := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold oscillatorD
  rw [deriv_deriv_modeVort hF hr, deriv_modeVort hF hr]
  simp only [h1, h2, Dform, modeVort, modeRadial]
  rw [hF.deriv_deriv_eq, logPot_eq, Real.exp_log hr]
  push_cast
  field_simp
  ring

theorem continuousOn_Dform (hF : WholeLineData c F) : ContinuousOn (Dform c F) (Ioi 0) := by
  have hc := hF.im_ne_zero
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono fun r hr => ne_of_gt hr
  have hFl : ContinuousOn (fun r => F (Real.log r)) (Ioi 0) :=
    hF.smooth.continuous.comp_continuousOn hlog
  have hF'l : ContinuousOn (fun r => deriv F (Real.log r)) (Ioi 0) :=
    hF.continuous_deriv.comp_continuousOn hlog
  have hk : Continuous fun r : ℝ => kappa c (r ^ 2) := (continuous_kappa hc).comp (continuous_pow 2)
  have hk1 : Continuous fun r : ℝ => kappa1 c (r ^ 2) :=
    (continuous_kappa1 hc).comp (continuous_pow 2)
  have hk2 : Continuous fun r : ℝ => kappa2 c (r ^ 2) :=
    (continuous_kappa2 hc).comp (continuous_pow 2)
  have hR : Continuous fun r : ℝ => (r : ℂ) := Complex.continuous_ofReal
  unfold Dform
  refine (hFl.mul ?_).add (hF'l.mul ?_)
  · exact (((((continuous_const.mul hk1).add ((continuous_const.mul (hR.pow 2)).mul hk2)).add
      ((hR.pow 2).mul hk1)).add (continuous_const.mul hk)).add (hk.pow 2)).continuousOn
  · exact ((continuous_const.mul hk1).add (hk.div_const 2)).continuousOn

theorem norm_add5_le (a b c d e : ℂ) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have h1 := norm_add_le (a + b + c + d) e
  have h2 := norm_add_le (a + b + c) d
  have h3 := norm_add_le (a + b) c
  have h4 := norm_add_le a b
  linarith

/-- **The Gaussian bound** `|Dh(r)| ≤ C(1 + r²)²e^{-r²/4}` for `r > 0`. -/
theorem norm_Dform_le (hF : WholeLineData c F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      ‖Dform c F r‖ ≤ C * ((1 + r ^ 2) ^ 2 * Real.exp (-(r ^ 2 / 4))) := by
  have hc := hF.im_ne_zero
  have hm : 0 < |c.im| := abs_pos.mpr hc
  obtain ⟨M, hM0, hM⟩ := hF.exists_bound
  obtain ⟨M', hM'0, hM'⟩ := hF.exists_bound_deriv
  set K0 : ℝ := 1 / |c.im|
  set K1 : ℝ := (1 + ‖c‖ + 1) / |c.im| ^ 2
  set K2 : ℝ := ((1 + ‖c‖ + 3) * (1 + ‖c‖) ^ 2 + (1 + ‖c‖ + 1) * (2 * (1 + ‖c‖))) / |c.im| ^ 4
  have hK0 : 0 ≤ K0 := by positivity
  have hK1 : 0 ≤ K1 := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  set Ct : ℝ := M * (4 * K1 + 4 * K2 + K1 + 2 * K0 + 4 * K0 ^ 2) + M' * (4 * K1 + K0 / 2)
  refine ⟨4 * Ct, by positivity, fun r hr => ?_⟩
  have hs0 : 0 ≤ r ^ 2 := by positivity
  have hB0 := gB_nonneg hs0
  have he1 := exp_quarter_le_one hs0
  have hBle : gB (r ^ 2) ≤ 4 * (1 + r ^ 2) := by
    unfold gB
    have h4 : 0 ≤ 4 * (1 + r ^ 2) := by positivity
    calc 4 * (1 + r ^ 2) * Real.exp (-(r ^ 2 / 4)) ≤ 4 * (1 + r ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left he1 h4
      _ = 4 * (1 + r ^ 2) := mul_one _
  have hB1 : gB (r ^ 2) ≤ (1 + r ^ 2) * gB (r ^ 2) :=
    le_mul_of_one_le_left hB0 (by linarith)
  have hk := norm_kappa_le_gB hc hs0
  have hk1 := norm_kappa1_le_gB hc hs0
  have hk2 := norm_kappa2_le_gB hc hs0
  have hr1 : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hPB : 0 ≤ (1 + r ^ 2) * gB (r ^ 2) := by positivity
  have t1 : ‖kappa1 c (r ^ 2)‖ ≤ K1 * ((1 + r ^ 2) * gB (r ^ 2)) :=
    hk1.trans (mul_le_mul_of_nonneg_left hB1 hK1)
  have t4 : ‖kappa c (r ^ 2)‖ ≤ K0 * ((1 + r ^ 2) * gB (r ^ 2)) :=
    hk.trans (mul_le_mul_of_nonneg_left hB1 hK0)
  have t2 : r ^ 2 * ‖kappa2 c (r ^ 2)‖ ≤ K2 * ((1 + r ^ 2) * gB (r ^ 2)) := by
    calc r ^ 2 * ‖kappa2 c (r ^ 2)‖ ≤ r ^ 2 * (K2 * gB (r ^ 2)) :=
          mul_le_mul_of_nonneg_left hk2 hs0
      _ ≤ (1 + r ^ 2) * (K2 * gB (r ^ 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hK2 hB0)
      _ = K2 * ((1 + r ^ 2) * gB (r ^ 2)) := by ring
  have t3 : r ^ 2 * ‖kappa1 c (r ^ 2)‖ ≤ K1 * ((1 + r ^ 2) * gB (r ^ 2)) := by
    calc r ^ 2 * ‖kappa1 c (r ^ 2)‖ ≤ r ^ 2 * (K1 * gB (r ^ 2)) :=
          mul_le_mul_of_nonneg_left hk1 hs0
      _ ≤ (1 + r ^ 2) * (K1 * gB (r ^ 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hK1 hB0)
      _ = K1 * ((1 + r ^ 2) * gB (r ^ 2)) := by ring
  have t5 : ‖kappa c (r ^ 2)‖ ^ 2 ≤ 4 * K0 ^ 2 * ((1 + r ^ 2) * gB (r ^ 2)) := by
    calc ‖kappa c (r ^ 2)‖ ^ 2 ≤ (K0 * gB (r ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hk 2
      _ = K0 ^ 2 * (gB (r ^ 2) * gB (r ^ 2)) := by ring
      _ ≤ K0 ^ 2 * (4 * (1 + r ^ 2) * gB (r ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBle hB0) (sq_nonneg _)
      _ = 4 * K0 ^ 2 * ((1 + r ^ 2) * gB (r ^ 2)) := by ring
  have hX : ‖4 * kappa1 c (r ^ 2) + 4 * (r : ℂ) ^ 2 * kappa2 c (r ^ 2) +
      (r : ℂ) ^ 2 * kappa1 c (r ^ 2) + 2 * kappa c (r ^ 2) + kappa c (r ^ 2) ^ 2‖ ≤
      (4 * K1 + 4 * K2 + K1 + 2 * K0 + 4 * K0 ^ 2) * ((1 + r ^ 2) * gB (r ^ 2)) := by
    have e : ‖4 * kappa1 c (r ^ 2) + 4 * (r : ℂ) ^ 2 * kappa2 c (r ^ 2) +
        (r : ℂ) ^ 2 * kappa1 c (r ^ 2) + 2 * kappa c (r ^ 2) + kappa c (r ^ 2) ^ 2‖ ≤
        4 * ‖kappa1 c (r ^ 2)‖ + 4 * (r ^ 2 * ‖kappa2 c (r ^ 2)‖) +
          r ^ 2 * ‖kappa1 c (r ^ 2)‖ + 2 * ‖kappa c (r ^ 2)‖ + ‖kappa c (r ^ 2)‖ ^ 2 := by
      refine (norm_add5_le _ _ _ _ _).trans (le_of_eq ?_)
      simp only [norm_mul, norm_pow, hr1]
      norm_num
      ring
    refine e.trans ?_
    linarith
  have hY : ‖4 * kappa1 c (r ^ 2) + kappa c (r ^ 2) / 2‖ ≤
      (4 * K1 + K0 / 2) * ((1 + r ^ 2) * gB (r ^ 2)) := by
    have e : ‖4 * kappa1 c (r ^ 2) + kappa c (r ^ 2) / 2‖ ≤
        4 * ‖kappa1 c (r ^ 2)‖ + ‖kappa c (r ^ 2)‖ / 2 := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      simp only [norm_mul, norm_div]
      norm_num
    refine e.trans ?_
    linarith
  calc ‖Dform c F r‖
      ≤ ‖F (Real.log r)‖ * ‖4 * kappa1 c (r ^ 2) + 4 * (r : ℂ) ^ 2 * kappa2 c (r ^ 2) +
          (r : ℂ) ^ 2 * kappa1 c (r ^ 2) + 2 * kappa c (r ^ 2) + kappa c (r ^ 2) ^ 2‖ +
        ‖deriv F (Real.log r)‖ * ‖4 * kappa1 c (r ^ 2) + kappa c (r ^ 2) / 2‖ := by
        unfold Dform
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul]
    _ ≤ M * ((4 * K1 + 4 * K2 + K1 + 2 * K0 + 4 * K0 ^ 2) * ((1 + r ^ 2) * gB (r ^ 2))) +
        M' * ((4 * K1 + K0 / 2) * ((1 + r ^ 2) * gB (r ^ 2))) :=
        add_le_add (mul_le_mul (hM _) hX (norm_nonneg _) hM0)
          (mul_le_mul (hM' _) hY (norm_nonneg _) hM'0)
    _ = 4 * Ct * ((1 + r ^ 2) ^ 2 * Real.exp (-(r ^ 2 / 4))) := by
        unfold gB
        ring

/-- **G3a, the domain of `D`** (line 1516, unit B0095): `Dh ∈ X_G` for the eigenvorticity `h`
of a whole-line mode. -/
theorem memXG_oscillatorD_modeVort (hF : WholeLineData c F) :
    MemXG (oscillatorD (modeVort c F)) := by
  obtain ⟨C, hC0, hC⟩ := norm_Dform_le hF
  have hcont : ContinuousOn (oscillatorD (modeVort c F)) (Ioi 0) :=
    (continuousOn_Dform hF).congr fun r hr => oscillatorD_modeVort hF hr
  have hw : Continuous gaussianWeightInv := by unfold gaussianWeightInv; fun_prop
  refine ⟨hcont.aestronglyMeasurable measurableSet_Ioi, ?_⟩
  have hint : IntegrableOn (fun r : ℝ => 4 * Real.pi * C ^ 2 *
      (r ^ 1 * Real.exp (-(r ^ 2 / 4)) + 4 * (r ^ 3 * Real.exp (-(r ^ 2 / 4))) +
        6 * (r ^ 5 * Real.exp (-(r ^ 2 / 4))) + 4 * (r ^ 7 * Real.exp (-(r ^ 2 / 4))) +
        r ^ 9 * Real.exp (-(r ^ 2 / 4)))) (Ioi 0) :=
    (((((integrableOn_pow_mul_gauss' 1).add ((integrableOn_pow_mul_gauss' 3).const_mul 4)).add
      ((integrableOn_pow_mul_gauss' 5).const_mul 6)).add
        ((integrableOn_pow_mul_gauss' 7).const_mul 4)).add
          (integrableOn_pow_mul_gauss' 9)).const_mul _
  refine hint.mono' ?_ ?_
  · exact (((hcont.norm.pow 2).mul hw.continuousOn).mul continuousOn_id).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hwr : 0 ≤ gaussianWeightInv r := by unfold gaussianWeightInv; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), oscillatorD_modeVort hF hr0]
    have hb := hC r hr0
    have hb2 : ‖Dform c F r‖ ^ 2 ≤ (C * ((1 + r ^ 2) ^ 2 * Real.exp (-(r ^ 2 / 4)))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have he : Real.exp (-(r ^ 2 / 4)) ^ 2 * Real.exp (r ^ 2 / 4) = Real.exp (-(r ^ 2 / 4)) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    calc ‖Dform c F r‖ ^ 2 * gaussianWeightInv r * r
        ≤ (C * ((1 + r ^ 2) ^ 2 * Real.exp (-(r ^ 2 / 4)))) ^ 2 * gaussianWeightInv r * r := by
          gcongr
      _ = 4 * Real.pi * C ^ 2 * ((1 + r ^ 2) ^ 4 * r) *
            (Real.exp (-(r ^ 2 / 4)) ^ 2 * Real.exp (r ^ 2 / 4)) := by
          unfold gaussianWeightInv
          ring
      _ = _ := by
          rw [he]
          ring

end UnforcedLeray.Cons.C01.Osc
