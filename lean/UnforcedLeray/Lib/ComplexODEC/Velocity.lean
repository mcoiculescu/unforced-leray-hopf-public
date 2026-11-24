import UnforcedLeray.Lib.ComplexODEC.Assembly
import UnforcedLeray.Lib.SpecialFunctions.GammaTails

/-!
# The streamfunction of the mode and its square-integrable velocity (INF18 O15 input)

Scoping note `scoping/INF10-INF12-INF18-Planar.md` §5 target O15 ("`Kq ∈ L²`"); manuscript
`paper/main.tex` lines 977 ("its velocity is smooth and square integrable") and 1181 (unit
B0056: `∇^⊥(φ e^{2iϑ})` is `O(r)` at zero and `O(r^{-3})` at infinity, hence in `L²`).

The streamfunction is `Ψ = φ(r) e^{2iϑ} = ofProfile 2 φ`; by the matching,
`Ψ(y) = β₀ y² b(|y|²)` (`modeStream_eq`), so `Ψ` is `C^∞`. Its gradient satisfies
`‖∇Ψ(y)‖ ≤ 2|y| |B(|y|²)| + 2|y|³ |B'(|y|²)|` with `B = β₀ b`, and `b = O(s^{-2})`,
`b' = O(s^{-3})` (from `r²φ → -𝔐/4` and `s³ b'(s) = ¼ ∫₀ˢ σ² κ b`), so
`‖∇Ψ(y)‖ ≤ K (1 + |y|)^{-3}`, which is square integrable on `ℝ²`.

The identification of `∇^⊥Ψ` with the Biot–Savart velocity `Kq` is target P8 and is not
proved here.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.ComplexODEC

open UnforcedLeray.GaussianVortex UnforcedLeray.Rayleigh UnforcedLeray.Sturm

variable {c : ℂ} {F : ℝ → ℂ}

/-- The streamfunction `Ψ = φ(r) e^{2iϑ}` of the mode on `ℂ = ℝ²` (tex line 1181). -/
def modeStream (F : ℝ → ℂ) : ℂ → ℂ := Planar.NUE.Ang.ofProfile 2 (modeRadial F)

theorem modeStream_eq {β₀ : ℂ} (hβ : ∀ t, F t = β₀ * regLog c t) (y : ℂ) :
    modeStream F y = y ^ 2 * (β₀ * regB c (‖y‖ ^ 2)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [modeStream, Planar.NUE.Ang.ofProfile, Planar.NUE.Ang.angPhase]
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hr' : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [modeStream, Planar.NUE.Ang.ofProfile, Planar.NUE.Ang.angPhase,
    modeRadial_eq hβ hr]
  rw [zpow_two, div_mul_div_comm]
  push_cast
  field_simp

theorem contDiff_modeStream (hF : WholeLineData c F) : ContDiff ℝ ∞ (modeStream F) := by
  obtain ⟨β₀, -, hβ⟩ := exists_mode_eq_regLog hF
  rw [show modeStream F = fun y => y ^ 2 * (β₀ * regB c (‖y‖ ^ 2)) from
    funext (modeStream_eq (fun t => (hβ t).1))]
  exact Planar.contDiff_angularTwo (contDiff_const.mul (contDiff_regB hF.im_ne_zero))

/-! ### The gradient of an angular-two function -/

/-- `‖D(y² B(|y|²))‖ ≤ 2|y| |B| + 2|y|³ |B'|`. -/
theorem norm_fderiv_angularTwo_le {B : ℝ → ℂ} (hB : Differentiable ℝ B) (y : ℂ) :
    ‖fderiv ℝ (fun y : ℂ => y ^ 2 * B (‖y‖ ^ 2)) y‖ ≤
      2 * ‖y‖ * ‖B (‖y‖ ^ 2)‖ + 2 * ‖y‖ ^ 3 * ‖deriv B (‖y‖ ^ 2)‖ := by
  have hP : HasFDerivAt (fun y : ℂ => y * y)
      (y • ContinuousLinearMap.id ℝ ℂ + y • ContinuousLinearMap.id ℝ ℂ) y :=
    (hasFDerivAt_id y).mul (hasFDerivAt_id y)
  have hN := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hQ := ((hB (‖y‖ ^ 2)).hasDerivAt.hasFDerivAt).comp y hN
  have h := hP.mul hQ
  have e : (fun y : ℂ => y ^ 2 * B (‖y‖ ^ 2)) = (fun y : ℂ => y * y) * (B ∘ fun x => ‖x‖ ^ 2) := by
    funext x; simp [sq]
  rw [e, h.fderiv]
  have hP' : ‖y • ContinuousLinearMap.id ℝ ℂ + y • ContinuousLinearMap.id ℝ ℂ‖ ≤ 2 * ‖y‖ := by
    refine (norm_add_le _ _).trans ?_
    have : ‖y • ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖y‖ := by
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
    linarith
  have hS : ‖(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv B (‖y‖ ^ 2)))‖ ≤
      ‖deriv B (‖y‖ ^ 2)‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun t => ?_
    simp [norm_smul, mul_comm]
  have hI : ‖(2 : ℕ) • innerSL ℝ y‖ ≤ 2 * ‖y‖ := by
    rw [two_nsmul]
    refine (norm_add_le _ _).trans ?_
    rw [innerSL_apply_norm]
    linarith
  have hQ' : ‖(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv B (‖y‖ ^ 2))).comp
      ((2 : ℕ) • innerSL ℝ y)‖ ≤ ‖deriv B (‖y‖ ^ 2)‖ * (2 * ‖y‖) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hS hI (norm_nonneg _) (norm_nonneg _))
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  simp only [Function.comp_apply]
  rw [norm_mul]
  calc ‖y‖ * ‖y‖ * ‖(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (deriv B (‖y‖ ^ 2))).comp ((2 : ℕ) • innerSL ℝ y)‖ +
        ‖B (‖y‖ ^ 2)‖ * ‖y • ContinuousLinearMap.id ℝ ℂ + y • ContinuousLinearMap.id ℝ ℂ‖
      ≤ ‖y‖ * ‖y‖ * (‖deriv B (‖y‖ ^ 2)‖ * (2 * ‖y‖)) + ‖B (‖y‖ ^ 2)‖ * (2 * ‖y‖) := by
        gcongr
    _ = 2 * ‖y‖ * ‖B (‖y‖ ^ 2)‖ + 2 * ‖y‖ ^ 3 * ‖deriv B (‖y‖ ^ 2)‖ := by ring

/-! ### Decay of `b` and `b'` -/

theorem exists_bound_sq_mul_modeRadial (hF : WholeLineData c F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ‖(r : ℂ) ^ 2 * modeRadial F r‖ ≤ C := by
  have hlim := tendsto_sq_mul_modeRadial hF
  set L := -(1 / 4) * modeQuadrupole c F
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hlim.norm.eventually (ge_mem_nhds
    (lt_add_one ‖L‖)))
  have hcont : ContinuousOn (fun r : ℝ => (r : ℂ) ^ 2 * modeRadial F r) (Icc 1 (max R 1)) :=
    ((Complex.continuous_ofReal.pow 2).continuousOn.mul (continuousOn_modeRadial hF)).mono
      fun r hr => lt_of_lt_of_le one_pos hr.1
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max |C₀| (‖L‖ + 1), le_trans (abs_nonneg _) (le_max_left _ _), fun r hr => ?_⟩
  rcases le_total r (max R 1) with h | h
  · exact ((hC₀ r ⟨hr, h⟩).trans (le_abs_self _)).trans (le_max_left _ _)
  · exact (hR r (le_trans (le_max_left _ _) h)).trans (le_max_right _ _)

/-- `‖b(s)‖ ≤ C (1 + s)^{-2}` on `s ≥ 0`. -/
theorem exists_decay_regB (hF : WholeLineData c F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 ≤ s → ‖regB c s‖ * (1 + s) ^ 2 ≤ C := by
  obtain ⟨β₀, hβ0, hβ⟩ := exists_mode_eq_regLog hF
  obtain ⟨Cφ, hCφ0, hCφ⟩ := exists_bound_sq_mul_modeRadial hF
  obtain ⟨Bb, hBb0, hBb⟩ := exists_bound_regB hF
  have hβpos : 0 < ‖β₀‖ := norm_pos_iff.mpr hβ0
  refine ⟨max (4 * Bb) (4 * Cφ / ‖β₀‖), le_trans (by positivity) (le_max_left _ _),
    fun s hs => ?_⟩
  rcases le_total s 1 with h1 | h1
  · refine le_trans ?_ (le_max_left _ _)
    have : (1 + s) ^ 2 ≤ 4 := by nlinarith
    calc ‖regB c s‖ * (1 + s) ^ 2 ≤ Bb * 4 :=
          mul_le_mul (hBb s hs) this (by positivity) hBb0
      _ = 4 * Bb := by ring
  · refine le_trans ?_ (le_max_right _ _)
    have hs0 : 0 < s := by linarith
    have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
    have hφ := modeRadial_eq (fun t => (hβ t).1) hr
    rw [hsq] at hφ
    have hb : regB c s = modeRadial F (Real.sqrt s) / (β₀ * (s : ℂ)) := by
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      rw [hφ]
      field_simp
    have h1' := hCφ (Real.sqrt s) (by rw [Real.one_le_sqrt]; exact h1)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hsq] at h1'
    rw [hb, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have h2 : (1 + s) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hβpos]
    calc ‖modeRadial F (Real.sqrt s)‖ * (1 + s) ^ 2 * ‖β₀‖
        ≤ ‖modeRadial F (Real.sqrt s)‖ * (4 * s ^ 2) * ‖β₀‖ := by gcongr
      _ = 4 * (s * ‖modeRadial F (Real.sqrt s)‖) * (‖β₀‖ * s) := by ring
      _ ≤ 4 * Cφ * (‖β₀‖ * s) := by gcongr

theorem avgPow_two_eq {g : ℝ → ℂ} {s : ℝ} (hs : 0 < s) :
    avgPow 2 g s = ((s ^ 3)⁻¹ : ℝ) • ∫ σ in (0 : ℝ)..s, (σ : ℂ) ^ 2 * g σ := by
  have hs' : s ≠ 0 := hs.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun σ : ℝ => (σ : ℂ) ^ 2 * g σ) hs'
  simp only [mul_zero, mul_one] at h
  unfold avgPow
  have e : ∀ u : ℝ, (u : ℂ) ^ 2 * g (s * u) = ((s ^ 2)⁻¹ : ℝ) • (((s * u : ℝ) : ℂ) ^ 2 * g (s * u)) :=
    fun u => by
      rw [Complex.real_smul]
      have : ((s : ℂ)) ≠ 0 := by exact_mod_cast hs'
      push_cast
      field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_smul, h, smul_smul]
  congr 1
  field_simp

theorem integrableOn_sq_mul_norm_kappa_regB (hF : WholeLineData c F) :
    IntegrableOn (fun σ : ℝ => σ ^ 2 * ‖kappa c σ * regB c σ‖) (Ioi 0) := by
  have hc := hF.im_ne_zero
  obtain ⟨Bb, hBb0, hBb⟩ := exists_bound_regB hF
  have hpos : 0 < |c.im| := abs_pos.mpr hc
  have hint := (Special.integrableOn_one_add_rpow_mul_exp_neg (M := 3) (c := 1 / 4)
    (by norm_num)).const_mul (2 * Bb / |c.im|)
  refine hint.mono' ?_ ?_
  · exact ((continuous_pow 2).mul ((contDiff_kappa hc).continuous.mul
      (contDiff_regB hc).continuous).norm).aestronglyMeasurable.restrict
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun σ hσ => ?_
    have hσ0 : (0 : ℝ) < σ := hσ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    have h1 := norm_kappa_le hc σ
    have h2 : |σ / 4 - 2| ≤ σ / 4 + 2 := by rw [abs_le]; constructor <;> linarith
    have h3 : σ ^ 2 * (σ / 4 + 2) ≤ 2 * (1 + σ) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith [sq_nonneg σ]
    have he : Real.exp (-(σ / 4)) = Real.exp (-(1 / 4 * σ)) := by ring_nf
    calc σ ^ 2 * (‖kappa c σ‖ * ‖regB c σ‖)
        ≤ σ ^ 2 * ((σ / 4 + 2) * Real.exp (-(σ / 4)) / |c.im| * Bb) := by
          gcongr
          · exact h1.trans (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le) hpos.le)
          · exact hBb σ hσ0.le
      _ = (σ ^ 2 * (σ / 4 + 2)) * Real.exp (-(1 / 4 * σ)) * (Bb / |c.im|) := by
          rw [he]; ring
      _ ≤ (2 * (1 + σ) ^ (3 : ℝ)) * Real.exp (-(1 / 4 * σ)) * (Bb / |c.im|) := by gcongr
      _ = 2 * Bb / |c.im| * ((1 + σ) ^ (3 : ℝ) * Real.exp (-(1 / 4 * σ))) := by ring

/-- `‖b'(s)‖ ≤ C (1 + s)^{-3}` on `s ≥ 0`. -/
theorem exists_decay_deriv_regB (hF : WholeLineData c F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 ≤ s → ‖deriv (regB c) s‖ * (1 + s) ^ 3 ≤ C := by
  have hc := hF.im_ne_zero
  obtain ⟨Bd, hBd0, hBd⟩ := exists_bound_deriv_regB hF
  have hint := integrableOn_sq_mul_norm_kappa_regB hF
  set K : ℝ := ∫ σ in Ioi (0 : ℝ), σ ^ 2 * ‖kappa c σ * regB c σ‖
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun σ hσ => by positivity
  refine ⟨max (8 * Bd) (2 * K), le_trans (by positivity) (le_max_left _ _), fun s hs => ?_⟩
  rcases le_total s 1 with h1 | h1
  · refine le_trans ?_ (le_max_left _ _)
    have : (1 + s) ^ 3 ≤ 8 := by
      have : 1 + s ≤ 2 := by linarith
      calc (1 + s) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) this 3
        _ = 8 := by norm_num
    calc ‖deriv (regB c) s‖ * (1 + s) ^ 3 ≤ Bd * 8 :=
          mul_le_mul (hBd s hs) this (by positivity) hBd0
      _ = 8 * Bd := by ring
  · refine le_trans ?_ (le_max_right _ _)
    have hs0 : 0 < s := by linarith
    have hd : deriv (regB c) s = avgPow 2 (fun σ => kappa c σ * regB c σ) s / 4 := by
      unfold regB
      rw [deriv_regSol (contDiff_kappa hc).continuous]
    rw [hd, avgPow_two_eq hs0, norm_div, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), Complex.norm_ofNat]
    have hI : ‖∫ σ in (0 : ℝ)..s, (σ : ℂ) ^ 2 * (kappa c σ * regB c σ)‖ ≤ K := by
      refine (intervalIntegral.norm_integral_le_integral_norm hs0.le).trans ?_
      rw [intervalIntegral.integral_of_le hs0.le]
      have e : ∀ σ : ℝ, 0 < σ → ‖(σ : ℂ) ^ 2 * (kappa c σ * regB c σ)‖ =
          σ ^ 2 * ‖kappa c σ * regB c σ‖ := fun σ hσ => by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
      rw [setIntegral_congr_fun measurableSet_Ioc fun σ hσ => e σ hσ.1]
      exact setIntegral_mono_set hint ((ae_restrict_mem measurableSet_Ioi).mono
        fun σ hσ => by positivity) (Eventually.of_forall Ioc_subset_Ioi_self)
    have h2 : (1 + s) ^ 3 ≤ 8 * s ^ 3 := by
      have : 1 + s ≤ 2 * s := by linarith
      calc (1 + s) ^ 3 ≤ (2 * s) ^ 3 := pow_le_pow_left₀ (by linarith) this 3
        _ = 8 * s ^ 3 := by ring
    have hs3 : 0 < s ^ 3 := by positivity
    calc (s ^ 3)⁻¹ * ‖∫ σ in (0 : ℝ)..s, (σ : ℂ) ^ 2 * (kappa c σ * regB c σ)‖ / 4 *
          (1 + s) ^ 3
        ≤ (s ^ 3)⁻¹ * K / 4 * (8 * s ^ 3) := by gcongr
      _ = 2 * K := by field_simp; ring

/-! ### The velocity is square integrable -/

theorem norm_fderiv_modeStream_le (hF : WholeLineData c F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℂ, ‖fderiv ℝ (modeStream F) y‖ ≤ K / (1 + ‖y‖) ^ 3 := by
  have hc := hF.im_ne_zero
  obtain ⟨β₀, -, hβ⟩ := exists_mode_eq_regLog hF
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_decay_regB hF
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_decay_deriv_regB hF
  have hB : Differentiable ℝ (fun s => β₀ * regB c s) :=
    (contDiff_const.mul (contDiff_regB hc)).differentiable (by simp)
  have e : modeStream F = fun y : ℂ => y ^ 2 * (β₀ * regB c (‖y‖ ^ 2)) :=
    funext (modeStream_eq (fun t => (hβ t).1))
  refine ⟨‖β₀‖ * (8 * C₁ + 16 * C₂), by positivity, fun y => ?_⟩
  rw [e]
  refine (norm_fderiv_angularTwo_le (B := fun s => β₀ * regB c s) hB y).trans ?_
  have hdB : deriv (fun s => β₀ * regB c s) (‖y‖ ^ 2) = β₀ * deriv (regB c) (‖y‖ ^ 2) :=
    deriv_const_mul _ ((contDiff_regB hc).differentiable (by simp) _)
  rw [hdB, norm_mul, norm_mul]
  set a := ‖y‖
  set s := a ^ 2
  have ha : 0 ≤ a := norm_nonneg y
  have hs : 0 ≤ s := by positivity
  have hb1 := hC₁ s hs
  have hb2 := hC₂ s hs
  set u := 1 + a
  set v := 1 + s
  have hu : 0 < u := by positivity
  have hv : 0 < v := by positivity
  have huv : u ^ 2 ≤ 2 * v := by simp only [u, v, s]; nlinarith [sq_nonneg (a - 1)]
  have hau : a ≤ u := by simp only [u]; linarith
  -- `‖b(s)‖ ≤ C₁ / v²`, `‖b'(s)‖ ≤ C₂ / v³`
  have hb1' : ‖regB c s‖ ≤ C₁ / v ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hb1
  have hb2' : ‖deriv (regB c) s‖ ≤ C₂ / v ^ 3 := by rw [le_div_iff₀ (by positivity)]; exact hb2
  have k1 : a / v ^ 2 ≤ 4 / u ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : u ^ 4 ≤ 4 * v ^ 2 := by
      calc u ^ 4 = (u ^ 2) ^ 2 := by ring
        _ ≤ (2 * v) ^ 2 := pow_le_pow_left₀ (by positivity) huv 2
        _ = 4 * v ^ 2 := by ring
    calc a * u ^ 3 ≤ u * u ^ 3 := by gcongr
      _ = u ^ 4 := by ring
      _ ≤ 4 * v ^ 2 := h4
  have k2 : a ^ 3 / v ^ 3 ≤ 8 / u ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc a ^ 3 * u ^ 3 ≤ u ^ 3 * u ^ 3 := by gcongr
      _ = (u ^ 2) ^ 3 := by ring
      _ ≤ (2 * v) ^ 3 := pow_le_pow_left₀ (by positivity) huv 3
      _ = 8 * v ^ 3 := by ring
  calc 2 * a * (‖β₀‖ * ‖regB c s‖) + 2 * a ^ 3 * (‖β₀‖ * ‖deriv (regB c) s‖)
      ≤ 2 * a * (‖β₀‖ * (C₁ / v ^ 2)) + 2 * a ^ 3 * (‖β₀‖ * (C₂ / v ^ 3)) := by gcongr
    _ = 2 * ‖β₀‖ * C₁ * (a / v ^ 2) + 2 * ‖β₀‖ * C₂ * (a ^ 3 / v ^ 3) := by ring
    _ ≤ 2 * ‖β₀‖ * C₁ * (4 / u ^ 3) + 2 * ‖β₀‖ * C₂ * (8 / u ^ 3) := by gcongr
    _ = ‖β₀‖ * (8 * C₁ + 16 * C₂) / u ^ 3 := by ring

/-- **The velocity is square integrable** (tex lines 977, 1181; unit B0056): the gradient of
the streamfunction `Ψ = φ e^{2iϑ}` lies in `L²(ℝ²)`. -/
theorem memLp_fderiv_modeStream (hF : WholeLineData c F) :
    MemLp (fderiv ℝ (modeStream F)) 2 volume := by
  obtain ⟨K, hK0, hK⟩ := norm_fderiv_modeStream_le hF
  have hcont : Continuous (fderiv ℝ (modeStream F)) :=
    (contDiff_modeStream hF).continuous_fderiv (by simp)
  have hg : MemLp (fun y : ℂ => K / (1 + ‖y‖) ^ 3) 2 volume := by
    have hm : AEStronglyMeasurable (fun y : ℂ => K / (1 + ‖y‖) ^ 3) volume :=
      (continuous_const.div ((continuous_const.add continuous_norm).pow 3) fun y =>
        pow_ne_zero 3 (by positivity : (0 : ℝ) < 1 + ‖y‖).ne').aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    have hI := (integrable_one_add_norm (E := ℂ) (μ := volume) (r := 6)
      (by rw [Complex.finrank_real_complex]; norm_num)).const_mul (K ^ 2)
    refine hI.congr (Eventually.of_forall fun y => ?_)
    have hpos : 0 < 1 + ‖y‖ := by positivity
    simp only
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow, ← pow_mul,
      Real.rpow_neg hpos.le, show (6 : ℝ) = ((3 * 2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_eq_mul_inv]
  exact hg.of_le hcont.aestronglyMeasurable (Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hK y)

end UnforcedLeray.ComplexODEC
