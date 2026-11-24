import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AZeroBmatLinear.Helpers
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AZeroBmatBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `a₀(B_{μ,ν}[A])` is Lipschitz in `μ` on `[0,1]`, uniformly for `A ∈ 𝒜` (source 4614-4618, 5919)

`‖a₀(B_{μ,ν}[A]) - a₀(B_{μ',ν}[A])‖ ≤ L |μ-μ'| M(A)`.  The integrands live on `(0, 1.1/ν]`
(`azBmat_zero`); there `B_μ - B_μ' = ((μ-μ')/t) A^y`, `|A^y(t)| ≤ t^{5/2}M(A)` and
`|t^μ - t^μ'| ≤ |μ-μ'||log t| max(t^μ,t^μ')`, with `|log t| t^{3/2}` bounded on `(0, T]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `t^μ - t^μ'` is controlled by `|μ-μ'||log t|` times the larger power. -/
theorem abs_rpow_sub_le {t : ℝ} (ht : 0 < t) (μ μ' : ℝ) :
    |t ^ μ - t ^ μ'| ≤ |μ - μ'| * |Real.log t| * max (t ^ μ) (t ^ μ') := by
  have key : ∀ x y : ℝ, y ≤ x → Real.exp x - Real.exp y ≤ (x - y) * Real.exp x := by
    intro x y hxy
    have h1 := Real.add_one_le_exp (-(x - y))
    have h2 : Real.exp x = Real.exp y * Real.exp (x - y) := by rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-(x - y)) * Real.exp (x - y) = 1 := by rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos (x - y)
    have h5 := Real.exp_pos y
    -- exp x - exp y = exp y (e^d - 1) ≤ exp y * d * e^d
    have h6 : (1 - (x - y)) * Real.exp (x - y) ≤ 1 := by
      calc (1 - (x - y)) * Real.exp (x - y) ≤ Real.exp (-(x - y)) * Real.exp (x - y) :=
            mul_le_mul_of_nonneg_right (by linarith) h4.le
        _ = 1 := h3
    rw [h2]
    nlinarith [mul_pos h5 h4]
  have e1 : t ^ μ = Real.exp (Real.log t * μ) := by
    rw [Real.rpow_def_of_pos ht]
  have e2 : t ^ μ' = Real.exp (Real.log t * μ') := by
    rw [Real.rpow_def_of_pos ht]
  rw [e1, e2]
  rcases le_total (Real.log t * μ') (Real.log t * μ) with h | h
  · have := key _ _ h
    have hpos : 0 ≤ Real.exp (Real.log t * μ) - Real.exp (Real.log t * μ') := by
      linarith [Real.exp_le_exp.2 h]
    rw [abs_of_nonneg hpos]
    refine this.trans ?_
    have hx : Real.log t * μ - Real.log t * μ' = Real.log t * (μ - μ') := by ring
    rw [hx]
    have : (Real.log t * (μ - μ')) ≤ |μ - μ'| * |Real.log t| := by
      calc Real.log t * (μ - μ') ≤ |Real.log t * (μ - μ')| := le_abs_self _
        _ = |μ - μ'| * |Real.log t| := by rw [abs_mul]; ring
    exact mul_le_mul this (le_max_left _ _) (Real.exp_pos _).le (by positivity)
  · have := key _ _ h
    have hpos : 0 ≤ Real.exp (Real.log t * μ') - Real.exp (Real.log t * μ) := by
      linarith [Real.exp_le_exp.2 h]
    rw [abs_sub_comm, abs_of_nonneg hpos]
    refine this.trans ?_
    have hx : Real.log t * μ' - Real.log t * μ = Real.log t * (μ' - μ) := by ring
    rw [hx]
    have : (Real.log t * (μ' - μ)) ≤ |μ - μ'| * |Real.log t| := by
      calc Real.log t * (μ' - μ) ≤ |Real.log t * (μ' - μ)| := le_abs_self _
        _ = |μ - μ'| * |Real.log t| := by rw [abs_mul, abs_sub_comm]; ring
    exact mul_le_mul this (le_max_right _ _) (Real.exp_pos _).le (by positivity)

/-- `|log t| t^{3/2}` is bounded on `(0, T]`. -/
theorem abs_log_mul_rpow_le {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    |Real.log t| * t ^ (3 / 2 : ℝ) ≤ 1 + T * T ^ (3 / 2 : ℝ) := by
  have hT : 0 < T := lt_of_lt_of_le ht htT
  have hT32 : 0 ≤ T ^ (3 / 2 : ℝ) := Real.rpow_nonneg hT.le _
  rcases le_total t 1 with h | h
  · have hl : Real.log t ≤ 0 := Real.log_nonpos ht.le h
    rw [abs_of_nonpos hl]
    have h1 : -Real.log t ≤ 1 / t := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
      rw [Real.log_inv] at this
      rw [one_div]; linarith
    have h2 : t ^ (3 / 2 : ℝ) ≤ t := by
      have := Real.rpow_le_rpow_of_exponent_ge ht h (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      simpa using this
    have h3 : (-Real.log t) * t ^ (3 / 2 : ℝ) ≤ 1 := by
      calc (-Real.log t) * t ^ (3 / 2 : ℝ) ≤ (1 / t) * t :=
            mul_le_mul h1 h2 (Real.rpow_nonneg ht.le _) (by positivity)
        _ = 1 := by field_simp
    nlinarith [mul_nonneg hT.le hT32]
  · have hl : 0 ≤ Real.log t := Real.log_nonneg h
    rw [abs_of_nonneg hl]
    have h1 : Real.log t ≤ T := by
      have := Real.log_le_sub_one_of_pos ht
      linarith
    have h2 : t ^ (3 / 2 : ℝ) ≤ T ^ (3 / 2 : ℝ) := Real.rpow_le_rpow ht.le htT (by norm_num)
    have := mul_le_mul h1 h2 (Real.rpow_nonneg ht.le _) hT.le
    linarith

/-- The meridional functional `Q(M) = d(M) - i e(M)`. -/
def azQ (M : Mat3) : ℂ := ((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ)

theorem azQ_sub (M N : Mat3) : azQ M - azQ N = azQ (M - N) := by
  unfold azQ Bd Be
  simp only [Pi.sub_apply]
  push_cast
  ring

theorem azInt_eq (lam : ℂ) (μ : ℝ) (B : ℝ → Mat3) {t : ℝ} (ht : 0 < t) :
    azInt lam μ B t = ((t ^ μ : ℝ) : ℂ) * Complex.exp (-lam * (t : ℂ)) * azQ (B t) := by
  unfold azInt azQ
  rw [Complex.ofReal_cpow ht.le]

theorem Bmat_sub (ν μ μ' : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) {t : ℝ} :
    Bmat ν μ χ A t - Bmat ν μ' χ A t = ((μ - μ') / t) • Ay ν χ A t := by
  unfold Bmat
  rw [add_sub_add_left_eq_sub, ← sub_smul, sub_div]

theorem norm_exp_le {lam : ℂ} {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ‖Complex.exp (-lam * (t : ℂ))‖ ≤ Real.exp (|lam.re| * T) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have hre : (-lam * (t : ℂ)).re = -lam.re * t := by simp
  rw [hre]
  have ha : 0 ≤ (|lam.re| + lam.re) * t :=
    mul_nonneg (by linarith [neg_abs_le lam.re]) ht.le
  have hb : 0 ≤ |lam.re| * (T - t) := mul_nonneg (abs_nonneg _) (by linarith)
  nlinarith [ha, hb]

theorem rpow_le_max {t T μ : ℝ} (ht : 0 < t) (htT : t ≤ T) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    t ^ μ ≤ max 1 T := by
  rcases le_total t 1 with h | h
  · exact (Real.rpow_le_one ht.le h hμ0).trans (le_max_left _ _)
  · have := Real.rpow_le_rpow_of_exponent_le h hμ1
    rw [Real.rpow_one] at this
    exact this.trans (htT.trans (le_max_right _ _))

/-- The pointwise difference bound on `(0, T]`. -/
theorem azInt_diff_bound {as : ℝ} {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) {ν : ℝ} (hν : 0 < ν)
    (lam : ℂ) {μ μ' : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hμ'0 : 0 ≤ μ') (hμ'1 : μ' ≤ 1)
    (A : ℝ → Mat3) (hA : IsAffElem as A) {t : ℝ} (ht : 0 < t) (htT : t ≤ (11 / 10 : ℝ) / ν) :
    ‖azInt lam μ (Bmat ν μ χ A) t - azInt lam μ' (Bmat ν μ' χ A) t‖ ≤
      (max 1 ((11 / 10 : ℝ) / ν) * Real.exp (|lam.re| * ((11 / 10 : ℝ) / ν)) *
        (4 * (1 + ((11 / 10 : ℝ) / ν) * ((11 / 10 : ℝ) / ν) ^ (3 / 2 : ℝ)) +
          2 * ((11 / 10 : ℝ) / ν) ^ (3 / 2 : ℝ))) * |μ - μ'| * affM ν χ A := by
  set T : ℝ := (11 / 10 : ℝ) / ν with hTdef
  have hT : 0 < T := lt_of_lt_of_le ht htT
  set m1 : ℝ := max 1 T with hm1
  set e1 : ℝ := Real.exp (|lam.re| * T) with he1
  set M : ℝ := affM ν χ A with hMdef
  have hM : 0 ≤ M := affM_nonneg ν χ A
  have hm1pos : 1 ≤ m1 := le_max_left _ _
  have he1pos : 0 < e1 := Real.exp_pos _
  set E : ℂ := Complex.exp (-lam * (t : ℂ)) with hE
  have hEn : ‖E‖ ≤ e1 := norm_exp_le ht htT
  have hPμ : t ^ μ ≤ m1 := rpow_le_max ht htT hμ0 hμ1
  have hPμ' : t ^ μ' ≤ m1 := rpow_le_max ht htT hμ'0 hμ'1
  have hPμ0 : 0 ≤ t ^ μ := Real.rpow_nonneg ht.le _
  have hPμ'0 : 0 ≤ t ^ μ' := Real.rpow_nonneg ht.le _
  -- sizes of B and Ay
  have hbdd := aySumBdd_of sDerivIterDiffOn sDerivIterLeibniz as χ hχ ν hν A hA
  have hAy := fac_frob_Ay_le ν χ A hbdd t ht htT
  have hfAy : frob (Ay ν χ A t) ≤ t ^ (5 / 2 : ℝ) * M := by
    have := fac_frob_nonneg (t • deriv (Ay ν χ A) t)
    linarith
  have hBμ : frob (Bmat ν μ χ A t) ≤ (1 + μ) * t ^ (3 / 2 : ℝ) * M :=
    bmatBound as χ hχ ν μ hν hμ0 A hA t ht htT
  have hQμ : ‖azQ (Bmat ν μ χ A t)‖ ≤ 2 * ((1 + μ) * t ^ (3 / 2 : ℝ) * M) :=
    (norm_azQ_le _).trans (by linarith)
  have ht32 : 0 ≤ t ^ (3 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  have hQμ2 : ‖azQ (Bmat ν μ χ A t)‖ ≤ 4 * (t ^ (3 / 2 : ℝ) * M) := by
    refine hQμ.trans ?_
    have : (1 + μ) * t ^ (3 / 2 : ℝ) * M ≤ 2 * (t ^ (3 / 2 : ℝ) * M) := by
      have := mul_nonneg ht32 hM
      nlinarith
    linarith
  -- difference of Q's
  have hdiffB : frob (Bmat ν μ χ A t - Bmat ν μ' χ A t) ≤ |μ - μ'| * (t ^ (3 / 2 : ℝ) * M) := by
    rw [Bmat_sub, fac_frob_smul, abs_div, abs_of_pos ht]
    have : |μ - μ'| / t * frob (Ay ν χ A t) ≤ |μ - μ'| / t * (t ^ (5 / 2 : ℝ) * M) :=
      mul_le_mul_of_nonneg_left hfAy (by positivity)
    refine this.trans (le_of_eq ?_)
    rw [fac_s52 t ht]
    field_simp
  have hQd : ‖azQ (Bmat ν μ χ A t) - azQ (Bmat ν μ' χ A t)‖ ≤
      2 * (|μ - μ'| * (t ^ (3 / 2 : ℝ) * M)) := by
    rw [azQ_sub]
    exact (norm_azQ_le _).trans (by linarith)
  have ht32T : t ^ (3 / 2 : ℝ) ≤ T ^ (3 / 2 : ℝ) := Real.rpow_le_rpow ht.le htT (by norm_num)
  have hlog := abs_log_mul_rpow_le ht htT
  -- the decomposition
  have hdec : azInt lam μ (Bmat ν μ χ A) t - azInt lam μ' (Bmat ν μ' χ A) t =
      (((t ^ μ : ℝ) - t ^ μ' : ℝ) : ℂ) * E * azQ (Bmat ν μ χ A t) +
        ((t ^ μ' : ℝ) : ℂ) * E *
          (azQ (Bmat ν μ χ A t) - azQ (Bmat ν μ' χ A t)) := by
    rw [azInt_eq lam μ _ ht, azInt_eq lam μ' _ ht]
    push_cast
    ring
  rw [hdec]
  refine (norm_add_le _ _).trans ?_
  have hT1 : ‖(((t ^ μ : ℝ) - t ^ μ' : ℝ) : ℂ) * E * azQ (Bmat ν μ χ A t)‖ ≤
      m1 * e1 * (4 * (1 + T * T ^ (3 / 2 : ℝ))) * |μ - μ'| * M := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hd := abs_rpow_sub_le ht μ μ'
    have hmax : max (t ^ μ) (t ^ μ') ≤ m1 := max_le hPμ hPμ'
    have hd2 : |t ^ μ - t ^ μ'| ≤ |μ - μ'| * |Real.log t| * m1 :=
      hd.trans (mul_le_mul_of_nonneg_left hmax (by positivity))
    have hq : ‖azQ (Bmat ν μ χ A t)‖ ≤ 4 * (t ^ (3 / 2 : ℝ) * M) := hQμ2
    have hQn := norm_nonneg (azQ (Bmat ν μ χ A t))
    have hEn0 := norm_nonneg E
    calc |t ^ μ - t ^ μ'| * ‖E‖ * ‖azQ (Bmat ν μ χ A t)‖
        ≤ (|μ - μ'| * |Real.log t| * m1) * e1 * (4 * (t ^ (3 / 2 : ℝ) * M)) := by
          apply mul_le_mul (mul_le_mul hd2 hEn hEn0 (by positivity)) hq hQn (by positivity)
      _ = m1 * e1 * 4 * |μ - μ'| * ((|Real.log t| * t ^ (3 / 2 : ℝ)) * M) := by ring
      _ ≤ m1 * e1 * 4 * |μ - μ'| * ((1 + T * T ^ (3 / 2 : ℝ)) * M) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hlog hM
      _ = m1 * e1 * (4 * (1 + T * T ^ (3 / 2 : ℝ))) * |μ - μ'| * M := by ring
  have hT2 : ‖((t ^ μ' : ℝ) : ℂ) * E * (azQ (Bmat ν μ χ A t) - azQ (Bmat ν μ' χ A t))‖ ≤
      m1 * e1 * (2 * T ^ (3 / 2 : ℝ)) * |μ - μ'| * M := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hPμ'0]
    have hEn0 := norm_nonneg E
    have hQn := norm_nonneg (azQ (Bmat ν μ χ A t) - azQ (Bmat ν μ' χ A t))
    calc t ^ μ' * ‖E‖ * ‖azQ (Bmat ν μ χ A t) - azQ (Bmat ν μ' χ A t)‖
        ≤ m1 * e1 * (2 * (|μ - μ'| * (T ^ (3 / 2 : ℝ) * M))) := by
          apply mul_le_mul (mul_le_mul hPμ' hEn hEn0 (by linarith)) _ hQn (by positivity)
          refine hQd.trans ?_
          have : |μ - μ'| * (t ^ (3 / 2 : ℝ) * M) ≤ |μ - μ'| * (T ^ (3 / 2 : ℝ) * M) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht32T hM) (abs_nonneg _)
          linarith
      _ = m1 * e1 * (2 * T ^ (3 / 2 : ℝ)) * |μ - μ'| * M := by ring
  have : m1 * e1 * (4 * (1 + T * T ^ (3 / 2 : ℝ))) * |μ - μ'| * M +
      m1 * e1 * (2 * T ^ (3 / 2 : ℝ)) * |μ - μ'| * M =
      (m1 * e1 * (4 * (1 + T * T ^ (3 / 2 : ℝ)) + 2 * T ^ (3 / 2 : ℝ))) * |μ - μ'| * M := by
    ring
  linarith

/-- **`a₀(B_{μ,ν}[A])` is Lipschitz in `μ ∈ [0,1]`**, uniformly on `𝒜`. -/
theorem aZero_lip {as : ℝ} {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) (lam ell : ℂ) {ν : ℝ}
    (hν : 0 < ν) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ μ μ' : ℝ, 0 ≤ μ → μ ≤ 1 → 0 ≤ μ' → μ' ≤ 1 →
      ∀ A : ℝ → Mat3, IsAffElem as A →
        ‖aZero lam ell (μ : ℂ) (Bmat ν μ χ A) - aZero lam ell (μ' : ℂ) (Bmat ν μ' χ A)‖ ≤
          L * |μ - μ'| * affM ν χ A := by
  set T : ℝ := (11 / 10 : ℝ) / ν with hTdef
  have hT : 0 < T := div_pos (by norm_num) hν
  set Cc : ℝ := max 1 T * Real.exp (|lam.re| * T) *
    (4 * (1 + T * T ^ (3 / 2 : ℝ)) + 2 * T ^ (3 / 2 : ℝ)) with hCc
  have hCc0 : 0 ≤ Cc := by
    have : 0 ≤ T ^ (3 / 2 : ℝ) := Real.rpow_nonneg hT.le _
    have : 0 ≤ T * T ^ (3 / 2 : ℝ) := mul_nonneg hT.le this
    have h1 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
    rw [hCc]; positivity
  refine ⟨‖-(1 / 2 : ℂ) * ell‖ * T * Cc, by positivity, ?_⟩
  intro μ μ' hμ0 hμ1 hμ'0 hμ'1 A hA
  have i1 := integrableOn_azInt_Bmat hχ μ hν hμ0 lam A hA
  have i2 := integrableOn_azInt_Bmat hχ μ' hν hμ'0 lam A hA
  rw [aZero_eq_azInt, aZero_eq_azInt, ← mul_sub, ← integral_sub i1 i2, norm_mul]
  set Kd : ℝ := Cc * |μ - μ'| * affM ν χ A with hKd
  have hbd : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖azInt lam μ (Bmat ν μ χ A) t - azInt lam μ' (Bmat ν μ' χ A) t‖ ≤
        Set.indicator (Ioc 0 T) (fun _ : ℝ => Kd) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    by_cases htT : t ≤ T
    · rw [Set.indicator_of_mem (show t ∈ Ioc 0 T from ⟨ht0, htT⟩)]
      exact azInt_diff_bound hχ hν lam hμ0 hμ1 hμ'0 hμ'1 A hA ht0 htT
    · have hlt : T < t := not_le.1 htT
      rw [azInt_zero_of_Bmat_zero lam μ _ t (azBmat_zero hχ μ hν A t hlt),
        azInt_zero_of_Bmat_zero lam μ' _ t (azBmat_zero hχ μ' hν A t hlt), sub_zero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCc0 (abs_nonneg _)) (affM_nonneg ν χ A)) _
  have h1 := norm_integral_le_of_norm_le (integrable_indicator_Ioc_const T Kd) hbd
  rw [integral_indicator_const _ measurableSet_Ioc, real_restrict_Ioc_eq _ hT.le,
    smul_eq_mul] at h1
  calc ‖-(1 / 2 : ℂ) * ell‖ * ‖∫ t in Ioi (0 : ℝ),
        (azInt lam μ (Bmat ν μ χ A) t - azInt lam μ' (Bmat ν μ' χ A) t)‖
      ≤ ‖-(1 / 2 : ℂ) * ell‖ * (T * Kd) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖-(1 / 2 : ℂ) * ell‖ * T * Cc * |μ - μ'| * affM ν χ A := by rw [hKd]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
