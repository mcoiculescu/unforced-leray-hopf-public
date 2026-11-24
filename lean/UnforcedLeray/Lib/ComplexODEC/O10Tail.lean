import UnforcedLeray.Lib.ComplexODEC.Quadrupole
import UnforcedLeray.Lib.ComplexODEC.Bounds
import UnforcedLeray.Lib.SpecialFunctions.GammaTails
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# Quantitative Gaussian tails for the O10 far field

This leaf is kept separate from the stable `Quadrupole` dependency while the canonical branch
verifies its oscillator action.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff Nat

namespace UnforcedLeray.ComplexODEC

private def gaussTailWeight (s : ℝ) : ℝ := Real.exp (-(s ^ 2 / 4))

/-- Restricting the angular-two field to the positive real axis recovers its radial profile. -/
theorem modeQ_eq_modeVort_ofReal {c : ℂ} {F : ℝ → ℂ} {r : ℝ} (hr : 0 < r) :
    modeQ c F (r : ℂ) = modeVort c F r := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [modeQ, Planar.NUE.Ang.ofProfile, Planar.NUE.Ang.angPhase,
    Complex.norm_real, abs_of_pos hr, hr']

/-- On the positive real axis the vorticity is `r² β(r²)` for the O14 angular profile. -/
theorem modeVort_eq_modeBeta_on_pos {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    ∃ β₀ : ℂ, modeVort c F r = (r : ℂ) ^ 2 * modeBeta c β₀ (r ^ 2) := by
  obtain ⟨β₀, -, hβ⟩ := exists_mode_eq_regLog hF
  have hq2 := modeQ_eq (c := c) (F := F) (β₀ := β₀)
    (fun t => (hβ t).1) (r : ℂ)
  rw [modeQ_eq_modeVort_ofReal hr] at hq2
  exact ⟨β₀, by simpa [Complex.norm_real, abs_of_pos hr] using hq2⟩

/-- Every radial derivative of the actual mode inherits O14's sharp Gaussian envelope. The
radial restriction is linear (`r ↦ (r : ℂ)`), so its iterated derivatives are controlled directly
by the Cartesian Frechet derivatives of `modeQ`. -/
theorem contDiffAt_modeVort {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ∞ (modeVort c F) r := by
  let g : ℝ → ℂ := fun x => modeQ c F (x : ℂ)
  have hg : ContDiff ℝ ∞ g := by
    have haxis0 := Complex.ofRealCLM.contDiff.comp
      (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ))
    have haxis : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
      convert haxis0 using 1
      ext x
      exact Complex.ofRealCLM_apply x
    simpa [g, Function.comp_def] using (contDiff_modeQ hF).comp haxis
  have heq : (modeVort c F) =ᶠ[𝓝 r] g := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (modeQ_eq_modeVort_ofReal hx).symm
  exact hg.contDiffAt.congr_of_eventuallyEq heq

theorem exists_norm_iteratedDeriv_modeVort_bound {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) (k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv k (modeVort c F) r‖ ≤
        C * (1 + r) ^ N * Real.exp (-(r ^ 2 / 4)) := by
  let g : ℝ → ℂ := fun r => modeQ c F (r : ℂ)
  have hq : ContDiff ℝ ∞ (modeQ c F) := contDiff_modeQ hF
  obtain ⟨C, N, hO14⟩ := norm_iteratedFDeriv_modeQ_le hF k
  have hEq : Set.EqOn (modeVort c F) g (Ioi 0) := by
    intro r hr
    exact (modeQ_eq_modeVort_ofReal hr).symm
  have hEqDeriv := hEq.iteratedDeriv_of_isOpen isOpen_Ioi k
  refine ⟨C, N, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hcomp := Complex.ofRealCLM.iteratedFDeriv_comp_right
    (f := modeQ c F) hq r (i := k) (by simp)
  have hcomp' : iteratedFDeriv ℝ k g r =
      (iteratedFDeriv ℝ k (modeQ c F) (r : ℂ)).compContinuousLinearMap
        (fun _ : Fin k => Complex.ofRealCLM) := by
    simpa [g, Function.comp_def] using hcomp
  have hnorm : ‖iteratedFDeriv ℝ k g r‖ ≤
      ‖iteratedFDeriv ℝ k (modeQ c F) (r : ℂ)‖ := by
    rw [hcomp']
    calc
      _ ≤ ‖iteratedFDeriv ℝ k (modeQ c F) (r : ℂ)‖ *
          ∏ _i : Fin k, ‖Complex.ofRealCLM‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ k (modeQ c F) (r : ℂ)‖ := by
        simp [Complex.ofRealCLM_norm]
  have hradial : ‖iteratedDeriv k g r‖ ≤
      C * (1 + r) ^ N * Real.exp (-(r ^ 2 / 4)) := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    calc
      _ ≤ ‖iteratedFDeriv ℝ k (modeQ c F) (r : ℂ)‖ := hnorm
      _ ≤ C * (1 + ‖(r : ℂ)‖) ^ N * Real.exp (-‖(r : ℂ)‖ ^ 2 / 4) := hO14 _
      _ = C * (1 + r) ^ N * Real.exp (-(r ^ 2 / 4)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
        congr 1
        ring
  rw [hEqDeriv (Set.mem_Ioi.mpr hr0)]
  exact hradial

/-- The radial derivatives of the complex reciprocal agree with the explicit real formula. -/
theorem iteratedDeriv_complex_ofReal_inv_formula (k : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    iteratedDeriv k (fun x : ℝ => ((x : ℂ)⁻¹)) r =
      (((-1 : ℝ) ^ k * (Nat.factorial k : ℝ) * r ^ (-1 - (k : ℤ))) : ℂ) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hreal : iteratedDeriv k (fun x : ℝ => 1 / x) r =
      (-1 : ℝ) ^ k * (Nat.factorial k : ℝ) * r ^ (-1 - (k : ℤ)) := by
    have hw := (iteratedDerivWithin_one_div (𝕜 := ℝ) (s := Set.Ioi (0 : ℝ))
      k isOpen_Ioi) hr0
    have ho := (iteratedDerivWithin_of_isOpen (f := fun x : ℝ => 1 / x)
      (n := k) isOpen_Ioi) hr0
    exact ho.symm.trans hw
  have hsmooth : ContDiffAt ℝ ⊤ (fun x : ℝ => x⁻¹) r :=
    contDiffAt_inv ℝ hr0.ne'
  have hcomp := Complex.ofRealCLM.iteratedFDeriv_comp_left hsmooth
    (i := k) le_top
  have hidentity : (fun x : ℝ => ((x : ℂ)⁻¹)) =
      Complex.ofRealCLM ∘ (fun x : ℝ => x⁻¹) := by
    funext x
    simp
  rw [hidentity, iteratedDeriv_eq_iteratedFDeriv, hcomp]
  change (↑(iteratedDeriv k (fun x : ℝ => x⁻¹) r) : ℂ) = _
  simpa [one_div] using congrArg (fun x : ℝ => (x : ℂ)) hreal

/-- The `k`th derivative of the complex reciprocal is bounded by `k!` on radii at least one. -/
theorem norm_iteratedDeriv_complex_ofReal_inv_le {r : ℝ} (hr : 1 ≤ r) (k : ℕ) :
    ‖iteratedDeriv k (fun x : ℝ => ((x : ℂ)⁻¹)) r‖ ≤ Nat.factorial k := by
  have hpow_nonneg : 0 ≤ r ^ (-1 - (k : ℤ)) := zpow_nonneg (by linarith : 0 ≤ r) _
  have hpow_le : r ^ (-1 - (k : ℤ)) ≤ 1 := by
    have he : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hr)
  rw [iteratedDeriv_complex_ofReal_inv_formula k hr]
  have hcast : ((↑(-1 : ℝ) : ℂ) ^ k * (↑(Nat.factorial k : ℝ) : ℂ) *
      (↑r : ℂ) ^ (-1 - (k : ℤ))) =
      ((((-1 : ℝ) ^ k * (Nat.factorial k : ℝ) * r ^ (-1 - (k : ℤ))) : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (show 0 ≤ (Nat.factorial k : ℝ) by positivity), abs_of_nonneg hpow_nonneg]
  exact mul_le_of_le_one_right (by positivity : 0 ≤ (Nat.factorial k : ℝ)) hpow_le

/-- Every finite radial derivative of the inverse-radius vorticity integrand retains the sharp
Gaussian exponent; the polynomial and constant may depend on the derivative order. -/
theorem exists_norm_iteratedDeriv_inv_mul_modeVort_bound {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) (k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv k (fun x : ℝ => (x : ℂ)⁻¹ * modeVort c F x) r‖ ≤
        C * (1 + r) ^ N * gaussTailWeight r := by
  let B : ℕ → ℝ := fun j => Classical.choose
    (exists_norm_iteratedDeriv_modeVort_bound hF j)
  let P : ℕ → ℕ := fun j => Classical.choose
    (Classical.choose_spec (exists_norm_iteratedDeriv_modeVort_bound hF j))
  have hB (j : ℕ) : ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv j (modeVort c F) r‖ ≤ B j * (1 + r) ^ P j * gaussTailWeight r := by
    simpa [B, P, gaussTailWeight] using Classical.choose_spec
      (Classical.choose_spec (exists_norm_iteratedDeriv_modeVort_bound hF j))
  have hBnonneg (j : ℕ) : 0 ≤ B j := by
    by_contra hn
    have hn' : B j < 0 := lt_of_not_ge hn
    have hpos : 0 < (1 + (1 : ℝ)) ^ P j * gaussTailWeight 1 :=
      mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
    have hb := hB j 1 (by norm_num)
    have hneg : B j * ((1 + (1 : ℝ)) ^ P j * gaussTailWeight 1) < 0 :=
      mul_neg_of_neg_of_pos hn' hpos
    have hnonneg := norm_nonneg (iteratedDeriv j (modeVort c F) 1)
    linarith
  let f : ℝ → ℂ := fun x => (x : ℂ)⁻¹
  let g : ℝ → ℂ := modeVort c F
  let coeff : ℕ → ℝ := fun i => (k.choose i : ℝ) * (Nat.factorial i : ℝ) * B (k - i)
  let C : ℝ := ∑ i ∈ Finset.range (k + 1), coeff i
  let N : ℕ := ∑ i ∈ Finset.range (k + 1), P (k - i)
  refine ⟨C, N, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hinv : ContDiffAt ℝ ∞ f r := by
    have hreal : ContDiffAt ℝ ∞ (fun x : ℝ => x⁻¹) r := contDiffAt_inv ℝ hr0.ne'
    have hcomp := hreal.continuousLinearMap_comp Complex.ofRealCLM
    have heq : f = Complex.ofRealCLM ∘ (fun x : ℝ => x⁻¹) := by
      funext x
      simp [f]
    simpa only [heq] using hcomp
  have hmode : ContDiffAt ℝ ∞ g r := contDiffAt_modeVort hF hr0
  have hmul := iteratedDeriv_mul
    (hinv.of_le (natCast_le_infty k)) (hmode.of_le (natCast_le_infty k))
  change ‖iteratedDeriv k (f * g) r‖ ≤ C * (1 + r) ^ N * gaussTailWeight r
  rw [hmul]
  have hsum := norm_sum_le (Finset.range (k + 1)) (fun i : ℕ =>
    (k.choose i : ℝ) * iteratedDeriv i f r * iteratedDeriv (k - i) g r)
  have hcoeff_nonneg : ∀ i ∈ Finset.range (k + 1), 0 ≤ coeff i := by
    intro i hi
    simp [coeff]
    positivity [hBnonneg (k - i)]
  have hsumPow :
      (∑ i ∈ Finset.range (k + 1), coeff i * (1 + r) ^ P (k - i)) ≤
        ∑ i ∈ Finset.range (k + 1), coeff i * (1 + r) ^ N := by
    apply Finset.sum_le_sum
    intro i hi
    have hpow : P (k - i) ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum (f := fun j : ℕ => P (k - j))
        (fun j hj => Nat.zero_le _) hi
    have hbase : 1 ≤ 1 + r := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hpow)
      (hcoeff_nonneg i hi)
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        ‖(k.choose i : ℝ) * iteratedDeriv i f r * iteratedDeriv (k - i) g r‖ := hsum
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        coeff i * (1 + r) ^ P (k - i) * gaussTailWeight r := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hrec := norm_iteratedDeriv_complex_ofReal_inv_le hr i
      have hmod := hB (k - i) r hr
      have hchoose : 0 ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
      calc
        ‖(k.choose i : ℝ) * iteratedDeriv i f r * iteratedDeriv (k - i) g r‖ =
            (k.choose i : ℝ) * ‖iteratedDeriv i f r‖ * ‖iteratedDeriv (k - i) g r‖ := by
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Nat.cast_nonneg _)]
        _ ≤ (k.choose i : ℝ) * (Nat.factorial i : ℝ) *
            (B (k - i) * (1 + r) ^ P (k - i) * gaussTailWeight r) := by
              gcongr
        _ = coeff i * (1 + r) ^ P (k - i) * gaussTailWeight r := by
              simp [coeff, mul_assoc]
    _ ≤ C * (1 + r) ^ N * gaussTailWeight r := by
      calc
        (∑ i ∈ Finset.range (k + 1), coeff i * (1 + r) ^ P (k - i) * gaussTailWeight r)
            ≤ ∑ i ∈ Finset.range (k + 1), coeff i * (1 + r) ^ N * gaussTailWeight r := by
              apply Finset.sum_le_sum
              intro i hi
              have hpow : P (k - i) ≤ N := by
                change P (k - i) ≤ ∑ j ∈ Finset.range (k + 1), P (k - j)
                exact Finset.single_le_sum (f := fun j : ℕ => P (k - j))
                  (fun j hj => Nat.zero_le _) hi
              have hbase : 1 ≤ 1 + r := by linarith
              gcongr <;> positivity [hcoeff_nonneg i hi, Real.exp_pos (-(r ^ 2 / 4))]
        _ = (∑ i ∈ Finset.range (k + 1), coeff i * (1 + r) ^ N) * gaussTailWeight r := by
              rw [Finset.sum_mul]
        _ = (∑ i ∈ Finset.range (k + 1), coeff i) *
              ((1 + r) ^ N * gaussTailWeight r) := by
              rw [← Finset.sum_mul]
              ring
        _ = C * (1 + r) ^ N * gaussTailWeight r := by
              dsimp [C]
              ring


private theorem hasDerivAt_gaussTailWeight (r : ℝ) :
    HasDerivAt gaussTailWeight (-(r / 2) * gaussTailWeight r) r := by
  have hsquare : HasDerivAt (fun s : ℝ => s ^ 2 / 4) (2 * r / 4) r := by
    simpa [pow_one] using (hasDerivAt_pow 2 r).div_const 4
  have hcoef : (2 * r / 4 : ℝ) = r / 2 := by ring
  rw [hcoef] at hsquare
  have harg : HasDerivAt (fun s : ℝ => -(s ^ 2 / 4)) (-(r / 2)) r := by
    change HasDerivAt (-(fun s : ℝ => s ^ 2 / 4)) (-(r / 2)) r
    exact hsquare.neg
  have hexp := (Real.hasDerivAt_exp (-(r ^ 2 / 4))).comp r harg
  convert hexp using 1 <;> try rfl
  simp [gaussTailWeight, mul_comm]

/-- Exact first polynomial Gaussian tail, retaining the manuscript's exponent `1/4`. -/
theorem integral_Ioi_gaussTailWeight_one_eq {r : ℝ} (hr : 0 ≤ r) :
    ∫ s in Ioi r, s * Real.exp (-(s ^ 2 / 4)) =
      2 * Real.exp (-(r ^ 2 / 4)) := by
  have hrate : Tendsto (fun s : ℝ => s ^ 2 / 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num)
  have hlim : Tendsto (fun s : ℝ => -2 * gaussTailWeight s) atTop (𝓝 0) := by
    have harg : Tendsto (fun s : ℝ => -(s ^ 2 / 4)) atTop atBot := by
      simpa only [Function.comp_def] using tendsto_neg_atTop_atBot.comp hrate
    have h := Real.tendsto_exp_atBot.comp harg
    simpa [gaussTailWeight, mul_comm] using h.const_mul (-2)
  have hcont : ContinuousWithinAt (fun s : ℝ => -2 * gaussTailWeight s) (Ici r) r := by
    fun_prop [gaussTailWeight]
  have hderiv : ∀ s ∈ Ioi r,
      HasDerivAt (fun x : ℝ => -2 * gaussTailWeight x)
        (s * gaussTailWeight s) s := by
    intro s hs
    have h := (hasDerivAt_const s (-2 : ℝ)).mul (hasDerivAt_gaussTailWeight s)
    convert h using 1 <;> try rfl
    ring_nf
  have hint : IntegrableOn (fun s : ℝ => s * gaussTailWeight s) (Ioi r) := by
    simpa [gaussTailWeight] using
      (integrableOn_pow_mul_gauss 1).mono_set (Ioi_subset_Ioi hr)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  simpa [gaussTailWeight] using h

private theorem tendsto_gaussTailWeight_sq_mul (r : ℝ) :
    Tendsto (fun s : ℝ => s ^ 2 * gaussTailWeight s) atTop (𝓝 0) := by
  have hx : Tendsto (fun s : ℝ => s ^ 2 / 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num)
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
  convert h.const_mul 4 using 1 <;> try rfl
  · ext s
    simp [gaussTailWeight]
    ring
  · simp

private theorem tendsto_gaussTailWeight_fourth_mul (r : ℝ) :
    Tendsto (fun s : ℝ => s ^ 4 * gaussTailWeight s) atTop (𝓝 0) := by
  have hx : Tendsto (fun s : ℝ => s ^ 2 / 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num)
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hx
  convert h.const_mul 16 using 1 <;> try rfl
  · ext s
    simp [gaussTailWeight]
    ring
  · simp

/-- Exact cubic Gaussian moment, with the same exponent as the mode estimate. -/
theorem integral_Ioi_gaussTailWeight_three_eq {r : ℝ} (hr : 0 ≤ r) :
    ∫ s in Ioi r, s ^ 3 * gaussTailWeight s =
      2 * (r ^ 2 + 4) * gaussTailWeight r := by
  let P : ℝ → ℝ := fun s => (-2) * ((s ^ 2 + 4) * gaussTailWeight s)
  have hlim : Tendsto P atTop (𝓝 0) := by
    have h0 : Tendsto gaussTailWeight atTop (𝓝 0) := by
      have hx : Tendsto (fun s : ℝ => s ^ 2 / 4) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num)
      have harg : Tendsto (fun s : ℝ => -(s ^ 2 / 4)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp hx
      change Tendsto (fun s : ℝ => Real.exp (-(s ^ 2 / 4))) atTop (𝓝 0)
      exact Real.tendsto_exp_atBot.comp harg
    have hsum := (tendsto_gaussTailWeight_sq_mul 0).add (h0.const_mul 4)
    have hsum' : Tendsto (fun s : ℝ => (s ^ 2 + 4) * gaussTailWeight s)
        atTop (𝓝 0) := by
      convert hsum using 1 <;> try rfl
      · ext s
        ring
      · simp
    simpa [P] using hsum'.const_mul (-2)
  have hcont : ContinuousWithinAt P (Ici r) r := by
    dsimp [P]
    fun_prop [gaussTailWeight]
  have hderiv : ∀ s ∈ Ioi r, HasDerivAt P (s ^ 3 * gaussTailWeight s) s := by
    intro s hs
    have hpoly : HasDerivAt (fun x : ℝ => x ^ 2 + 4) (2 * s) s := by
      simpa using (hasDerivAt_pow 2 s).add_const 4
    have h := (hasDerivAt_const s (-2 : ℝ)).mul
      (hpoly.mul (hasDerivAt_gaussTailWeight s))
    convert h using 1 <;> try rfl
    ring_nf
  have hint : IntegrableOn (fun s : ℝ => s ^ 3 * gaussTailWeight s) (Ioi r) := by
    simpa [gaussTailWeight] using
      (integrableOn_pow_mul_gauss 3).mono_set (Ioi_subset_Ioi hr)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  simpa [P, gaussTailWeight, mul_comm, mul_left_comm, mul_assoc] using h

/-- Exact quintic Gaussian moment, used for the cubic mode-vorticity tail. -/
theorem integral_Ioi_gaussTailWeight_five_eq {r : ℝ} (hr : 0 ≤ r) :
    ∫ s in Ioi r, s ^ 5 * gaussTailWeight s =
      2 * (r ^ 4 + 8 * r ^ 2 + 32) * gaussTailWeight r := by
  let P : ℝ → ℝ := fun s => (-2) * ((s ^ 4 + 8 * s ^ 2 + 32) * gaussTailWeight s)
  have hlim : Tendsto P atTop (𝓝 0) := by
    have h0 : Tendsto gaussTailWeight atTop (𝓝 0) := by
      have hx : Tendsto (fun s : ℝ => s ^ 2 / 4) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num)
      have harg : Tendsto (fun s : ℝ => -(s ^ 2 / 4)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp hx
      change Tendsto (fun s : ℝ => Real.exp (-(s ^ 2 / 4))) atTop (𝓝 0)
      exact Real.tendsto_exp_atBot.comp harg
    have hsum := (tendsto_gaussTailWeight_fourth_mul 0).add
      ((tendsto_gaussTailWeight_sq_mul 0).const_mul 8)
    have hsum' : Tendsto (fun s : ℝ => (s ^ 4 + 8 * s ^ 2) * gaussTailWeight s)
        atTop (𝓝 0) := by
      convert hsum using 1 <;> try rfl
      · ext s
        ring
      · simp
    have hsum'' := hsum'.add (h0.const_mul 32)
    have hsum''' : Tendsto (fun s : ℝ => (s ^ 4 + 8 * s ^ 2 + 32) * gaussTailWeight s)
        atTop (𝓝 0) := by
      convert hsum'' using 1 <;> try rfl
      · ext s
        ring
      · simp
    simpa [P] using hsum'''.const_mul (-2)
  have hcont : ContinuousWithinAt P (Ici r) r := by
    dsimp [P]
    fun_prop [gaussTailWeight]
  have hderiv : ∀ s ∈ Ioi r, HasDerivAt P (s ^ 5 * gaussTailWeight s) s := by
    intro s hs
    have hpoly : HasDerivAt (fun x : ℝ => x ^ 4 + 8 * x ^ 2 + 32)
        (4 * s ^ 3 + 16 * s) s := by
      have h := ((hasDerivAt_pow 4 s).add ((hasDerivAt_pow 2 s).const_mul 8)).add_const 32
      have h' := h.congr_deriv (show
          (4 * s ^ (4 - 1) + 8 * (2 * s ^ (2 - 1)) : ℝ) =
            4 * s ^ 3 + 16 * s by norm_num; ring)
      simpa [pow_one] using h'
    have h := (hasDerivAt_const s (-2 : ℝ)).mul
      (hpoly.mul (hasDerivAt_gaussTailWeight s))
    convert h using 1 <;> try rfl
    ring_nf
  have hint : IntegrableOn (fun s : ℝ => s ^ 5 * gaussTailWeight s) (Ioi r) := by
    simpa [gaussTailWeight] using
      (integrableOn_pow_mul_gauss 5).mono_set (Ioi_subset_Ioi hr)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  simpa [P, gaussTailWeight, mul_comm, mul_left_comm, mul_assoc] using h

/-- A polynomial Gaussian tail is bounded by a weaker Gaussian with an explicit Gamma constant. -/
theorem integral_Ioi_pow_gauss_le {k : ℕ} {r : ℝ} (hr : 1 ≤ r) :
    ∫ s in Ioi r, s ^ k * Real.exp (-(s ^ 2 / 4)) ≤
      Real.exp (-(r ^ 2 / 8)) *
        (Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1)) := by
  have hr0 : 0 ≤ r := by linarith
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hf : IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(s ^ 2 / 4))) (Ioi r) :=
    (integrableOn_pow_mul_gauss k).mono_set (Ioi_subset_Ioi hr0)
  have hg0base : IntegrableOn (fun s : ℝ => s ^ (k : ℝ) *
      Real.exp (-((1 / 8 : ℝ) * s))) (Ioi r) :=
    (Special.integrableOn_rpow_mul_exp_neg_mul_Ioi hk
      (by norm_num : (0 : ℝ) < 1 / 8)).mono_set (Ioi_subset_Ioi hr0)
  have hfun : (fun s : ℝ => s ^ (k : ℝ) * Real.exp (-(s / 8))) =
      fun s => s ^ (k : ℝ) * Real.exp (-((1 / 8 : ℝ) * s)) := by
    funext s
    congr 2 <;> ring
  rw [← hfun] at hg0base
  have hg0 : IntegrableOn (fun s : ℝ => s ^ (k : ℝ) * Real.exp (-(s / 8))) (Ioi r) := hg0base
  have hg : IntegrableOn (fun s : ℝ => Real.exp (-(r ^ 2 / 8)) *
      (s ^ (k : ℝ) * Real.exp (-(s / 8)))) (Ioi r) := hg0.const_mul _
  have hpt : ∀ s ∈ Ioi r, s ^ k * Real.exp (-(s ^ 2 / 4)) ≤
      Real.exp (-(r ^ 2 / 8)) * (s ^ (k : ℝ) * Real.exp (-(s / 8))) := by
    intro s hs
    have hrs : r ≤ s := le_of_lt hs
    have hs1 : 1 ≤ s := le_trans hr (le_of_lt hs)
    have hs_sq : s ≤ s ^ 2 := by nlinarith
    have hsq : r ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - r)]
    have hexp : Real.exp (-(s ^ 2 / 4)) ≤
        Real.exp (-(r ^ 2 / 8)) * Real.exp (-(s / 8)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      s ^ k * Real.exp (-(s ^ 2 / 4)) ≤
          s ^ k * (Real.exp (-(r ^ 2 / 8)) * Real.exp (-(s / 8))) :=
        mul_le_mul_of_nonneg_left hexp (pow_nonneg (by linarith : (0 : ℝ) ≤ s) k)
      _ = Real.exp (-(r ^ 2 / 8)) * (s ^ (k : ℝ) * Real.exp (-(s / 8))) := by
        rw [Real.rpow_natCast]
        ring
  have hmono := setIntegral_mono_on hf hg measurableSet_Ioi hpt
  calc
    ∫ s in Ioi r, s ^ k * Real.exp (-(s ^ 2 / 4)) ≤
        ∫ s in Ioi r, Real.exp (-(r ^ 2 / 8)) *
          (s ^ (k : ℝ) * Real.exp (-(s / 8))) := hmono
    _ = Real.exp (-(r ^ 2 / 8)) *
        ∫ s in Ioi r, s ^ (k : ℝ) * Real.exp (-(s / 8)) := by rw [integral_const_mul]
    _ ≤ Real.exp (-(r ^ 2 / 8)) *
        (Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have ht := Special.integral_Ioi_rpow_mul_exp_neg_le
        (a := (k : ℝ)) (b := 1 / 8) (L := r)
        hk (by norm_num) hr0
      have ht' : (∫ s in Ioi r, s ^ (k : ℝ) * Real.exp (-(s / 8))) ≤
          Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1) * Real.exp (-(r / 16)) := by
        have hscale : 2 / (1 / 8 : ℝ) = 16 := by norm_num
        have hrate : -(1 / 8 * r) / 2 = -(r / 16) := by ring
        rw [hscale, hrate] at ht
        have hintegrand : (fun s : ℝ => s ^ (k : ℝ) * Real.exp (-(s / 8))) =
            fun t => t ^ (k : ℝ) * Real.exp (-((1 / 8 : ℝ) * t)) := by
          funext t
          congr 2 <;> ring
        rw [hintegrand]
        exact ht
      calc
        ∫ s in Ioi r, s ^ (k : ℝ) * Real.exp (-(s / 8)) ≤
            Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1) * Real.exp (-(r / 16)) := ht'
        _ ≤ Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1) := by
          have he : Real.exp (-(r / 16)) ≤ 1 := by
            apply Real.exp_le_one_iff.mpr
            linarith
          have hA : 0 ≤ Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1) := by positivity
          simpa [mul_one] using mul_le_mul_of_nonneg_left he hA

/-- The actual growing-mode vorticity has every polynomial moment integrable on the positive
half-line. -/
theorem integrableOn_pow_mul_norm_modeVort {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ k * ‖modeVort c F s‖) (Ioi 0) := by
  have hn := (integrableOn_pow_mul_modeVort hF k).norm
  refine IntegrableOn.congr_fun hn (fun s hs => ?_) measurableSet_Ioi
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt hs)]

/-- Sharp cubic absolute tail for the actual mode vorticity. -/
theorem integral_Ioi_three_norm_modeVort_le {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ‖F t‖ ≤ M) {r : ℝ} (hr : 1 ≤ r) :
    ∫ s in Ioi r, s ^ 3 * ‖modeVort c F s‖ ≤
      (M / |c.im|) * (r ^ 4 / 2 + 8 * r ^ 2 + 32) * gaussTailWeight r := by
  let A : ℝ := M / |c.im|
  have hr0 : 0 ≤ r := by linarith
  have h3 : IntegrableOn (fun s : ℝ => s ^ 3 * ‖modeVort c F s‖) (Ioi r) :=
    (integrableOn_pow_mul_norm_modeVort hF 3).mono_set (Ioi_subset_Ioi hr0)
  have h5e : IntegrableOn (fun s : ℝ => s ^ 5 * gaussTailWeight s) (Ioi r) := by
    simpa [gaussTailWeight] using
      (integrableOn_pow_mul_gauss 5).mono_set (Ioi_subset_Ioi hr0)
  have h3e : IntegrableOn (fun s : ℝ => s ^ 3 * gaussTailWeight s) (Ioi r) := by
    simpa [gaussTailWeight] using
      (integrableOn_pow_mul_gauss 3).mono_set (Ioi_subset_Ioi hr0)
  let g : ℝ → ℝ := fun s => A / 4 * (s ^ 5 * gaussTailWeight s) +
    (2 * A) * (s ^ 3 * gaussTailWeight s)
  have hg : IntegrableOn g (Ioi r) := by
    dsimp [g]
    exact (h5e.const_mul _).add (h3e.const_mul _)
  have hpt : ∀ s ∈ Ioi r, s ^ 3 * ‖modeVort c F s‖ ≤ g s := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hr0 (le_of_lt hs)
    have hn := norm_modeVort_le hF.im_ne_zero hM0 hM s
    dsimp [g, A]
    calc
      s ^ 3 * ‖modeVort c F s‖ ≤
          s ^ 3 * (M / |c.im| * ((s ^ 2 / 4 + 2) * gaussTailWeight s)) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = M / |c.im| / 4 * (s ^ 5 * gaussTailWeight s) +
            (2 * (M / |c.im|)) * (s ^ 3 * gaussTailWeight s) := by ring
  have hmono := setIntegral_mono_on h3 hg measurableSet_Ioi hpt
  have hmajor : (fun s : ℝ => g s) = fun s =>
      A / 4 * (s ^ 5 * gaussTailWeight s) +
        (2 * A) * (s ^ 3 * gaussTailWeight s) := rfl
  have h5 := integral_Ioi_gaussTailWeight_five_eq hr0
  have h3' := integral_Ioi_gaussTailWeight_three_eq hr0
  have hcoef1 : 0 ≤ A / 4 := by positivity
  have hcoef2 : 0 ≤ 2 * A := by positivity
  calc
    ∫ s in Ioi r, s ^ 3 * ‖modeVort c F s‖ ≤ ∫ s in Ioi r, g s := hmono
    _ = (A / 4) * (∫ s in Ioi r, s ^ 5 * gaussTailWeight s) +
        (2 * A) * (∫ s in Ioi r, s ^ 3 * gaussTailWeight s) := by
          rw [hmajor, integral_add (h5e.const_mul _) (h3e.const_mul _),
            integral_const_mul, integral_const_mul]
    _ ≤ (A / 4) * (2 * (r ^ 4 + 8 * r ^ 2 + 32) * gaussTailWeight r) +
      (2 * A) * (2 * (r ^ 2 + 4) * gaussTailWeight r) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_of_eq h5) hcoef1)
          (mul_le_mul_of_nonneg_left (le_of_eq h3') hcoef2)
    _ = (M / |c.im|) * (r ^ 4 / 2 + 8 * r ^ 2 + 32) * gaussTailWeight r := by
      dsimp [A]
      ring


/-- Sharp first absolute tail moment for the actual mode vorticity. -/
theorem integral_Ioi_one_norm_modeVort_le {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ‖F t‖ ≤ M) {r : ℝ} (hr : 1 ≤ r) :
    ∫ s in Ioi r, s * ‖modeVort c F s‖ ≤
      (M / |c.im|) * (r ^ 2 / 2 + 6) * gaussTailWeight r := by
  let A : ℝ := M / |c.im|
  have hr0 : 0 ≤ r := by linarith
  have h1 : IntegrableOn (fun s : ℝ => s * ‖modeVort c F s‖) (Ioi r) := by
    simpa [pow_one] using
      (integrableOn_pow_mul_norm_modeVort hF 1).mono_set (Ioi_subset_Ioi hr0)
  have h3e : IntegrableOn (fun s : ℝ => s ^ 3 * gaussTailWeight s) (Ioi r) := by
    simpa [gaussTailWeight] using
      (integrableOn_pow_mul_gauss 3).mono_set (Ioi_subset_Ioi hr0)
  have h1e : IntegrableOn (fun s : ℝ => s * gaussTailWeight s) (Ioi r) := by
    simpa [gaussTailWeight] using
      (integrableOn_pow_mul_gauss 1).mono_set (Ioi_subset_Ioi hr0)
  let g : ℝ → ℝ := fun s => A / 4 * (s ^ 3 * gaussTailWeight s) +
    (2 * A) * (s * gaussTailWeight s)
  have hg : IntegrableOn g (Ioi r) := by
    dsimp [g]
    exact (h3e.const_mul _).add (h1e.const_mul _)
  have hpt : ∀ s ∈ Ioi r, s * ‖modeVort c F s‖ ≤ g s := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hr0 (le_of_lt hs)
    have hn := norm_modeVort_le hF.im_ne_zero hM0 hM s
    dsimp [g, A]
    calc
      s * ‖modeVort c F s‖ ≤
          s * (M / |c.im| * ((s ^ 2 / 4 + 2) * gaussTailWeight s)) :=
        mul_le_mul_of_nonneg_left hn hs0
      _ = M / |c.im| / 4 * (s ^ 3 * gaussTailWeight s) +
            (2 * (M / |c.im|)) * (s * gaussTailWeight s) := by ring
  have hmono := setIntegral_mono_on h1 hg measurableSet_Ioi hpt
  have hmajor : (fun s : ℝ => g s) = fun s =>
      A / 4 * (s ^ 3 * gaussTailWeight s) +
        (2 * A) * (s * gaussTailWeight s) := rfl
  have h3 := integral_Ioi_gaussTailWeight_three_eq hr0
  have h1' := integral_Ioi_gaussTailWeight_one_eq hr0
  have hcoef1 : 0 ≤ A / 4 := by positivity
  have hcoef2 : 0 ≤ 2 * A := by positivity
  calc
    ∫ s in Ioi r, s * ‖modeVort c F s‖ ≤ ∫ s in Ioi r, g s := hmono
    _ = (A / 4) * (∫ s in Ioi r, s ^ 3 * gaussTailWeight s) +
        (2 * A) * (∫ s in Ioi r, s * gaussTailWeight s) := by
          rw [hmajor, integral_add (h3e.const_mul _) (h1e.const_mul _),
            integral_const_mul, integral_const_mul]
    _ ≤ (A / 4) * (2 * (r ^ 2 + 4) * gaussTailWeight r) +
        (2 * A) * (2 * gaussTailWeight r) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (le_of_eq h3) hcoef1)
            (mul_le_mul_of_nonneg_left (le_of_eq h1') hcoef2)
    _ = (M / |c.im|) * (r ^ 2 / 2 + 6) * gaussTailWeight r := by
      dsimp [A]
      ring

/-- Differentiating a complex-valued tail integral at its lower endpoint. -/
theorem hasDerivAt_integral_Ioi_complex {a : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioi a))
    (hint : ∀ ρ, a < ρ → IntegrableOn f (Ioi ρ))
    {ρ₀ : ℝ} (hρ₀ : a < ρ₀) :
    HasDerivAt (fun ρ => ∫ r in Ioi ρ, f r) (-f ρ₀) ρ₀ := by
  set ρ₁ := (a + ρ₀) / 2 with hρ₁
  have h1 : a < ρ₁ := by rw [hρ₁]; linarith
  have h2 : ρ₁ < ρ₀ := by rw [hρ₁]; linarith
  have hsub : uIcc ρ₁ ρ₀ ⊆ Ioi a := by
    rw [uIcc_of_le h2.le]
    intro x hx
    exact lt_of_lt_of_le h1 hx.1
  have hii : IntervalIntegrable f volume ρ₁ ρ₀ := (hf.mono hsub).intervalIntegrable
  have hd : HasDerivAt (fun u => ∫ x in ρ₁..u, f x) (f ρ₀) ρ₀ :=
    intervalIntegral.integral_hasDerivAt_right hii
      (hf.stronglyMeasurableAtFilter isOpen_Ioi ρ₀ hρ₀)
      (hf.continuousAt (isOpen_Ioi.mem_nhds hρ₀))
  have hd' := (hasDerivAt_const ρ₀ (∫ r in Ioi ρ₁, f r)).sub hd
  rw [zero_sub] at hd'
  refine hd'.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds h2] with ρ hρ
  have hρ' : ρ₁ ≤ ρ := le_of_lt hρ
  show ∫ r in Ioi ρ, f r = (∫ r in Ioi ρ₁, f r) - ∫ x in ρ₁..ρ, f x
  rw [intervalIntegral.integral_of_le hρ', ← Ioc_union_Ioi_eq_Ioi hρ',
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((hint ρ₁ h1).mono_set Ioc_subset_Ioi_self) (hint ρ (lt_trans h1 hρ))]
  ring

/-- The inverse-radius moment is locally integrable on every positive tail. -/
theorem integrableOn_inv_mul_modeVort {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * modeVort c F s) (Ioi r) := by
  have hbase : IntegrableOn (fun s : ℝ => ‖modeVort c F s‖) (Ioi r) := by
    simpa using (integrableOn_pow_mul_norm_modeVort hF 0).mono_set
      (Ioi_subset_Ioi hr.le)
  have hmajor : IntegrableOn (fun s : ℝ => r⁻¹ * ‖modeVort c F s‖) (Ioi r) :=
    hbase.const_mul (r⁻¹)
  have hinv : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹) (Ioi r) :=
    Complex.continuous_ofReal.continuousOn.inv₀ (fun s hs =>
      by exact_mod_cast (ne_of_gt (lt_trans hr hs)))
  have hcont : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹ * modeVort c F s) (Ioi r) :=
    hinv.mul ((continuousOn_modeVort hF).mono (Ioi_subset_Ioi hr.le))
  refine hmajor.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := lt_trans hr hs
  have hinv_le : s⁻¹ ≤ r⁻¹ := inv_anti₀ hr hs.le
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  exact mul_le_mul_of_nonneg_right hinv_le (norm_nonneg (modeVort c F s))

/-- The inverse-radius vorticity tail is smooth on every positive radius interval; its derivative is
minus the actual inverse-radius vorticity. -/
theorem contDiffOn_inv_modeVort_tail {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) :
    ContDiffOn ℝ ∞ (fun r : ℝ => ∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s) (Ioi 0) := by
  let T : ℝ → ℂ := fun r => ∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s
  let f : ℝ → ℂ := fun r => (r : ℂ)⁻¹ * modeVort c F r
  let g : ℝ → ℂ := fun r => (r : ℂ)⁻¹ * modeQ c F (r : ℂ)
  have hfg : Set.EqOn f g (Ioi 0) := by
    intro r hr
    have hr' : 0 < r := by simpa using hr
    simp [f, g, modeQ_eq_modeVort_ofReal hr']
  have hOfReal : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  have hOfRealOn : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ)) (Ioi 0) := by
    exact hOfReal.contDiffOn
  have hInv : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ)⁻¹) (Ioi 0) := by
    have hmap : MapsTo (fun r : ℝ => (r : ℂ)) (Ioi 0) ({0}ᶜ) := by
      intro r hr
      have hr' : 0 < r := by simpa using hr
      change (r : ℂ) ≠ 0
      exact_mod_cast (ne_of_gt hr')
    exact (contDiffOn_inv (𝕜 := ℝ) (n := ∞)).comp hOfRealOn hmap
  have hg : ContDiffOn ℝ ∞ g (Ioi 0) := by
    dsimp [g]
    exact hInv.mul ((contDiff_modeQ hF).comp hOfReal).contDiffOn
  have hcontF : ContinuousOn f (Ioi 0) := by
    dsimp [f]
    have hinv : ContinuousOn (fun r : ℝ => (r : ℂ)⁻¹) (Ioi 0) :=
      Complex.continuous_ofReal.continuousOn.inv₀ (fun r hr => by exact_mod_cast hr.ne')
    exact hinv.mul (continuousOn_modeVort hF)
  have hintF : ∀ ρ : ℝ, 0 < ρ → IntegrableOn f (Ioi ρ) := by
    intro ρ hρ
    exact integrableOn_inv_mul_modeVort hF hρ
  have hderiv : Set.EqOn (deriv T) (fun r => -g r) (Ioi 0) := by
    intro r hr
    have hr' : 0 < r := by simpa using hr
    have h := hasDerivAt_integral_Ioi_complex hcontF hintF hr'
    have hd := h.deriv
    simpa [T, f, g, modeQ_eq_modeVort_ofReal hr'] using hd
  have hdiff : DifferentiableOn ℝ T (Ioi 0) := by
    intro r hr
    have hr' : 0 < r := by simpa using hr
    exact (hasDerivAt_integral_Ioi_complex hcontF hintF hr').differentiableAt.differentiableWithinAt
  have hderivCont : ContDiffOn ℝ ∞ (deriv T) (Ioi 0) :=
    hg.neg.congr (fun r hr => hderiv hr)
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  exact ⟨hdiff, hderivCont⟩



/-- Pointwise derivative identity for the inverse-radius tail on positive radii. -/
theorem deriv_inv_modeVort_tail_eq {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) :
    Set.EqOn (deriv (fun r : ℝ => ∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s))
      (fun r => -((r : ℂ)⁻¹ * modeVort c F r)) (Ioi 0) := by
  intro r hr
  have hr' : 0 < r := by simpa using hr
  have hcont : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹ * modeVort c F s) (Ioi 0) := by
    have hinv : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹) (Ioi 0) :=
      Complex.continuous_ofReal.continuousOn.inv₀ (fun s hs => by exact_mod_cast hs.ne')
    exact hinv.mul (continuousOn_modeVort hF)
  have hint : ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * modeVort c F s) (Ioi ρ) := by
    intro ρ hρ
    exact integrableOn_inv_mul_modeVort hF hρ
  have h := hasDerivAt_integral_Ioi_complex hcont hint hr'
  simpa using h.deriv

/-- Every positive-order derivative of the inverse-radius tail is the corresponding derivative of
its local integrand, obtained by iterating the exact endpoint derivative identity. -/
theorem iteratedDeriv_succ_inv_modeVort_tail {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {n : ℕ} {r : ℝ} (hr : 0 < r) :
    iteratedDeriv (n + 1) (fun x : ℝ => ∫ s in Ioi x, (s : ℂ)⁻¹ * modeVort c F s) r =
      iteratedDeriv n (fun x : ℝ => -((x : ℂ)⁻¹ * modeVort c F x)) r := by
  rw [iteratedDeriv_succ']
  exact (deriv_inv_modeVort_tail_eq hF).iteratedDeriv_of_isOpen isOpen_Ioi n
    (Set.mem_Ioi.mpr hr)

/-- Every positive-order radial derivative of the inverse-radius tail has a polynomial times the
sharp Gaussian envelope. -/
theorem exists_norm_iteratedDeriv_inv_modeVort_tail_bound {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) (n : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv (n + 1)
        (fun x : ℝ => ∫ s in Ioi x, (s : ℂ)⁻¹ * modeVort c F s) r‖ ≤
        C * (1 + r) ^ N * gaussTailWeight r := by
  obtain ⟨C, N, hprod⟩ := exists_norm_iteratedDeriv_inv_mul_modeVort_bound hF n
  refine ⟨C, N, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  rw [iteratedDeriv_succ_inv_modeVort_tail hF hr0]
  have hneg : (fun x : ℝ => -((x : ℂ)⁻¹ * modeVort c F x)) =
      fun x : ℝ => (-1 : ℂ) * ((x : ℂ)⁻¹ * modeVort c F x) := by
    funext x
    ring
  rw [hneg, iteratedDeriv_const_mul_field]
  simpa [norm_neg] using hprod r hr

/-- Polynomially weighted tails of the actual growing-mode vorticity have Gaussian decay, with
the constants inherited from its pointwise mode bound. -/
theorem integral_Ioi_pow_norm_modeVort_le {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ‖F t‖ ≤ M) {k : ℕ} {r : ℝ} (hr : 1 ≤ r) :
    ∫ s in Ioi r, s ^ k * ‖modeVort c F s‖ ≤
      (M / |c.im|) *
        (Real.Gamma (((k + 2 : ℕ) : ℝ) + 1) *
            16 ^ (((k + 2 : ℕ) : ℝ) + 1) / 4 +
          2 * Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1)) *
        Real.exp (-(r ^ 2 / 8)) := by
  have hr0 : 0 ≤ r := by linarith
  let A : ℝ := M / |c.im|
  let e : ℝ → ℝ := fun s => Real.exp (-(s ^ 2 / 4))
  let g : ℝ → ℝ := fun s => A * ((s ^ (k + 2) / 4 + 2 * s ^ k) * e s)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hf0 := integrableOn_pow_mul_norm_modeVort hF k
  have hf := hf0.mono_set (Ioi_subset_Ioi hr0)
  have hgBase : IntegrableOn
      (fun s : ℝ => (s ^ (k + 2) / 4 + 2 * s ^ k) * e s) (Ioi 0) := by
    have h := ((integrableOn_pow_mul_gauss (k + 2)).div_const 4).add
      ((integrableOn_pow_mul_gauss k).const_mul 2)
    refine IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
    simp [e]
    ring
  have hgAll : IntegrableOn (fun s : ℝ => A *
      ((s ^ (k + 2) / 4 + 2 * s ^ k) * e s)) (Ioi 0) := hgBase.const_mul A
  have hg : IntegrableOn (fun s : ℝ => A *
      ((s ^ (k + 2) / 4 + 2 * s ^ k) * e s)) (Ioi r) :=
    IntegrableOn.mono_set hgAll (Ioi_subset_Ioi hr0)
  have hpt : ∀ s ∈ Ioi r, s ^ k * ‖modeVort c F s‖ ≤ g s := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt (lt_of_le_of_lt hr0 hs)
    have hmode := norm_modeVort_le hF.im_ne_zero hM0 hM s
    calc
      s ^ k * ‖modeVort c F s‖ ≤
          s ^ k * (A * ((s ^ 2 / 4 + 2) * e s)) :=
        mul_le_mul_of_nonneg_left hmode (pow_nonneg hs0 k)
      _ = g s := by simp [g, A, e]; ring
  have htail := setIntegral_mono_on hf hg measurableSet_Ioi hpt
  have hEq : g = fun s : ℝ => A / 4 * (s ^ (k + 2) * e s) +
      (2 * A) * (s ^ k * e s) := by
    funext s
    simp [g, e]
    ring
  have hi2 : IntegrableOn (fun s : ℝ => s ^ (k + 2) * e s) (Ioi r) :=
    (integrableOn_pow_mul_gauss (k + 2)).mono_set (Ioi_subset_Ioi hr0)
  have hi0 : IntegrableOn (fun s : ℝ => s ^ k * e s) (Ioi r) :=
    (integrableOn_pow_mul_gauss k).mono_set (Ioi_subset_Ioi hr0)
  have hmajor : ∫ s in Ioi r, g s =
      (A / 4) * (∫ s in Ioi r, s ^ (k + 2) * e s) +
        (2 * A) * (∫ s in Ioi r, s ^ k * e s) := by
    rw [hEq]
    rw [integral_add (hi2.const_mul _) (hi0.const_mul _)]
    rw [integral_const_mul, integral_const_mul]
  have hk2 := integral_Ioi_pow_gauss_le (k := k + 2) hr
  have hk := integral_Ioi_pow_gauss_le (k := k) hr
  have hcoef2 : 0 ≤ A / 4 := by positivity
  have hcoef0 : 0 ≤ 2 * A := by positivity
  calc
    ∫ s in Ioi r, s ^ k * ‖modeVort c F s‖ ≤ ∫ s in Ioi r, g s := htail
    _ = (A / 4) * (∫ s in Ioi r, s ^ (k + 2) * e s) +
        (2 * A) * (∫ s in Ioi r, s ^ k * e s) := hmajor
    _ ≤ (A / 4) * (Real.exp (-(r ^ 2 / 8)) *
          (Real.Gamma (((k + 2 : ℕ) : ℝ) + 1) * 16 ^ (((k + 2 : ℕ) : ℝ) + 1))) +
        (2 * A) * (Real.exp (-(r ^ 2 / 8)) *
          (Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1))) := by
      simpa [e] using add_le_add
        (mul_le_mul_of_nonneg_left hk2 hcoef2)
        (mul_le_mul_of_nonneg_left hk hcoef0)
    _ = (M / |c.im|) *
        (Real.Gamma (((k + 2 : ℕ) : ℝ) + 1) *
            16 ^ (((k + 2 : ℕ) : ℝ) + 1) / 4 +
          2 * Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1)) *
        Real.exp (-(r ^ 2 / 8)) := by simp [A]; ring

/-- The same Gaussian tail controls the actual complex moment of the mode. -/
theorem norm_integral_Ioi_pow_modeVort_le {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ‖F t‖ ≤ M) {k : ℕ} {r : ℝ} (hr : 1 ≤ r) :
    ‖∫ s in Ioi r, (s : ℂ) ^ k * modeVort c F s‖ ≤
      (M / |c.im|) *
        (Real.Gamma (((k + 2 : ℕ) : ℝ) + 1) *
            16 ^ (((k + 2 : ℕ) : ℝ) + 1) / 4 +
          2 * Real.Gamma ((k : ℝ) + 1) * 16 ^ ((k : ℝ) + 1)) *
        Real.exp (-(r ^ 2 / 8)) := by
  have hr0 : 0 ≤ r := by linarith
  have hiC : IntegrableOn (fun s : ℝ => (s : ℂ) ^ k * modeVort c F s) (Ioi r) :=
    (integrableOn_pow_mul_modeVort hF k).mono_set (Ioi_subset_Ioi hr0)
  have hiR : IntegrableOn (fun s : ℝ => s ^ k * ‖modeVort c F s‖) (Ioi r) :=
    (integrableOn_pow_mul_norm_modeVort hF k).mono_set (Ioi_subset_Ioi hr0)
  have hpt : ∀ s ∈ Ioi r,
      ‖(s : ℂ) ^ k * modeVort c F s‖ ≤ s ^ k * ‖modeVort c F s‖ := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hr0 (le_of_lt hs)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs0]
  have hptAE : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioi r)),
      ‖(s : ℂ) ^ k * modeVort c F s‖ ≤ s ^ k * ‖modeVort c F s‖ :=
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => hpt s hs
  have hnorm := norm_integral_le_of_norm_le hiR hptAE
  refine hnorm.trans ?_
  exact integral_Ioi_pow_norm_modeVort_le hF hM0 hM hr

/-- Gaussian control of the inverse-radius complex tail moment. -/
theorem norm_integral_Ioi_inv_modeVort_le {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ‖F t‖ ≤ M) {r : ℝ} (hr : 1 ≤ r) :
    ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ ≤
      (M / |c.im|) *
        (Real.Gamma (((0 + 2 : ℕ) : ℝ) + 1) *
            16 ^ (((0 + 2 : ℕ) : ℝ) + 1) / 4 +
          2 * Real.Gamma ((0 : ℝ) + 1) * 16 ^ ((0 : ℝ) + 1)) *
        Real.exp (-(r ^ 2 / 8)) := by
  have hi : IntegrableOn (fun s : ℝ => ‖modeVort c F s‖) (Ioi r) := by
    simpa using (integrableOn_pow_mul_norm_modeVort hF 0).mono_set
      (Ioi_subset_Ioi (show 0 ≤ r by linarith))
  have hpt : ∀ s ∈ Ioi r,
      ‖(s : ℂ)⁻¹ * modeVort c F s‖ ≤ ‖modeVort c F s‖ := by
    intro s hs
    have hs0 : 0 < s := lt_trans (by linarith : (0 : ℝ) < r) hs
    have hs1 : 1 ≤ s := le_trans hr hs.le
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have hsInv : s⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hs0]
      linarith
    calc
      s⁻¹ * ‖modeVort c F s‖ ≤ 1 * ‖modeVort c F s‖ :=
        mul_le_mul_of_nonneg_right hsInv (norm_nonneg (modeVort c F s))
      _ = ‖modeVort c F s‖ := one_mul _
  have hptAE : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioi r)),
      ‖(s : ℂ)⁻¹ * modeVort c F s‖ ≤ ‖modeVort c F s‖ :=
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => hpt s hs
  have hnorm := norm_integral_le_of_norm_le hi hptAE
  have h0 := integral_Ioi_pow_norm_modeVort_le hF hM0 hM (k := 0) hr
  exact hnorm.trans (by simpa [pow_zero, Nat.cast_zero] using h0)

/-- The derivative of the actual far-field remainder is the inverse-radius vorticity tail. -/
theorem hasDerivAt_modeRadial_farField_remainder {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun x : ℝ => (x : ℂ) ^ 2 * modeRadial F x +
        (1 / 4 : ℂ) * modeQuadrupole c F)
      (-((r : ℂ) ^ 3 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s))) r := by
  let tail3 : ℝ → ℂ := fun x => ∫ s in Ioi x, (s : ℂ) ^ 3 * modeVort c F s
  let tailInv : ℝ → ℂ := fun x => ∫ s in Ioi x, (s : ℂ)⁻¹ * modeVort c F s
  let tailR : ℝ → ℂ := fun x => (1 / 4 : ℂ) * (tail3 x - (x : ℂ) ^ 4 * tailInv x)
  have hcont3 : ContinuousOn (fun s : ℝ => (s : ℂ) ^ 3 * modeVort c F s) (Ioi 0) :=
    (Complex.continuous_ofReal.continuousOn.pow 3).mul (continuousOn_modeVort hF)
  have hcontInv : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹ * modeVort c F s) (Ioi 0) := by
    have hinv : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹) (Ioi 0) :=
      Complex.continuous_ofReal.continuousOn.inv₀ (fun s hs => by exact_mod_cast hs.ne')
    exact hinv.mul (continuousOn_modeVort hF)
  have hint3 : ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun s : ℝ => (s : ℂ) ^ 3 * modeVort c F s) (Ioi ρ) := by
    intro ρ hρ
    exact (integrableOn_pow_mul_modeVort hF 3).mono_set (Ioi_subset_Ioi hρ.le)
  have hintInv : ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * modeVort c F s) (Ioi ρ) := by
    intro ρ hρ
    exact integrableOn_inv_mul_modeVort hF hρ
  have htail3 : HasDerivAt tail3 (-((r : ℂ) ^ 3 * modeVort c F r)) r := by
    simpa [tail3] using
      hasDerivAt_integral_Ioi_complex hcont3 hint3 hr
  have htailInv : HasDerivAt tailInv (-((r : ℂ)⁻¹ * modeVort c F r)) r := by
    simpa [tailInv] using
      hasDerivAt_integral_Ioi_complex hcontInv hintInv hr
  have hp4 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 4) (4 * (r : ℂ) ^ 3) r := by
    have hp := (hasDerivAt_pow 4 r).ofReal_comp
    convert hp using 1 <;> push_cast <;> ring
  have hcalc := (hasDerivAt_const r (1 / 4 : ℂ)).mul
    (htail3.sub (hp4.mul htailInv))
  have htail : HasDerivAt tailR
      (-((r : ℂ) ^ 3 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s))) r := by
    have hcomm : tailInv r = ∫ s in Ioi r, modeVort c F s * (s : ℂ)⁻¹ := by
      dsimp [tailInv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      ring
    have hcomm' : (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s) = tailInv r := by
      calc
        _ = ∫ s in Ioi r, modeVort c F s * (s : ℂ)⁻¹ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          ring
        _ = tailInv r := hcomm.symm
    have hderivEq :
        0 * (tail3 - (fun x : ℝ => (x : ℂ) ^ 4) * tailInv) r +
          (1 / 4 : ℂ) *
            (-((r : ℂ) ^ 3 * modeVort c F r) -
              (4 * (r : ℂ) ^ 3 * tailInv r +
                (r : ℂ) ^ 4 * (-((r : ℂ)⁻¹ * modeVort c F r)))) =
        -((r : ℂ) ^ 3 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s)) := by
      simp only [zero_mul]
      rw [hcomm']
      field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
      ring
    have hcalc' := hcalc.congr_deriv hderivEq
    convert hcalc' using 1 <;> try rfl <;> ring
  have heq : (fun x : ℝ => (x : ℂ) ^ 2 * modeRadial F x +
        (1 / 4 : ℂ) * modeQuadrupole c F) =ᶠ[𝓝 r] tailR := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact modeRadial_farField_remainder_eq_tail hF hx
  simpa only [neg_mul] using htail.congr_of_eventuallyEq heq

/-- O10 far-field estimate for the remainder after its nonzero quadrupole limit. -/
theorem norm_modeRadial_farField_remainder_le {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {r : ℝ} (hr : 1 ≤ r) :
    ‖(r : ℂ) ^ 2 * modeRadial F r + (1 / 4 : ℂ) * modeQuadrupole c F‖ ≤
      ((Classical.choose (hF.exists_bound) / |c.im|) / 4) *
        (r ^ 4 + 14 * r ^ 2 + 32) * gaussTailWeight r := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hM0, hM⟩ := Classical.choose_spec (hF.exists_bound)
  let A : ℝ := Classical.choose (hF.exists_bound) / |c.im|
  have h3abs := integral_Ioi_three_norm_modeVort_le hF hM0 hM hr
  have h1abs := integral_Ioi_one_norm_modeVort_le hF hM0 hM hr
  have h3int : IntegrableOn
      (fun s : ℝ => (s : ℂ) ^ 3 * modeVort c F s) (Ioi r) :=
    (integrableOn_pow_mul_modeVort hF 3).mono_set
      (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ r))
  have h3real : IntegrableOn
      (fun s : ℝ => s ^ 3 * ‖modeVort c F s‖) (Ioi r) :=
    (integrableOn_pow_mul_norm_modeVort hF 3).mono_set
      (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ r))
  have h3pt : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioi r)),
      ‖(s : ℂ) ^ 3 * modeVort c F s‖ ≤ s ^ 3 * ‖modeVort c F s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := le_trans (by linarith : (0 : ℝ) ≤ r) (le_of_lt hs)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  have h3complex := norm_integral_le_of_norm_le h3real h3pt
  have h3bound : ‖∫ s in Ioi r, (s : ℂ) ^ 3 * modeVort c F s‖ ≤
      A * (r ^ 4 / 2 + 8 * r ^ 2 + 32) * gaussTailWeight r := by
    exact h3complex.trans (by simpa [A] using h3abs)
  have hInvInt : IntegrableOn
      (fun s : ℝ => (s : ℂ)⁻¹ * modeVort c F s) (Ioi r) :=
    integrableOn_inv_mul_modeVort hF hr0
  have h1real : IntegrableOn
      (fun s : ℝ => s * ‖modeVort c F s‖) (Ioi r) := by
    simpa [pow_one] using
      (integrableOn_pow_mul_norm_modeVort hF 1).mono_set
        (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ r))
  have hInvpt : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioi r)),
      ‖(s : ℂ)⁻¹ * modeVort c F s‖ ≤ (s / r ^ 2) * ‖modeVort c F s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hr0 hs
    have hrs : r ≤ s := le_of_lt hs
    have hinv : s⁻¹ ≤ s / r ^ 2 := by
      have hr2 : r ^ 2 ≠ 0 := ne_of_gt (pow_pos hr0 2)
      have hsne : s ≠ 0 := ne_of_gt hs0
      field_simp [hr2, hsne]
      nlinarith [sq_nonneg (s - r)]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  have hMajInt : IntegrableOn
      (fun s : ℝ => (s / r ^ 2) * ‖modeVort c F s‖) (Ioi r) := by
    refine IntegrableOn.congr_fun (h1real.const_mul (1 / r ^ 2)) ?_ measurableSet_Ioi
    intro s hs
    ring
  have hInvNorm := norm_integral_le_of_norm_le hMajInt hInvpt
  have hInvNorm' :
      ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ ≤
        (1 / r ^ 2) * (∫ s in Ioi r, s * ‖modeVort c F s‖) := by
    calc
      _ ≤ ∫ s in Ioi r, (s / r ^ 2) * ‖modeVort c F s‖ := hInvNorm
      _ = (1 / r ^ 2) * (∫ s in Ioi r, s * ‖modeVort c F s‖) := by
        have heq : (fun s : ℝ => (s / r ^ 2) * ‖modeVort c F s‖) =
            fun s => (1 / r ^ 2) * (s * ‖modeVort c F s‖) := by
          funext s
          ring
        rw [heq, integral_const_mul]
  have hInvBound : ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ ≤
      A * (1 / 2 + 6 / r ^ 2) * gaussTailWeight r := by
    have hc : 0 ≤ 1 / r ^ 2 := by positivity
    calc
      _ ≤ (1 / r ^ 2) * (∫ s in Ioi r, s * ‖modeVort c F s‖) := by
        simpa using hInvNorm'
      _ ≤ (1 / r ^ 2) * (A * (r ^ 2 / 2 + 6) * gaussTailWeight r) :=
        mul_le_mul_of_nonneg_left (by simpa [A] using h1abs) hc
      _ = A * (1 / 2 + 6 / r ^ 2) * gaussTailWeight r := by
        field_simp [ne_of_gt hr0]
  have hEq := modeRadial_farField_remainder_eq_tail hF hr0
  rw [hEq]
  calc
    ‖(1 / 4 : ℂ) * ((∫ s in Ioi r, (s : ℂ) ^ 3 * modeVort c F s) -
        (r : ℂ) ^ 4 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s))‖ ≤
        (1 / 4 : ℝ) * (‖∫ s in Ioi r, (s : ℂ) ^ 3 * modeVort c F s‖ +
          ‖(r : ℂ) ^ 4 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s)‖) := by
      calc
        _ = ‖(1 / 4 : ℂ)‖ * ‖(∫ s in Ioi r, (s : ℂ) ^ 3 * modeVort c F s) -
              (r : ℂ) ^ 4 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s)‖ := norm_mul _ _
        _ = (1 / 4 : ℝ) * ‖(∫ s in Ioi r, (s : ℂ) ^ 3 * modeVort c F s) -
              (r : ℂ) ^ 4 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s)‖ := by norm_num
        _ ≤ (1 / 4 : ℝ) * (‖∫ s in Ioi r, (s : ℂ) ^ 3 * modeVort c F s‖ +
              ‖(r : ℂ) ^ 4 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s)‖) := by
            gcongr
            exact norm_sub_le _ _
    _ ≤ (1 / 4 : ℝ) *
        (A * (r ^ 4 / 2 + 8 * r ^ 2 + 32) * gaussTailWeight r +
          r ^ 4 * (A * (1 / 2 + 6 / r ^ 2) * gaussTailWeight r)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add h3bound
      calc
        ‖(r : ℂ) ^ 4 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s)‖ =
            r ^ 4 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ r)]
        _ ≤ r ^ 4 * (A * (1 / 2 + 6 / r ^ 2) * gaussTailWeight r) :=
          mul_le_mul_of_nonneg_left hInvBound (by positivity)
    _ = (A / 4) * (r ^ 4 + 14 * r ^ 2 + 32) * gaussTailWeight r := by
      field_simp [ne_of_gt hr0]
      ring

/-- First radial derivative of the renormalized far-field remainder has the same sharp Gaussian
rate, with the polynomial supplied by the inverse-radius tail. -/
theorem norm_deriv_modeRadial_farField_remainder_le {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {r : ℝ} (hr : 1 ≤ r) :
    ‖deriv (fun x : ℝ => (x : ℂ) ^ 2 * modeRadial F x +
        (1 / 4 : ℂ) * modeQuadrupole c F) r‖ ≤
      (Classical.choose (hF.exists_bound) / |c.im|) *
        (r ^ 3 / 2 + 6 * r) * gaussTailWeight r := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hM0, hM⟩ := Classical.choose_spec (hF.exists_bound)
  have h1abs := integral_Ioi_one_norm_modeVort_le hF hM0 hM hr
  have h1real : IntegrableOn
      (fun s : ℝ => s * ‖modeVort c F s‖) (Ioi r) := by
    simpa [pow_one] using
      (integrableOn_pow_mul_norm_modeVort hF 1).mono_set
        (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ r))
  have hInvpt : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioi r)),
      ‖(s : ℂ)⁻¹ * modeVort c F s‖ ≤ (s / r ^ 2) * ‖modeVort c F s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hr0 hs
    have hrs : r ≤ s := le_of_lt hs
    have hinv : s⁻¹ ≤ s / r ^ 2 := by
      have hr2 : r ^ 2 ≠ 0 := ne_of_gt (pow_pos hr0 2)
      have hsne : s ≠ 0 := ne_of_gt hs0
      field_simp [hr2, hsne]
      nlinarith [sq_nonneg (s - r)]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  have hMajInt : IntegrableOn
      (fun s : ℝ => (s / r ^ 2) * ‖modeVort c F s‖) (Ioi r) := by
    refine IntegrableOn.congr_fun (h1real.const_mul (1 / r ^ 2)) ?_ measurableSet_Ioi
    intro s hs
    ring
  have hInvNorm := norm_integral_le_of_norm_le hMajInt hInvpt
  have hInvNorm' :
      ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ ≤
        (1 / r ^ 2) * (∫ s in Ioi r, s * ‖modeVort c F s‖) := by
    calc
      _ ≤ ∫ s in Ioi r, (s / r ^ 2) * ‖modeVort c F s‖ := hInvNorm
      _ = (1 / r ^ 2) * (∫ s in Ioi r, s * ‖modeVort c F s‖) := by
        have heq : (fun s : ℝ => (s / r ^ 2) * ‖modeVort c F s‖) =
            fun s => (1 / r ^ 2) * (s * ‖modeVort c F s‖) := by
          funext s
          ring
        rw [heq, integral_const_mul]
  have hInvBound : ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ ≤
      (Classical.choose (hF.exists_bound) / |c.im|) *
        (1 / 2 + 6 / r ^ 2) * gaussTailWeight r := by
    have hc : 0 ≤ 1 / r ^ 2 := by positivity
    calc
      _ ≤ (1 / r ^ 2) * (∫ s in Ioi r, s * ‖modeVort c F s‖) := by
        simpa using hInvNorm'
      _ ≤ (1 / r ^ 2) *
          ((Classical.choose (hF.exists_bound) / |c.im|) * (r ^ 2 / 2 + 6) *
            gaussTailWeight r) :=
        mul_le_mul_of_nonneg_left (by simpa using h1abs) hc
      _ = (Classical.choose (hF.exists_bound) / |c.im|) *
          (1 / 2 + 6 / r ^ 2) * gaussTailWeight r := by
        field_simp [ne_of_gt hr0]
  have hD := hasDerivAt_modeRadial_farField_remainder hF hr0
  rw [hD.deriv, norm_neg, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r)]
  calc
    r ^ 3 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ ≤
        r ^ 3 * ((Classical.choose (hF.exists_bound) / |c.im|) *
          (1 / 2 + 6 / r ^ 2) * gaussTailWeight r) :=
      mul_le_mul_of_nonneg_left hInvBound (by positivity)
    _ = (Classical.choose (hF.exists_bound) / |c.im|) *
        (r ^ 3 / 2 + 6 * r) * gaussTailWeight r := by
      field_simp [ne_of_gt hr0]

/-- Second radial derivative of the renormalized remainder, obtained by differentiating the
inverse-radius tail once more. -/
theorem norm_second_deriv_modeRadial_farField_remainder_le {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {r : ℝ} (hr : 1 ≤ r) :
    ‖deriv (deriv (fun x : ℝ => (x : ℂ) ^ 2 * modeRadial F x +
        (1 / 4 : ℂ) * modeQuadrupole c F)) r‖ ≤
      (Classical.choose (hF.exists_bound) / |c.im|) *
        (r ^ 4 / 4 + 7 * r ^ 2 / 2 + 18) * gaussTailWeight r := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hM0, hM⟩ := Classical.choose_spec (hF.exists_bound)
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ 2 * modeRadial F x +
    (1 / 4 : ℂ) * modeQuadrupole c F
  let tailInv : ℝ → ℂ := fun x => ∫ s in Ioi x, (s : ℂ)⁻¹ * modeVort c F s
  have hcontInv : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹ * modeVort c F s) (Ioi 0) := by
    have hinv : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹) (Ioi 0) :=
      Complex.continuous_ofReal.continuousOn.inv₀ (fun s hs => by exact_mod_cast hs.ne')
    exact hinv.mul (continuousOn_modeVort hF)
  have hintInv : ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * modeVort c F s) (Ioi ρ) := by
    intro ρ hρ
    exact integrableOn_inv_mul_modeVort hF hρ
  have htailInv : HasDerivAt tailInv (-((r : ℂ)⁻¹ * modeVort c F r)) r := by
    simpa [tailInv] using
      hasDerivAt_integral_Ioi_complex hcontInv hintInv hr0
  have hp3 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 3) (3 * (r : ℂ) ^ 2) r := by
    have hp := (hasDerivAt_pow 3 r).ofReal_comp
    convert hp using 1 <;> push_cast <;> ring
  have hD : HasDerivAt (fun x : ℝ => -((x : ℂ) ^ 3 * tailInv x))
      (-(3 * (r : ℂ) ^ 2 * tailInv r + (r : ℂ) ^ 3 *
        (-((r : ℂ)⁻¹ * modeVort c F r)))) r := hp3.mul htailInv |>.neg
  have hEq : deriv f =ᶠ[𝓝 r] (fun x : ℝ => -((x : ℂ) ^ 3 * tailInv x)) := by
    filter_upwards [Ioi_mem_nhds hr0] with x hx
    exact (hasDerivAt_modeRadial_farField_remainder hF hx).deriv
  have hSecond := hD.congr_of_eventuallyEq hEq
  have hSecondVal :
      -(3 * (r : ℂ) ^ 2 * tailInv r + (r : ℂ) ^ 3 *
        (-((r : ℂ)⁻¹ * modeVort c F r))) =
        -(3 * (r : ℂ) ^ 2 * tailInv r) + (r : ℂ) ^ 2 * modeVort c F r := by
    field_simp [Complex.ofReal_ne_zero.mpr hr0.ne']
    ring
  have hFirstBound := norm_deriv_modeRadial_farField_remainder_le hF hr
  have hFirstEq := (hasDerivAt_modeRadial_farField_remainder hF hr0).deriv
  have hTailBound :
      ‖tailInv r‖ ≤ (Classical.choose (hF.exists_bound) / |c.im|) *
        (1 / 2 + 6 / r ^ 2) * gaussTailWeight r := by
    have hFirst : r ^ 3 * ‖tailInv r‖ ≤
        (Classical.choose (hF.exists_bound) / |c.im|) *
          (r ^ 3 / 2 + 6 * r) * gaussTailWeight r := by
      rw [hFirstEq, norm_neg, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r)] at hFirstBound
      simpa [tailInv] using hFirstBound
    have hr3 : 0 < r ^ 3 := pow_pos hr0 3
    calc
      _ ≤ ((Classical.choose (hF.exists_bound) / |c.im|) *
          (r ^ 3 / 2 + 6 * r) * gaussTailWeight r) / r ^ 3 := by
        apply (le_div_iff₀ hr3).2
        nlinarith [hFirst]
      _ = (Classical.choose (hF.exists_bound) / |c.im|) *
          (1 / 2 + 6 / r ^ 2) * gaussTailWeight r := by
        field_simp [ne_of_gt hr0]
  have hmode := norm_modeVort_le hF.im_ne_zero hM0 hM r
  have hmode' : ‖modeVort c F r‖ ≤
      (Classical.choose (hF.exists_bound) / |c.im|) *
        (r ^ 2 / 4 + 2) * gaussTailWeight r := by
    simpa [gaussTailWeight, mul_assoc] using hmode
  rw [hSecond.deriv, hSecondVal]
  calc
    ‖-(3 * (r : ℂ) ^ 2 * tailInv r) + (r : ℂ) ^ 2 * modeVort c F r‖ ≤
        ‖-(3 * (r : ℂ) ^ 2 * tailInv r)‖ +
          ‖(r : ℂ) ^ 2 * modeVort c F r‖ := norm_add_le _ _
    _ = ‖3 * (r : ℂ) ^ 2 * tailInv r‖ +
          ‖(r : ℂ) ^ 2 * modeVort c F r‖ := by rw [norm_neg]
    _ ≤ 3 * r ^ 2 * ((Classical.choose (hF.exists_bound) / |c.im|) *
          (1 / 2 + 6 / r ^ 2) * gaussTailWeight r) +
        r ^ 2 * ((Classical.choose (hF.exists_bound) / |c.im|) *
          (r ^ 2 / 4 + 2) * gaussTailWeight r) := by
      apply add_le_add
      · rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ r)]
        norm_num
        gcongr
      · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ r)]
        exact mul_le_mul_of_nonneg_left hmode' (by positivity)
    _ = (Classical.choose (hF.exists_bound) / |c.im|) *
        (r ^ 4 / 4 + 7 * r ^ 2 / 2 + 18) * gaussTailWeight r := by
      field_simp [ne_of_gt hr0]
      ring

/-- The inverse-radius tail itself has the sharp Gaussian envelope for `r≥1`. -/
theorem norm_inv_modeVort_tail_le {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {r : ℝ} (hr : 1 ≤ r) :
    ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ ≤
      (Classical.choose (hF.exists_bound) / |c.im|) *
        (1 / 2 + 6 / r ^ 2) * gaussTailWeight r := by
  have hr0 : 0 < r := by linarith
  have hFirstBound := norm_deriv_modeRadial_farField_remainder_le hF hr
  have hFirstEq := (hasDerivAt_modeRadial_farField_remainder hF hr0).deriv
  have hFirst : r ^ 3 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ ≤
      (Classical.choose (hF.exists_bound) / |c.im|) *
        (r ^ 3 / 2 + 6 * r) * gaussTailWeight r := by
    rw [hFirstEq, norm_neg, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r)] at hFirstBound
    simpa using hFirstBound
  have hr3 : 0 < r ^ 3 := pow_pos hr0 3
  calc
    _ ≤ ((Classical.choose (hF.exists_bound) / |c.im|) *
        (r ^ 3 / 2 + 6 * r) * gaussTailWeight r) / r ^ 3 := by
      apply (le_div_iff₀ hr3).2
      nlinarith [hFirst]
    _ = (Classical.choose (hF.exists_bound) / |c.im|) *
        (1 / 2 + 6 / r ^ 2) * gaussTailWeight r := by
      field_simp [ne_of_gt hr0]


private theorem iteratedDeriv_ofReal_cube_eq (k : ℕ) {r : ℝ} :
    iteratedDeriv k (fun x : ℝ => (x : ℂ) ^ 3) r =
      Complex.ofRealCLM (iteratedDeriv k (fun x : ℝ => x ^ 3) r) := by
  let p : ℝ → ℝ := fun x => x ^ 3
  have hfun : (fun x : ℝ => (x : ℂ) ^ 3) = Complex.ofRealCLM ∘ p := by
    funext x
    simp [p]
  have hp : ContDiffAt ℝ ⊤ p r := contDiffAt_id.pow 3
  have hcomp := Complex.ofRealCLM.iteratedFDeriv_comp_left hp (i := k) le_top
  calc
    iteratedDeriv k (fun x : ℝ => (x : ℂ) ^ 3) r =
        (iteratedFDeriv ℝ k (Complex.ofRealCLM ∘ p) r)
          (fun _ : Fin k => (1 : ℝ)) := by rw [hfun]; rfl
    _ = Complex.ofRealCLM ((iteratedFDeriv ℝ k p r)
          (fun _ : Fin k => (1 : ℝ))) := by rw [hcomp]; rfl
    _ = Complex.ofRealCLM (iteratedDeriv k p r) := by
          have hder : (iteratedFDeriv ℝ k p r) (fun _ : Fin k => (1 : ℝ)) =
              iteratedDeriv k p r := (iteratedDeriv_eq_iteratedFDeriv (𝕜 := ℝ)
                (f := p) (x := r) (n := k)).symm
          exact congrArg Complex.ofRealCLM hder
    _ = Complex.ofRealCLM (iteratedDeriv k (fun x : ℝ => x ^ 3) r) := by rfl

private theorem iteratedDeriv_ofReal_cube_fourth {r : ℝ} :
    iteratedDeriv 4 (fun x : ℝ => (x : ℂ) ^ 3) r = 0 := by
  have htrans := iteratedDeriv_ofReal_cube_eq 4 (r := r)
  have hreal : iteratedDeriv 4 (fun x : ℝ => x ^ 3) r = 0 := by
    norm_num [iteratedDeriv_pow]
  calc
    iteratedDeriv 4 (fun x : ℝ => (x : ℂ) ^ 3) r =
        Complex.ofRealCLM (iteratedDeriv 4 (fun x : ℝ => x ^ 3) r) := htrans
    _ = 0 := by rw [hreal]; norm_num

private theorem norm_iteratedDeriv_ofReal_cube_le {i : ℕ} {r : ℝ} (hr : 1 ≤ r) :
    ‖iteratedDeriv i (fun x : ℝ => (x : ℂ) ^ 3) r‖ ≤ 6 * (1 + r) ^ 3 := by
  have htrans := iteratedDeriv_ofReal_cube_eq i (r := r)
  have hnorm : ‖iteratedDeriv i (fun x : ℝ => (x : ℂ) ^ 3) r‖ =
      |iteratedDeriv i (fun x : ℝ => x ^ 3) r| := by
    calc
      _ = ‖Complex.ofRealCLM (iteratedDeriv i (fun x : ℝ => x ^ 3) r)‖ :=
          congrArg norm htrans
      _ = |iteratedDeriv i (fun x : ℝ => x ^ 3) r| := by
          rw [Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  have hr0 : 0 ≤ r := by linarith
  have hR : r ≤ 1 + r := by linarith
  have hbig : 1 ≤ (1 + r) ^ 3 := one_le_pow₀ (by linarith : 1 ≤ 1 + r)
  have hcub : r ^ 3 ≤ (1 + r) ^ 3 := pow_le_pow_left₀ hr0 hR 3
  have hsq : r ^ 2 ≤ r ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr (show 0 ≤ r - 1 by linarith))]
  have hlin : r ≤ r ^ 3 := by
    have hsq1 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
    nlinarith [hr, hsq1]
  by_cases hi : i ≤ 3
  · interval_cases i
    · norm_num [iteratedDeriv_pow, Nat.descFactorial]
      rw [abs_of_nonneg hr0]
      nlinarith [hcub]
    · norm_num [iteratedDeriv_pow, Nat.descFactorial]
      nlinarith [hsq, hcub]
    · norm_num [iteratedDeriv_pow, Nat.descFactorial]
      rw [abs_of_nonneg hr0]
      nlinarith [hlin, hcub]
    · norm_num [iteratedDeriv_pow, Nat.descFactorial]
      nlinarith [hbig]
  · have hgt : 3 < i := by omega
    rw [iteratedDeriv_pow, Nat.descFactorial_eq_zero_iff_lt.mpr hgt]
    norm_num
    positivity

/-- Every derivative order, including order zero, of the inverse-radius tail has a polynomial
multiple of the sharp Gaussian envelope on `r≥1`. -/
theorem exists_norm_iteratedDeriv_inv_modeVort_tail_bound_all {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) (n : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv n (fun x : ℝ => ∫ s in Ioi x, (s : ℂ)⁻¹ * modeVort c F s) r‖ ≤
        C * (1 + r) ^ N * gaussTailWeight r := by
  cases n with
  | zero =>
      let A : ℝ := Classical.choose (hF.exists_bound) / |c.im|
      obtain ⟨hM0, _⟩ := Classical.choose_spec (hF.exists_bound)
      have hA : 0 ≤ A := div_nonneg hM0 (abs_nonneg _)
      refine ⟨A * 7, 0, fun r hr => ?_⟩
      have htail := norm_inv_modeVort_tail_le hF hr
      have hr0 : 0 < r := by linarith
      have hcoef : 1 / 2 + 6 / r ^ 2 ≤ 7 := by
        have hden : 0 < r ^ 2 := pow_pos hr0 2
        have hsmall : 6 / r ^ 2 ≤ 6 := (div_le_iff₀ hden).2 (by nlinarith [sq_nonneg (r - 1)])
        linarith
      calc
        ‖∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s‖ ≤
            A * (1 / 2 + 6 / r ^ 2) * gaussTailWeight r := by
              simpa [A] using htail
        _ ≤ A * 7 * (1 + r) ^ 0 * gaussTailWeight r := by
              simp only [pow_zero, mul_one]
              gcongr
              exact (Real.exp_pos _).le
  | succ m =>
      obtain ⟨C, N, h⟩ := exists_norm_iteratedDeriv_inv_modeVort_tail_bound hF m
      exact ⟨C, N, h⟩


/-- All radial derivatives of the renormalized far-field remainder have a polynomial times the
sharp `exp(-r²/4)` envelope on `r≥1`. -/
theorem exists_norm_iteratedDeriv_modeRadial_farField_remainder_bound
    {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv k (fun x : ℝ => (x : ℂ) ^ 2 * modeRadial F x +
        (1 / 4 : ℂ) * modeQuadrupole c F) r‖ ≤
        C * (1 + r) ^ N * gaussTailWeight r := by
  by_cases hk : k = 0
  · subst k
    let A : ℝ := Classical.choose (hF.exists_bound) / |c.im|
    obtain ⟨hM0, _⟩ := Classical.choose_spec (hF.exists_bound)
    have hA : 0 ≤ A := div_nonneg hM0 (abs_nonneg _)
    refine ⟨A / 4 * 47, 4, fun r hr => ?_⟩
    have hsharp := norm_modeRadial_farField_remainder_le hF hr
    have hbase : 1 ≤ 1 + r := by linarith
    have hpow2 : r ^ 2 ≤ (1 + r) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hpow4 : r ^ 4 ≤ (1 + r) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    have hpow2' : r ^ 2 ≤ (1 + r) ^ 4 := by
      calc r ^ 2 ≤ (1 + r) ^ 2 := hpow2
        _ ≤ (1 + r) ^ 4 := by nlinarith [sq_nonneg ((1 + r) ^ 2)]
    have hconst : 1 ≤ (1 + r) ^ 4 := one_le_pow₀ hbase
    have hpoly : r ^ 4 + 14 * r ^ 2 + 32 ≤ 47 * (1 + r) ^ 4 := by
      nlinarith [hpow4, hpow2', hconst]
    calc
      ‖(r : ℂ) ^ 2 * modeRadial F r +
          (1 / 4 : ℂ) * modeQuadrupole c F‖ ≤ A / 4 *
          (r ^ 4 + 14 * r ^ 2 + 32) * gaussTailWeight r := by simpa [A] using hsharp
      _ ≤ A / 4 * 47 * (1 + r) ^ 4 * gaussTailWeight r := by
        have hA4 : 0 ≤ A / 4 := div_nonneg hA (by norm_num)
        calc
          A / 4 * (r ^ 4 + 14 * r ^ 2 + 32) * gaussTailWeight r ≤
              (A / 4 * (47 * (1 + r) ^ 4)) * gaussTailWeight r := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpoly hA4) (Real.exp_pos _).le
          _ = A / 4 * 47 * (1 + r) ^ 4 * gaussTailWeight r := by ring
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let m : ℕ := k - 1
    have hm : m + 1 = k := by dsimp [m]; omega
    let B : ℕ → ℝ := fun j => Classical.choose
      (exists_norm_iteratedDeriv_inv_modeVort_tail_bound_all hF j)
    let P : ℕ → ℕ := fun j => Classical.choose
      (Classical.choose_spec (exists_norm_iteratedDeriv_inv_modeVort_tail_bound_all hF j))
    have hT (j : ℕ) : ∀ r : ℝ, 1 ≤ r →
        ‖iteratedDeriv j (fun x : ℝ => ∫ s in Ioi x, (s : ℂ)⁻¹ * modeVort c F s) r‖ ≤
          B j * (1 + r) ^ P j * gaussTailWeight r := by
      simpa [B, P, gaussTailWeight] using Classical.choose_spec
        (Classical.choose_spec (exists_norm_iteratedDeriv_inv_modeVort_tail_bound_all hF j))
    have hBnonneg (j : ℕ) : 0 ≤ B j := by
      by_contra hn
      have hn' : B j < 0 := lt_of_not_ge hn
      have hpos : 0 < (1 + (1 : ℝ)) ^ P j * gaussTailWeight 1 :=
        mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
      have hb := hT j 1 (by norm_num)
      have hneg : B j * ((1 + (1 : ℝ)) ^ P j * gaussTailWeight 1) < 0 :=
        mul_neg_of_neg_of_pos hn' hpos
      have hbneg : ‖iteratedDeriv j
          (fun x : ℝ => ∫ s in Ioi x, (s : ℂ)⁻¹ * modeVort c F s) 1‖ < 0 := by
        exact lt_of_le_of_lt hb (by simpa [mul_assoc] using hneg)
      exact (not_lt_of_ge (norm_nonneg _)) hbneg
    refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * 6 * B (m - i),
      3 + ∑ i ∈ Finset.range (m + 1), P (m - i), fun r hr => ?_⟩
    let T : ℝ → ℂ := fun x => ∫ s in Ioi x, (s : ℂ)⁻¹ * modeVort c F s
    let cube : ℝ → ℂ := fun x => (x : ℂ) ^ 3
    let R : ℝ → ℂ := fun x => (x : ℂ) ^ 2 * modeRadial F x +
      (1 / 4 : ℂ) * modeQuadrupole c F
    have hderivEq : Set.EqOn (deriv R) (fun x => -(cube x * T x)) (Ioi 0) := by
      intro x hx
      have hx0 : 0 < x := by simpa using hx
      simpa [R, cube, T] using (hasDerivAt_modeRadial_farField_remainder hF hx0).deriv
    have hIter := hderivEq.iteratedDeriv_of_isOpen isOpen_Ioi m (Set.mem_Ioi.mpr (by linarith : 0 < r))
    rw [show k = m + 1 by omega, iteratedDeriv_succ', hIter]
    have hneg : (fun x : ℝ => -(cube x * T x)) =
        fun x : ℝ => (-1 : ℂ) * (cube x * T x) := by
      funext x
      ring
    rw [hneg, iteratedDeriv_const_mul_field]
    simp only [norm_mul, norm_neg, norm_one, one_mul]
    have hcube : ContDiffAt ℝ ∞ cube r := by
      have haxis0 := Complex.ofRealCLM.contDiff.comp (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ))
      have haxis : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
        convert haxis0 using 1
        ext x
        exact Complex.ofRealCLM_apply x
      exact haxis.contDiffAt.pow 3
    have hTcont : ContDiffAt ℝ ∞ T r :=
      (contDiffOn_inv_modeVort_tail hF).contDiffAt
        (isOpen_Ioi.mem_nhds (by change 0 < r; linarith))
    have hmul := iteratedDeriv_mul
      (hcube.of_le (natCast_le_infty m)) (hTcont.of_le (natCast_le_infty m))
    change ‖iteratedDeriv m (cube * T) r‖ ≤
      (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * 6 * B (m - i)) *
        (1 + r) ^ (3 + ∑ i ∈ Finset.range (m + 1), P (m - i)) * gaussTailWeight r
    rw [hmul]
    have hsum := norm_sum_le (Finset.range (m + 1)) (fun i : ℕ =>
      (m.choose i : ℝ) * iteratedDeriv i cube r * iteratedDeriv (m - i) T r)
    have hcoeff_nonneg : ∀ i ∈ Finset.range (m + 1),
        0 ≤ (m.choose i : ℝ) * 6 * B (m - i) := by
      intro i hi
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num)) (hBnonneg (m - i))
    have hsumPoly :
        (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * 6 * B (m - i) *
          (1 + r) ^ (3 + P (m - i))) ≤
        (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * 6 * B (m - i)) *
          (1 + r) ^ (3 + ∑ i ∈ Finset.range (m + 1), P (m - i)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hpow : P (m - i) ≤ ∑ j ∈ Finset.range (m + 1), P (m - j) :=
        Finset.single_le_sum (f := fun j : ℕ => P (m - j)) (fun j hj => Nat.zero_le _) hi
      have hbase : 1 ≤ 1 + r := by linarith
      have hdegree : 3 + P (m - i) ≤ 3 + ∑ j ∈ Finset.range (m + 1), P (m - j) := by omega
      gcongr
      exact hcoeff_nonneg i hi
    calc
      ‖∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * iteratedDeriv i cube r * iteratedDeriv (m - i) T r‖ ≤
          ∑ i ∈ Finset.range (m + 1),
            ‖(m.choose i : ℝ) * iteratedDeriv i cube r * iteratedDeriv (m - i) T r‖ := hsum
      _ ≤ ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * 6 * B (m - i) *
            (1 + r) ^ (3 + P (m - i)) * gaussTailWeight r := by
        apply Finset.sum_le_sum
        intro i hi
        have hrec := norm_iteratedDeriv_ofReal_cube_le (i := i) (r := r) hr
        have htail := hT (m - i) r hr
        calc
          ‖(m.choose i : ℝ) * iteratedDeriv i cube r * iteratedDeriv (m - i) T r‖ =
              (m.choose i : ℝ) * ‖iteratedDeriv i cube r‖ * ‖iteratedDeriv (m - i) T r‖ := by
                rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (Nat.cast_nonneg _)]
          _ ≤ (m.choose i : ℝ) * 6 * B (m - i) *
              (1 + r) ^ (3 + P (m - i)) * gaussTailWeight r := by
                have hc : 0 ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
                have hb : 0 ≤ B (m - i) := hBnonneg _
                have hw : 0 ≤ gaussTailWeight r := (Real.exp_pos _).le
                have hpow : (1 + r) ^ 3 * (1 + r) ^ P (m - i) =
                    (1 + r) ^ (3 + P (m - i)) := by rw [← pow_add]
                have hprod :
                    ‖iteratedDeriv i cube r‖ * ‖iteratedDeriv (m - i) T r‖ ≤
                      6 * (1 + r) ^ 3 *
                        (B (m - i) * (1 + r) ^ P (m - i) * gaussTailWeight r) := by
                  exact mul_le_mul hrec htail (norm_nonneg _)
                    (by positivity [hBnonneg (m - i)])
                calc
                  _ = (m.choose i : ℝ) *
                      (‖iteratedDeriv i cube r‖ * ‖iteratedDeriv (m - i) T r‖) := by ring
                  _ ≤ (m.choose i : ℝ) *
                      (6 * (1 + r) ^ 3 *
                        (B (m - i) * (1 + r) ^ P (m - i) * gaussTailWeight r)) :=
                        mul_le_mul_of_nonneg_left hprod hc
                  _ = (m.choose i : ℝ) * 6 * B (m - i) *
                      ((1 + r) ^ 3 * (1 + r) ^ P (m - i)) * gaussTailWeight r := by ring
                  _ = (m.choose i : ℝ) * 6 * B (m - i) *
                      (1 + r) ^ (3 + P (m - i)) * gaussTailWeight r := by rw [hpow]
      _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * 6 * B (m - i)) *
            (1 + r) ^ (3 + ∑ i ∈ Finset.range (m + 1), P (m - i)) * gaussTailWeight r := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right hsumPoly (Real.exp_pos _).le


private theorem complexRecip_iterated (j : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    iteratedDeriv j (fun x : ℝ => ((x : ℂ)⁻¹)) r =
      (((-1 : ℝ) ^ j * (j.factorial : ℝ) * r ^ (-1 - (j : ℤ))) : ℂ) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hreal : iteratedDeriv j (fun x : ℝ => 1 / x) r =
      (-1 : ℝ) ^ j * (j.factorial : ℝ) * r ^ (-1 - (j : ℤ)) := by
    have hw := (iteratedDerivWithin_one_div (𝕜 := ℝ) (s := Set.Ioi (0 : ℝ))
      j isOpen_Ioi) hr0
    have ho := (iteratedDerivWithin_of_isOpen (f := fun x : ℝ => 1 / x)
      (n := j) isOpen_Ioi) hr0
    exact ho.symm.trans hw
  have hsmooth : ContDiffAt ℝ ⊤ (fun x : ℝ => x⁻¹) r := contDiffAt_inv ℝ hr0.ne'
  have hcomp := Complex.ofRealCLM.iteratedFDeriv_comp_left hsmooth
    (i := j) le_top
  have hidentity : (fun x : ℝ => ((x : ℂ)⁻¹)) =
      Complex.ofRealCLM ∘ (fun x : ℝ => x⁻¹) := by
    funext x
    simp
  rw [hidentity, iteratedDeriv_eq_iteratedFDeriv, hcomp]
  change (↑(iteratedDeriv j (fun x : ℝ => x⁻¹) r) : ℂ) = _
  simpa [one_div] using congrArg (fun x : ℝ => (x : ℂ)) hreal

private theorem norm_complexRecip_iterated_le (j : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    ‖iteratedDeriv j (fun x : ℝ => ((x : ℂ)⁻¹)) r‖ ≤ (j.factorial : ℝ) := by
  have hpow_nonneg : 0 ≤ r ^ (-1 - (j : ℤ)) := zpow_nonneg (by linarith : 0 ≤ r) _
  have hpow_le : r ^ (-1 - (j : ℤ)) ≤ 1 := by
    have he : (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hr)
  rw [complexRecip_iterated j hr]
  have hcast : ((↑(-1 : ℝ) : ℂ) ^ j * (↑(j.factorial : ℝ) : ℂ) *
      (↑r : ℂ) ^ (-1 - (j : ℤ))) =
      (((-1 : ℝ) ^ j * (j.factorial : ℝ) * r ^ (-1 - (j : ℤ)) : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (show 0 ≤ (j.factorial : ℝ) by positivity),
    abs_of_nonneg hpow_nonneg]
  exact mul_le_of_le_one_right (by positivity : 0 ≤ (j.factorial : ℝ)) hpow_le

private theorem exists_norm_iteratedDeriv_invSq_bound (k : ℕ) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv k (fun x : ℝ => ((x : ℂ)⁻¹) ^ 2) r‖ ≤ C := by
  let f : ℝ → ℂ := fun x => (x : ℂ)⁻¹
  let D : ℝ := ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ)
  refine ⟨D, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hf : ContDiffAt ℝ ∞ f r := by
    have hreal : ContDiffAt ℝ ∞ (fun x : ℝ => x⁻¹) r := contDiffAt_inv ℝ hr0.ne'
    have hcomp := hreal.continuousLinearMap_comp Complex.ofRealCLM
    have heq : f = Complex.ofRealCLM ∘ (fun x : ℝ => x⁻¹) := by
      funext x
      simp [f]
    simpa only [heq] using hcomp
  have hmul := iteratedDeriv_mul
    (hf.of_le (natCast_le_infty k)) (hf.of_le (natCast_le_infty k))
  have hfEq : (fun x : ℝ => ((x : ℂ)⁻¹) ^ 2) = f * f := by
    funext x
    simp [f, pow_two]
  rw [hfEq]
  change ‖iteratedDeriv k (f * f) r‖ ≤ D
  rw [hmul]
  have hsum := norm_sum_le (Finset.range (k + 1)) (fun i : ℕ =>
    (k.choose i : ℝ) * iteratedDeriv i f r * iteratedDeriv (k - i) f r)
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        ‖(k.choose i : ℝ) * iteratedDeriv i f r * iteratedDeriv (k - i) f r‖ := hsum
    _ ≤ D := by
      dsimp [D]
      apply Finset.sum_le_sum
      intro i hi
      have hc : 0 ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
      have hfi : ‖iteratedDeriv i f r‖ ≤ (i.factorial : ℝ) := by
        simpa [f] using norm_complexRecip_iterated_le i hr
      have hfj : ‖iteratedDeriv (k - i) f r‖ ≤ ((k - i).factorial : ℝ) := by
        simpa [f] using norm_complexRecip_iterated_le (k - i) hr
      calc
        ‖(k.choose i : ℝ) * iteratedDeriv i f r * iteratedDeriv (k - i) f r‖ =
            (k.choose i : ℝ) * ‖iteratedDeriv i f r‖ *
              ‖iteratedDeriv (k - i) f r‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Nat.cast_nonneg _)]
        _ = (k.choose i : ℝ) *
            (‖iteratedDeriv i f r‖ * ‖iteratedDeriv (k - i) f r‖) := by ring
        _ ≤ (k.choose i : ℝ) *
            ((i.factorial : ℝ) * ((k - i).factorial : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hfi hfj (norm_nonneg _) (by positivity)) hc
        _ = (k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ) := by ring



/-- Every radial derivative of `modeRadial − C∞ r⁻²`, with `C∞ = −M/4`, has a polynomial
multiple of the sharp `exp(-r²/4)` envelope on `r≥1`. -/
theorem exists_norm_iteratedDeriv_modeRadial_asymptotic_remainder_bound
    {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv k (fun x : ℝ => modeRadial F x +
        (1 / 4 : ℂ) * modeQuadrupole c F * ((x : ℂ)⁻¹) ^ 2) r‖ ≤
        C * (1 + r) ^ N * gaussTailWeight r := by
  let D : ℕ → ℝ := fun j => Classical.choose (exists_norm_iteratedDeriv_invSq_bound j)
  let P : ℕ → ℕ := fun j => Classical.choose
    (Classical.choose_spec (exists_norm_iteratedDeriv_modeRadial_farField_remainder_bound hF j))
  let C0 : ℕ → ℝ := fun j => Classical.choose
    (exists_norm_iteratedDeriv_modeRadial_farField_remainder_bound hF j)
  let N0 : ℕ → ℕ := fun j => Classical.choose
    (Classical.choose_spec (exists_norm_iteratedDeriv_modeRadial_farField_remainder_bound hF j))
  have hRbound (j : ℕ) (r : ℝ) (hr : 1 ≤ r) :
      ‖iteratedDeriv j (fun x : ℝ => (x : ℂ) ^ 2 * modeRadial F x +
        (1 / 4 : ℂ) * modeQuadrupole c F) r‖ ≤
        C0 j * (1 + r) ^ N0 j * gaussTailWeight r := by
    simpa [C0, N0, gaussTailWeight] using Classical.choose_spec
      (Classical.choose_spec (exists_norm_iteratedDeriv_modeRadial_farField_remainder_bound hF j)) r hr
  have hinvSq (j : ℕ) (r : ℝ) (hr : 1 ≤ r) :
      ‖iteratedDeriv j (fun x : ℝ => ((x : ℂ)⁻¹) ^ 2) r‖ ≤ D j := by
    simpa [D] using Classical.choose_spec (exists_norm_iteratedDeriv_invSq_bound j) r hr
  have hDnonneg (j : ℕ) : 0 ≤ D j := by
    by_contra hn
    have hn' : D j < 0 := lt_of_not_ge hn
    have hb := hinvSq j 1 (by norm_num)
    have hneg : D j < 0 := hn'
    exact (not_lt_of_ge (norm_nonneg _)) (lt_of_le_of_lt hb hneg)
  have hCnonneg (j : ℕ) : 0 ≤ C0 j := by
    by_contra hn
    have hn' : C0 j < 0 := lt_of_not_ge hn
    have hpos : 0 < (1 + (1 : ℝ)) ^ N0 j * gaussTailWeight 1 :=
      mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
    have hb := hRbound j 1 (by norm_num)
    have hneg : C0 j * ((1 + (1 : ℝ)) ^ N0 j * gaussTailWeight 1) < 0 :=
      mul_neg_of_neg_of_pos hn' hpos
    have hbneg : ‖iteratedDeriv j
        (fun x : ℝ => (x : ℂ) ^ 2 * modeRadial F x +
          (1 / 4 : ℂ) * modeQuadrupole c F) 1‖ < 0 := by
      exact lt_of_le_of_lt hb (by simpa [mul_assoc] using hneg)
    exact (not_lt_of_ge (norm_nonneg _)) hbneg
  let A : ℕ → ℝ := fun i => (k.choose i : ℝ) * D i * C0 (k - i)
  let C : ℝ := ∑ i ∈ Finset.range (k + 1), A i
  let N : ℕ := ∑ i ∈ Finset.range (k + 1), N0 (k - i)
  refine ⟨C, N, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  let invSq : ℝ → ℂ := fun x => ((x : ℂ)⁻¹) ^ 2
  let R : ℝ → ℂ := fun x => (x : ℂ) ^ 2 * modeRadial F x +
    (1 / 4 : ℂ) * modeQuadrupole c F
  have hInv : ContDiffAt ℝ ∞ (fun x : ℝ => (x : ℂ)⁻¹) r := by
    have hreal : ContDiffAt ℝ ∞ (fun x : ℝ => x⁻¹) r := contDiffAt_inv ℝ hr0.ne'
    have hcomp := hreal.continuousLinearMap_comp Complex.ofRealCLM
    have heq : (fun x : ℝ => (x : ℂ)⁻¹) =
        Complex.ofRealCLM ∘ (fun x : ℝ => x⁻¹) := by
      funext x
      simp
    simpa only [heq] using hcomp
  have hInvSq : ContDiffAt ℝ ∞ invSq r := by
    have hfun : invSq = (fun x : ℝ => (x : ℂ)⁻¹) *
        (fun x : ℝ => (x : ℂ)⁻¹) := by
      funext x
      simp [invSq, pow_two]
    rw [hfun]
    exact hInv.mul hInv
  have hRadial : ContDiffAt ℝ ∞ (modeRadial F) r := by
    change ContDiffAt ℝ ∞ (fun x : ℝ => F (Real.log x)) r
    have hFAt : ContDiffAt ℝ ∞ F (Real.log r) := hF.smooth.contDiffAt
    have hlog : ContDiffAt ℝ ∞ Real.log r := Real.contDiffAt_log.mpr hr0.ne'
    exact ContDiffAt.comp r hFAt hlog
  have hAxis : ContDiffAt ℝ ∞ (fun x : ℝ => (x : ℂ)) r := by
    have haxis0 := Complex.ofRealCLM.contDiff.comp
      (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ))
    have haxis : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
      convert haxis0 using 1
      ext x
      exact Complex.ofRealCLM_apply x
    exact haxis.contDiffAt
  have hR : ContDiffAt ℝ ∞ R r := by
    dsimp [R]
    exact (hAxis.pow 2).mul hRadial |>.add contDiffAt_const
  have hmul := iteratedDeriv_mul
    (hInvSq.of_le (natCast_le_infty k)) (hR.of_le (natCast_le_infty k))
  have hEq : Set.EqOn
      (fun x : ℝ => modeRadial F x + (1 / 4 : ℂ) * modeQuadrupole c F *
        ((x : ℂ)⁻¹) ^ 2)
      (invSq * R) (Ioi 0) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (by simpa using hx)
    have hxs : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
    dsimp [invSq, R]
    field_simp
  have hEqIter := hEq.iteratedDeriv_of_isOpen isOpen_Ioi k
    (Set.mem_Ioi.mpr (by linarith : 0 < r))
  rw [hEqIter, hmul]
  have hsum := norm_sum_le (Finset.range (k + 1)) (fun i : ℕ =>
    (k.choose i : ℝ) * iteratedDeriv i invSq r * iteratedDeriv (k - i) R r)
  have hA_nonneg (i : ℕ) : 0 ≤ A i := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hDnonneg i)) (hCnonneg (k - i))
  have hsumPoly :
      (∑ i ∈ Finset.range (k + 1), A i * (1 + r) ^ N0 (k - i)) ≤
        (∑ i ∈ Finset.range (k + 1), A i) * (1 + r) ^ N := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hpow : N0 (k - i) ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum (f := fun j : ℕ => N0 (k - j))
        (fun j hj => Nat.zero_le _) hi
    have hbase : 1 ≤ 1 + r := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hpow) (hA_nonneg i)
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        ‖(k.choose i : ℝ) * iteratedDeriv i invSq r * iteratedDeriv (k - i) R r‖ := hsum
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        A i * (1 + r) ^ N0 (k - i) * gaussTailWeight r := by
      apply Finset.sum_le_sum
      intro i hi
      have hdi := hinvSq i r hr
      have hri := hRbound (k - i) r hr
      have hc : 0 ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
      have hterm :
          ‖(k.choose i : ℝ) * iteratedDeriv i invSq r * iteratedDeriv (k - i) R r‖ =
          (k.choose i : ℝ) * ‖iteratedDeriv i invSq r‖ *
            ‖iteratedDeriv (k - i) R r‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg _)]
      rw [hterm]
      have hright : 0 ≤ C0 (k - i) * (1 + r) ^ N0 (k - i) * gaussTailWeight r :=
        mul_nonneg (mul_nonneg (hCnonneg (k - i))
          (pow_nonneg (by linarith : 0 ≤ 1 + r) _)) (Real.exp_pos _).le
      have hprod : ‖iteratedDeriv i invSq r‖ *
          ‖iteratedDeriv (k - i) R r‖ ≤
          D i * (C0 (k - i) * (1 + r) ^ N0 (k - i) * gaussTailWeight r) := by
        exact mul_le_mul hdi hri (norm_nonneg _) (hDnonneg i)
      calc
        _ = (k.choose i : ℝ) *
            (‖iteratedDeriv i invSq r‖ * ‖iteratedDeriv (k - i) R r‖) := by ring
        _ ≤ (k.choose i : ℝ) *
            (D i * (C0 (k - i) * (1 + r) ^ N0 (k - i) * gaussTailWeight r)) :=
              mul_le_mul_of_nonneg_left hprod hc
        _ = A i * (1 + r) ^ N0 (k - i) * gaussTailWeight r := by
              dsimp [A]
              ring
    _ ≤ (∑ i ∈ Finset.range (k + 1), A i) * (1 + r) ^ N * gaussTailWeight r := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hsumPoly (Real.exp_pos _).le


end UnforcedLeray.ComplexODEC
