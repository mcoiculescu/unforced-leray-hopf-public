import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIa.Clock.FrameKernels
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3
import UnforcedLeray.Lib.Gaussian.MovingCell
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Part III-a, task `PartIII-a:T21/c3/3/2`: oscillator mode forcing (`ComplModeForceOscillator`, SP 2905)

Source of record: `the November 2 reference manuscript` (SP), line 2905.
Proves `complModeForceOscillator`: using `IsSeedKernels κ` (`PartI.seedModeRegularity_proof`) and
termwise differentiation of the periodized sum `perE κ d(r) j` (`Gaussian.movingCell_identity` with
`d'(r) / d(r) = -1 / (2 * a(r)² * clockTheta ν r)`), establishes the periodization identity
`movOscRes κ ν r j = (clockTheta ν r)⁻¹ * perSum d(r) (movD (κ.e j))` and bounds its `X_{m,d(r)}`
norm by `C₁ / clockTheta ν r` together with `AEStronglyMeasurable`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace OscillatorForceSub

/-- Continuous `ℝ`-linear map identifying `ℝ × ℝ` with `ℂ` as `planeToC`. -/
def planeToCCLM : (ℝ × ℝ) →L[ℝ] ℂ :=
  ((Complex.equivRealProdCLM.symm : (ℝ × ℝ) ≃L[ℝ] ℂ) : (ℝ × ℝ) →L[ℝ] ℂ)

lemma planeToCCLM_apply (y : ℝ × ℝ) : planeToCCLM y = planeToC y := by
  apply Complex.ext <;> simp [planeToCCLM, planeToC]

lemma norm_planeToC_sq (y : ℝ × ℝ) : ‖planeToC y‖ ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [planeToC]
  ring

lemma norm_le_norm_planeToC (y : ℝ × ℝ) : ‖y‖ ≤ ‖planeToC y‖ := by
  have hsq := norm_planeToC_sq y
  have h1 : |y.1| ≤ ‖planeToC y‖ := by
    have : |y.1| * |y.1| ≤ ‖planeToC y‖ * ‖planeToC y‖ := by
      nlinarith [sq_abs y.1, sq_nonneg y.2, hsq]
    exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) this
  have h2 : |y.2| ≤ ‖planeToC y‖ := by
    have : |y.2| * |y.2| ≤ ‖planeToC y‖ * ‖planeToC y‖ := by
      nlinarith [sq_abs y.2, sq_nonneg y.1, hsq]
    exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) this
  exact max_le h1 h2

lemma seedPlanar_eq_of_eqOn_Ioi {f g : ℝ → ℂ} (hfg : EqOn f g (Ioi 0)) :
    PartI.seedPlanar f = PartI.seedPlanar g := by
  funext z
  unfold PartI.seedPlanar Planar.NUE.Ang.ofProfile Planar.NUE.Ang.angPhase
  by_cases hz : z = 0
  · subst hz; simp
  · rw [hfg (norm_pos_iff.mpr hz)]

/-- Polynomial-times-Gaussian bound absorbed into `exp(-(y₁² + y₂²)/8)`. -/
lemma poly_exp_quarter_le_exp_eighth (N : ℕ) (y : ℝ × ℝ) :
    (1 + ‖planeToC y‖) ^ N * Real.exp (-(‖planeToC y‖ ^ 2) / 4) ≤
      Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
  have h1 : (1 + ‖planeToC y‖) ^ N ≤ (Real.exp ‖planeToC y‖) ^ N := by
    gcongr
    linarith [Real.add_one_le_exp ‖planeToC y‖]
  rw [← Real.exp_nat_mul] at h1
  have h2 : (N : ℝ) * ‖planeToC y‖ ≤ ‖planeToC y‖ ^ 2 / 8 + 2 * (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (‖planeToC y‖ - 4 * (N : ℝ))]
  have h3 := Real.exp_le_exp.mpr h2
  rw [Real.exp_add] at h3
  have h4 : (1 + ‖planeToC y‖) ^ N ≤
      Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (‖planeToC y‖ ^ 2 / 8) := by
    linarith [h1, h3]
  calc (1 + ‖planeToC y‖) ^ N * Real.exp (-(‖planeToC y‖ ^ 2) / 4)
      ≤ (Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (‖planeToC y‖ ^ 2 / 8)) *
          Real.exp (-(‖planeToC y‖ ^ 2) / 4) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(‖planeToC y‖ ^ 2) / 8) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ = Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
        rw [norm_planeToC_sq]

/-- Smoothness and weighted Gaussian derivative decay for `κ.e j` under `IsSeedKernels κ`. -/
theorem seed_e_smooth_decay {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    (∀ j : Fin 2, ContDiff ℝ ∞ (κ.e j)) ∧
    (∀ j : Fin 2, ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ × ℝ,
      (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (κ.e j) y‖ ≤
        C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) := by
  obtain ⟨lam, h, hh, ℓ, hIS, he0, he1, _⟩ := hκ
  obtain ⟨_, _, h', hae', hsm', hder', _, _, _, _, _, _⟩ :=
    PartI.seedModeRegularity_proof lam h hh ℓ hIS
  have hcont_h' : ContinuousOn h' (Ioi 0) := by
    have hcd : ContinuousOn (fun r : ℝ => PartI.seedPlanar h' (r : ℂ)) (Ioi 0) :=
      (hsm'.continuous.comp Complex.continuous_ofReal).continuousOn
    exact hcd.congr (fun r hr => (seedPlanar_ofReal_eq h' r hr).symm)
  have hcont_h : ContinuousOn h (Ioi 0) := by
    have hce : ContinuousOn (fun r : ℝ => κ.e 0 (r, 0)) (Ioi 0) :=
      ((κ.e_cont 0).comp (continuous_id.prodMk continuous_const)).continuousOn
    refine hce.congr (fun r hr => ?_)
    have hpl : planeToC (r, 0) = (r : ℂ) := by
      apply Complex.ext <;> simp [planeToC]
    dsimp only
    rw [he0 (r, 0), hpl, seedPlanar_ofReal_eq h r hr]
  have heq_h'h : EqOn h' h (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi hcont_h' hcont_h
  have hsp_eq : PartI.seedPlanar h = PartI.seedPlanar h' :=
    (seedPlanar_eq_of_eqOn_Ioi heq_h'h).symm
  have he0_eq : κ.e 0 = (PartI.seedPlanar h') ∘ planeToCCLM := by
    funext y
    simp only [Function.comp_apply, planeToCCLM_apply, he0 y, hsp_eq]
  have he1_eq : κ.e 1 = Complex.conjLIE ∘ (κ.e 0) := by
    funext y
    simp only [Function.comp_apply, Complex.conjLIE_apply, he1 y, he0 y]
  have hsm0 : ContDiff ℝ ∞ (κ.e 0) := by
    rw [he0_eq]
    exact hsm'.comp planeToCCLM.contDiff
  have hsm1 : ContDiff ℝ ∞ (κ.e 1) := by
    rw [he1_eq]
    exact Complex.conjCLE.contDiff.comp hsm0
  refine ⟨fun j => by fin_cases j; exacts [hsm0, hsm1], fun j k => ?_⟩
  obtain ⟨C0, N, hC0⟩ := hder' k
  have hsm_k : ContDiff ℝ k (PartI.seedPlanar h') :=
    hsm'.of_le (by exact_mod_cast le_top)
  set C : ℝ := |C0| * ‖planeToCCLM‖ ^ k * Real.exp (2 * ((N + 1 : ℕ) : ℝ) ^ 2)
  have hC_nonneg : 0 ≤ C := by positivity
  refine ⟨C, hC_nonneg, fun y => ?_⟩
  have hnorm_j : ‖iteratedFDeriv ℝ k (κ.e j) y‖ = ‖iteratedFDeriv ℝ k (κ.e 0) y‖ := by
    fin_cases j
    · rfl
    · change ‖iteratedFDeriv ℝ k (κ.e 1) y‖ = ‖iteratedFDeriv ℝ k (κ.e 0) y‖
      rw [he1_eq, Complex.conjLIE.norm_iteratedFDeriv_comp_left (κ.e 0) y k]
  have hcomp : ‖iteratedFDeriv ℝ k (κ.e 0) y‖ ≤
      ‖iteratedFDeriv ℝ k (PartI.seedPlanar h') (planeToC y)‖ * ‖planeToCCLM‖ ^ k := by
    rw [he0_eq, ContinuousLinearMap.iteratedFDeriv_comp_right planeToCCLM hsm_k y le_rfl]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [planeToCCLM_apply]
  have hbase : ‖iteratedFDeriv ℝ k (PartI.seedPlanar h') (planeToC y)‖ ≤
      |C0| * (1 + ‖planeToC y‖) ^ N * Real.exp (-(‖planeToC y‖ ^ 2) / 4) := by
    refine (hC0 (planeToC y)).trans ?_
    gcongr
    exact le_abs_self C0
  have hy_le : 1 + ‖y‖ ≤ 1 + ‖planeToC y‖ := by linarith [norm_le_norm_planeToC y]
  rw [hnorm_j]
  calc (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (κ.e 0) y‖
      ≤ (1 + ‖planeToC y‖) *
          ((|C0| * (1 + ‖planeToC y‖) ^ N * Real.exp (-(‖planeToC y‖ ^ 2) / 4)) *
            ‖planeToCCLM‖ ^ k) := by
        refine mul_le_mul hy_le (hcomp.trans ?_) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = |C0| * ‖planeToCCLM‖ ^ k *
          ((1 + ‖planeToC y‖) ^ (N + 1) * Real.exp (-(‖planeToC y‖ ^ 2) / 4)) := by
        rw [pow_succ]
        ring
    _ ≤ |C0| * ‖planeToCCLM‖ ^ k *
          (Real.exp (2 * ((N + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) := by
        refine mul_le_mul_of_nonneg_left (poly_exp_quarter_le_exp_eighth (N + 1) y) (by positivity)
    _ = C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
        simp only [C]
        ring

/-- Translate bounds of order `0, 1, 2` for `κ.e j` in the form required by
`Gaussian.movingCell_identity`. -/
lemma seed_e_translate_bounds {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (j : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ z : ℝ × ℝ, ‖κ.e j z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ (κ.e j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 (κ.e j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) := by
  have hdec := (seed_e_smooth_decay hκ).2 j
  obtain ⟨C0, hC0_pos, hC0⟩ := hdec 0
  obtain ⟨C1, hC1_pos, hC1⟩ := hdec 1
  obtain ⟨C2, hC2_pos, hC2⟩ := hdec 2
  set C := 16 * max C0 (max C1 C2)
  refine ⟨C, by positivity, fun z => ?_, fun z => ?_, fun z => ?_⟩
  · have h0 := hC0 z
    rw [norm_iteratedFDeriv_zero] at h0
    have hle : ‖κ.e j z‖ ≤ (1 + ‖z‖) * ‖κ.e j z‖ := by
      nlinarith [norm_nonneg z, norm_nonneg (κ.e j z)]
    have hmax : C0 ≤ max C0 (max C1 C2) := le_max_left _ _
    calc ‖κ.e j z‖ ≤ C0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := hle.trans h0
      _ ≤ max C0 (max C1 C2) * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
          mul_le_mul hmax (FrameCont.exp_le_translate_weight z.1 z.2)
            (Real.exp_pos _).le (by positivity)
      _ = C * (1 + |z.1|) ^ (-(2 : ℝ)) := by simp only [C]; ring
  · have h1 := hC1 z
    rw [norm_iteratedFDeriv_one] at h1
    have hmax : C1 ≤ max C0 (max C1 C2) := le_trans (le_max_left _ _) (le_max_right _ _)
    calc (1 + ‖z‖) * ‖fderiv ℝ (κ.e j) z‖
        ≤ C1 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := h1
      _ ≤ max C0 (max C1 C2) * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
          mul_le_mul hmax (FrameCont.exp_le_translate_weight z.1 z.2)
            (Real.exp_pos _).le (by positivity)
      _ = C * (1 + |z.1|) ^ (-(2 : ℝ)) := by simp only [C]; ring
  · have h2 := hC2 z
    have hle : ‖iteratedFDeriv ℝ 2 (κ.e j) z‖ ≤
        (1 + ‖z‖) * ‖iteratedFDeriv ℝ 2 (κ.e j) z‖ := by
      nlinarith [norm_nonneg z, norm_nonneg (iteratedFDeriv ℝ 2 (κ.e j) z)]
    have hmax : C2 ≤ max C0 (max C1 C2) := le_trans (le_max_right _ _) (le_max_right _ _)
    calc ‖iteratedFDeriv ℝ 2 (κ.e j) z‖
        ≤ C2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := hle.trans h2
      _ ≤ max C0 (max C1 C2) * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
          mul_le_mul hmax (FrameCont.exp_le_translate_weight z.1 z.2)
            (Real.exp_pos _).le (by positivity)
      _ = C * (1 + |z.1|) ^ (-(2 : ℝ)) := by simp only [C]; ring

/-- For any `C²` complex field `W`, `movD W` agrees with `Gaussian.dilationGen W`. -/
lemma movD_eq_dilationGen {W : ℝ × ℝ → ℂ} (hW : ContDiff ℝ 2 W) (y : ℝ × ℝ) :
    movD W y = UnforcedLeray.Gaussian.dilationGen W y := by
  have hd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have h11 : ContDiff ℝ (1 + 1) W := by rwa [one_add_one_eq_two]
  have hdQ : Differentiable ℝ (UnforcedLeray.Cyl.partialQ W) :=
    (UnforcedLeray.Cyl.contDiff_partialQ h11).differentiable (by norm_num)
  have hdE : Differentiable ℝ (UnforcedLeray.Cyl.partialEta W) :=
    (UnforcedLeray.Cyl.contDiff_partialEta h11).differentiable (by norm_num)
  have hpQ : UnforcedLeray.Cyl.partialQ W = pdCx 0 W := by
    funext z
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hd z]
    rfl
  have hpE : UnforcedLeray.Cyl.partialEta W = pdCx 1 W := by
    funext z
    rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hd z]
    rfl
  have hlap : UnforcedLeray.Cyl.laplacian W y = ladLapCx W y := by
    unfold UnforcedLeray.Cyl.laplacian ladLapCx
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hdQ y,
      UnforcedLeray.Cyl.partialEta_eq_fderiv hdE y, hpQ, hpE]
    rfl
  have hy_decomp : y = y.1 • B0579.dir 0 + y.2 • B0579.dir 1 := by
    ext <;> simp [B0579.dir]
  have hdir : fderiv ℝ W y y = ((y.1 : ℝ) : ℂ) * pdCx 0 W y + ((y.2 : ℝ) : ℂ) * pdCx 1 W y := by
    have happ := congrArg (fderiv ℝ W y) hy_decomp
    rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul] at happ
    rw [happ]
    simp [pdCx, Complex.real_smul]
  rw [UnforcedLeray.Gaussian.dilationGen_eq, hlap, hdir]
  unfold movD
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Age derivative of the moving cell length `d(r) = cellLen (ν ^ (-2)) (clockA ν r)`. -/
lemma hasDerivAt_cellLen {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    let d := fun r' => cellLen (ν ^ (-2 : ℝ)) (clockA ν r')
    let ϑ := (clockA ν r) ^ (-2 : ℝ) * (clockTheta ν r)⁻¹
    HasDerivAt d (-(ϑ / 2) * d r) r := by
  intro d ϑ
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsq : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha0
  have hdA : HasDerivAt (clockA ν) ν r := FrameAmplSub.hasDerivAt_clockA ν r
  have hdSqrt : HasDerivAt (fun r' => Real.sqrt (clockA ν r'))
      (ν / (2 * Real.sqrt (clockA ν r))) r := hdA.sqrt ha0.ne'
  have hdDiv := (hasDerivAt_const r (ν ^ (-2 : ℝ))).div hdSqrt hsq.ne'
  refine hdDiv.congr_deriv ?_
  dsimp only [d, ϑ, cellLen]
  rw [Real.rpow_neg ha0.le, Real.rpow_two, Real.sq_sqrt ha0.le]
  unfold clockTheta
  rw [inv_inv]
  field_simp [ha0.ne', hsq.ne']
  rw [Real.sq_sqrt ha0.le]
  ring

/-- Exact periodization identity for `movOscRes`:
`movOscRes κ ν r j y = (clockTheta ν r : ℂ)⁻¹ * perSum d(r) (movD (κ.e j)) y` (SP 2905). -/
theorem movOscRes_eq_perSum_movD {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (j : Fin 2) (y : ℝ × ℝ) :
    movOscRes κ ν r j y =
      (clockTheta ν r : ℂ)⁻¹ *
        perSum (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (movD (κ.e j)) y := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  set d : ℝ → ℝ := fun r' => cellLen (ν ^ (-2 : ℝ)) (clockA ν r')
  have hd0 : 0 < d r := div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha0)
  have hsm_inf : ContDiff ℝ ∞ (κ.e j) := (seed_e_smooth_decay hκ).1 j
  have hsm2 : ContDiff ℝ 2 (κ.e j) := hsm_inf.of_le (by simp)
  obtain ⟨C, _, h0, h1, h2⟩ := seed_e_translate_bounds hκ j
  set ϑ : ℝ := (clockA ν r) ^ (-2 : ℝ) * (clockTheta ν r)⁻¹
  have hd_deriv : HasDerivAt d (-(ϑ / 2) * d r) r := hasDerivAt_cellLen hν hr
  have hmov := UnforcedLeray.Gaussian.movingCell_identity hsm2 (s := 2) (by norm_num)
    h0 h1 h2 hd0 hd_deriv y
  have hper_eq : ∀ r', perE κ (d r') j = UnforcedLeray.Gaussian.periodize (d r') (κ.e j) := by
    intro r'
    funext z
    exact perSum_eq_periodize (d r') (κ.e j) z
  have hper_cd : ContDiff ℝ 2 (perE κ (d r) j) := by
    rw [hper_eq r]
    exact UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (N := (2 : ℕ)) (by norm_num) hd0.ne'
      hsm2 (UnforcedLeray.Gaussian.iteratedFDeriv_bounds_of h0 h1 h2)
  have hder_per : HasDerivAt (fun r' => perE κ (d r') j y)
      ((-(ϑ / 2) * d r) • -UnforcedLeray.Gaussian.periodShift (κ.e j) (d r) y) r := by
    simp_rw [hper_eq]
    exact (UnforcedLeray.Gaussian.hasDerivAt_periodize_period
      (hsm2.differentiable (by norm_num)) (by norm_num) hd0 h0 h1 y).scomp r hd_deriv
  have hladDt : ladDt (fun r' y' => perE κ (d r') j y') r y =
      deriv (fun r' => UnforcedLeray.Gaussian.periodize (d r') (κ.e j) y) r := by
    rw [ladDt_eq_of_hasDerivAt hder_per]
    simp_rw [← hper_eq]
    exact hder_per.deriv.symm
  have hD_per : movD (perE κ (d r) j) y =
      UnforcedLeray.Gaussian.dilationGen (UnforcedLeray.Gaussian.periodize (d r) (κ.e j)) y := by
    rw [movD_eq_dilationGen hper_cd, hper_eq r]
  have hD_e : perSum (d r) (movD (κ.e j)) y =
      UnforcedLeray.Gaussian.periodize (d r) (UnforcedLeray.Gaussian.dilationGen (κ.e j)) y := by
    rw [perSum_eq_periodize]
    congr 1
    funext z
    exact movD_eq_dilationGen hsm2 z
  have ha2_mul_ϑ : (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * (ϑ : ℂ) = (clockTheta ν r : ℂ)⁻¹ := by
    have h_real : (clockA ν r) ^ (2 : ℝ) * (clockA ν r) ^ (-2 : ℝ) = 1 := by
      rw [← Real.rpow_add ha0]
      norm_num
    simp only [ϑ, Complex.ofReal_mul, Complex.ofReal_inv, ← mul_assoc]
    have h_cx : (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) = 1 := by
      exact_mod_cast h_real
    rw [h_cx, one_mul]
  have hmov_cx := congrArg (fun w : ℂ => (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * w) hmov
  simp only [Complex.real_smul] at hmov_cx
  unfold movOscRes movEz
  rw [hD_per, hladDt, hD_e, ← ha2_mul_ϑ]
  linear_combination hmov_cx

/-- Smoothness and Gaussian decay of `movD (κ.e j)`. -/
lemma movD_seed_decay {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (j : Fin 2) :
    Continuous (movD (κ.e j)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ × ℝ, ‖movD (κ.e j) y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
  have hsm_inf : ContDiff ℝ ∞ (κ.e j) := (seed_e_smooth_decay hκ).1 j
  have hsm2 : ContDiff ℝ 2 (κ.e j) := hsm_inf.of_le (by simp)
  have hcont : Continuous (movD (κ.e j)) := by
    unfold movD ladLapCx pdCx
    have hd1 : ∀ k : Fin 2, ContDiff ℝ 2 (fun y => fderiv ℝ (κ.e j) y (B0579.dir k)) :=
      fun k => (hsm_inf.fderiv_right (m := (2 : ℕ)) (by simp)).clm_apply contDiff_const
    have hd2 : ∀ k : Fin 2, Continuous (fun y =>
        fderiv ℝ (fun z => fderiv ℝ (κ.e j) z (B0579.dir k)) y (B0579.dir k)) :=
      fun k => (((hd1 k).fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply contDiff_const).continuous
    have hc1 := hd2 0
    have hc2 := hd2 1
    have hc3 := (hd1 0).continuous
    have hc4 := (hd1 1).continuous
    have hc0 := hsm_inf.continuous
    fun_prop
  have hdec := (seed_e_smooth_decay hκ).2 j
  obtain ⟨C0, hC0_pos, hC0⟩ := hdec 0
  obtain ⟨C1, hC1_pos, hC1⟩ := hdec 1
  obtain ⟨C2, hC2_pos, hC2⟩ := hdec 2
  refine ⟨hcont, 2 * C2 + C1 + 2 * C0, by positivity, fun y => ?_⟩
  rw [movD_eq_dilationGen hsm2, UnforcedLeray.Gaussian.dilationGen_eq]
  have hlap : ‖UnforcedLeray.Cyl.laplacian (κ.e j) y‖ ≤
      2 * C2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    have h1 := UnforcedLeray.Gaussian.norm_laplacian_le hsm2 y
    have h2 : ‖iteratedFDeriv ℝ 2 (κ.e j) y‖ ≤
        (1 + ‖y‖) * ‖iteratedFDeriv ℝ 2 (κ.e j) y‖ := by
      nlinarith [norm_nonneg y, norm_nonneg (iteratedFDeriv ℝ 2 (κ.e j) y)]
    have h3 := h2.trans (hC2 y)
    linarith
  have hdrift : ‖(1 / 2 : ℝ) • fderiv ℝ (κ.e j) y y‖ ≤
      C1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have h1 : ‖fderiv ℝ (κ.e j) y y‖ ≤ (1 + ‖y‖) * ‖iteratedFDeriv ℝ 1 (κ.e j) y‖ := by
      rw [norm_iteratedFDeriv_one]
      refine ((fderiv ℝ (κ.e j) y).le_opNorm y).trans ?_
      nlinarith [norm_nonneg (fderiv ℝ (κ.e j) y), norm_nonneg y]
    have h2 := h1.trans (hC1 y)
    linarith [norm_nonneg (fderiv ℝ (κ.e j) y y)]
  have hval : ‖(2 : ℝ) • κ.e j y‖ ≤ 2 * C0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h1 : ‖κ.e j y‖ ≤ (1 + ‖y‖) * ‖iteratedFDeriv ℝ 0 (κ.e j) y‖ := by
      rw [norm_iteratedFDeriv_zero]
      nlinarith [norm_nonneg (κ.e j y), norm_nonneg y]
    have h2 := h1.trans (hC0 y)
    linarith
  calc ‖UnforcedLeray.Cyl.laplacian (κ.e j) y + (1 / 2 : ℝ) • fderiv ℝ (κ.e j) y y +
          (2 : ℝ) • κ.e j y‖
      ≤ ‖UnforcedLeray.Cyl.laplacian (κ.e j) y‖ + ‖(1 / 2 : ℝ) • fderiv ℝ (κ.e j) y y‖ +
          ‖(2 : ℝ) • κ.e j y‖ := by
        linarith [norm_add_le (UnforcedLeray.Cyl.laplacian (κ.e j) y +
          (1 / 2 : ℝ) • fderiv ℝ (κ.e j) y y) ((2 : ℝ) • κ.e j y),
          norm_add_le (UnforcedLeray.Cyl.laplacian (κ.e j) y)
          ((1 / 2 : ℝ) • fderiv ℝ (κ.e j) y y)]
    _ ≤ 2 * C2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) +
          C1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) +
          2 * C0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
        linarith
    _ = (2 * C2 + C1 + 2 * C0) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring

/-- Pointwise Gaussian bound on `B0579.cell d` (`d ≥ 1`) for `perSum d g` when `g` has Gaussian
decay `exp(-(y₁² + y₂²)/8)`. -/
lemma perSum_pointwise_of_gauss {g : ℝ × ℝ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hg : ∀ y : ℝ × ℝ, ‖g y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ d : ℝ, 1 ≤ d → ∀ x ∈ B0579.cell d,
      ‖perSum d g x‖ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
  set S : ℝ := ∑' n : ℤ, Real.exp (-(n : ℝ) ^ 2 / (4 * 16))
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨C * S, mul_nonneg hC0 hS0, fun d hd x hx => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hx1 : |x.1| ≤ d / 2 := by
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hx
    rw [abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hterm : ∀ n : ℤ, ‖g (x.1 + n * d, x.2)‖ ≤
      C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) * Real.exp (-(n : ℝ) ^ 2 / (4 * 16)) := by
    intro n
    refine (hg (x.1 + n * d, x.2)).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
    by_cases hn : n = 0
    · subst hn
      simp only [Int.cast_zero, zero_mul, add_zero]
      nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    · have hN : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have hND : |(n : ℝ)| * d = |(n : ℝ) * d| := by rw [abs_mul, abs_of_pos hd0]
      have htri : |(n : ℝ) * d| ≤ |x.1 + n * d| + |x.1| := by
        calc |(n : ℝ) * d| = |(x.1 + n * d) - x.1| := by congr 1; ring
          _ ≤ |x.1 + n * d| + |x.1| := abs_sub _ _
      have hlow : |(n : ℝ)| * d / 2 ≤ |x.1 + n * d| := by
        nlinarith [mul_le_mul_of_nonneg_right hN hd0.le]
      have hsq : ((n : ℝ) * d) ^ 2 / 4 ≤ (x.1 + n * d) ^ 2 := by
        have h := pow_le_pow_left₀ (by positivity) hlow 2
        have e1 : (|(n : ℝ)| * d / 2) ^ 2 = ((n : ℝ) * d) ^ 2 / 4 := by
          rw [div_pow, mul_pow, sq_abs]; ring
        rwa [e1, sq_abs] at h
      have hx2 : x.1 ^ 2 ≤ d ^ 2 / 4 := by
        have := pow_le_pow_left₀ (abs_nonneg x.1) hx1 2
        rw [sq_abs, div_pow] at this
        linarith
      have hn2 : 1 ≤ (n : ℝ) ^ 2 := by
        have : 1 ≤ |(n : ℝ)| ^ 2 := by nlinarith
        rwa [sq_abs] at this
      have hd2 : 1 ≤ d ^ 2 := by nlinarith
      have hA : x.1 ^ 2 ≤ (x.1 + n * d) ^ 2 := by
        have : d ^ 2 / 4 ≤ ((n : ℝ) * d) ^ 2 / 4 := by
          rw [mul_pow]; nlinarith [sq_nonneg d]
        linarith
      have hB : (n : ℝ) ^ 2 / 4 ≤ (x.1 + n * d) ^ 2 := by
        have : (n : ℝ) ^ 2 / 4 ≤ ((n : ℝ) * d) ^ 2 / 4 := by
          rw [mul_pow]; nlinarith [sq_nonneg (n : ℝ)]
        linarith
      nlinarith [sq_nonneg x.2]
  have hsumR : Summable (fun n : ℤ =>
      C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) * Real.exp (-(n : ℝ) ^ 2 / (4 * 16))) :=
    summable_exp_int_sq.mul_left _
  have hsumG : Summable (fun n : ℤ => ‖g (x.1 + n * d, x.2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumR
  calc ‖perSum d g x‖ ≤ ∑' n : ℤ, ‖g (x.1 + n * d, x.2)‖ := by
        unfold perSum
        exact norm_tsum_le_tsum_norm hsumG
    _ ≤ ∑' n : ℤ, C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) *
          Real.exp (-(n : ℝ) ^ 2 / (4 * 16)) := hsumG.tsum_le_tsum hterm hsumR
    _ = (C * S) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
        rw [tsum_mul_left]; ring

end OscillatorForceSub

open OscillatorForceSub

/-- **Leaf 2 (`ComplModeForceOscillator`, `PartIII-a:T21/c3/3/2`, SP 2905)**: the oscillator and
cell-length drift residual `movOscRes κ ν r j = θ(r)⁻¹ P_{d(r)}(D e_j)` is a.e. strongly measurable
and bounded in `X_{m,d(r)}` by `C₁ / clockTheta ν r`. -/
theorem complModeForceOscillator (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplModeForceOscillator κ := by
  intro hκ m hm
  obtain ⟨hcont0, C_D0, hCD0_pos, hCD0⟩ := movD_seed_decay hκ 0
  obtain ⟨hcont1, C_D1, hCD1_pos, hCD1⟩ := movD_seed_decay hκ 1
  obtain ⟨M0, hM0_pos, hM0⟩ := perSum_pointwise_of_gauss hCD0_pos hCD0
  obtain ⟨M1, hM1_pos, hM1⟩ := perSum_pointwise_of_gauss hCD1_pos hCD1
  obtain ⟨K_m, hKm_pos, hKm⟩ := xNorm_le_of_gauss (m := m) (by linarith)
  set M := max M0 M1
  have hM_pos : 0 ≤ M := le_trans hM0_pos (le_max_left _ _)
  refine ⟨M * K_m, 1, mul_nonneg hM_pos hKm_pos, le_rfl, fun b hb => ?_⟩
  refine ⟨1, zero_lt_one, fun ν hν r hr hbr j => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν_le1 : ν ≤ 1 := hν.2
  have hθ_ge1 : 1 ≤ clockTheta ν r := hb.trans hbr
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ_ge1
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hd_ge1 : 1 ≤ d := ComplCouplingSub.one_le_cellLen_of_theta hν_pos hν_le1 hr hθ_ge1
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd_ge1
  have hOsc_eq : movOscRes κ ν r j =
      fun y => (clockTheta ν r : ℂ)⁻¹ * perSum d (movD (κ.e j)) y := by
    funext y
    exact movOscRes_eq_perSum_movD hκ hν_pos hr j y
  have hper_cont : Continuous (perSum d (movD (κ.e j))) := by
    fin_cases j
    · exact FrameCont.perSum_continuous hcont0
        (fun z => (hCD0 z).trans (by
          have := FrameCont.exp_le_translate_weight z.1 z.2
          calc C_D0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
              ≤ C_D0 * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
                mul_le_mul_of_nonneg_left this hCD0_pos
            _ = (16 * C_D0) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring)) hd_pos.ne'
    · exact FrameCont.perSum_continuous hcont1
        (fun z => (hCD1 z).trans (by
          have := FrameCont.exp_le_translate_weight z.1 z.2
          calc C_D1 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
              ≤ C_D1 * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
                mul_le_mul_of_nonneg_left this hCD1_pos
            _ = (16 * C_D1) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring)) hd_pos.ne'
  refine ⟨?_, ?_⟩
  · rw [hOsc_eq]
    exact (continuous_const.mul hper_cont).aestronglyMeasurable
  · rw [hOsc_eq]
    have hpt : ∀ x ∈ B0579.cell d,
        ‖(clockTheta ν r : ℂ)⁻¹ * perSum d (movD (κ.e j)) x‖ ≤
          (M / clockTheta ν r) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
      intro x hx
      rw [norm_mul, norm_inv, Complex.norm_of_nonneg hθ_pos.le]
      have hper_le : ‖perSum d (movD (κ.e j)) x‖ ≤
          M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
        fin_cases j
        · exact (hM0 d hd_ge1 x hx).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
        · exact (hM1 d hd_ge1 x hx).trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
      calc (clockTheta ν r)⁻¹ * ‖perSum d (movD (κ.e j)) x‖
          ≤ (clockTheta ν r)⁻¹ * (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) :=
            mul_le_mul_of_nonneg_left hper_le (inv_nonneg.2 hθ_pos.le)
        _ = (M / clockTheta ν r) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
            ring
    refine (hKm d (M / clockTheta ν r) _ (div_nonneg hM_pos hθ_pos.le) hpt).trans ?_
    refine le_of_eq ?_
    congr 1
    ring

end UnforcedLeray.Short.IIIa
