import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.Pullback
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.GradPerSum
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound.GramInvSplit
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.DivZero
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.TrainV
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjIBP
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_3.AdjFubini0

/-!
# Helper 2 for `PartIII-a:T21/c3/2/1/2/3/3/1/4`: Moving Euler Adjoint Pairing Identity

Source of record: `the November 2 reference manuscript` (SP), lines 2862-2865 and
2905-2918.

Proves that for sufficiently large moving cell length `d = cellLen (ν ^ (-2 : ℝ)) (clockA ν r)`
(`ν ∈ (0, 1]`, `IsBUCTrain tr`), the moving linearised Euler adjoint `movEulerAdj` acting on
`perLam κ d i` transposes against `perE κ d k` on `B0579.cell d` into `movL tr r (perE κ d k)`:
`∫ y in B0579.cell d, movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam κ d i) y * perE κ d k y =`
`  ∫ y in B0579.cell d, perLam κ d i y * movL tr r (perE κ d k) y`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.MovFrameLeavesAux

private lemma gauss16_integrableOn_cell (d : ℝ) :
    IntegrableOn (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) (B0579.cell d) := by
  have h := UnforcedLeray.Gaussian.integrable_gauss_plane (a := 4) (by norm_num)
  have h' : Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
    h.congr (Eventually.of_forall fun y => by norm_num)
  exact h'.integrableOn

private lemma integrableOn_cell_of_le_gauss16 {d M : ℝ} {f : ℝ × ℝ → ℂ} (hf : Continuous f)
    (hbd : ∀ y ∈ B0579.cell d, ‖f y‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :
    IntegrableOn f (B0579.cell d) := by
  have hmeas : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  exact ((gauss16_integrableOn_cell d).const_mul M).mono'
    hf.aestronglyMeasurable.restrict ((ae_restrict_iff' hmeas).mpr (Eventually.of_forall hbd))

private lemma pd_re_eq {H : ℝ × ℝ → ℂ} (hH : Differentiable ℝ H) (l : Fin 2) (y : ℝ × ℝ) :
    B0579.pd l (fun z => (H z).re) y = (pdCx l H y).re := by
  have h : HasFDerivAt (fun z => (H z).re) (Complex.reCLM.comp (fderiv ℝ H y)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hH y).hasFDerivAt
  unfold B0579.pd pdCx
  rw [h.fderiv]
  rfl

private lemma pd_im_eq {H : ℝ × ℝ → ℂ} (hH : Differentiable ℝ H) (l : Fin 2) (y : ℝ × ℝ) :
    B0579.pd l (fun z => (H z).im) y = (pdCx l H y).im := by
  have h : HasFDerivAt (fun z => (H z).im) (Complex.imCLM.comp (fderiv ℝ H y)) y :=
    Complex.imCLM.hasFDerivAt.comp y (hH y).hasFDerivAt
  unfold B0579.pd pdCx
  rw [h.fderiv]
  rfl

private lemma movingTrainV_divFree {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (y : ℝ × ℝ) :
    B0579.pd 0 (fun z => movingTrainV tr r z 0) y +
      B0579.pd 1 (fun z => movingTrainV tr r z 1) y = 0 := by
  set a := clockA ν r
  have ha1 : 1 ≤ a := one_le_clockA hν.le hr
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  have hk_ne : a ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ha0 _).ne'
  have hvC : ContDiff ℝ ∞ (fun z : ℝ × ℝ => tr.v r z) :=
    contDiffOn_univ.1 (tr.isTrain.smooth_v.comp
      ((contDiffOn_const (c := r)).prodMk contDiffOn_id)
      (fun z _ => (⟨hr, mem_univ z⟩ : ((r, z) : ℝ × (ℝ × ℝ)) ∈ Ici (0 : ℝ) ×ˢ univ)))
  have hvr : ∀ l : Fin 2, Differentiable ℝ (fun z : ℝ × ℝ => tr.v r z l) := fun l =>
    (((EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff).comp hvC).differentiable
      (by simp)
  have hpd0 := E0.rescaleRHS_pd (fun z => tr.v r z 0) (Real.sqrt a) (a ^ (3 / 2 : ℝ)) hsa hk_ne 0 y
  have hpd1 := E0.rescaleRHS_pd (fun z => tr.v r z 1) (Real.sqrt a) (a ^ (3 / 2 : ℝ)) hsa hk_ne 1 y
  set z : ℝ × ℝ := (Real.sqrt a * y.1, Real.sqrt a * y.2)
  have hsol := tr.isTrain.solenoidal r hr z
  unfold UnforcedLeray.Cyl.divergence at hsol
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv (hvr 0) z,
    UnforcedLeray.Cyl.partialEta_eq_fderiv (hvr 1) z] at hsol
  have hsol' : B0579.pd 0 (fun w => tr.v r w 0) z + B0579.pd 1 (fun w => tr.v r w 1) z = 0 := hsol
  unfold movingTrainV
  rw [hpd0, hpd1]
  dsimp only [a, z] at hsol' ⊢
  linear_combination (a ^ (3 / 2 : ℝ) * Real.sqrt a) * hsol'

/-- Transport cylinder IBP for a `C¹` divergence-free `d`-periodic field `V` bounded on
`B0579.cell d` against `Φ = perLam κ d i` and `Ψ = perE κ d k`. -/
private lemma integral_transCx_perLam_mul_perE {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {d CV : ℝ} (hd1 : 1 ≤ d) (hCV0 : 0 ≤ CV)
    {V : ℝ × ℝ → Fin 2 → ℝ} (hV1 : ContDiff ℝ 1 V)
    (hVper : ∀ y : ℝ × ℝ, V (y.1 + d, y.2) = V y)
    (hVdiv : ∀ y : ℝ × ℝ, B0579.pd 0 (fun z => V z 0) y + B0579.pd 1 (fun z => V z 1) y = 0)
    (hVbd : ∀ y ∈ B0579.cell d, ∀ l : Fin 2, |V y l| ≤ CV)
    (hGinv : ∀ m n : Fin 2, ‖(perGram κ d)⁻¹ m n‖ ≤ 3)
    (i k : Fin 2) :
    IntegrableOn (fun y => E0.transCx V (perLam κ d i) y * perE κ d k y) (B0579.cell d) ∧
    IntegrableOn (fun y => perLam κ d i y * E0.transCx V (perE κ d k) y) (B0579.cell d) ∧
    (∫ y in B0579.cell d, E0.transCx V (perLam κ d i) y * perE κ d k y) =
      -(∫ y in B0579.cell d, perLam κ d i y * E0.transCx V (perE κ d k) y) := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  -- Regularity and periodicity of `Φ = perLam κ d i` and `Ψ = perE κ d k`
  obtain ⟨hCD, C, _, h0, h1, h2⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  have hperLam0_CD : ∀ j : Fin 2, ContDiff ℝ 2 (perLam0 κ d j) := by
    intro j
    obtain ⟨ht0, ht1, ht2⟩ := ComplCouplingHeat.translate_jet2_bounds (h0 j) (h1 j) (h2 j)
    have heq : perLam0 κ d j = UnforcedLeray.Gaussian.periodize d (κ.lamP j) :=
      ComplCouplingHeat.perSum_eq_periodize_fun d (κ.lamP j)
    rw [heq]
    exact UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (N := (2 : ℕ)) (by norm_num) hd0.ne'
      (hCD j) (UnforcedLeray.Gaussian.iteratedFDeriv_bounds_of ht0 ht1 ht2)
  set Φ : ℝ × ℝ → ℂ := perLam κ d i
  set Ψ : ℝ × ℝ → ℂ := perE κ d k
  have hΦ_eq : Φ = fun y => (perGram κ d)⁻¹ i 0 * perLam0 κ d 0 y +
      (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 y := by
    funext y; unfold Φ perLam; exact Fin.sum_univ_two _
  have hΦ1 : ContDiff ℝ 1 Φ := by
    rw [hΦ_eq]
    exact ((contDiff_const.mul ((hperLam0_CD 0).of_le (by norm_num))).add
      (contDiff_const.mul ((hperLam0_CD 1).of_le (by norm_num))))
  have hΦd : Differentiable ℝ Φ := hΦ1.differentiable (by norm_num)
  have hΦper : ∀ y : ℝ × ℝ, Φ (y.1 + d, y.2) = Φ y := by
    intro y
    rw [hΦ_eq]
    dsimp only
    rw [show perLam0 κ d 0 (y.1 + d, y.2) = perLam0 κ d 0 y from
        CutFTCDual.perSum_periodic d (κ.lamP 0) y,
      show perLam0 κ d 1 (y.1 + d, y.2) = perLam0 κ d 1 y from
        CutFTCDual.perSum_periodic d (κ.lamP 1) y]
  have hΨ2 : ContDiff ℝ 2 Ψ := by
    have hsm2 : ContDiff ℝ 2 (κ.e k) := ((OscillatorForceSub.seed_e_smooth_decay hκ).1 k).of_le
      (by simp)
    obtain ⟨_, _, he0, he1, he2⟩ := OscillatorForceSub.seed_e_translate_bounds hκ k
    have heq : Ψ = UnforcedLeray.Gaussian.periodize d (κ.e k) :=
      ComplCouplingHeat.perSum_eq_periodize_fun d (κ.e k)
    rw [heq]
    exact UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (N := (2 : ℕ)) (by norm_num) hd0.ne'
      hsm2 (UnforcedLeray.Gaussian.iteratedFDeriv_bounds_of he0 he1 he2)
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ2.of_le (by norm_num)
  have hΨd : Differentiable ℝ Ψ := hΨ1.differentiable (by norm_num)
  have hΨper : ∀ y : ℝ × ℝ, Ψ (y.1 + d, y.2) = Ψ y :=
    fun y => CutFTCDual.perSum_periodic d (κ.e k) y
  have hVl1 : ∀ l : Fin 2, ContDiff ℝ 1 (fun y => V y l) := fun l =>
    ((ContinuousLinearMap.proj l : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff).comp hV1
  have hVl_d : ∀ l : Fin 2, Differentiable ℝ (fun y => V y l) := fun l =>
    (hVl1 l).differentiable (by norm_num)
  -- Cell bounds on `Φ`, `pdCx l Φ`, `Ψ`, `pdCx l Ψ`
  obtain ⟨B_0, hB0_pos, hB0⟩ := Lam0B.perLam0_sup κ
  have hΦ_sup : ∀ y ∈ B0579.cell d, ‖Φ y‖ ≤ 6 * B_0 := by
    intro y hy
    rw [hΦ_eq]
    calc ‖(perGram κ d)⁻¹ i 0 * perLam0 κ d 0 y + (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 y‖
        ≤ ‖(perGram κ d)⁻¹ i 0 * perLam0 κ d 0 y‖ +
            ‖(perGram κ d)⁻¹ i 1 * perLam0 κ d 1 y‖ := norm_add_le _ _
      _ = ‖(perGram κ d)⁻¹ i 0‖ * ‖perLam0 κ d 0 y‖ +
            ‖(perGram κ d)⁻¹ i 1‖ * ‖perLam0 κ d 1 y‖ := by rw [norm_mul, norm_mul]
      _ ≤ 3 * B_0 + 3 * B_0 := add_le_add
          (mul_le_mul (hGinv i 0) (hB0 d hd1 0 y hy) (norm_nonneg _) (by norm_num))
          (mul_le_mul (hGinv i 1) (hB0 d hd1 1 y hy) (norm_nonneg _) (by norm_num))
      _ = 6 * B_0 := by ring
  obtain ⟨_, _, _, hgrad_dec, hder0⟩ := seedLamGradPerSum κ hκ
  obtain ⟨Bg00, hBg00_pos, hBg00⟩ := ComplCouplingHeat.perSum_cell_sup_of_inv_sq_decay
    (hgrad_dec 0 0)
  obtain ⟨Bg01, hBg01_pos, hBg01⟩ := ComplCouplingHeat.perSum_cell_sup_of_inv_sq_decay
    (hgrad_dec 0 1)
  obtain ⟨Bg10, _, hBg10⟩ := ComplCouplingHeat.perSum_cell_sup_of_inv_sq_decay
    (hgrad_dec 1 0)
  obtain ⟨Bg11, _, hBg11⟩ := ComplCouplingHeat.perSum_cell_sup_of_inv_sq_decay
    (hgrad_dec 1 1)
  set B_g : ℝ := max (max Bg00 Bg01) (max Bg10 Bg11)
  have hBg_pos : 0 ≤ B_g := le_trans hBg00_pos (le_trans (le_max_left _ _) (le_max_left _ _))
  have hpdLam0_sup : ∀ (j l : Fin 2), ∀ y ∈ B0579.cell d, ‖pdCx l (perLam0 κ d j) y‖ ≤ B_g := by
    intro j l y hy
    rw [(hder0 hd1 j l y).2]
    fin_cases j <;> fin_cases l
    · exact (hBg00 d hd1 y hy).trans (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact (hBg01 d hd1 y hy).trans (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact (hBg10 d hd1 y hy).trans (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact (hBg11 d hd1 y hy).trans (le_trans (le_max_right _ _) (le_max_right _ _))
  have hpdΦ_sup : ∀ l : Fin 2, ∀ y ∈ B0579.cell d, ‖pdCx l Φ y‖ ≤ 6 * B_g := by
    intro l y hy
    have h1 := CutFTCAux.pdCx_perLam_eq κ d i l y
      ((hperLam0_CD 0).differentiable (by norm_num) y)
      ((hperLam0_CD 1).differentiable (by norm_num) y)
    change ‖pdCx l (perLam κ d i) y‖ ≤ 6 * B_g
    rw [h1, Fin.sum_univ_two]
    calc ‖(perGram κ d)⁻¹ i 0 * pdCx l (perLam0 κ d 0) y +
            (perGram κ d)⁻¹ i 1 * pdCx l (perLam0 κ d 1) y‖
        ≤ ‖(perGram κ d)⁻¹ i 0‖ * ‖pdCx l (perLam0 κ d 0) y‖ +
            ‖(perGram κ d)⁻¹ i 1‖ * ‖pdCx l (perLam0 κ d 1) y‖ := by
          simpa [norm_mul] using norm_add_le
            ((perGram κ d)⁻¹ i 0 * pdCx l (perLam0 κ d 0) y)
            ((perGram κ d)⁻¹ i 1 * pdCx l (perLam0 κ d 1) y)
      _ ≤ 3 * B_g + 3 * B_g := add_le_add
          (mul_le_mul (hGinv i 0) (hpdLam0_sup 0 l y hy) (norm_nonneg _) (by norm_num))
          (mul_le_mul (hGinv i 1) (hpdLam0_sup 1 l y hy) (norm_nonneg _) (by norm_num))
      _ = 6 * B_g := by ring
  obtain ⟨M_E, hME0, hE_all⟩ := EulerErrorSub.perE_and_pdCx_gauss_bounds hκ
  obtain ⟨hΨ_gauss, _, hpdΨ_gauss⟩ := hE_all d hd1 k
  -- Continuity and `IntegrableOn` of `transCx V Φ * Ψ`, `Φ * transCx V Ψ`, and flux `G`
  have hpdΦ_cont : ∀ l : Fin 2, Continuous (pdCx l Φ) := fun l =>
    (hΦ1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hpdΨ_cont : ∀ l : Fin 2, Continuous (pdCx l Ψ) := fun l =>
    (hΨ1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hTΦ_cont : Continuous (E0.transCx V Φ) := by
    unfold E0.transCx
    exact ((Complex.continuous_ofReal.comp (hVl1 0).continuous).mul (hpdΦ_cont 0)).add
      ((Complex.continuous_ofReal.comp (hVl1 1).continuous).mul (hpdΦ_cont 1))
  have hTΨ_cont : Continuous (E0.transCx V Ψ) := by
    unfold E0.transCx
    exact ((Complex.continuous_ofReal.comp (hVl1 0).continuous).mul (hpdΨ_cont 0)).add
      ((Complex.continuous_ofReal.comp (hVl1 1).continuous).mul (hpdΨ_cont 1))
  have hInt_lhs : IntegrableOn (fun y => E0.transCx V Φ y * Ψ y) (B0579.cell d) := by
    refine integrableOn_cell_of_le_gauss16 (hTΦ_cont.mul hΨ1.continuous)
      (M := (12 * CV * B_g) * M_E) (fun y hy => ?_)
    have hT : ‖E0.transCx V Φ y‖ ≤ 12 * CV * B_g := by
      have h := E0.norm_transCx_le V Φ CV hCV0 y (hVbd y hy 0) (hVbd y hy 1)
      have h0 := hpdΦ_sup 0 y hy
      have h1 := hpdΦ_sup 1 y hy
      nlinarith
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hT (hΨ_gauss y hy) (norm_nonneg _) (by positivity)
  have hInt_rhs : IntegrableOn (fun y => Φ y * E0.transCx V Ψ y) (B0579.cell d) := by
    refine integrableOn_cell_of_le_gauss16 (hΦ1.continuous.mul hTΨ_cont)
      (M := (6 * B_0) * (2 * CV * M_E)) (fun y hy => ?_)
    have hT : ‖E0.transCx V Ψ y‖ ≤ (2 * CV * M_E) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
      have h := E0.norm_transCx_le V Ψ CV hCV0 y (hVbd y hy 0) (hVbd y hy 1)
      have h0 := hpdΨ_gauss 0 y hy
      have h1 := hpdΨ_gauss 1 y hy
      nlinarith [Real.exp_pos (-(y.1 ^ 2 + y.2 ^ 2) / 16)]
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hΦ_sup y hy) hT (norm_nonneg _) (by positivity)
  -- Flux `G l y := (V y l : ℂ) * (Φ y * Ψ y)` and `E0.cellDivZero` on real/imaginary parts
  set G : Fin 2 → ℝ × ℝ → ℂ := fun l y => ((V y l : ℝ) : ℂ) * (Φ y * Ψ y)
  have hG1 : ∀ l : Fin 2, ContDiff ℝ 1 (G l) := fun l =>
    (Complex.ofRealCLM.contDiff.comp (hVl1 l)).mul (hΦ1.mul hΨ1)
  have hGd : ∀ l : Fin 2, Differentiable ℝ (G l) := fun l => (hG1 l).differentiable (by norm_num)
  have hG0_per : ∀ y : ℝ × ℝ, G 0 (y.1 + d, y.2) = G 0 y := by
    intro y
    simp only [G, hVper y, hΦper y, hΨper y]
  have hG1_int : IntegrableOn (G 1) (B0579.cell d) := by
    refine integrableOn_cell_of_le_gauss16 (hG1 1).continuous
      (M := CV * (6 * B_0) * M_E) (fun y hy => ?_)
    dsimp only [G]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc, mul_assoc]
    exact mul_le_mul (hVbd y hy 1)
      (mul_le_mul (hΦ_sup y hy) (hΨ_gauss y hy) (norm_nonneg _) (by positivity))
      (by positivity) hCV0
  have hdiv_G : ∀ y : ℝ × ℝ,
      pdCx 0 (G 0) y + pdCx 1 (G 1) y = E0.transCx V Φ y * Ψ y + Φ y * E0.transCx V Ψ y := by
    intro y
    have hVc_d : ∀ l : Fin 2, Differentiable ℝ (fun z : ℝ × ℝ => ((V z l : ℝ) : ℂ)) :=
      fun l => Complex.ofRealCLM.differentiable.comp (hVl_d l)
    have hΦΨ_d : Differentiable ℝ (fun z => Φ z * Ψ z) := hΦd.mul hΨd
    dsimp only [G]
    rw [ibpPdCx_mul (hVc_d 0) hΦΨ_d 0 y, ibpPdCx_mul (hVc_d 1) hΦΨ_d 1 y,
      ibpPdCx_ofReal _ (hVl_d 0) 0 y, ibpPdCx_ofReal _ (hVl_d 1) 1 y,
      ibpPdCx_mul hΦd hΨd 0 y, ibpPdCx_mul hΦd hΨd 1 y]
    have hdivC : (((B0579.pd 0 (fun z => V z 0) y : ℝ) : ℂ) +
        ((B0579.pd 1 (fun z => V z 1) y : ℝ) : ℂ)) = 0 := by
      rw [← Complex.ofReal_add, hVdiv y, Complex.ofReal_zero]
    unfold E0.transCx
    linear_combination (Φ y * Ψ y) * hdivC
  have hInt_sum : IntegrableOn
      (fun y => E0.transCx V Φ y * Ψ y + Φ y * E0.transCx V Ψ y) (B0579.cell d) :=
    hInt_lhs.add hInt_rhs
  have hRe_zero : ∫ y in B0579.cell d,
      (E0.transCx V Φ y * Ψ y + Φ y * E0.transCx V Ψ y).re = 0 := by
    have hpt_re : ∀ y : ℝ × ℝ,
        B0579.pd 0 (fun z => (G 0 z).re) y + B0579.pd 1 (fun z => (G 1 z).re) y =
          (E0.transCx V Φ y * Ψ y + Φ y * E0.transCx V Ψ y).re := by
      intro y
      rw [pd_re_eq (hGd 0) 0 y, pd_re_eq (hGd 1) 1 y, ← Complex.add_re, hdiv_G y]
    have h0_re : ContDiff ℝ 1 (fun z => (G 0 z).re) := Complex.reCLM.contDiff.comp (hG1 0)
    have h1_re : ContDiff ℝ 1 (fun z => (G 1 z).re) := Complex.reCLM.contDiff.comp (hG1 1)
    have hp0_re : ∀ y : ℝ × ℝ, (G 0 (y.1 + d, y.2)).re = (G 0 y).re :=
      fun y => congrArg Complex.re (hG0_per y)
    have hi1_re : IntegrableOn (fun z => (G 1 z).re) (B0579.cell d) :=
      Complex.reCLM.integrable_comp hG1_int
    have hdiv_re : IntegrableOn
        (fun y => B0579.pd 0 (fun z => (G 0 z).re) y + B0579.pd 1 (fun z => (G 1 z).re) y)
        (B0579.cell d) :=
      (Complex.reCLM.integrable_comp hInt_sum).congr (ae_of_all _ fun y => (hpt_re y).symm)
    have hz := E0.cellDivZero d hd0 _ _ h0_re h1_re hp0_re hi1_re hdiv_re
    rwa [integral_congr_ae (ae_of_all _ fun y => hpt_re y)] at hz
  have hIm_zero : ∫ y in B0579.cell d,
      (E0.transCx V Φ y * Ψ y + Φ y * E0.transCx V Ψ y).im = 0 := by
    have hpt_im : ∀ y : ℝ × ℝ,
        B0579.pd 0 (fun z => (G 0 z).im) y + B0579.pd 1 (fun z => (G 1 z).im) y =
          (E0.transCx V Φ y * Ψ y + Φ y * E0.transCx V Ψ y).im := by
      intro y
      rw [pd_im_eq (hGd 0) 0 y, pd_im_eq (hGd 1) 1 y, ← Complex.add_im, hdiv_G y]
    have h0_im : ContDiff ℝ 1 (fun z => (G 0 z).im) := Complex.imCLM.contDiff.comp (hG1 0)
    have h1_im : ContDiff ℝ 1 (fun z => (G 1 z).im) := Complex.imCLM.contDiff.comp (hG1 1)
    have hp0_im : ∀ y : ℝ × ℝ, (G 0 (y.1 + d, y.2)).im = (G 0 y).im :=
      fun y => congrArg Complex.im (hG0_per y)
    have hi1_im : IntegrableOn (fun z => (G 1 z).im) (B0579.cell d) :=
      Complex.imCLM.integrable_comp hG1_int
    have hdiv_im : IntegrableOn
        (fun y => B0579.pd 0 (fun z => (G 0 z).im) y + B0579.pd 1 (fun z => (G 1 z).im) y)
        (B0579.cell d) :=
      (Complex.imCLM.integrable_comp hInt_sum).congr (ae_of_all _ fun y => (hpt_im y).symm)
    have hz := E0.cellDivZero d hd0 _ _ h0_im h1_im hp0_im hi1_im hdiv_im
    rwa [integral_congr_ae (ae_of_all _ fun y => hpt_im y)] at hz
  have hSum_zero :
      (∫ y in B0579.cell d, (E0.transCx V Φ y * Ψ y + Φ y * E0.transCx V Ψ y)) = 0 := by
    rw [← integral_re_add_im hInt_sum]
    change ((∫ x in B0579.cell d, (E0.transCx V Φ x * Ψ x + Φ x * E0.transCx V Ψ x).re : ℝ) : ℂ) +
      ((∫ x in B0579.cell d, (E0.transCx V Φ x * Ψ x + Φ x * E0.transCx V Ψ x).im : ℝ) : ℂ) *
        Complex.I = 0
    rw [hRe_zero, hIm_zero]
    simp
  rw [integral_add hInt_lhs hInt_rhs] at hSum_zero
  exact ⟨hInt_lhs, hInt_rhs, eq_neg_of_add_eq_zero_left hSum_zero⟩

/-- Fubini transposition between `kerAdj d F` and `kerVelCx d Ψ` on `B0579.cell d` for any
continuous `d`-periodic Gaussian-bounded `Ψ` (`d ≥ 1`). -/
private lemma integral_kerAdj_mul_eq_kerVelCx {d M_E : ℝ} (hd1 : 1 ≤ d) (_hME0 : 0 ≤ M_E)
    {F : Fin 2 → ℝ × ℝ → ℂ} (hF : ∀ l : Fin 2, IntegrableOn (F l) (B0579.cell d))
    {Ψ : ℝ × ℝ → ℂ} (hΨ_cont : Continuous Ψ)
    (hΨ_per : ∀ y : ℝ × ℝ, Ψ (y.1 + d, y.2) = Ψ y)
    (hΨ_sup : ∀ y : ℝ × ℝ, ‖Ψ y‖ ≤ M_E)
    (hΨ_int : IntegrableOn Ψ (B0579.cell d)) :
    IntegrableOn (fun y => kerAdj d F y * Ψ y) (B0579.cell d) ∧
    IntegrableOn (fun x => ∑ l : Fin 2, F l x * kerVelCx d Ψ x l) (B0579.cell d) ∧
    (∫ y in B0579.cell d, kerAdj d F y * Ψ y) =
      ∫ x in B0579.cell d, ∑ l : Fin 2, F l x * kerVelCx d Ψ x l := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  obtain ⟨C, hC0, hNF⟩ := kerNearFar
  obtain ⟨hmeas, hper, _, hnear, hfar⟩ := hNF d hd1
  have hcell_eq : B0579.cell d = UnforcedLeray.Cyl.cell d := AdjFubiniAux.cell_eq d
  have hL : (∫⁻ y in UnforcedLeray.Cyl.cell d, ‖Ψ y‖ₑ) < ⊤ := by
    rw [← hcell_eq]
    exact hΨ_int.2
  set M : ℝ≥0∞ := ENNReal.ofReal M_E * ENNReal.ofReal C +
      ENNReal.ofReal C * ∫⁻ y in UnforcedLeray.Cyl.cell d, ‖Ψ y‖ₑ
  have hMtop : M ≠ ⊤ :=
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL⟩).ne
  -- Uniform kernel slice bound `∫⁻ y in cell d, ‖kerD d (x - y) l‖ₑ * ‖Ψ y‖ₑ ≤ M`
  have hbound : ∀ (l : Fin 2) (x : ℝ × ℝ),
      (∫⁻ y in B0579.cell d, ‖kerD d (x - y) l‖ₑ * ‖Ψ y‖ₑ) ≤ M := by
    intro l x
    rw [hcell_eq]
    have hnear' : (∫⁻ z in UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
        ∑ i, ‖kerD d z i‖ₑ) ≤ ENNReal.ofReal C := by
      rwa [← hcell_eq]
    have hfar' : ∀ z ∈ UnforcedLeray.Cyl.cell d, z ∉ Metric.ball (0 : ℝ × ℝ) 1 →
        ∀ i, |kerD d z i| ≤ C := by
      rw [← hcell_eq]; exact hfar
    have hΨperC : UnforcedLeray.Cyl.IsPeriodic d Ψ := hΨ_per
    have hΨper_enorm : UnforcedLeray.Cyl.IsPeriodic d (fun y : ℝ × ℝ => ‖Ψ y‖ₑ) :=
      fun z => by simp only [hΨperC z]
    have hGper : UnforcedLeray.Cyl.IsPeriodic d
        (fun w : ℝ × ℝ => ‖kerD d w l‖ₑ * ‖Ψ (x - w)‖ₑ) := by
      intro w
      have h1 : Ψ (x - (w.1 + d, w.2)) = Ψ (x - w) := by
        have := hΨperC.sub_eq (x - w)
        rw [← this]
        congr 1
        ext <;> simp; ring
      simp only [h1, hper w l]
    have e1 : (∫⁻ y in UnforcedLeray.Cyl.cell d, ‖kerD d (x - y) l‖ₑ * ‖Ψ y‖ₑ) =
        ∫⁻ w in UnforcedLeray.Cyl.cell d, ‖kerD d w l‖ₑ * ‖Ψ (x - w)‖ₑ := by
      have := UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hGper x
      rw [← this]
      refine lintegral_congr fun y => ?_
      simp
    rw [e1]
    have hmb : MeasurableSet (Metric.ball (0 : ℝ × ℝ) 1) := Metric.isOpen_ball.measurableSet
    rw [← lintegral_inter_add_sdiff _ _ hmb]
    dsimp only [M]
    refine add_le_add ?_ ?_
    · calc (∫⁻ w in UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
            ‖kerD d w l‖ₑ * ‖Ψ (x - w)‖ₑ)
          ≤ ∫⁻ w in UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
              ENNReal.ofReal M_E * ∑ i, ‖kerD d w i‖ₑ := by
            refine setLIntegral_mono' ((UnforcedLeray.Cyl.measurableSet_cell d).inter hmb)
              fun w _ => ?_
            rw [mul_comm (ENNReal.ofReal M_E)]
            refine mul_le_mul'
              (Finset.single_le_sum (f := fun i => ‖kerD d w i‖ₑ) (fun _ _ => bot_le)
                (Finset.mem_univ l)) ?_
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hΨ_sup _)
        _ = ENNReal.ofReal M_E *
              ∫⁻ w in UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ i, ‖kerD d w i‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal M_E * ENNReal.ofReal C := by gcongr
    · calc (∫⁻ w in UnforcedLeray.Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1,
            ‖kerD d w l‖ₑ * ‖Ψ (x - w)‖ₑ)
          ≤ ∫⁻ w in UnforcedLeray.Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1,
              ENNReal.ofReal C * ‖Ψ (x - w)‖ₑ := by
            refine setLIntegral_mono' ((UnforcedLeray.Cyl.measurableSet_cell d).diff hmb)
              fun w hw => ?_
            gcongr
            rw [← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_ofReal (hfar' w hw.1 hw.2 l)
        _ ≤ ∫⁻ w in UnforcedLeray.Cyl.cell d, ENNReal.ofReal C * ‖Ψ (x - w)‖ₑ :=
            lintegral_mono_set sdiff_subset
        _ = ENNReal.ofReal C * ∫⁻ w in UnforcedLeray.Cyl.cell d, ‖Ψ (x - w)‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal C * ∫⁻ y in UnforcedLeray.Cyl.cell d, ‖Ψ y‖ₑ := by
            rw [UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0
              (G := fun y => ‖Ψ y‖ₑ) hΨper_enorm x]
  -- Tonelli + Fubini on `μ.prod μ`
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell d)
  have hkm : ∀ l : Fin 2, Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => kerD d (p.1 - p.2) l :=
    fun l => (hmeas l).comp (measurable_fst.sub measurable_snd)
  have hHl : ∀ l : Fin 2, Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      F l p.1 * ((kerD d (p.1 - p.2) l : ℝ) : ℂ) * Ψ p.2) (μ.prod μ) := by
    intro l
    have hF1 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F l p.1) (μ.prod μ) :=
      (hF l).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have hF2 : AEStronglyMeasurable
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((kerD d (p.1 - p.2) l : ℝ) : ℂ)) (μ.prod μ) :=
      (Complex.measurable_ofReal.comp (hkm l)).aestronglyMeasurable
    have hF3 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Ψ p.2) (μ.prod μ) :=
      (hΨ_cont.comp continuous_snd).aestronglyMeasurable
    have hsm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        F l p.1 * ((kerD d (p.1 - p.2) l : ℝ) : ℂ) * Ψ p.2) (μ.prod μ) :=
      (hF1.mul hF2).mul hF3
    refine ⟨hsm, ?_⟩
    show (∫⁻ p, ‖F l p.1 * ((kerD d (p.1 - p.2) l : ℝ) : ℂ) * Ψ p.2‖ₑ ∂(μ.prod μ)) < ⊤
    rw [lintegral_prod _ hsm.enorm]
    have hin : ∀ x : ℝ × ℝ,
        (∫⁻ y, ‖F l x * ((kerD d (x - y) l : ℝ) : ℂ) * Ψ y‖ₑ ∂μ) ≤ ‖F l x‖ₑ * M := by
      intro x
      calc (∫⁻ y, ‖F l x * ((kerD d (x - y) l : ℝ) : ℂ) * Ψ y‖ₑ ∂μ)
          = ∫⁻ y, ‖F l x‖ₑ * (‖kerD d (x - y) l‖ₑ * ‖Ψ y‖ₑ) ∂μ := by
            refine lintegral_congr fun y => ?_
            simp only [enorm_mul, AdjFubiniAux.enorm_ofReal_complex, mul_assoc]
        _ = ‖F l x‖ₑ * ∫⁻ y, ‖kerD d (x - y) l‖ₑ * ‖Ψ y‖ₑ ∂μ := by
            refine lintegral_const_mul'' _ ?_
            exact (((hmeas l).comp (measurable_const.sub measurable_id)).enorm.mul
              hΨ_cont.measurable.enorm).aemeasurable
        _ ≤ ‖F l x‖ₑ * M := by gcongr; exact hbound l x
    calc (∫⁻ x, ∫⁻ y, ‖F l x * ((kerD d (x - y) l : ℝ) : ℂ) * Ψ y‖ₑ ∂μ ∂μ)
        ≤ ∫⁻ x, ‖F l x‖ₑ * M ∂μ := lintegral_mono hin
      _ = (∫⁻ x, ‖F l x‖ₑ ∂μ) * M := lintegral_mul_const' _ _ hMtop
      _ < ⊤ := ENNReal.mul_lt_top (hF l).hasFiniteIntegral hMtop.lt_top
  set Hs : (ℝ × ℝ) → (ℝ × ℝ) → ℂ :=
    fun x y => ∑ l : Fin 2, F l x * ((kerD d (x - y) l : ℝ) : ℂ) * Ψ y
  have hHsI : Integrable (Function.uncurry Hs) (μ.prod μ) :=
    integrable_finsetSum _ fun l _ => hHl l
  have hkey : ∀ y : ℝ × ℝ, kerAdj d F y * Ψ y = ∫ x, Hs x y ∂μ := by
    intro y
    unfold kerAdj
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Hs, Finset.sum_mul]
  have hinner : ∀ x : ℝ × ℝ, ∫ y, Hs x y ∂μ = ∑ l : Fin 2, F l x * kerVelCx d Ψ x l := by
    intro x
    have hIy : ∀ l : Fin 2, Integrable (fun y => Ψ y * ((kerD d (x - y) l : ℝ) : ℂ)) μ := by
      intro l
      refine ⟨(hΨ_cont.measurable.mul
          (Complex.measurable_ofReal.comp
            ((hmeas l).comp (measurable_const.sub measurable_id)))).aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      calc (∫⁻ y, ‖Ψ y * ((kerD d (x - y) l : ℝ) : ℂ)‖ₑ ∂μ)
          = ∫⁻ y, ‖kerD d (x - y) l‖ₑ * ‖Ψ y‖ₑ ∂μ := by
            refine lintegral_congr fun y => ?_
            rw [enorm_mul, AdjFubiniAux.enorm_ofReal_complex, mul_comm]
        _ ≤ M := hbound l x
        _ < ⊤ := hMtop.lt_top
    have e : ∀ y : ℝ × ℝ, Hs x y = ∑ l : Fin 2, F l x * (Ψ y * ((kerD d (x - y) l : ℝ) : ℂ)) := by
      intro y
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    simp_rw [e]
    rw [integral_finsetSum _ fun l _ => (hIy l).const_mul (F l x)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · show Integrable (fun y => kerAdj d F y * Ψ y) μ
    simp_rw [hkey]
    exact hHsI.integral_prod_right
  · show Integrable (fun x => ∑ l : Fin 2, F l x * kerVelCx d Ψ x l) μ
    simp_rw [← hinner]
    exact hHsI.integral_prod_left
  · calc (∫ y in B0579.cell d, kerAdj d F y * Ψ y)
        = ∫ y, ∫ x, Hs x y ∂μ ∂μ := by simp_rw [hkey]; rfl
      _ = ∫ x, ∫ y, Hs x y ∂μ ∂μ := (integral_integral_swap hHsI).symm
      _ = ∫ x in B0579.cell d, ∑ l : Fin 2, F l x * kerVelCx d Ψ x l := by
          simp_rw [hinner]; rfl

/-- **Moving Euler adjoint / `movL` pairing identity**: for `IsSeedKernels κ`, there exists
`D_E ≥ 1` such that whenever `ν ∈ Ioc 0 1`, `IsBUCTrain tr`, `0 ≤ r`, and
`D_E ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)`,
`∫_{cell d} movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam κ d i) * perE κ d k =`
`  ∫_{cell d} perLam κ d i * movL tr r (perE κ d k)`. -/
theorem movEulerAdj_pairing_perE_eq_movL {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ D_E : ℝ, 1 ≤ D_E ∧
      ∀ {ν : ℝ}, ν ∈ Ioc (0 : ℝ) 1 →
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ {r : ℝ}, 0 ≤ r →
            D_E ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) →
            ∀ (i k : Fin 2),
              ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
                  ComplCouplingEuler.movEulerAdj
                    (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
                    (movingTrainV tr r) (movingTrainE tr r)
                    (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) y *
                    perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k y =
                ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
                  perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y *
                    movL tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k) y := by
  obtain ⟨ν_bdd, hν_bdd, hBddAll⟩ := CutFTCDual.ladTrainBddAll_unconditional 2
  obtain ⟨D_1, hD1, hGramInv⟩ := ComplCouplingHeat.perGram_inv_entry_bound κ
  obtain ⟨B_0, hB0_pos, hB0⟩ := Lam0B.perLam0_sup κ
  set D_E : ℝ := max D_1 (max 1 ((ν_bdd⁻¹) ^ 2))
  have hDE1 : 1 ≤ D_E := le_trans hD1 (le_max_left _ _)
  refine ⟨D_E, hDE1, fun {ν} hν tr hBUC {r} hr hd_ge i k => ?_⟩
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hν_pos : 0 < ν := hν.1
  have hd1 : 1 ≤ d := hDE1.trans hd_ge
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hd_D1 : D_1 ≤ d := (le_max_left _ _).trans hd_ge
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν_pos.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsa1 : 1 ≤ Real.sqrt (clockA ν r) := Real.one_le_sqrt.2 ha1
  have hsa0 : 0 < Real.sqrt (clockA ν r) := lt_of_lt_of_le zero_lt_one hsa1
  -- Deduce `ν ≤ ν_bdd` from `(ν_bdd⁻¹) ^ 2 ≤ D_E ≤ d ≤ (ν⁻¹) ^ 2`
  have hd_le_c : d ≤ (ν⁻¹) ^ 2 := by
    have hc_eq : ν ^ (-2 : ℝ) = (ν⁻¹) ^ 2 := by
      rw [Real.rpow_neg hν_pos.le, Real.rpow_two, inv_pow]
    unfold d cellLen
    rw [hc_eq]
    exact div_le_self (by positivity) hsa1
  have hν_le_bdd : ν ≤ ν_bdd := by
    have hsq : (ν_bdd⁻¹) ^ 2 ≤ (ν⁻¹) ^ 2 :=
      le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd_ge) hd_le_c
    have hinv_le : ν_bdd⁻¹ ≤ ν⁻¹ := by
      nlinarith [sq_nonneg (ν⁻¹ - ν_bdd⁻¹), inv_pos.2 hν_bdd, inv_pos.2 hν_pos]
    exact (inv_le_inv₀ hν_bdd hν_pos).mp hinv_le
  obtain ⟨C_tr, hBdd⟩ := hBddAll ν ⟨hν_pos, hν_le_bdd⟩ tr hBUC r hr
  -- Physical cell membership for `z = (√a y.1, √a y.2)` when `y ∈ B0579.cell d`
  have hz_mem : ∀ y ∈ B0579.cell d,
      (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) ∈
        B0579.cell (ν ^ (-2 : ℝ)) := by
    intro y hy
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true]
    have hmul : Real.sqrt (clockA ν r) * (d / 2) = ν ^ (-2 : ℝ) / 2 := by
      dsimp [d, cellLen]
      field_simp [hsa0.ne']
    exact ⟨by linarith [mul_le_mul_of_nonneg_left hy.1.1 hsa0.le, hmul],
      by linarith [mul_lt_mul_of_pos_left hy.1.2 hsa0, hmul]⟩
  -- 1. Transport IBP part
  obtain ⟨hV1, hVper⟩ := AdjE1.movingTrainVReg ν (ν ^ (-2 : ℝ)) tr r hr ha0
  have hVdiv := movingTrainV_divFree tr hν_pos hr
  set CV : ℝ := (clockA ν r) ^ (3 / 2 : ℝ) * max C_tr 0
  have hCV0 : 0 ≤ CV := by positivity
  have hVbd : ∀ y ∈ B0579.cell d, ∀ l : Fin 2, |movingTrainV tr r y l| ≤ CV := by
    intro y hy l
    unfold movingTrainV
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
    exact mul_le_mul_of_nonneg_left
      (((hBdd r ⟨hr, le_rfl⟩ _ (hz_mem y hy)).1 l).trans (le_max_left _ _))
      (Real.rpow_nonneg ha0.le _)
  obtain ⟨hInt_T_lhs, hInt_T_rhs, hIBP_T⟩ :=
    integral_transCx_perLam_mul_perE hκ hd1 hCV0 hV1 hVper hVdiv hVbd (hGramInv d hd_D1) i k
  -- 2. Kernel Fubini part
  set F : Fin 2 → ℝ × ℝ → ℂ :=
    fun l w => perLam κ d i w * (B0579.pd l (movingTrainE tr r) w : ℂ)
  set M_F : ℝ := (6 * B_0) * ((clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0)
  have hMF0 : 0 ≤ M_F := by positivity
  have hF_int : ∀ l : Fin 2, IntegrableOn (F l) (B0579.cell d) := by
    intro l
    have hΦ_cont : Continuous (perLam κ d i) := by
      have heq : perLam κ d i =
          fun y => (perGram κ d)⁻¹ i 0 * perLam0 κ d 0 y +
            (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 y := by
        funext y; unfold perLam; exact Fin.sum_univ_two _
      rw [heq]
      exact (continuous_const.mul (Lam0B.perLam0_continuous κ hd0 0)).add
        (continuous_const.mul (Lam0B.perLam0_continuous κ hd0 1))
    have hgrad_cont : Continuous (fun w => (B0579.pd l (movingTrainE tr r) w : ℂ)) := by
      have heq : (fun w => (B0579.pd l (movingTrainE tr r) w : ℂ)) =
          fun w => (movingTrainGradE tr r w l : ℂ) :=
        funext fun w => congrArg Complex.ofReal
          (DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν_pos hr l w)
      rw [heq]
      exact Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainGradE tr hr l)
    refine ⟨(hΦ_cont.mul hgrad_cont).aestronglyMeasurable.restrict, ?_⟩
    have hjb_bd : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖F l w‖ ≤ M_F := by
      intro w hw
      set z : ℝ × ℝ := (Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2)
      have hjb_le : B0579.jb w ≤ B0579.jb z := by
        unfold B0579.jb
        dsimp [z]
        have h1 : w.1 ^ 2 ≤ (Real.sqrt (clockA ν r) * w.1) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt ha0.le]
          exact le_mul_of_one_le_left (sq_nonneg w.1) ha1
        have h2 : w.2 ^ 2 ≤ (Real.sqrt (clockA ν r) * w.2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt ha0.le]
          exact le_mul_of_one_le_left (sq_nonneg w.2) ha1
        linarith
      have hjb_sq : B0579.jb w ^ 2 ≤ B0579.jb z ^ ((2 + 2 : ℝ) / 2) := by
        have hexp : (2 + 2 : ℝ) / 2 = (2 : ℕ) := by norm_num
        rw [hexp, Real.rpow_natCast]
        exact pow_le_pow_left₀ (B0579.jb_pos w).le hjb_le 2
      have hEc_bd : B0579.jb z ^ ((2 + 2 : ℝ) / 2) *
          |B0579.pd l (UnforcedLeray.B0238.Ec tr r) z| ≤ max C_tr 0 :=
        ((hBdd r ⟨hr, le_rfl⟩ z (hz_mem w hw)).2 l).trans (le_max_left _ _)
      have hgrad_bd : B0579.jb w ^ 2 * |B0579.pd l (movingTrainE tr r) w| ≤
          (clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0 := by
        rw [DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν_pos hr l w]
        unfold movingTrainGradE
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _), ← mul_left_comm]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ha0.le _)
        exact (mul_le_mul_of_nonneg_right hjb_sq (abs_nonneg _)).trans hEc_bd
      have hΦ_bd : ‖perLam κ d i w‖ ≤ 6 * B_0 := by
        unfold perLam
        rw [Fin.sum_univ_two]
        calc ‖(perGram κ d)⁻¹ i 0 * perLam0 κ d 0 w + (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 w‖
            ≤ ‖(perGram κ d)⁻¹ i 0‖ * ‖perLam0 κ d 0 w‖ +
                ‖(perGram κ d)⁻¹ i 1‖ * ‖perLam0 κ d 1 w‖ := by
              simpa [norm_mul] using norm_add_le
                ((perGram κ d)⁻¹ i 0 * perLam0 κ d 0 w)
                ((perGram κ d)⁻¹ i 1 * perLam0 κ d 1 w)
          _ ≤ 3 * B_0 + 3 * B_0 := add_le_add
              (mul_le_mul (hGramInv d hd_D1 i 0) (hB0 d hd1 0 w hw) (norm_nonneg _) (by norm_num))
              (mul_le_mul (hGramInv d hd_D1 i 1) (hB0 d hd1 1 w hw) (norm_nonneg _) (by norm_num))
          _ = 6 * B_0 := by ring
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc B0579.jb w ^ 2 * (‖perLam κ d i w‖ * |B0579.pd l (movingTrainE tr r) w|)
          = ‖perLam κ d i w‖ * (B0579.jb w ^ 2 * |B0579.pd l (movingTrainE tr r) w|) := by ring
        _ ≤ (6 * B_0) * ((clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0) :=
            mul_le_mul hΦ_bd hgrad_bd (by positivity) (by positivity)
    exact lt_of_le_of_lt (DirectEulerSub.lintegral_cell_le_of_jb_sq hMF0 hjb_bd) ENNReal.ofReal_lt_top
  obtain ⟨M_E, hME0, hE_all⟩ := EulerErrorSub.perE_and_pdCx_gauss_bounds hκ
  obtain ⟨hΨ_gauss, hΨ_sup, _⟩ := hE_all d hd1 k
  have hΨ_cont : Continuous (perE κ d k) := by
    have hsm2 : ContDiff ℝ 2 (κ.e k) := ((OscillatorForceSub.seed_e_smooth_decay hκ).1 k).of_le
      (by simp)
    obtain ⟨_, _, he0, he1, he2⟩ := OscillatorForceSub.seed_e_translate_bounds hκ k
    have heq : perE κ d k = UnforcedLeray.Gaussian.periodize d (κ.e k) :=
      ComplCouplingHeat.perSum_eq_periodize_fun d (κ.e k)
    rw [heq]
    exact (UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (N := (2 : ℕ)) (by norm_num) hd0.ne'
      hsm2 (UnforcedLeray.Gaussian.iteratedFDeriv_bounds_of he0 he1 he2)).continuous
  have hΨ_per : ∀ y : ℝ × ℝ, perE κ d k (y.1 + d, y.2) = perE κ d k y :=
    fun y => CutFTCDual.perSum_periodic d (κ.e k) y
  have hΨ_int : IntegrableOn (perE κ d k) (B0579.cell d) :=
    integrableOn_cell_of_le_gauss16 hΨ_cont hΨ_gauss
  obtain ⟨hInt_K_lhs, hInt_K_rhs, hFub_K⟩ :=
    integral_kerAdj_mul_eq_kerVelCx hd1 hME0 hF_int hΨ_cont hΨ_per hΨ_sup hΨ_int
  -- 3. Combine Transport IBP and Kernel Fubini
  have hlhs_eq :
      (fun y => ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
          (perLam κ d i) y * perE κ d k y) =
        fun y => E0.transCx (movingTrainV tr r) (perLam κ d i) y * perE κ d k y -
          kerAdj d F y * perE κ d k y := by
    funext y
    unfold ComplCouplingEuler.movEulerAdj
    dsimp only [F]
    ring
  have hrhs_K_eq :
      (fun x => ∑ l : Fin 2, F l x * kerVelCx d (perE κ d k) x l) =
        fun x => perLam κ d i x *
          (kerVelCx d (perE κ d k) x 0 * ((movingTrainGradE tr r x 0 : ℝ) : ℂ) +
            kerVelCx d (perE κ d k) x 1 * ((movingTrainGradE tr r x 1 : ℝ) : ℂ)) := by
    funext x
    simp only [Fin.sum_univ_two, F,
      DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν_pos hr 0 x,
      DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν_pos hr 1 x]
    ring
  have hrhs_eq :
      (fun x => perLam κ d i x * movL tr r (perE κ d k) x) =
        fun x => -(perLam κ d i x * E0.transCx (movingTrainV tr r) (perE κ d k) x) -
          (∑ l : Fin 2, F l x * kerVelCx d (perE κ d k) x l) := by
    funext x
    rw [congrFun hrhs_K_eq x]
    unfold movL E0.transCx
    dsimp only [d]
    ring
  rw [hlhs_eq,
    integral_sub (f := fun y => E0.transCx (movingTrainV tr r) (perLam κ d i) y * perE κ d k y)
      (g := fun y => kerAdj d F y * perE κ d k y) hInt_T_lhs hInt_K_lhs,
    hrhs_eq,
    integral_sub
      (f := fun x => -(perLam κ d i x * E0.transCx (movingTrainV tr r) (perE κ d k) x))
      (g := fun x => ∑ l : Fin 2, F l x * kerVelCx d (perE κ d k) x l)
      hInt_T_rhs.neg hInt_K_rhs,
    integral_neg, hIBP_T, hFub_K]

end UnforcedLeray.Short.IIIa.MovFrameLeavesAux
