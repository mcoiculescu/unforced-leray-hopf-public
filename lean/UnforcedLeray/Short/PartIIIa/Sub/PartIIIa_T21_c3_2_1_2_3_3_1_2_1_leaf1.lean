import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L2_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Residual

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/2/1/1`: Leaf V `FrameVecReg`

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2918,
2937-2945, 2074-2105.

Proves `frameVecReg`: the zero-extended frame vectors `I_d E_j(s(σ))` (`frameEFun`) and
relative free residuals `I_d (E_z - (G_free - β₀) E_j)` (`frameRFun`) lie in `L²_m` along the
block, and `σ ↦ I_d R_j(s(σ))` is continuous on `[0, B]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

namespace FrameDuhamelSub

section Helpers

/-- Weighted Gaussian integrability on `Planar.wMeasure m` for `m ≥ 0`. -/
private lemma integrable_gauss_wMeasure {m : ℝ} (hm : 0 ≤ m) :
    Integrable (fun z : ℂ => Real.exp (-(z.re ^ 2 + z.im ^ 2) / 8)) (Planar.wMeasure m) := by
  have hvol : Integrable (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ m *
      Real.exp (-(z.re ^ 2 + z.im ^ 2) / 8)) volume := by
    have hjb := integrable_jb_gauss hm
    have hmp := Complex.volume_preserving_equiv_real_prod
    have hcomp := (hmp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding
      (g := fun x : ℝ × ℝ => B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8))).2 hjb
    refine hcomp.congr (Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, B0579.jb]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring_nf
  rw [Planar.wMeasure_eq_B0008, B0008.wMeasure,
    integrable_withDensity_iff (B0008.measurable_density m).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  refine hvol.congr (Eventually.of_forall fun z => ?_)
  simp [B0008.coe_density, mul_comm]

/-- `MemLp` in `Planar.wMeasure m` from `AEStronglyMeasurable` and a Gaussian bound. -/
private lemma memLp_of_gauss_wMeasure {m : ℝ} (hm : 0 ≤ m) {f : ℂ → ℂ}
    (hf_meas : AEStronglyMeasurable f (Planar.wMeasure m)) {M : ℝ} (_hM : 0 ≤ M)
    (hf_bd : ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16)) :
    MemLp f 2 (Planar.wMeasure m) := by
  rw [memLp_two_iff_integrable_sq_norm hf_meas]
  have hdom : Integrable (fun z : ℂ => M ^ 2 * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 8))
      (Planar.wMeasure m) :=
    (integrable_gauss_wMeasure hm).const_mul (M ^ 2)
  refine hdom.mono' (hf_meas.norm.pow 2) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h1 : ‖f z‖ ^ 2 ≤ (M * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hf_bd z) 2
  refine h1.trans_eq ?_
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- `perSum d f y` is continuous in `d` on `[1, ∞)` when `f` is continuous with inverse-square
horizontal decay. -/
private lemma continuousOn_perSum_period {f : ℝ × ℝ → ℂ} (hf : Continuous f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖f z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) (y : ℝ × ℝ) :
    ContinuousOn (fun d : ℝ => perSum d f y) (Ici 1) := by
  unfold perSum
  have hterm : ∀ n : ℤ, ContinuousOn (fun d : ℝ => f (y.1 + (n : ℝ) * d, y.2)) (Ici 1) := by
    intro n
    exact hf.comp_continuousOn
      ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).prodMk continuousOn_const)
  have hsum : Summable (fun n : ℤ =>
      C * (1 + |y.1|) ^ (2 : ℝ) * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
    (UnforcedLeray.Gaussian.summable_one_add_abs_int_rpow (s := 2) (by norm_num)).mul_left _
  refine continuousOn_tsum hterm hsum fun n d hd => ?_
  have hd1 : (1 : ℝ) ≤ d := hd
  have hpeetre := UnforcedLeray.Gaussian.one_add_abs_rpow_neg_le (s := 2) (by norm_num)
    (y.1 + (n : ℝ) * d) (-y.1)
  have hadd : y.1 + (n : ℝ) * d + -y.1 = (n : ℝ) * d := by ring
  rw [hadd, abs_neg] at hpeetre
  have hnd : 1 + |(n : ℝ)| ≤ 1 + |(n : ℝ) * d| := by
    rw [abs_mul, abs_of_pos (by linarith : 0 < d)]
    nlinarith [abs_nonneg (n : ℝ)]
  have hnd_rpow : (1 + |(n : ℝ) * d|) ^ (-(2 : ℝ)) ≤ (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hnd (by norm_num)
  calc ‖f (y.1 + (n : ℝ) * d, y.2)‖
      ≤ C * (1 + |y.1 + (n : ℝ) * d|) ^ (-(2 : ℝ)) := hC _
    _ ≤ C * ((1 + |y.1|) ^ (2 : ℝ) * (1 + |(n : ℝ) * d|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hpeetre hC0
    _ ≤ C * ((1 + |y.1|) ^ (2 : ℝ) * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnd_rpow (by positivity)) hC0
    _ = C * (1 + |y.1|) ^ (2 : ℝ) * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by ring

/-- A vertical line `{z : ℂ | z.re = x₀}` has Lebesgue measure zero. -/
private lemma volume_re_eq_zero (x₀ : ℝ) : volume {z : ℂ | z.re = x₀} = 0 := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hS : MeasurableSet ({x₀} ×ˢ (univ : Set ℝ)) :=
    (measurableSet_singleton x₀).prod MeasurableSet.univ
  have hpre : Complex.measurableEquivRealProd ⁻¹' ({x₀} ×ˢ (univ : Set ℝ)) =
      {z : ℂ | z.re = x₀} := by
    ext z
    simp [Complex.measurableEquivRealProd_apply]
  rw [← hpre, hmp.measure_preimage hS.nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- `‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ z, ‖f z - g z‖ ^ 2 ∂(Planar.wMeasure m)`. -/
private lemma norm_sq_toLp_sub {m : ℝ} {f g : ℂ → ℂ}
    (hf : MemLp f 2 (Planar.wMeasure m)) (hg : MemLp g 2 (Planar.wMeasure m)) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 =
      ∫ z : ℂ, ‖f z - g z‖ ^ 2 ∂(Planar.wMeasure m) := by
  have hsub : MemLp (f - g) 2 (Planar.wMeasure m) := hf.sub hg
  rw [← MemLp.toLp_sub hf hg, Lp.norm_toLp]
  have hnonneg : 0 ≤ᵐ[Planar.wMeasure m] fun z => ‖f z - g z‖ ^ 2 :=
    Eventually.of_forall fun z => sq_nonneg _
  have h1 : (eLpNorm (f - g) 2 (Planar.wMeasure m)).toReal ^ 2 =
      ((eLpNorm (f - g) 2 (Planar.wMeasure m)) ^ (2 : ℝ)).toReal := by
    rw [← ENNReal.toReal_rpow, Real.rpow_two]
  rw [h1, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [h2, ← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num), ENNReal.rpow_one]
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg (hsub.aestronglyMeasurable.norm.pow 2)]
  congr 1
  refine lintegral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Pi.sub_apply]
  rw [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

/-- Algebraic rewrite of `movFreeRes` in terms of `movOscRes` and the transport term. -/
private lemma movFreeRes_eq_neg_movOscRes_add (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) :
    movFreeRes κ tr r j y =
      -movOscRes κ ν r j y +
        (((movingTrainV tr r y 0 : ℝ) : ℂ) *
            pdCx 0 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y +
          ((movingTrainV tr r y 1 : ℝ) : ℂ) *
            pdCx 1 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y) := by
  unfold movFreeRes movOscRes
  ring

private lemma continuous_movBeta0 (P : PlanarData) (ν : ℝ) : Continuous (movBeta0 P ν) := by
  have h : movBeta0 P ν = fun r => P.eigenvalue.re + P.kappa.re * (ν * clockA ν r) := by
    funext r
    unfold movBeta0 clockTheta
    rw [div_inv_eq_mul]
  rw [h]
  unfold clockA
  fun_prop

end Helpers

/-- **Leaf V is proved (`FrameVecReg`, SP 2891-2905)**: `frameEFun` and `frameRFun` lie in `L²_m`
along `[0, B]` by Gaussian tails of `perE` and its derivatives and boundedness of `tr.v`, and
`σ ↦ I_d R_j(s(σ))` is continuous on `[0, B]` by dominated convergence (moving cell boundary is
Lebesgue-null). -/
theorem frameVecReg (κ : PlanarFrameKernels) : FrameVecReg κ := by
  intro P m K B b ν tr t₁ t₂ ctx j
  obtain ⟨hκ, _hP, hm, _hB, hb, hν, _hF, htr, ht₁, h12, hbt, hBe⟩ := ctx
  have hm0 : 0 ≤ m := by linarith
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  -- Basic clock and cell-length properties for `σ ∈ [0, B]`
  have hage_mem : ∀ σ ∈ Icc (0 : ℝ) B, ageAt ν t₁ σ ∈ Icc t₁ t₂ :=
    fun σ hσ => VariationOfConstantsSub.ageAt_mem_Icc hν ht₁ h12 hBe hσ
  have hd_ge1 : ∀ σ ∈ Icc (0 : ℝ) B, 1 ≤ dOf ν t₁ σ := by
    intro σ hσ
    have hs := hage_mem σ hσ
    have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans hs.1
    have hbs : b ≤ clockTheta ν (ageAt ν t₁ σ) := hbt.trans (clockTheta_le_of_le hν hs0 hs.2)
    exact ComplMildYAux.cellLen_one_le_of_theta hν hs0 hb hbs
  have hθ_ge1 : ∀ σ ∈ Icc (0 : ℝ) B, 1 ≤ clockTheta ν (ageAt ν t₁ σ) := by
    intro σ hσ
    have hs := hage_mem σ hσ
    have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans hs.1
    exact hb.trans (hbt.trans (clockTheta_le_of_le hν hs0 hs.2))
  have hA_le : ∀ σ ∈ Icc (0 : ℝ) B, clockA ν (ageAt ν t₁ σ) ≤ ν⁻¹ := by
    intro σ hσ
    have hs := hage_mem σ hσ
    have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans hs.1
    have ha0 : 0 < clockA ν (ageAt ν t₁ σ) := by
      have := one_le_clockA hν.le hs0; linarith
    have hθ1 : 1 ≤ (ν * clockA ν (ageAt ν t₁ σ))⁻¹ := hθ_ge1 σ hσ
    have hmul : ν * clockA ν (ageAt ν t₁ σ) ≤ 1 := by
      have hpos : 0 < ν * clockA ν (ageAt ν t₁ σ) := mul_pos hν ha0
      have := mul_le_mul_of_nonneg_left hθ1 hpos.le
      rwa [mul_one, mul_inv_cancel₀ hpos.ne'] at this
    exact (le_div_iff₀' hν).mpr hmul |>.trans_eq (inv_eq_one_div ν).symm
  -- Gaussian bounds for `perE`, `pdCx (perE)`, and `perSum d (movD (κ.e j))`
  obtain ⟨M_E, hME0, hME⟩ := EulerErrorSub.perE_and_pdCx_gauss_bounds hκ
  obtain ⟨hcont_D, C_D, hCD0, hCD⟩ := OscillatorForceSub.movD_seed_decay hκ j
  obtain ⟨M_D, hMD0, hMD⟩ := OscillatorForceSub.perSum_pointwise_of_gauss hCD0 hCD
  -- Uniform bound for `tr.v` on `[0, t₂]` and `movBeta0` on `[t₁, t₂]`
  obtain ⟨V_max, hV_max⟩ := htr.sup_bound ht₂
  set V₀ : ℝ := max V_max 0
  have hV₀ : 0 ≤ V₀ := le_max_right _ _
  have htrV_bd : ∀ σ ∈ Icc (0 : ℝ) B, ∀ y : ℝ × ℝ, ∀ k : Fin 2,
      |movingTrainV tr (ageAt ν t₁ σ) y k| ≤ ν⁻¹ ^ (3 / 2 : ℝ) * V₀ := by
    intro σ hσ y k
    have hs := hage_mem σ hσ
    have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans hs.1
    have ha1 : 1 ≤ clockA ν (ageAt ν t₁ σ) := one_le_clockA hν.le hs0
    have hApow : clockA ν (ageAt ν t₁ σ) ^ (3 / 2 : ℝ) ≤ ν⁻¹ ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (hA_le σ hσ) (by norm_num)
    have hv_le : |tr.v (ageAt ν t₁ σ)
        (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
          Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2) k| ≤ V₀ := by
      have h1 : ‖tr.v (ageAt ν t₁ σ)
          (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
            Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2) k‖ ≤
          ‖tr.v (ageAt ν t₁ σ)
          (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
            Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2)‖ :=
        PiLp.norm_apply_le _ k
      exact (h1.trans (hV_max _ ⟨hs0, hs.2⟩ _)).trans (le_max_left _ _)
    unfold movingTrainV
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact mul_le_mul hApow hv_le (abs_nonneg _) (by positivity)
  have hβ_cont : ContinuousOn (movBeta0 P ν) (Icc t₁ t₂) :=
    (continuous_movBeta0 P ν).continuousOn
  obtain ⟨B_max, hB_max⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ_cont
  set B₀ : ℝ := max B_max 0
  have hB₀ : 0 ≤ B₀ := le_max_right _ _
  have hβ_bd : ∀ σ ∈ Icc (0 : ℝ) B, |movBeta0 P ν (ageAt ν t₁ σ)| ≤ B₀ :=
    fun σ hσ => (hB_max _ (hage_mem σ hσ)).trans (le_max_left _ _)
  -- Combined Gaussian bound constant for `frameRFun`
  set M_R : ℝ := M_D + 2 * (ν⁻¹ ^ (3 / 2 : ℝ) * V₀) * M_E + B₀ * M_E
  have hMR0 : 0 ≤ M_R := by positivity
  have hR_bd : ∀ σ ∈ Icc (0 : ℝ) B, ∀ z : ℂ,
      ‖frameRFun κ P ν tr t₁ j σ z‖ ≤ M_R * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by
    intro σ hσ z
    unfold frameRFun cellZeroExt
    by_cases hz : cToPlane z ∈ B0579.cell (dOf ν t₁ σ)
    · rw [Set.indicator_of_mem hz]
      set s := ageAt ν t₁ σ
      set d := dOf ν t₁ σ
      have hs0 : 0 ≤ s := ht₁.trans (hage_mem σ hσ).1
      have hd1 : 1 ≤ d := hd_ge1 σ hσ
      have hθ1 : 1 ≤ clockTheta ν s := hθ_ge1 σ hσ
      have hθ0 : 0 < clockTheta ν s := by linarith
      rw [movFreeRes_eq_neg_movOscRes_add,
        OscillatorForceSub.movOscRes_eq_perSum_movD hκ hν hs0 j (cToPlane z)]
      have h1 : ‖-((clockTheta ν s : ℂ)⁻¹ * perSum d (movD (κ.e j)) (cToPlane z))‖ ≤
          M_D * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by
        rw [norm_neg, norm_mul, norm_inv, Complex.norm_of_nonneg hθ0.le]
        have hinv : (clockTheta ν s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hθ1
        have hps := hMD d hd1 (cToPlane z) hz
        simp only [cToPlane] at hps
        calc (clockTheta ν s)⁻¹ * ‖perSum d (movD (κ.e j)) (cToPlane z)‖
            ≤ 1 * (M_D * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16)) :=
              mul_le_mul hinv hps (norm_nonneg _) zero_le_one
          _ = M_D * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := one_mul _
      have htr_term : ∀ k : Fin 2,
          ‖((movingTrainV tr s (cToPlane z) k : ℝ) : ℂ) *
              pdCx k (perE κ d j) (cToPlane z)‖ ≤
            (ν⁻¹ ^ (3 / 2 : ℝ) * V₀) * M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by
        intro k
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hpd := (hME d hd1 j).2.2 k (cToPlane z) hz
        simp only [cToPlane] at hpd
        calc |movingTrainV tr s (cToPlane z) k| * ‖pdCx k (perE κ d j) (cToPlane z)‖
            ≤ (ν⁻¹ ^ (3 / 2 : ℝ) * V₀) * (M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16)) :=
              mul_le_mul (htrV_bd σ hσ (cToPlane z) k) hpd (norm_nonneg _) (by positivity)
          _ = (ν⁻¹ ^ (3 / 2 : ℝ) * V₀) * M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by ring
      have hβ_term : ‖((movBeta0 P ν s : ℝ) : ℂ) * perE κ d j (cToPlane z)‖ ≤
          B₀ * M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hpe := (hME d hd1 j).1 (cToPlane z) hz
        simp only [cToPlane] at hpe
        calc |movBeta0 P ν s| * ‖perE κ d j (cToPlane z)‖
            ≤ B₀ * (M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16)) :=
              mul_le_mul (hβ_bd σ hσ) hpe (norm_nonneg _) hB₀
          _ = B₀ * M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by ring
      calc ‖-((clockTheta ν s : ℂ)⁻¹ * perSum d (movD (κ.e j)) (cToPlane z)) +
              (((movingTrainV tr s (cToPlane z) 0 : ℝ) : ℂ) *
                  pdCx 0 (perE κ d j) (cToPlane z) +
                ((movingTrainV tr s (cToPlane z) 1 : ℝ) : ℂ) *
                  pdCx 1 (perE κ d j) (cToPlane z)) +
              ((movBeta0 P ν s : ℝ) : ℂ) * perE κ d j (cToPlane z)‖
          ≤ ‖-((clockTheta ν s : ℂ)⁻¹ * perSum d (movD (κ.e j)) (cToPlane z))‖ +
              (‖((movingTrainV tr s (cToPlane z) 0 : ℝ) : ℂ) *
                  pdCx 0 (perE κ d j) (cToPlane z)‖ +
                ‖((movingTrainV tr s (cToPlane z) 1 : ℝ) : ℂ) *
                  pdCx 1 (perE κ d j) (cToPlane z)‖) +
              ‖((movBeta0 P ν s : ℝ) : ℂ) * perE κ d j (cToPlane z)‖ :=
            (norm_add_le _ _).trans
              (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) le_rfl)
        _ ≤ M_D * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) +
              ((ν⁻¹ ^ (3 / 2 : ℝ) * V₀) * M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) +
                (ν⁻¹ ^ (3 / 2 : ℝ) * V₀) * M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16)) +
              B₀ * M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) :=
            add_le_add (add_le_add h1 (add_le_add (htr_term 0) (htr_term 1))) hβ_term
        _ = M_R * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by ring
    · rw [Set.indicator_of_notMem hz, norm_zero]
      positivity
  -- Gaussian bound for `frameEFun`
  have hE_bd : ∀ σ ∈ Icc (0 : ℝ) B, ∀ z : ℂ,
      ‖frameEFun κ ν t₁ j σ z‖ ≤ M_E * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by
    intro σ hσ z
    unfold frameEFun cellZeroExt
    by_cases hz : cToPlane z ∈ B0579.cell (dOf ν t₁ σ)
    · rw [Set.indicator_of_mem hz]
      have hpe := (hME (dOf ν t₁ σ) (hd_ge1 σ hσ) j).1 (cToPlane z) hz
      simpa [cToPlane] using hpe
    · rw [Set.indicator_of_notMem hz, norm_zero]
      positivity
  -- `AEStronglyMeasurable` and `MemLp` for `frameEFun` and `frameRFun`
  have hcToPlane_cont : Continuous cToPlane :=
    Complex.continuous_re.prodMk Complex.continuous_im
  have hE_meas : ∀ σ ∈ Icc (0 : ℝ) B,
      AEStronglyMeasurable (frameEFun κ ν t₁ j σ) (Planar.wMeasure m) := by
    intro σ hσ
    have hd0 : 0 < dOf ν t₁ σ := by linarith [hd_ge1 σ hσ]
    have hcont : Continuous (perE κ (dOf ν t₁ σ) j) := FrameCont.perE_continuous κ hd0 j
    have hS : MeasurableSet (B0579.cell (dOf ν t₁ σ)) :=
      measurableSet_Ico.prod MeasurableSet.univ
    exact ((hcont.measurable.indicator hS).comp hcToPlane_cont.measurable).aestronglyMeasurable
  have hR_meas : ∀ σ ∈ Icc (0 : ℝ) B,
      AEStronglyMeasurable (frameRFun κ P ν tr t₁ j σ) (Planar.wMeasure m) := by
    intro σ hσ
    set s := ageAt ν t₁ σ
    set d := dOf ν t₁ σ
    have hs0 : 0 ≤ s := ht₁.trans (hage_mem σ hσ).1
    have hd0 : 0 < d := by linarith [hd_ge1 σ hσ]
    have hE_c : Continuous (perE κ d j) := FrameCont.perE_continuous κ hd0 j
    have hD_c : Continuous (perSum d (movD (κ.e j))) :=
      FrameCont.perSum_continuous hcont_D (C := 16 * C_D) (fun z => (hCD z).trans (by
        have := FrameCont.exp_le_translate_weight z.1 z.2
        calc C_D * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
            ≤ C_D * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
              mul_le_mul_of_nonneg_left this hCD0
          _ = (16 * C_D) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring)) hd0.ne'
    have hpd0_c : Continuous (pdCx 0 (perE κ d j)) := EulerErrorSub.continuous_pdCx_perE hκ hd0 j 0
    have hpd1_c : Continuous (pdCx 1 (perE κ d j)) := EulerErrorSub.continuous_pdCx_perE hκ hd0 j 1
    have hV0_c : Continuous (fun y => ((movingTrainV tr s y 0 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainV tr hs0 0)
    have hV1_c : Continuous (fun y => ((movingTrainV tr s y 1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainV tr hs0 1)
    have h_eq : frameRFun κ P ν tr t₁ j σ = fun z =>
        (B0579.cell d).indicator (fun y =>
          -((clockTheta ν s : ℂ)⁻¹ * perSum d (movD (κ.e j)) y) +
            (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 (perE κ d j) y +
              ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 (perE κ d j) y) +
            ((movBeta0 P ν s : ℝ) : ℂ) * perE κ d j y) (cToPlane z) := by
      funext z
      unfold frameRFun cellZeroExt
      congr 1
      funext y
      rw [movFreeRes_eq_neg_movOscRes_add,
        OscillatorForceSub.movOscRes_eq_perSum_movD hκ hν hs0 j y]
    rw [h_eq]
    have hg_c : Continuous (fun y =>
        -((clockTheta ν s : ℂ)⁻¹ * perSum d (movD (κ.e j)) y) +
          (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 (perE κ d j) y +
            ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 (perE κ d j) y) +
          ((movBeta0 P ν s : ℝ) : ℂ) * perE κ d j y) := by
      refine (((continuous_const.mul hD_c).neg).add
        ((hV0_c.mul hpd0_c).add (hV1_c.mul hpd1_c))).add (continuous_const.mul hE_c)
    have hS : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
    exact ((hg_c.measurable.indicator hS).comp hcToPlane_cont.measurable).aestronglyMeasurable
  have hE_memLp : ∀ σ ∈ Icc (0 : ℝ) B,
      MemLp (frameEFun κ ν t₁ j σ) 2 (Planar.wMeasure m) :=
    fun σ hσ => memLp_of_gauss_wMeasure hm0 (hE_meas σ hσ) hME0 (hE_bd σ hσ)
  have hR_memLp : ∀ σ ∈ Icc (0 : ℝ) B,
      MemLp (frameRFun κ P ν tr t₁ j σ) 2 (Planar.wMeasure m) :=
    fun σ hσ => memLp_of_gauss_wMeasure hm0 (hR_meas σ hσ) hMR0 (hR_bd σ hσ)
  open Classical in
  let Ej : ℝ → Planar.L2w m := fun σ =>
    if h : σ ∈ Icc (0 : ℝ) B then (hE_memLp σ h).toLp (frameEFun κ ν t₁ j σ) else 0
  open Classical in
  let Rj : ℝ → Planar.L2w m := fun σ =>
    if h : σ ∈ Icc (0 : ℝ) B then (hR_memLp σ h).toLp (frameRFun κ P ν tr t₁ j σ) else 0
  refine ⟨Ej, Rj, ?_, ?_, ?_⟩
  · intro σ hσ
    simp only [Ej, hσ, ↓reduceDIte]
    exact Planar.volume_ac m (hE_memLp σ hσ).coeFn_toLp
  · intro σ hσ
    simp only [Rj, hσ, ↓reduceDIte]
    exact Planar.volume_ac m (hR_memLp σ hσ).coeFn_toLp
  · -- Continuity of `Rj` on `[0, B]`
    obtain ⟨C_e, hCe⟩ := FrameCont.e_translate_bound κ
    have hCe0 : 0 ≤ C_e := by
      have h0 := hCe j (0, 0)
      have hn : 0 ≤ ‖κ.e j (0, 0)‖ := norm_nonneg _
      simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at h0
      linarith
    have hperE_cont : ∀ y : ℝ × ℝ, ContinuousOn (fun d : ℝ => perE κ d j y) (Ici 1) :=
      fun y => continuousOn_perSum_period (κ.e_cont j) hCe0 (hCe j) y
    have hperD_cont : ∀ y : ℝ × ℝ,
        ContinuousOn (fun d : ℝ => perSum d (movD (κ.e j)) y) (Ici 1) :=
      fun y => continuousOn_perSum_period hcont_D (C := 16 * C_D) (by positivity)
        (fun z => (hCD z).trans (by
          have := FrameCont.exp_le_translate_weight z.1 z.2
          calc C_D * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
              ≤ C_D * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
                mul_le_mul_of_nonneg_left this hCD0
            _ = (16 * C_D) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring)) y
    have hpd_dec := (OscillatorForceSub.seed_e_smooth_decay hκ).2 j 1
    obtain ⟨C_pd, hCpd0, hCpd⟩ := hpd_dec
    have hsm_e : ContDiff ℝ ∞ (κ.e j) := (OscillatorForceSub.seed_e_smooth_decay hκ).1 j
    have hpd_cont : ∀ (k : Fin 2) (y : ℝ × ℝ),
        ContinuousOn (fun d : ℝ => pdCx k (perE κ d j) y) (Ici 1) := by
      intro k y
      have heq : EqOn (fun d : ℝ => pdCx k (perE κ d j) y)
          (fun d : ℝ => perSum d (pdCx k (κ.e j)) y) (Ici 1) :=
        fun d hd => EulerErrorTail.pdCx_perE_eq hκ (by linarith [mem_Ici.1 hd] : (0 : ℝ) < d) j k y
      refine ContinuousOn.congr ?_ heq
      have hpc : Continuous (pdCx k (κ.e j)) := by
        unfold pdCx
        exact (((hsm_e.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous)
      refine continuousOn_perSum_period hpc (C := 16 * C_pd) (by positivity) (fun z => ?_) y
      have hdir : ‖B0579.dir k‖ ≤ 1 := by fin_cases k <;> simp [B0579.dir]
      have h1 : ‖pdCx k (κ.e j) z‖ ≤ (1 + ‖z‖) * ‖iteratedFDeriv ℝ 1 (κ.e j) z‖ := by
        unfold pdCx
        rw [norm_iteratedFDeriv_one]
        have := (fderiv ℝ (κ.e j) z).le_opNorm (B0579.dir k)
        nlinarith [norm_nonneg z, norm_nonneg (fderiv ℝ (κ.e j) z)]
      calc ‖pdCx k (κ.e j) z‖
          ≤ C_pd * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := h1.trans (hCpd z)
        _ ≤ C_pd * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (FrameCont.exp_le_translate_weight z.1 z.2) hCpd0
        _ = (16 * C_pd) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring
    -- Continuity of `ageAt ν t₁` and `dOf ν t₁` on `[0, B]`
    have hnu_lt : ∀ σ ∈ Icc (0 : ℝ) B, ν * (movingZ ν t₁ + σ) < 1 := by
      intro σ hσ
      have hlt2 : ν * movingZ ν t₂ < 1 := by
        unfold movingZ clockA
        have hpos : 0 < 1 + ν * t₂ := by positivity
        rw [mul_div_assoc', div_lt_one hpos]
        linarith
      have hle : movingZ ν t₁ + σ ≤ movingZ ν t₂ := by linarith [hσ.2, hBe]
      exact (mul_le_mul_of_nonneg_left hle hν.le).trans_lt hlt2
    have hage_cont : ContinuousOn (ageAt ν t₁) (Icc (0 : ℝ) B) := by
      unfold ageAt FrameStableSub.moveAgeOfZ
      refine ContinuousOn.div (continuousOn_const.add continuousOn_id)
        (continuousOn_const.sub (continuousOn_const.mul (continuousOn_const.add continuousOn_id)))
        fun σ hσ => by linarith [hnu_lt σ hσ]
    have hd_cont : ContinuousOn (dOf ν t₁) (Icc (0 : ℝ) B) := by
      unfold dOf cellLen
      refine continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn ?_) (fun σ hσ => ?_)
      · exact (FlowMeas.continuousOn_clockA (Ici 0)).comp hage_cont
          fun σ hσ => ht₁.trans (hage_mem σ hσ).1
      · have ha : 1 ≤ clockA ν (ageAt ν t₁ σ) :=
          one_le_clockA hν.le (ht₁.trans (hage_mem σ hσ).1)
        exact (Real.sqrt_pos.2 (by linarith)).ne'
    -- Sequential dominated convergence at each `σ₀ ∈ Icc 0 B`
    intro σ₀ hσ₀
    rw [ContinuousWithinAt, Filter.tendsto_iff_seq_tendsto]
    intro u₀ hu₀
    obtain ⟨hu₀_lim, hu₀_ev⟩ := tendsto_nhdsWithin_iff.1 hu₀
    rw [Filter.eventually_atTop] at hu₀_ev
    obtain ⟨N₀, hu₀_mem⟩ := hu₀_ev
    set u : ℕ → ℝ := fun n => u₀ (n + N₀)
    have hu_mem : ∀ n, u n ∈ Icc (0 : ℝ) B := fun n => hu₀_mem (n + N₀) (Nat.le_add_left N₀ n)
    have hu_lim : Tendsto u atTop (𝓝 σ₀) :=
      hu₀_lim.comp (tendsto_add_atTop_nat N₀)
    suffices h_main : Tendsto (fun n => Rj (u n)) atTop (𝓝 (Rj σ₀)) by
      exact (tendsto_add_atTop_iff_nat N₀).1 h_main
    have h_sq_tendsto : Tendsto (fun n => ‖Rj (u n) - Rj σ₀‖ ^ 2) atTop (𝓝 0) := by
      have heq_sq : (fun n => ‖Rj (u n) - Rj σ₀‖ ^ 2) =
          (fun n => ∫ z : ℂ, ‖frameRFun κ P ν tr t₁ j (u n) z -
            frameRFun κ P ν tr t₁ j σ₀ z‖ ^ 2 ∂(Planar.wMeasure m)) := by
        funext n
        simp only [Rj, hu_mem n, hσ₀, ↓reduceDIte]
        exact norm_sq_toLp_sub (hR_memLp (u n) (hu_mem n)) (hR_memLp σ₀ hσ₀)
      rw [heq_sq]
      have hzero : (0 : ℝ) = ∫ _ : ℂ, (0 : ℝ) ∂(Planar.wMeasure m) := by simp
      rw [hzero]
      refine tendsto_integral_of_dominated_convergence
        (fun z => (2 * M_R) ^ 2 * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 8)) ?_ ?_ ?_ ?_
      · intro n
        exact ((hR_meas (u n) (hu_mem n)).sub (hR_meas σ₀ hσ₀)).norm.pow 2
      · exact (integrable_gauss_wMeasure hm0).const_mul ((2 * M_R) ^ 2)
      · intro n
        refine Eventually.of_forall fun z => ?_
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have h1 : ‖frameRFun κ P ν tr t₁ j (u n) z - frameRFun κ P ν tr t₁ j σ₀ z‖ ≤
            2 * M_R * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by
          calc ‖frameRFun κ P ν tr t₁ j (u n) z - frameRFun κ P ν tr t₁ j σ₀ z‖
              ≤ ‖frameRFun κ P ν tr t₁ j (u n) z‖ + ‖frameRFun κ P ν tr t₁ j σ₀ z‖ :=
                norm_sub_le _ _
            _ ≤ M_R * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) +
                  M_R * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) :=
                add_le_add (hR_bd (u n) (hu_mem n) z) (hR_bd σ₀ hσ₀ z)
            _ = 2 * M_R * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16) := by ring
        have h2 : ‖frameRFun κ P ν tr t₁ j (u n) z - frameRFun κ P ν tr t₁ j σ₀ z‖ ^ 2 ≤
            (2 * M_R * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 16)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        refine h2.trans_eq ?_
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring
      · set d₀ := dOf ν t₁ σ₀
        have hnull : volume ({z : ℂ | z.re = -d₀ / 2} ∪ {z : ℂ | z.re = d₀ / 2}) = 0 :=
          measure_union_null (volume_re_eq_zero (-d₀ / 2)) (volume_re_eq_zero (d₀ / 2))
        have hnull_w : Planar.wMeasure m ({z : ℂ | z.re = -d₀ / 2} ∪ {z : ℂ | z.re = d₀ / 2}) = 0 :=
          Planar.wMeasure_ac m hnull
        have hae : ∀ᵐ z ∂(Planar.wMeasure m),
            z ∉ ({z : ℂ | z.re = -d₀ / 2} ∪ {z : ℂ | z.re = d₀ / 2}) := by
          rw [ae_iff]
          convert hnull_w using 2
          ext z
          simp
          tauto
        refine hae.mono fun z hz => ?_
        simp only [mem_union, Set.mem_ofPred_eq, not_or] at hz
        have hdu : Tendsto (fun n => dOf ν t₁ (u n)) atTop (𝓝 d₀) :=
          (hd_cont σ₀ hσ₀).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
            _ hu_lim (Eventually.of_forall hu_mem))
        have hau : Tendsto (fun n => ageAt ν t₁ (u n)) atTop (𝓝 (ageAt ν t₁ σ₀)) :=
          (hage_cont σ₀ hσ₀).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
            _ hu_lim (Eventually.of_forall hu_mem))
        suffices hpt : Tendsto (fun n => frameRFun κ P ν tr t₁ j (u n) z) atTop
            (𝓝 (frameRFun κ P ν tr t₁ j σ₀ z)) by
          have hsub := hpt.sub_const (frameRFun κ P ν tr t₁ j σ₀ z)
          simpa using (hsub.norm.pow 2)
        by_cases hcell : cToPlane z ∈ B0579.cell d₀
        · have hmem_open : -d₀ / 2 < z.re ∧ z.re < d₀ / 2 := by
            simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, cToPlane] at hcell
            exact ⟨lt_of_le_of_ne (by linarith [hcell.1]) (Ne.symm hz.1), hcell.2⟩
          have hev_in : ∀ᶠ n in atTop, cToPlane z ∈ B0579.cell (dOf ν t₁ (u n)) := by
            have h1 : ∀ᶠ n in atTop, -dOf ν t₁ (u n) / 2 < z.re :=
              (hdu.neg.div_const 2).eventually (Iio_mem_nhds hmem_open.1)
            have h2 : ∀ᶠ n in atTop, z.re < dOf ν t₁ (u n) / 2 :=
              (hdu.div_const 2).eventually (Ioi_mem_nhds hmem_open.2)
            filter_upwards [h1, h2] with n hn1 hn2
            simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, cToPlane]
            exact ⟨by linarith, hn2⟩
          set y := cToPlane z
          have h0_eq : frameRFun κ P ν tr t₁ j σ₀ z =
              movFreeRes κ tr (ageAt ν t₁ σ₀) j y +
                ((movBeta0 P ν (ageAt ν t₁ σ₀) : ℝ) : ℂ) * perE κ d₀ j y := by
            unfold frameRFun cellZeroExt
            exact Set.indicator_of_mem hcell _
          rw [h0_eq]
          have hev_eq : (fun n => movFreeRes κ tr (ageAt ν t₁ (u n)) j y +
                ((movBeta0 P ν (ageAt ν t₁ (u n)) : ℝ) : ℂ) *
                  perE κ (dOf ν t₁ (u n)) j y) =ᶠ[atTop]
              fun n => frameRFun κ P ν tr t₁ j (u n) z :=
            hev_in.mono fun n hn => by
              unfold frameRFun cellZeroExt
              exact (Set.indicator_of_mem
                (show cToPlane z ∈ B0579.cell (dOf ν t₁ (u n)) from hn)
                (fun y => movFreeRes κ tr (ageAt ν t₁ (u n)) j y +
                  ((movBeta0 P ν (ageAt ν t₁ (u n)) : ℝ) : ℂ) *
                    perE κ (dOf ν t₁ (u n)) j y)).symm
          refine Tendsto.congr' hev_eq ?_
          · have heq_n : (fun n => movFreeRes κ tr (ageAt ν t₁ (u n)) j y +
                  ((movBeta0 P ν (ageAt ν t₁ (u n)) : ℝ) : ℂ) *
                    perE κ (dOf ν t₁ (u n)) j y) =
                (fun n => -((clockTheta ν (ageAt ν t₁ (u n)) : ℂ)⁻¹ *
                    perSum (dOf ν t₁ (u n)) (movD (κ.e j)) y) +
                  (((movingTrainV tr (ageAt ν t₁ (u n)) y 0 : ℝ) : ℂ) *
                      pdCx 0 (perE κ (dOf ν t₁ (u n)) j) y +
                    ((movingTrainV tr (ageAt ν t₁ (u n)) y 1 : ℝ) : ℂ) *
                      pdCx 1 (perE κ (dOf ν t₁ (u n)) j) y) +
                  ((movBeta0 P ν (ageAt ν t₁ (u n)) : ℝ) : ℂ) *
                    perE κ (dOf ν t₁ (u n)) j y) := by
              funext n
              rw [movFreeRes_eq_neg_movOscRes_add,
                OscillatorForceSub.movOscRes_eq_perSum_movD hκ hν
                  (ht₁.trans (hage_mem (u n) (hu_mem n)).1) j y]
            have heq_0 : movFreeRes κ tr (ageAt ν t₁ σ₀) j y +
                  ((movBeta0 P ν (ageAt ν t₁ σ₀) : ℝ) : ℂ) * perE κ d₀ j y =
                -((clockTheta ν (ageAt ν t₁ σ₀) : ℂ)⁻¹ * perSum d₀ (movD (κ.e j)) y) +
                  (((movingTrainV tr (ageAt ν t₁ σ₀) y 0 : ℝ) : ℂ) * pdCx 0 (perE κ d₀ j) y +
                    ((movingTrainV tr (ageAt ν t₁ σ₀) y 1 : ℝ) : ℂ) * pdCx 1 (perE κ d₀ j) y) +
                  ((movBeta0 P ν (ageAt ν t₁ σ₀) : ℝ) : ℂ) * perE κ d₀ j y := by
              rw [movFreeRes_eq_neg_movOscRes_add,
                OscillatorForceSub.movOscRes_eq_perSum_movD hκ hν
                  (ht₁.trans (hage_mem σ₀ hσ₀).1) j y]
            rw [heq_n, heq_0]
            have hs0 : 0 ≤ ageAt ν t₁ σ₀ := ht₁.trans (hage_mem σ₀ hσ₀).1
            have hθ_lim : Tendsto (fun n => ((clockTheta ν (ageAt ν t₁ (u n)) : ℝ) : ℂ)⁻¹) atTop
                (𝓝 ((clockTheta ν (ageAt ν t₁ σ₀) : ℝ) : ℂ)⁻¹) := by
              have hcθ : ContinuousAt (clockTheta ν) (ageAt ν t₁ σ₀) := by
                unfold clockTheta clockA
                have ha : 1 ≤ clockA ν (ageAt ν t₁ σ₀) := one_le_clockA hν.le hs0
                have hθne : ν * (1 + ν * ageAt ν t₁ σ₀) ≠ 0 := by
                  change ν * clockA ν (ageAt ν t₁ σ₀) ≠ 0
                  positivity
                fun_prop (disch := exact hθne)
              exact (Complex.continuous_ofReal.continuousAt.tendsto.comp (hcθ.tendsto.comp hau)).inv₀
                (by exact_mod_cast (show clockTheta ν (ageAt ν t₁ σ₀) ≠ 0 by
                  linarith [hθ_ge1 σ₀ hσ₀]))
            have hD_lim : Tendsto (fun n => perSum (dOf ν t₁ (u n)) (movD (κ.e j)) y) atTop
                (𝓝 (perSum d₀ (movD (κ.e j)) y)) :=
              (hperD_cont y d₀ (hd_ge1 σ₀ hσ₀)).tendsto.comp
                (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdu
                  (Eventually.of_forall fun n => hd_ge1 (u n) (hu_mem n)))
            have hE_lim : Tendsto (fun n => perE κ (dOf ν t₁ (u n)) j y) atTop
                (𝓝 (perE κ d₀ j y)) :=
              (hperE_cont y d₀ (hd_ge1 σ₀ hσ₀)).tendsto.comp
                (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdu
                  (Eventually.of_forall fun n => hd_ge1 (u n) (hu_mem n)))
            have hpd_lim : ∀ k : Fin 2,
                Tendsto (fun n => pdCx k (perE κ (dOf ν t₁ (u n)) j) y) atTop
                  (𝓝 (pdCx k (perE κ d₀ j) y)) := fun k =>
              (hpd_cont k y d₀ (hd_ge1 σ₀ hσ₀)).tendsto.comp
                (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdu
                  (Eventually.of_forall fun n => hd_ge1 (u n) (hu_mem n)))
            have hβ_lim : Tendsto (fun n => ((movBeta0 P ν (ageAt ν t₁ (u n)) : ℝ) : ℂ)) atTop
                (𝓝 ((movBeta0 P ν (ageAt ν t₁ σ₀) : ℝ) : ℂ)) :=
              Complex.continuous_ofReal.continuousAt.tendsto.comp
                ((continuous_movBeta0 P ν).continuousAt.tendsto.comp hau)
            have hV_lim : ∀ k : Fin 2,
                Tendsto (fun n => ((movingTrainV tr (ageAt ν t₁ (u n)) y k : ℝ) : ℂ)) atTop
                  (𝓝 ((movingTrainV tr (ageAt ν t₁ σ₀) y k : ℝ) : ℂ)) := by
              intro k
              refine Complex.continuous_ofReal.continuousAt.tendsto.comp ?_
              have h_cont_r : ContinuousWithinAt
                  (fun r => movingTrainV tr r y k) (Ici 0) (ageAt ν t₁ σ₀) := by
                unfold movingTrainV
                have hcA : ContinuousWithinAt (clockA ν) (Ici 0) (ageAt ν t₁ σ₀) :=
                  (FlowMeas.continuousOn_clockA (Ici 0)) _ hs0
                have hAp : ContinuousWithinAt (fun r => clockA ν r ^ (3 / 2 : ℝ)) (Ici 0)
                    (ageAt ν t₁ σ₀) :=
                  hcA.rpow_const (Or.inr (by norm_num))
                have hv_c : ContinuousWithinAt (fun r => tr.v r
                    (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) k)
                    (Ici 0) (ageAt ν t₁ σ₀) := by
                  have hsm : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
                      (Ici 0 ×ˢ univ) := tr.isTrain.smooth_v.continuousOn
                  have hmap : ContinuousWithinAt (fun r => (r,
                      (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)))
                      (Ici 0) (ageAt ν t₁ σ₀) :=
                    continuousWithinAt_id.prodMk
                      (((Real.continuous_sqrt.continuousAt.comp_continuousWithinAt hcA).mul
                        continuousWithinAt_const).prodMk
                        ((Real.continuous_sqrt.continuousAt.comp_continuousWithinAt hcA).mul
                          continuousWithinAt_const))
                  have h_cwa : ContinuousWithinAt (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
                      (Ici 0 ×ˢ univ) (ageAt ν t₁ σ₀,
                        (Real.sqrt (clockA ν (ageAt ν t₁ σ₀)) * y.1,
                          Real.sqrt (clockA ν (ageAt ν t₁ σ₀)) * y.2)) :=
                    hsm _ ⟨hs0, mem_univ _⟩
                  have h_comp : ContinuousWithinAt
                      ((fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) ∘
                        fun r => (r, (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)))
                      (Ici 0) (ageAt ν t₁ σ₀) :=
                    ContinuousWithinAt.comp h_cwa hmap (fun r hr => ⟨hr, mem_univ _⟩)
                  exact (PiLp.continuous_apply 2 _ k).continuousAt.comp_continuousWithinAt h_comp
                exact hAp.mul hv_c
              exact h_cont_r.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
                _ hau (Eventually.of_forall fun n => ht₁.trans (hage_mem (u n) (hu_mem n)).1))
            exact (((hθ_lim.mul hD_lim).neg).add
              (((hV_lim 0).mul (hpd_lim 0)).add ((hV_lim 1).mul (hpd_lim 1)))).add
              (hβ_lim.mul hE_lim)
        · have hnot_open : z.re < -d₀ / 2 ∨ d₀ / 2 < z.re := by
            simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, cToPlane, not_and,
              not_lt] at hcell
            by_cases hlt : z.re < -d₀ / 2
            · exact Or.inl hlt
            · exact Or.inr (lt_of_le_of_ne (hcell (by linarith)) (Ne.symm hz.2))
          have hev_out : ∀ᶠ n in atTop, cToPlane z ∉ B0579.cell (dOf ν t₁ (u n)) := by
            rcases hnot_open with hlt | hgt
            · have h1 : ∀ᶠ n in atTop, z.re < -dOf ν t₁ (u n) / 2 :=
                (hdu.neg.div_const 2).eventually (Ioi_mem_nhds hlt)
              filter_upwards [h1] with n hn
              simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, cToPlane, not_and]
              intro hle
              linarith
            · have h2 : ∀ᶠ n in atTop, dOf ν t₁ (u n) / 2 < z.re :=
                (hdu.div_const 2).eventually (Iio_mem_nhds hgt)
              filter_upwards [h2] with n hn
              simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, cToPlane, not_and,
                not_lt]
              intro _
              linarith
          have h0 : frameRFun κ P ν tr t₁ j σ₀ z = 0 := by
            unfold frameRFun cellZeroExt
            exact Set.indicator_of_notMem hcell _
          rw [h0]
          refine tendsto_const_nhds.congr' (hev_out.mono fun n hn => ?_)
          unfold frameRFun cellZeroExt
          exact (Set.indicator_of_notMem hn _).symm
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsqrt := (Real.continuous_sqrt.continuousAt.tendsto.comp h_sq_tendsto)
    simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
    refine hsqrt.congr (fun n => Real.sqrt_sq (norm_nonneg _))

end FrameDuhamelSub

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
