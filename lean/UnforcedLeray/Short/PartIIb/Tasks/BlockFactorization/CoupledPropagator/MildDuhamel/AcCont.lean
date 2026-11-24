import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_2
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.CylWeightedKernel
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.TrainGradCoeff
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Helper for `PartII-b:F2/2/1`: Strong continuity of `r ↦ Ac r w` on `[0, p.H]`

Proves `continuousOn_Ac_apply`: under the hypotheses of `MildDuhamelEvolutionStep`,
`r ↦ Ac r w` is continuous on `Icc 0 p.H` in `Xmc p.c m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.MildDuhamelAux

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartI

/-- Pointwise time-continuity of `r ↦ trainGradE tr r x` on `Icc 0 H` (`0 ≤ H`). -/
theorem continuousOn_trainGradE_time {ν c H : ℝ} (tr : B0140.TrainSol ν c)
    (hH : 0 ≤ H) (x : B0579.Plane) :
    ContinuousOn (fun r => trainGradE tr r x) (Icc 0 H) := by
  set T : ℝ := H + 1
  have hT0 : 0 < T := by dsimp [T]; linarith
  set S : Set (ℝ × Cyl.Plane) := Icc 0 T ×ˢ (univ : Set Cyl.Plane)
  have huniq : UniqueDiffOn ℝ S := UniqueDiffOn.prod (uniqueDiffOn_Icc hT0) uniqueDiffOn_univ
  have hsm : ContDiffOn ℝ ∞ (fun y : ℝ × Cyl.Plane => tr.v y.1 y.2) S :=
    tr.isTrain.smooth_v.mono (prod_mono Icc_subset_Ici_self (subset_refl _))
  have hF1 := crFc_contDiffOn hsm 1
  have hF0 := crFc_contDiffOn hsm 0
  set E' : ℝ × Cyl.Plane → ℝ := fun y =>
    fderivWithin ℝ (crFc tr.v 1) S y crEQ - fderivWithin ℝ (crFc tr.v 0) S y crEE
  have hE'sm : ContDiffOn ℝ ∞ E' S := by
    have h1 : ContDiffOn ℝ ∞ (fderivWithin ℝ (crFc tr.v 1) S) S :=
      hF1.fderivWithin huniq (by simp)
    have h0 : ContDiffOn ℝ ∞ (fderivWithin ℝ (crFc tr.v 0) S) S :=
      hF0.fderivWithin huniq (by simp)
    exact (h1.clm_apply contDiffOn_const).sub (h0.clm_apply contDiffOn_const)
  have hcurl : ∀ r ∈ Icc (0 : ℝ) T, B0238.Ec tr r = fun z => E' (r, z) := by
    intro r hr
    funext z
    exact crCurl_within hsm hr
  have hpd : ∀ r ∈ Icc (0 : ℝ) T, ∀ j : Fin 2,
      B0579.pd j (B0238.Ec tr r) x = fderivWithin ℝ E' S (r, x) (0, B0579.dir j) := by
    intro r hr j
    have hmem : ((r, x) : ℝ × Cyl.Plane) ∈ S := ⟨hr, mem_univ _⟩
    have hd : HasFDerivWithinAt E' (fderivWithin ℝ E' S (r, x)) S (r, x) :=
      ((hE'sm.differentiableOn (by simp)) _ hmem).hasFDerivWithinAt
    have hι : HasFDerivAt (fun y : Cyl.Plane => ((r, y) : ℝ × Cyl.Plane))
        ((0 : Cyl.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Cyl.Plane)) x :=
      (hasFDerivAt_const r x).prodMk (hasFDerivAt_id x)
    have hcomp := hd.comp x (hι.hasFDerivWithinAt (s := Set.univ)) (fun y _ => ⟨hr, mem_univ _⟩)
    have hfd : HasFDerivAt (fun y : Cyl.Plane => E' (r, y))
        ((fderivWithin ℝ E' S (r, x)).comp
          ((0 : Cyl.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Cyl.Plane))) x :=
      hasFDerivWithinAt_univ.mp hcomp
    unfold B0579.pd
    rw [hcurl r hr, hfd.fderiv]
    simp
  have hcont_j : ∀ j : Fin 2,
      ContinuousOn (fun r => B0579.pd j (B0238.Ec tr r) x) (Icc 0 H) := by
    intro j
    have hcontS : ContinuousOn (fun y => fderivWithin ℝ E' S y (0, B0579.dir j)) S :=
      (hE'sm.continuousOn_fderivWithin huniq (by simp)).clm_apply continuousOn_const
    have hcomp : ContinuousOn (fun r => fderivWithin ℝ E' S (r, x) (0, B0579.dir j)) (Icc 0 H) :=
      hcontS.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨⟨hr.1, hr.2.trans (by dsimp [T]; linarith)⟩, mem_univ _⟩)
    exact hcomp.congr fun r hr => hpd r ⟨hr.1, hr.2.trans (by dsimp [T]; linarith)⟩ j
  unfold trainGradE
  exact (hcont_j 0).prodMk (hcont_j 1)

/-- Uniform `IsCylWeightedCoeff` bound for `trainGradE p.train r` across `r ∈ Icc 0 p.H`. -/
theorem exists_uniform_trainGradE_coeff
    {m Sig : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1)
    (hAge : p.ageCut = Sig) {δ : ℝ} (hδ0 : 0 < δ)
    (hTCM : TrainCloseM m p.train Sig δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Icc 0 p.H, IsCylWeightedCoeff p.c m B (trainGradE p.train r) := by
  have hc : 1 ≤ p.c := bgRegime_c_ge_one hbg hν1
  have hν : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  obtain ⟨C_tr, hC_tr, hStep⟩ := trainGradCoeffStep_proof m hm Sig hSig
  set B : ℝ := C_tr + C_tr * (p.c ^ (-2 : ℝ) + δ)
  have hB_pos : 0 < B := by
    have hc_rpow : 0 ≤ p.c ^ (-2 : ℝ) := Real.rpow_nonneg hc_pos.le _
    dsimp [B]
    positivity
  refine ⟨B, hB_pos, fun r hr => ?_⟩
  set σ : ℝ := r * p.ν
  have hσ0 : 0 ≤ σ := mul_nonneg hr.1 hν.le
  have hσ1 : σ ≤ Sig := by
    dsimp [σ]
    exact (le_div_iff₀ hν).mp (hr.2.trans_eq hH_eq)
  have hσ_div : σ / p.ν = r := mul_div_cancel_right₀ r hν.ne'
  obtain ⟨h1, h2⟩ := hStep p d dm dp hbg hc δ hδ0.le hTCM σ ⟨hσ0, hσ1⟩
  have hsum := h1.add h2
  have hfun : (fun x => planarGradE σ x + (trainGradE p.train (σ / p.ν) x - planarGradE σ x)) =
      trainGradE p.train r := by
    funext x
    rw [hσ_div, add_sub_cancel]
  rwa [hfun] at hsum

/-- Strong continuity `ContinuousOn (fun r => Ac r w) (Icc 0 p.H)` in `Xmc p.c m`. -/
theorem continuousOn_Ac_apply
    {m Sig : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1)
    (hAge : p.ageCut = Sig) {δ : ℝ} (hδ0 : 0 < δ)
    (hTCM : TrainCloseM m p.train Sig δ)
    {Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hAc : ∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s))
    (w : Xmc p.c m) :
    ContinuousOn (fun r => Ac r w) (Icc 0 p.H) := by
  have hc : 1 ≤ p.c := bgRegime_c_ge_one hbg hν1
  have hm1 : 1 < m := by linarith
  have hH_nn : 0 ≤ p.H := by
    rw [Params.H, hAge]
    exact div_nonneg hSig.le p.ν_pos.le
  obtain ⟨B, hB, hCoeff⟩ := exists_uniform_trainGradE_coeff hm hSig hbg hν1 hAge hδ0 hTCM
  set μ : Measure B0579.Plane := B0579.cellMeasure p.c m
  have hw_cont : Continuous (fun x : B0579.Plane => B * B0579.jb x ^ (-(m / 2 + 1))) :=
    continuous_const.mul (B0579.continuous_jb_rpow _)
  let b₀ : B0579.Plane → B0579.Plane := fun x => (B * B0579.jb x ^ (-(m / 2 + 1)), 0)
  let b₁ : B0579.Plane → B0579.Plane := fun x => (0, B * B0579.jb x ^ (-(m / 2 + 1)))
  have hb₀ : IsCylWeightedCoeff p.c m B b₀ := by
    refine ⟨hw_cont.prodMk continuous_const, fun x _hx => ?_⟩
    have hnn : 0 ≤ B * B0579.jb x ^ (-(m / 2 + 1)) :=
      mul_nonneg hB.le (Real.rpow_nonneg (B0579.jb_pos x).le _)
    dsimp [b₀]
    rw [abs_of_nonneg hnn, abs_zero, add_zero, mul_assoc, B0579.jb_rpow_mul,
      neg_add_cancel, Real.rpow_zero, mul_one]
  have hb₁ : IsCylWeightedCoeff p.c m B b₁ := by
    refine ⟨continuous_const.prodMk hw_cont, fun x _hx => ?_⟩
    have hnn : 0 ≤ B * B0579.jb x ^ (-(m / 2 + 1)) :=
      mul_nonneg hB.le (Real.rpow_nonneg (B0579.jb_pos x).le _)
    dsimp [b₁]
    rw [abs_zero, zero_add, abs_of_nonneg hnn, mul_assoc, B0579.jb_rpow_mul,
      neg_add_cancel, Real.rpow_zero, mul_one]
  have hg₀ : MemLp (cylWeightedOpFun p.c b₀ w) 2 μ :=
    memLp_cylWeightedOpFun hc hm1 hB.le hb₀ w
  have hg₁ : MemLp (cylWeightedOpFun p.c b₁ w) 2 μ :=
    memLp_cylWeightedOpFun hc hm1 hB.le hb₁ w
  let M_fn : B0579.Plane → ℝ :=
    fun x => 2 * (‖cylWeightedOpFun p.c b₀ w x‖ + ‖cylWeightedOpFun p.c b₁ w x‖)
  have hM_lp : MemLp M_fn 2 μ := (hg₀.norm.add hg₁.norm).const_mul 2
  have hM_fin : (∫⁻ x, ‖M_fn x‖ₑ ^ 2 ∂μ) ≠ ⊤ := by
    rw [← B0592.eLpNorm_two_sq]
    exact (ENNReal.pow_lt_top hM_lp.eLpNorm_lt_top).ne
  have hae_cell : ∀ᵐ x ∂μ, x ∈ B0579.cell p.c :=
    (B0579.cellMeasure_ac p.c m).ae_le (ae_restrict_mem (B0579.measurableSet_cell p.c))
  have hpt_bd : ∀ r ∈ Icc 0 p.H, ∀ x ∈ B0579.cell p.c,
      ‖cylAc p.train r w x‖ ≤
        ‖cylWeightedOpFun p.c b₀ w x‖ + ‖cylWeightedOpFun p.c b₁ w x‖ := by
    intro r hr x hx
    have hmul := (hCoeff r hr).2 x hx
    have hinv : B0579.jb x ^ (m / 2 + 1) * B0579.jb x ^ (-(m / 2 + 1)) = 1 := by
      rw [B0579.jb_rpow_mul, add_neg_cancel, Real.rpow_zero]
    have hsum_le :
        |(trainGradE p.train r x).1| + |(trainGradE p.train r x).2| ≤
          B * B0579.jb x ^ (-(m / 2 + 1)) := by
      calc |(trainGradE p.train r x).1| + |(trainGradE p.train r x).2|
          = ((|(trainGradE p.train r x).1| + |(trainGradE p.train r x).2|) *
              B0579.jb x ^ (m / 2 + 1)) * B0579.jb x ^ (-(m / 2 + 1)) := by
            rw [mul_assoc, hinv, mul_one]
        _ ≤ B * B0579.jb x ^ (-(m / 2 + 1)) :=
            mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg (B0579.jb_pos x).le _)
    have h0_le : |(trainGradE p.train r x).1| ≤ B * B0579.jb x ^ (-(m / 2 + 1)) :=
      le_trans (le_add_of_nonneg_right (abs_nonneg _)) hsum_le
    have h1_le : |(trainGradE p.train r x).2| ≤ B * B0579.jb x ^ (-(m / 2 + 1)) :=
      le_trans (le_add_of_nonneg_left (abs_nonneg _)) hsum_le
    have hw_nn : 0 ≤ B * B0579.jb x ^ (-(m / 2 + 1)) :=
      mul_nonneg hB.le (Real.rpow_nonneg (B0579.jb_pos x).le _)
    have hg0_eq : ‖cylWeightedOpFun p.c b₀ w x‖ =
        |Cyl.K p.c w x 0| * (B * B0579.jb x ^ (-(m / 2 + 1))) := by
      simp only [cylWeightedOpFun, b₀, Real.norm_eq_abs, mul_zero, add_zero, abs_neg,
        abs_mul, abs_of_nonneg hw_nn]
    have hg1_eq : ‖cylWeightedOpFun p.c b₁ w x‖ =
        |Cyl.K p.c w x 1| * (B * B0579.jb x ^ (-(m / 2 + 1))) := by
      simp only [cylWeightedOpFun, b₁, Real.norm_eq_abs, mul_zero, zero_add, abs_neg,
        abs_mul, abs_of_nonneg hw_nn]
    rw [hg0_eq, hg1_eq]
    unfold cylAc
    rw [Real.norm_eq_abs, abs_neg]
    calc |Cyl.K p.c w x 0 * B0579.pd 0 (B0238.Ec p.train r) x +
            Cyl.K p.c w x 1 * B0579.pd 1 (B0238.Ec p.train r) x|
        ≤ |Cyl.K p.c w x 0 * B0579.pd 0 (B0238.Ec p.train r) x| +
            |Cyl.K p.c w x 1 * B0579.pd 1 (B0238.Ec p.train r) x| := abs_add_le _ _
      _ = |Cyl.K p.c w x 0| * |(trainGradE p.train r x).1| +
            |Cyl.K p.c w x 1| * |(trainGradE p.train r x).2| := by
          simp only [trainGradE, abs_mul]
      _ ≤ |Cyl.K p.c w x 0| * (B * B0579.jb x ^ (-(m / 2 + 1))) +
            |Cyl.K p.c w x 1| * (B * B0579.jb x ^ (-(m / 2 + 1))) :=
          add_le_add (mul_le_mul_of_nonneg_left h0_le (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h1_le (abs_nonneg _))
  intro r₀ hr₀
  rw [ContinuousWithinAt, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  let F : ℝ → B0579.Plane → ℝ≥0∞ :=
    fun r x => ‖cylAc p.train r w x - cylAc p.train r₀ w x‖ₑ ^ 2
  have hF_meas : ∀ᶠ r in 𝓝[Icc 0 p.H] r₀, AEMeasurable (F r) μ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hae_sub : (fun x => cylAc p.train r w x - cylAc p.train r₀ w x) =ᵐ[μ]
        fun x => (Ac r w : B0579.Plane → ℝ) x - (Ac r₀ w : B0579.Plane → ℝ) x :=
      (hAc r hr w).symm.sub (hAc r₀ hr₀ w).symm
    have haesm : AEStronglyMeasurable
        (fun x => cylAc p.train r w x - cylAc p.train r₀ w x) μ :=
      ((Lp.aestronglyMeasurable (Ac r w)).sub (Lp.aestronglyMeasurable (Ac r₀ w))).congr
        hae_sub.symm
    exact haesm.enorm.pow_const 2
  have hF_bd : ∀ᶠ r in 𝓝[Icc 0 p.H] r₀, ∀ᵐ x ∂μ, F r x ≤ ‖M_fn x‖ₑ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [hae_cell] with x hx
    have hdiff_le : ‖cylAc p.train r w x - cylAc p.train r₀ w x‖ ≤ M_fn x := by
      calc ‖cylAc p.train r w x - cylAc p.train r₀ w x‖
          ≤ ‖cylAc p.train r w x‖ + ‖cylAc p.train r₀ w x‖ := norm_sub_le _ _
        _ ≤ (‖cylWeightedOpFun p.c b₀ w x‖ + ‖cylWeightedOpFun p.c b₁ w x‖) +
              (‖cylWeightedOpFun p.c b₀ w x‖ + ‖cylWeightedOpFun p.c b₁ w x‖) :=
            add_le_add (hpt_bd r hr x hx) (hpt_bd r₀ hr₀ x hx)
        _ = M_fn x := by dsimp [M_fn]; ring
    have hM_nn : 0 ≤ M_fn x := by dsimp [M_fn]; positivity
    have henorm : ‖cylAc p.train r w x - cylAc p.train r₀ w x‖ₑ ≤ ‖M_fn x‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg hM_nn]
      exact ENNReal.ofReal_le_ofReal hdiff_le
    exact pow_le_pow_left₀ zero_le henorm 2
  have hF_lim : ∀ᵐ x ∂μ, Tendsto (fun r => F r x) (𝓝[Icc 0 p.H] r₀) (𝓝 0) := by
    refine Eventually.of_forall fun x => ?_
    have htg := continuousOn_trainGradE_time p.train hH_nn x r₀ hr₀
    have hcyl_cont : ContinuousWithinAt (fun r => cylAc p.train r w x) (Icc 0 p.H) r₀ := by
      have hfst : ContinuousWithinAt (fun r => (trainGradE p.train r x).1) (Icc 0 p.H) r₀ :=
        continuous_fst.continuousAt.comp_continuousWithinAt htg
      have hsnd : ContinuousWithinAt (fun r => (trainGradE p.train r x).2) (Icc 0 p.H) r₀ :=
        continuous_snd.continuousAt.comp_continuousWithinAt htg
      change ContinuousWithinAt
        (fun r => -(Cyl.K p.c w x 0 * (trainGradE p.train r x).1 +
          Cyl.K p.c w x 1 * (trainGradE p.train r x).2)) (Icc 0 p.H) r₀
      exact ((continuousWithinAt_const.mul hfst).add (continuousWithinAt_const.mul hsnd)).neg
    have hsub0 : Tendsto (fun r => cylAc p.train r w x - cylAc p.train r₀ w x)
        (𝓝[Icc 0 p.H] r₀) (𝓝 0) := by
      have h := hcyl_cont.tendsto.sub (tendsto_const_nhds (x := cylAc p.train r₀ w x))
      rwa [sub_self] at h
    have henorm0 : Tendsto (fun r => ‖cylAc p.train r w x - cylAc p.train r₀ w x‖ₑ)
        (𝓝[Icc 0 p.H] r₀) (𝓝 0) := by
      have h := (continuous_enorm.tendsto (0 : ℝ)).comp hsub0
      rwa [enorm_zero] at h
    have hpow0 := ((ENNReal.continuous_pow 2).tendsto (0 : ℝ≥0∞)).comp henorm0
    rwa [zero_pow (by norm_num)] at hpow0
  have h_lint : Tendsto (fun r => ∫⁻ x, F r x ∂μ) (𝓝[Icc 0 p.H] r₀) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ)
      (f := fun _ => (0 : ℝ≥0∞)) (fun x => ‖M_fn x‖ₑ ^ 2) hF_meas hF_bd hM_fin hF_lim
    simpa using h
  have h_rpow : Tendsto (fun r => (∫⁻ x, F r x ∂μ) ^ (1 / 2 : ℝ))
      (𝓝[Icc 0 p.H] r₀) (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto (0 : ℝ≥0∞)).comp h_lint
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  refine h_rpow.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hae_sub : (⇑(Ac r w) - ⇑(Ac r₀ w)) =ᵐ[μ]
      fun x => cylAc p.train r w x - cylAc p.train r₀ w x :=
    (hAc r hr w).sub (hAc r₀ hr₀ w)
  rw [eLpNorm_congr_ae hae_sub,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, one_div, F]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_natCast _ 2]
  norm_num

end UnforcedLeray.Short.IIb.MildDuhamelAux
