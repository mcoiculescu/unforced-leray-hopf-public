import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.RawAndInletL4
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2_2_2_1
import UnforcedLeray.Short.PartIIb.Tasks.DatumFacts.RawDatumSmooth

/-!
# Age-zero train stream jets and `O(s)` far-field raw comparison (helper for `PartII-b:B3/2/1/1`)

Source of record: `the November 2 reference manuscript`, lines 2593-2596
(`short-bg:raw-heat`: at large radius `s = R²/ϱ² ≤ 1`, the `O(s)` inlet expansion of `U_raw` gives
`|D^j(U_raw(τ) - N_v(datumProfile(ψ(0))))(y)| ≤ C (1 + |y|)^{-3}` for `j ≤ 2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.RawHeatAux

open UnforcedLeray UnforcedLeray.Cyl UnforcedLeray.Train
open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.IIb.RawAndInletL4

/-- Unconditional `TrainStreamWtdBdd` from `RawAndInletL4`. -/
theorem trainStreamWtdBdd_uncond : PartIIIb.Concrete.TrainStreamWtdBdd := by
  have hF : PartIIIb.Concrete.WeightedTrainFluctAgeJetFixed :=
    PartIIIb.Concrete.weightedTrainFluctAgeJetFixed_of
      PartI.trainFluctAgeJetFixed fluctDoubledWeightPoly_proof
  exact PartIIIb.Concrete.trainStreamWtdBdd_of
    (PartIIIb.Concrete.trainFluctWtdBdd_of (RawAndInletL4.trainFluctWtdAgeJet_of_s23 hF))
    RawAndInletL4.trainMeanWtdBdd_s23

/-! ## 1. Continuity of `(q, η)`-jets of `tr.ψ s` as `s → 0⁺` and `O(s)` MVT bounds -/

private theorem psi_eta_ftc {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (q η M : ℝ) :
    tr.ψ s (q, η) - tr.ψ s (q, M) = ∫ t in η..M, tr.v s (q, t) 0 := by
  have hψd : Differentiable ℝ (tr.ψ s) := tr.isTrain.stream_differentiable s hs
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => tr.ψ s (q, t')) (-tr.v s (q, t) 0) t := by
    intro t
    have hpath : HasDerivAt (fun t' : ℝ => ((q, t') : Plane)) ((0 : ℝ), (1 : ℝ)) t :=
      (hasDerivAt_const t q).prodMk (hasDerivAt_id' t)
    have hdiffAt : DifferentiableAt ℝ (fun t' : ℝ => tr.ψ s (q, t')) t :=
      (hψd (q, t)).comp t hpath.differentiableAt
    have hval : -tr.v s (q, t) 0 = deriv (fun t' : ℝ => tr.ψ s (q, t')) t := by
      rw [tr.isTrain.stream s hs (q, t), toVec_zero]
      show -(-deriv (fun y : ℝ => tr.ψ s (q, y)) t) = _
      ring
    rw [hval]
    exact hdiffAt.hasDerivAt
  have hcont : Continuous (fun t : ℝ => -tr.v s (q, t) 0) := by
    have hmap : Continuous (fun t : ℝ => ((s, (q, t)) : ℝ × Plane)) :=
      continuous_const.prodMk (continuous_const.prodMk continuous_id)
    have hv0 : Continuous (fun t : ℝ => tr.v s (q, t) 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp
        (tr.isTrain.smooth_v.continuousOn.comp_continuous hmap fun t => ⟨hs, trivial⟩)
    exact hv0.neg
  have hFTC : ∫ t in η..M, -tr.v s (q, t) 0 = tr.ψ s (q, M) - tr.ψ s (q, η) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at hFTC
  linarith

private theorem tendsto_psi_zero {ν c : ℝ} (tr : B0140.TrainSol ν c) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hbd : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ z : Plane, (1 + |z.2|) * |tr.ψ s z| ≤ C₀)
    (w : Plane) :
    Tendsto (fun s : ℝ => tr.ψ s w) (𝓝[>] 0) (𝓝 (tr.ψ 0 w)) := by
  rcases w with ⟨q, η⟩
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hdec0 : Tendsto (fun M : ℝ => tr.ψ 0 (q, M)) atTop (𝓝 0) := by
    have hcomap : Tendsto (fun M : ℝ => ((q, M) : Plane)) atTop
        (comap (fun z : Plane => |z.2|) atTop) := by
      rw [tendsto_comap_iff]
      exact tendsto_abs_atTop_atTop
    exact (tr.isTrain.stream_decay 0 le_rfl).comp hcomap
  have hdecC : Tendsto (fun M : ℝ => C₀ / (1 + |M|)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ => 1 + |M|) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 tendsto_abs_atTop_atTop
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp h1).const_mul C₀
  have hevM : ∀ᶠ M : ℝ in atTop,
      0 ≤ M ∧ |tr.ψ 0 (q, M)| < ε / 3 ∧ C₀ / (1 + |M|) < ε / 3 := by
    filter_upwards [Ici_mem_atTop (0 : ℝ),
      hdec0.eventually (Metric.ball_mem_nhds (0 : ℝ) (ε := ε / 3) (by positivity)),
      hdecC.eventually (Metric.ball_mem_nhds (0 : ℝ) (ε := ε / 3) (by positivity))] with M hM0 h1 h2
    rw [Real.dist_eq, sub_zero] at h1 h2
    rw [abs_of_nonneg (div_nonneg hC₀ (by positivity))] at h2
    exact ⟨hM0, h1, h2⟩
  obtain ⟨M, _, hM_psi0, hM_C0⟩ := hevM.exists
  -- Compact uniform continuity of `(s, t) ↦ tr.v s (q, t) 0` on `[0, 1] × uIcc η M`
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ uIcc η M
  have hK_comp : IsCompact K := isCompact_Icc.prod isCompact_uIcc
  let g : ℝ × ℝ → ℝ := fun p => tr.v p.1 (q, p.2) 0
  have hg_cont : ContinuousOn g K := by
    have hmap : Continuous (fun p : ℝ × ℝ => ((p.1, (q, p.2)) : ℝ × Plane)) :=
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
    have hmaps : MapsTo (fun p : ℝ × ℝ => ((p.1, (q, p.2)) : ℝ × Plane)) K (Ici 0 ×ˢ univ) :=
      fun p hp => ⟨hp.1.1, trivial⟩
    exact (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp_continuousOn
      (tr.isTrain.smooth_v.continuousOn.comp hmap.continuousOn hmaps)
  have hg_uc := hK_comp.uniformContinuousOn_of_continuous hg_cont
  set δ₁ : ℝ := (ε / 3) / (|M - η| + 1)
  have hδ₁ : 0 < δ₁ := by positivity
  obtain ⟨δ₂, hδ₂, huc⟩ := Metric.uniformContinuousOn_iff.1 hg_uc δ₁ hδ₁
  refine ⟨min 1 (δ₂ / 2), lt_min one_pos (half_pos hδ₂), fun s hs_gt hs_dist => ?_⟩
  have hs0 : 0 < s := hs_gt
  rw [Real.dist_eq, sub_zero, abs_of_pos hs0] at hs_dist
  have hs1 : s ≤ 1 := hs_dist.le.trans (min_le_left _ _)
  have hsδ : s < δ₂ := lt_of_lt_of_le hs_dist ((min_le_right _ _).trans (by linarith))
  have hps_bd : |tr.ψ s (q, M)| < ε / 3 := by
    have h := hbd s hs0 hs1 (q, M)
    have hpos : 0 < 1 + |M| := by positivity
    have hdiv : |tr.ψ s (q, M)| ≤ C₀ / (1 + |M|) := by
      rw [le_div_iff₀' hpos]
      exact h
    exact lt_of_le_of_lt hdiv hM_C0
  have hint_diff : |(∫ t in η..M, tr.v s (q, t) 0) - (∫ t in η..M, tr.v 0 (q, t) 0)| < ε / 3 := by
    have hcs : Continuous (fun t : ℝ => tr.v s (q, t) 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp
        (tr.isTrain.smooth_v.continuousOn.comp_continuous
          (continuous_const.prodMk (continuous_const.prodMk continuous_id)) fun _ => ⟨hs0.le, trivial⟩)
    have hc0 : Continuous (fun t : ℝ => tr.v 0 (q, t) 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp
        (tr.isTrain.smooth_v.continuousOn.comp_continuous
          (continuous_const.prodMk (continuous_const.prodMk continuous_id))
          fun _ => ⟨show (0 : ℝ) ≤ 0 from le_rfl, trivial⟩)
    rw [← intervalIntegral.integral_sub (hcs.intervalIntegrable _ _) (hc0.intervalIntegrable _ _),
      ← Real.norm_eq_abs]
    have hpt : ∀ t ∈ uIoc η M, ‖tr.v s (q, t) 0 - tr.v 0 (q, t) 0‖ ≤ δ₁ := by
      intro t ht
      have ht' : t ∈ uIcc η M := uIoc_subset_uIcc ht
      have hp1 : (s, t) ∈ K := ⟨⟨hs0.le, hs1⟩, ht'⟩
      have hp0 : ((0 : ℝ), t) ∈ K := ⟨⟨le_rfl, zero_le_one⟩, ht'⟩
      have hd : dist (s, t) ((0 : ℝ), t) < δ₂ := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_pos hs0, max_eq_left hs0.le]
        exact hsδ
      have h := huc (s, t) hp1 (0, t) hp0 hd
      rw [Real.dist_eq] at h
      rw [Real.norm_eq_abs]
      exact h.le
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have hlt : δ₁ * |M - η| < ε / 3 := by
      have hden : 0 < |M - η| + 1 := by positivity
      calc (ε / 3) / (|M - η| + 1) * |M - η|
          < (ε / 3) / (|M - η| + 1) * (|M - η| + 1) := by gcongr; linarith
        _ = ε / 3 := div_mul_cancel₀ _ hden.ne'
    exact lt_of_le_of_lt hle hlt
  have hftc_s := psi_eta_ftc tr hs0.le q η M
  have hftc_0 := psi_eta_ftc tr le_rfl q η M
  have hdecomp : tr.ψ s (q, η) - tr.ψ 0 (q, η) =
      tr.ψ s (q, M) - tr.ψ 0 (q, M) +
        ((∫ t in η..M, tr.v s (q, t) 0) - (∫ t in η..M, tr.v 0 (q, t) 0)) := by linarith
  rw [Real.dist_eq, hdecomp]
  calc |tr.ψ s (q, M) - tr.ψ 0 (q, M) +
        ((∫ t in η..M, tr.v s (q, t) 0) - (∫ t in η..M, tr.v 0 (q, t) 0))|
      ≤ |tr.ψ s (q, M) - tr.ψ 0 (q, M)| +
          |(∫ t in η..M, tr.v s (q, t) 0) - (∫ t in η..M, tr.v 0 (q, t) 0)| := abs_add_le _ _
    _ ≤ |tr.ψ s (q, M)| + |tr.ψ 0 (q, M)| +
          |(∫ t in η..M, tr.v s (q, t) 0) - (∫ t in η..M, tr.v 0 (q, t) 0)| := by
        linarith [abs_sub (tr.ψ s (q, M)) (tr.ψ 0 (q, M))]
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

private def streamDualCLM : Vec →L[ℝ] (Plane →L[ℝ] ℝ) :=
  (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) -
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem fderiv_psi_eq_streamDual {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 ≤ s) :
    fderiv ℝ (tr.ψ s) = streamDualCLM ∘ (tr.v s) := by
  funext z
  have hd : DifferentiableAt ℝ (tr.ψ s) z := tr.isTrain.stream_differentiable s hs z
  apply ContinuousLinearMap.ext
  rintro ⟨dq, dη⟩
  have h10 : fderiv ℝ (tr.ψ s) z (1, 0) = tr.v s z 1 := by
    have hp : HasDerivAt (fun x : ℝ => ((x, z.2) : Plane)) (1, 0) z.1 :=
      (hasDerivAt_id' z.1).prodMk (hasDerivAt_const z.1 z.2)
    have hc : HasDerivAt (fun x : ℝ => tr.ψ s (x, z.2)) (fderiv ℝ (tr.ψ s) z (1, 0)) z.1 :=
      hd.hasFDerivAt.comp_hasDerivAt z.1 hp
    rw [tr.isTrain.stream s hs z, toVec_one]
    exact hc.deriv.symm
  have h01 : fderiv ℝ (tr.ψ s) z (0, 1) = -tr.v s z 0 := by
    have hp : HasDerivAt (fun y : ℝ => ((z.1, y) : Plane)) (0, 1) z.2 :=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id' z.2)
    have hc : HasDerivAt (fun y : ℝ => tr.ψ s (z.1, y)) (fderiv ℝ (tr.ψ s) z (0, 1)) z.2 :=
      hd.hasFDerivAt.comp_hasDerivAt z.2 hp
    rw [tr.isTrain.stream s hs z, toVec_zero]
    show fderiv ℝ (tr.ψ s) z (0, 1) = -(-deriv (fun y : ℝ => tr.ψ s (z.1, y)) z.2)
    rw [neg_neg]
    exact hc.deriv.symm
  have hv_split : ((dq, dη) : Plane) = dq • ((1 : ℝ), (0 : ℝ)) + dη • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv_split, map_add, map_smul, map_smul, h10, h01]
  simp [streamDualCLM]
  ring

private theorem contDiff_v_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.v s) := by
  have hg_sq : ContDiff ℝ ∞ (fun p : ℝ × Plane => (p.1 ^ 2, p.2)) := by fun_prop
  have hVsq : ContDiff ℝ ∞ (fun p : ℝ × Plane => tr.v (p.1 ^ 2) p.2) :=
    tr.isTrain.smooth_v.comp_contDiff hg_sq (fun p => ⟨sq_nonneg p.1, trivial⟩)
  have heq : tr.v s = (fun p : ℝ × Plane => tr.v (p.1 ^ 2) p.2) ∘ (fun z : Plane => (√s, z)) := by
    funext z
    simp [Real.sq_sqrt hs]
  rw [heq]
  exact hVsq.comp (by fun_prop)

theorem contDiff_psi_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.ψ s) :=
  contDiff_infty_iff_fderiv.2 ⟨tr.isTrain.stream_differentiable s hs, by
    rw [fderiv_psi_eq_streamDual tr hs]
    exact streamDualCLM.contDiff.comp (contDiff_v_slice tr hs)⟩

private theorem tendsto_iteratedFDeriv_psi_zero {ν c : ℝ} (tr : B0140.TrainSol ν c) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hbd : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ z : Plane, (1 + |z.2|) * |tr.ψ s z| ≤ C₀)
    (k : ℕ) (w : Plane) :
    Tendsto (fun s : ℝ => iteratedFDeriv ℝ k (tr.ψ s) w) (𝓝[>] 0)
      (𝓝 (iteratedFDeriv ℝ k (tr.ψ 0) w)) := by
  cases k with
  | zero =>
    have heq : ∀ s : ℝ, iteratedFDeriv ℝ 0 (tr.ψ s) w =
        (continuousMultilinearCurryFin0 ℝ Plane ℝ).symm (tr.ψ s w) := fun _ => rfl
    simp_rw [heq]
    exact ((continuousMultilinearCurryFin0 ℝ Plane ℝ).symm.continuous.tendsto _).comp
      (tendsto_psi_zero tr hC₀ hbd w)
  | succ m =>
    let Vsq : ℝ × Plane → Vec := fun p => tr.v (p.1 ^ 2) p.2
    have hg_sq : ContDiff ℝ ∞ (fun p : ℝ × Plane => (p.1 ^ 2, p.2)) := by fun_prop
    have hVsq : ContDiff ℝ ∞ Vsq :=
      tr.isTrain.smooth_v.comp_contDiff hg_sq (fun p => ⟨sq_nonneg p.1, trivial⟩)
    let inrP : Plane →L[ℝ] ℝ × Plane := ContinuousLinearMap.inr ℝ ℝ Plane
    have hform : ∀ s : ℝ, 0 ≤ s → iteratedFDeriv ℝ (m + 1) (tr.ψ s) w =
        (continuousMultilinearCurryRightEquiv' ℝ m Plane ℝ).symm
          (streamDualCLM.compContinuousMultilinearMap
            ((iteratedFDeriv ℝ m Vsq (√s, w)).compContinuousLinearMap fun _ => inrP)) := by
      intro s hs
      have hv_eq : tr.v s = (fun p : ℝ × Plane => Vsq (p + (√s, (0 : Plane)))) ∘ inrP := by
        funext z
        simp [Vsq, inrP, Real.sq_sqrt hs]
      have htrans_cd : ContDiff ℝ ∞ (fun p : ℝ × Plane => Vsq (p + (√s, (0 : Plane)))) :=
        hVsq.comp (contDiff_id.add contDiff_const)
      have hv_jet : iteratedFDeriv ℝ m (tr.v s) w =
          (iteratedFDeriv ℝ m Vsq (√s, w)).compContinuousLinearMap (fun _ => inrP) := by
        rw [hv_eq, inrP.iteratedFDeriv_comp_right htrans_cd w (by exact_mod_cast le_top),
          iteratedFDeriv_comp_add_right]
        simp [inrP]
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, fderiv_psi_eq_streamDual tr hs,
        streamDualCLM.iteratedFDeriv_comp_left (contDiff_v_slice tr hs).contDiffAt
          (by exact_mod_cast le_top),
        hv_jet]
    have hcont_V : Continuous (fun s : ℝ =>
        (continuousMultilinearCurryRightEquiv' ℝ m Plane ℝ).symm
          (streamDualCLM.compContinuousMultilinearMap
            ((iteratedFDeriv ℝ m Vsq (√s, w)).compContinuousLinearMap fun _ => inrP))) := by
      have hc1 : Continuous (fun s : ℝ => iteratedFDeriv ℝ m Vsq (√s, w)) :=
        (hVsq.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
          (Real.continuous_sqrt.prodMk continuous_const)
      have hc2 : Continuous (fun s : ℝ =>
          (iteratedFDeriv ℝ m Vsq (√s, w)).compContinuousLinearMap fun _ => inrP) :=
        (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin m => inrP)).continuous.comp hc1
      have hc3 : Continuous (fun s : ℝ =>
          streamDualCLM.compContinuousMultilinearMap
            ((iteratedFDeriv ℝ m Vsq (√s, w)).compContinuousLinearMap fun _ => inrP)) :=
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
          (fun _ : Fin m => Plane) Vec (Plane →L[ℝ] ℝ) streamDualCLM).continuous.comp hc2
      exact (continuousMultilinearCurryRightEquiv' ℝ m Plane ℝ).symm.continuous.comp hc3
    have hlim0 := (hcont_V.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [← hform 0 le_rfl] at hlim0
    refine hlim0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact (hform s hs.le).symm

private theorem norm_inr_plane_le : ‖ContinuousLinearMap.inr ℝ ℝ Plane‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  simp [Prod.norm_def]

/-- Weighted `(q, η)`-jet bounds for `tr.ψ 0` and for the `O(s)` increment `tr.ψ s - tr.ψ 0` on
`0 < s ≤ 1`, deduced from `TrainStreamWtdBdd` by `s → 0⁺` continuity and the mean value theorem. -/
theorem psi_zero_and_sub_wtd_jet {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ))
    {W k : ℕ} {C0 Ck Ck1 : ℝ} (hC0 : 0 ≤ C0) (_hCk : 0 ≤ Ck) (_hCk1 : 0 ≤ Ck1)
    (hb0 : ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) * ‖iteratedFDeriv ℝ 0 (fun y : ℝ × Plane => tr.ψ y.1 y.2) x‖ ≤ C0)
    (hbk : ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ W * ‖iteratedFDeriv ℝ k (fun y : ℝ × Plane => tr.ψ y.1 y.2) x‖ ≤ Ck)
    (hbk1 : ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ W * ‖iteratedFDeriv ℝ (k + 1) (fun y : ℝ × Plane => tr.ψ y.1 y.2) x‖ ≤ Ck1) :
    (∀ w : Plane, (1 + |w.2|) ^ W * ‖iteratedFDeriv ℝ k (tr.ψ 0) w‖ ≤ Ck) ∧
    (∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ w : Plane,
      (1 + |w.2|) ^ W * ‖iteratedFDeriv ℝ k (fun w' => tr.ψ s w' - tr.ψ 0 w') w‖ ≤ Ck1 * s) := by
  let Ψ : ℝ × Plane → ℝ := fun y => tr.ψ y.1 y.2
  let inrP : Plane →L[ℝ] ℝ × Plane := ContinuousLinearMap.inr ℝ ℝ Plane
  let L_inr := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin k => inrP)
  have hL_norm : ‖L_inr‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun M => ?_
    have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le M (fun _ : Fin k => inrP)
    have hprod : ∏ _i : Fin k, ‖inrP‖ ≤ 1 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_one₀ (norm_nonneg _) norm_inr_plane_le
    calc ‖L_inr M‖ ≤ ‖M‖ * ∏ _i : Fin k, ‖inrP‖ := h1
      _ ≤ ‖M‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = 1 * ‖M‖ := by ring
  have hb0' : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ z : Plane, (1 + |z.2|) * |tr.ψ s z| ≤ C0 := by
    intro s hs0 hs1 z
    have h := hb0 (s, z) hs0 hs1
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have htend : ∀ w : Plane,
      Tendsto (fun r : ℝ => iteratedFDeriv ℝ k (tr.ψ r) w) (𝓝[>] 0)
        (𝓝 (iteratedFDeriv ℝ k (tr.ψ 0) w)) :=
    tendsto_iteratedFDeriv_psi_zero tr hC0 hb0' k
  have hslice_eq : ∀ (r : ℝ), 0 < r → ∀ w : Plane,
      iteratedFDeriv ℝ k (tr.ψ r) w = L_inr (iteratedFDeriv ℝ k Ψ (r, w)) := by
    intro r hr w
    exact PsiJetInteriorAux.slice_plane_iteratedFDeriv Ψ hΨ k hr w
  have hslice_bd : ∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ w : Plane,
      (1 + |w.2|) ^ W * ‖iteratedFDeriv ℝ k (tr.ψ r) w‖ ≤ Ck := by
    intro r hr0 hr1 w
    rw [hslice_eq r hr0 w]
    have hn : ‖L_inr (iteratedFDeriv ℝ k Ψ (r, w))‖ ≤ ‖iteratedFDeriv ℝ k Ψ (r, w)‖ := by
      calc ‖L_inr (iteratedFDeriv ℝ k Ψ (r, w))‖
          ≤ ‖L_inr‖ * ‖iteratedFDeriv ℝ k Ψ (r, w)‖ := L_inr.le_opNorm _
        _ ≤ 1 * ‖iteratedFDeriv ℝ k Ψ (r, w)‖ :=
          mul_le_mul_of_nonneg_right hL_norm (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ k Ψ (r, w)‖ := one_mul _
    exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans (hbk (r, w) hr0 hr1)
  have hzero_bd : ∀ w : Plane, (1 + |w.2|) ^ W * ‖iteratedFDeriv ℝ k (tr.ψ 0) w‖ ≤ Ck := by
    intro w
    have hlim : Tendsto (fun r : ℝ => (1 + |w.2|) ^ W * ‖iteratedFDeriv ℝ k (tr.ψ r) w‖)
        (𝓝[>] 0) (𝓝 ((1 + |w.2|) ^ W * ‖iteratedFDeriv ℝ k (tr.ψ 0) w‖)) :=
      ((htend w).norm).const_mul _
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
    exact hslice_bd r hr.1 hr.2.le w
  refine ⟨hzero_bd, fun s hs0 hs1 w => ?_⟩
  -- Differentiability and derivative bound in `r ∈ Ioc 0 1`
  let f : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin k => Plane) ℝ :=
    fun r => iteratedFDeriv ℝ k (tr.ψ r) w
  have hf_deriv : ∀ r : ℝ, 0 < r → r ≤ 1 → DifferentiableAt ℝ f r ∧
      ‖deriv f r‖ ≤ Ck1 * ((1 + |w.2|) ^ W)⁻¹ := by
    intro r hr0 hr1
    have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
    have hrw_mem : (r, w) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hr0, trivial⟩
    have hF_diff : DifferentiableAt ℝ (iteratedFDeriv ℝ k Ψ) (r, w) :=
      ((hΨ.contDiffAt (hopen.mem_nhds hrw_mem)).iteratedFDeriv_right (m := 1) (i := k)
        (by exact_mod_cast le_top)).differentiableAt one_ne_zero
    have hpath : HasDerivAt (fun x : ℝ => ((x, w) : ℝ × Plane)) (1, (0 : Plane)) r :=
      (hasDerivAt_id' r).prodMk (hasDerivAt_const r w)
    have hg_hd : HasDerivAt (fun x : ℝ => L_inr (iteratedFDeriv ℝ k Ψ (x, w)))
        (L_inr (fderiv ℝ (iteratedFDeriv ℝ k Ψ) (r, w) (1, (0 : Plane)))) r :=
      L_inr.hasFDerivAt.comp_hasDerivAt r (hF_diff.hasFDerivAt.comp_hasDerivAt r hpath)
    have hev : f =ᶠ[𝓝 r] fun x : ℝ => L_inr (iteratedFDeriv ℝ k Ψ (x, w)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hr0] with x hx
      exact hslice_eq x hx w
    have hf_hd : HasDerivAt f
        (L_inr (fderiv ℝ (iteratedFDeriv ℝ k Ψ) (r, w) (1, (0 : Plane)))) r :=
      hg_hd.congr_of_eventuallyEq hev
    refine ⟨hf_hd.differentiableAt, ?_⟩
    rw [hf_hd.deriv]
    have h10_norm : ‖((1 : ℝ), (0 : Plane))‖ = 1 := by simp [Prod.norm_def]
    have hnorm_fd : ‖fderiv ℝ (iteratedFDeriv ℝ k Ψ) (r, w)‖ =
        ‖iteratedFDeriv ℝ (k + 1) Ψ (r, w)‖ := norm_fderiv_iteratedFDeriv
    have hstep1 : ‖L_inr (fderiv ℝ (iteratedFDeriv ℝ k Ψ) (r, w) (1, (0 : Plane)))‖ ≤
        ‖iteratedFDeriv ℝ (k + 1) Ψ (r, w)‖ := by
      calc ‖L_inr (fderiv ℝ (iteratedFDeriv ℝ k Ψ) (r, w) (1, (0 : Plane)))‖
          ≤ ‖L_inr‖ * ‖fderiv ℝ (iteratedFDeriv ℝ k Ψ) (r, w) (1, (0 : Plane))‖ :=
            L_inr.le_opNorm _
        _ ≤ 1 * (‖fderiv ℝ (iteratedFDeriv ℝ k Ψ) (r, w)‖ * ‖((1 : ℝ), (0 : Plane))‖) :=
            mul_le_mul hL_norm ((fderiv ℝ (iteratedFDeriv ℝ k Ψ) (r, w)).le_opNorm _)
              (norm_nonneg _) zero_le_one
        _ = ‖iteratedFDeriv ℝ (k + 1) Ψ (r, w)‖ := by rw [one_mul, h10_norm, mul_one, hnorm_fd]
    have hw_pos : 0 < (1 + |w.2|) ^ W := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀' hw_pos]
    exact (mul_le_mul_of_nonneg_left hstep1 hw_pos.le).trans (hbk1 (r, w) hr0 hr1)
  -- Apply MVT on `[r, s]` for `r ∈ Ioo 0 s`, then send `r → 0⁺`
  set M : ℝ := Ck1 * ((1 + |w.2|) ^ W)⁻¹
  have hMvt : ∀ r ∈ Ioo 0 s, ‖f s - f r‖ ≤ M * (s - r) := by
    intro r hr
    have hsub : ∀ x ∈ Icc r s, 0 < x ∧ x ≤ 1 :=
      fun x hx => ⟨lt_of_lt_of_le hr.1 hx.1, hx.2.trans hs1⟩
    have hm := (convex_Icc r s).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hf_deriv x (hsub x hx).1 (hsub x hx).2).1)
      (fun x hx => (hf_deriv x (hsub x hx).1 (hsub x hx).2).2)
      (left_mem_Icc.2 hr.2.le) (right_mem_Icc.2 hr.2.le)
    rwa [Real.norm_eq_abs, abs_of_pos (sub_pos.2 hr.2)] at hm
  have hlimL : Tendsto (fun r : ℝ => ‖f s - f r‖) (𝓝[>] 0) (𝓝 ‖f s - f 0‖) :=
    ((htend w).const_sub (f s)).norm
  have hlimR : Tendsto (fun r : ℝ => M * (s - r)) (𝓝[>] 0) (𝓝 (M * s)) := by
    have hc : Continuous (fun r : ℝ => M * (s - r)) := by fun_prop
    have h0 : M * (s - 0) = M * s := by ring
    rw [← h0]
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle0 : ‖f s - f 0‖ ≤ M * s := by
    refine le_of_tendsto_of_tendsto hlimL hlimR ?_
    filter_upwards [Ioo_mem_nhdsGT hs0] with r hr
    exact hMvt r hr
  have hsub_apply : iteratedFDeriv ℝ k (fun w' => tr.ψ s w' - tr.ψ 0 w') w = f s - f 0 :=
    iteratedFDeriv_sub_apply
      ((contDiff_psi_slice tr hs0.le).contDiffAt.of_le (by exact_mod_cast le_top))
      ((contDiff_psi_slice tr le_rfl).contDiffAt.of_le (by exact_mod_cast le_top))
  have hw_pos : 0 < (1 + |w.2|) ^ W := by positivity
  rw [hsub_apply]
  calc (1 + |w.2|) ^ W * ‖f s - f 0‖
      ≤ (1 + |w.2|) ^ W * (Ck1 * ((1 + |w.2|) ^ W)⁻¹ * s) :=
        mul_le_mul_of_nonneg_left hle0 hw_pos.le
    _ = Ck1 * ((1 + |w.2|) ^ W * ((1 + |w.2|) ^ W)⁻¹) * s := by ring
    _ = Ck1 * s := by rw [mul_inv_cancel₀ hw_pos.ne', mul_one]

/-! ## 2. Reparameterized `u = √s` far-field ring-lift decay (`0 < Axi.age p.R y ≤ 1`, `j ≤ 2`) -/

private def sqAgeMap (x : ℝ × Plane) : ℝ × Plane := (x.1 ^ 2, x.2)

private theorem contDiff_sqAgeMap : ContDiff ℝ ∞ sqAgeMap := by
  unfold sqAgeMap
  fun_prop

private theorem fderiv_sqAgeMap_apply (x dx : ℝ × Plane) :
    fderiv ℝ sqAgeMap x dx = (2 * x.1 * dx.1, dx.2) := by
  have h1 : HasFDerivAt (fun p : ℝ × Plane => p.1 ^ 2)
      ((2 * x.1) • ContinuousLinearMap.fst ℝ ℝ Plane) x := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using
      ((ContinuousLinearMap.fst ℝ ℝ Plane).hasFDerivAt (x := x)).pow 2
  have h2 : HasFDerivAt sqAgeMap
      (((2 * x.1) • ContinuousLinearMap.fst ℝ ℝ Plane).prod (ContinuousLinearMap.snd ℝ ℝ Plane)) x :=
    h1.prodMk ((ContinuousLinearMap.snd ℝ ℝ Plane).hasFDerivAt (x := x))
  rw [h2.fderiv]
  rfl

private theorem norm_fderiv_sqAgeMap_le {x : ℝ × Plane} (hx0 : 0 ≤ x.1) (hx1 : x.1 ≤ 1) :
    ‖fderiv ℝ sqAgeMap x‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun dx => ?_
  rw [fderiv_sqAgeMap_apply, Prod.norm_def]
  have hdx1 : |dx.1| ≤ ‖dx‖ := le_max_left _ _
  have hdx2 : ‖dx.2‖ ≤ ‖dx‖ := le_max_right _ _
  have h1 : |2 * x.1 * dx.1| ≤ 2 * ‖dx‖ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hx0]
    calc 2 * x.1 * |dx.1| ≤ 2 * 1 * ‖dx‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx1 (by norm_num)) hdx1 (abs_nonneg _) (by norm_num)
      _ = 2 * ‖dx‖ := by ring
  exact max_le h1 (by linarith [norm_nonneg dx])

private theorem norm_iteratedFDeriv_two_sqAgeMap_le (x : ℝ × Plane) :
    ‖iteratedFDeriv ℝ 2 sqAgeMap x‖ ≤ 2 := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  -- Direct `HasFDerivAt` of `y ↦ fderiv ℝ sqAgeMap y`
  let M : (ℝ × Plane) →L[ℝ] (ℝ × Plane) →L[ℝ] (ℝ × Plane) :=
    ((ContinuousLinearMap.fst ℝ ℝ Plane).smulRight
      ((ContinuousLinearMap.fst ℝ ℝ Plane).prod (0 : ℝ × Plane →L[ℝ] Plane)))
  have hfd_eq : fderiv ℝ sqAgeMap = fun y : ℝ × Plane =>
      (2 : ℝ) • M y + (0 : ℝ × Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ Plane) := by
    funext y
    apply ContinuousLinearMap.ext
    intro dx
    rw [fderiv_sqAgeMap_apply]
    simp [M]
    ring
  have hhd : HasFDerivAt (fderiv ℝ sqAgeMap) ((2 : ℝ) • M) x := by
    rw [hfd_eq]
    exact (((2 : ℝ) • M).hasFDerivAt (x := x)).add_const
      ((0 : ℝ × Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ Plane))
  rw [hhd.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun dy => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg dy)) fun dx => ?_
  simp only [smul_apply, M, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', zero_apply,
    Prod.smul_mk, smul_eq_mul, smul_zero, Prod.norm_def, norm_zero]
  refine max_le ?_ (by positivity)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hdy : |dy.1| ≤ ‖dy‖ := le_max_left _ _
  have hdx : |dx.1| ≤ ‖dx‖ := le_max_left _ _
  calc 2 * (|dy.1| * |dx.1|) ≤ 2 * (‖dy‖ * ‖dx‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hdy hdx (abs_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 2 * ‖dy‖ * ‖dx‖ := by ring

private theorem sqrtFrameJet_sqrt_age (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ y : Space, y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ j (fun z => √(Axi.age R z)) y‖ ≤ C * √(Axi.age R y) ^ (j + 1) ∧
      ‖iteratedFDeriv ℝ j Axi.frameL y‖ ≤ C * √(Axi.age R y) ^ j := by
  obtain ⟨C1, hC1, h1⟩ := SqrtFrameJetsAux.varrho_inv_jet j
  obtain ⟨C2, hC2, h2⟩ := SqrtFrameJetsAux.frameL_jet j
  refine ⟨C1 + C2, by positivity, fun R hR y hy => ?_⟩
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  set t := (Axi.ϱ y)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 hϱ
  have hR0 : 0 < R := by linarith
  set u := R * t with hu
  have hsq : √(Axi.age R y) = u := by
    rw [Axi.sqrt_age hR0 hy, hu, ht]; ring
  have hu0 : 0 < u := by positivity
  have htu : t ≤ u := by nlinarith
  have hfun : (fun z : Space => √(Axi.age R z)) =ᶠ[𝓝 y] (R • fun z : Space => (Axi.ϱ z)⁻¹) := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds (show y ∈ Axi.axisᶜ from hy)] with z hz
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Axi.sqrt_age hR0 hz, div_eq_mul_inv]
  have hcd : ContDiffAt ℝ j (fun z : Space => (Axi.ϱ z)⁻¹) y :=
    ((Axi.contDiffOn_ϱ.inv fun _ hy => Axi.ϱ_ne_zero hy).contDiffAt
      (Axi.isOpen_compl_axis.mem_nhds hy)).of_le (by exact_mod_cast le_top)
  have hD : iteratedFDeriv ℝ j (fun z : Space => √(Axi.age R z)) y =
      R • iteratedFDeriv ℝ j (fun z : Space => (Axi.ϱ z)⁻¹) y := by
    rw [hfun.iteratedFDeriv ℝ j |>.self_of_nhds, iteratedFDeriv_const_smul_apply hcd]
  rw [hsq]
  have hA : ‖iteratedFDeriv ℝ j (fun z : Space => √(Axi.age R z)) y‖ ≤ C1 * u ^ (j + 1) := by
    rw [hD, norm_smul, Real.norm_of_nonneg hR0.le]
    calc R * ‖iteratedFDeriv ℝ j (fun z : Space => (Axi.ϱ z)⁻¹) y‖
        ≤ R * (C1 * t ^ (j + 1)) := mul_le_mul_of_nonneg_left (h1 y hy) hR0.le
      _ = C1 * (u * t ^ j) := by rw [hu]; ring
      _ ≤ C1 * (u * u ^ j) := by
          apply mul_le_mul_of_nonneg_left _ hC1.le
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le htu j) hu0.le
      _ = C1 * u ^ (j + 1) := by ring
  have hB : ‖iteratedFDeriv ℝ j Axi.frameL y‖ ≤ C2 * u ^ j := by
    calc _ ≤ C2 * t ^ j := h2 y hy
      _ ≤ C2 * u ^ j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le htu j) hC2.le
  constructor
  · exact hA.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hu0.le _))
  · exact hB.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hu0.le _))

private def uChart (R τ : ℝ) (y : Space) : ℝ × Plane :=
  (√(Axi.age R y), (Axi.phase R τ y, Axi.trans R y))

private theorem contDiffOn_uChart {R : ℝ} (hR0 : R ≠ 0) (τ : ℝ) :
    ContDiffOn ℝ ∞ (uChart R τ) Axi.axisᶜ :=
  (ChartJetsAux.contDiffOn_sqrt_age hR0).prodMk
    ((ChartJetsAux.contDiffOn_phase hR0 τ).prodMk (ChartJetsAux.contDiffOn_trans R))

private theorem uChart_jet_le (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (R τ : ℝ), 1 ≤ R → ∀ y : Space, y ∉ Axi.axis → Axi.age R y ≤ 1 →
      ‖iteratedFDeriv ℝ j (uChart R τ) y‖ ≤
        C * (1 + |Axi.trans R y|) * √(Axi.age R y) ^ j := by
  obtain ⟨CS, hCS, hSF⟩ := sqrtFrameJet_sqrt_age j
  obtain ⟨CP, hCP, hP'⟩ := phaseJets j hj
  obtain ⟨CT, hCT, hT'⟩ := transJets j hj
  refine ⟨1 + CS + CP + CT, by linarith, fun R τ hR y hy hs1 => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hU : Axi.axisᶜ ∈ 𝓝 y := Axi.isOpen_compl_axis.mem_nhds hy
  have cA : ContDiffAt ℝ ∞ (fun z => √(Axi.age R z)) y :=
    (ChartJetsAux.contDiffOn_sqrt_age hR0.ne').contDiffAt hU
  have cP : ContDiffAt ℝ ∞ (Axi.phase R τ) y :=
    (ChartJetsAux.contDiffOn_phase hR0.ne' τ).contDiffAt hU
  have cT : ContDiffAt ℝ ∞ (Axi.trans R) y :=
    (ChartJetsAux.contDiffOn_trans R).contDiffAt hU
  have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hD : iteratedFDeriv ℝ j (uChart R τ) y =
      (iteratedFDeriv ℝ j (fun z => √(Axi.age R z)) y).prod
        ((iteratedFDeriv ℝ j (Axi.phase R τ) y).prod (iteratedFDeriv ℝ j (Axi.trans R) y)) := by
    rw [show uChart R τ = fun z => (√(Axi.age R z), (Axi.phase R τ z, Axi.trans R z)) from rfl,
      iteratedFDeriv_prodMk cA (cP.prodMk cT) hj', iteratedFDeriv_prodMk cP cT hj']
  rw [hD, ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  set t : ℝ := (Axi.ϱ y)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 hϱ
  set u : ℝ := √(Axi.age R y) with hu
  have hu_eq : u = R * t := by rw [hu, Axi.sqrt_age hR0 hy, ht, div_eq_mul_inv]
  have hu0 : 0 < u := by rw [hu_eq]; positivity
  have hu1 : u ≤ 1 := by
    rw [hu]
    exact Real.sqrt_le_one.2 hs1
  have htu : t ≤ u := by rw [hu_eq]; nlinarith
  have tpow : ∀ n : ℕ, t ^ n ≤ u ^ n := fun n => pow_le_pow_left₀ ht0.le htu n
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hη0 : 0 ≤ |Axi.trans R y| := abs_nonneg _
  have hη1 : (1 : ℝ) ≤ 1 + |Axi.trans R y| := by linarith
  have hum1 : 0 ≤ u ^ (m + 1) := pow_nonneg hu0.le (m + 1)
  set Csum : ℝ := 1 + CS + CP + CT
  have hCsum0 : 0 ≤ Csum := by positivity
  refine max_le ?_ (max_le ?_ ?_)
  · have b1 := (hSF R hR y hy).1
    rw [← hu] at b1
    have hu_pow : u ^ (m + 1 + 1) ≤ u ^ (m + 1) := by
      rw [pow_succ]
      exact mul_le_of_le_one_right hum1 hu1
    calc ‖iteratedFDeriv ℝ (m + 1) (fun z => √(Axi.age R z)) y‖
        ≤ CS * u ^ (m + 1 + 1) := b1
      _ ≤ CS * u ^ (m + 1) := mul_le_mul_of_nonneg_left hu_pow hCS.le
      _ ≤ Csum * u ^ (m + 1) := mul_le_mul_of_nonneg_right (by linarith) hum1
      _ ≤ Csum * (1 + |Axi.trans R y|) * u ^ (m + 1) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCsum0 hη1) hum1
  · have b2 := hP' R τ y hR0 hy
    rw [← ht] at b2
    have e : CP * R * t ^ (m + 1) = CP * (u * t ^ m) := by rw [hu_eq]; ring
    rw [e] at b2
    have hut : u * t ^ m ≤ u ^ (m + 1) := by
      calc u * t ^ m ≤ u * u ^ m := mul_le_mul_of_nonneg_left (tpow m) hu0.le
        _ = u ^ (m + 1) := by ring
    calc ‖iteratedFDeriv ℝ (m + 1) (Axi.phase R τ) y‖
        ≤ CP * u ^ (m + 1) := b2.trans (mul_le_mul_of_nonneg_left hut hCP.le)
      _ ≤ Csum * u ^ (m + 1) := mul_le_mul_of_nonneg_right (by linarith) hum1
      _ ≤ Csum * (1 + |Axi.trans R y|) * u ^ (m + 1) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCsum0 hη1) hum1
  · have b3 := hT' R y hR0 hy
    rw [← ht] at b3
    have e : CT * (|Axi.trans R y| + R) * t ^ (m + 1) =
        CT * (|Axi.trans R y| * t ^ (m + 1) + u * t ^ m) := by rw [hu_eq]; ring
    rw [e] at b3
    have h1 : |Axi.trans R y| * t ^ (m + 1) ≤ |Axi.trans R y| * u ^ (m + 1) :=
      mul_le_mul_of_nonneg_left (tpow (m + 1)) hη0
    have h2 : u * t ^ m ≤ u ^ (m + 1) := by
      calc u * t ^ m ≤ u * u ^ m := mul_le_mul_of_nonneg_left (tpow m) hu0.le
        _ = u ^ (m + 1) := by ring
    calc ‖iteratedFDeriv ℝ (m + 1) (Axi.trans R) y‖
        ≤ CT * (1 + |Axi.trans R y|) * u ^ (m + 1) := by
          have e2 : CT * (1 + |Axi.trans R y|) * u ^ (m + 1) =
              CT * (|Axi.trans R y| * u ^ (m + 1) + u ^ (m + 1)) := by ring
          rw [e2]
          exact b3.trans (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCT.le)
      _ ≤ Csum * (1 + |Axi.trans R y|) * u ^ (m + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hum1
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem datumProfile_eq_ringStreamProfile_snd {R : ℝ} {ψ : Plane → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (m : ℝ × Plane) :
    UnforcedLeray.Cons.C03.Concrete.datumProfile R⁻¹ ψ m.2 =
      Axi.ringStreamProfile R (fun n : ℝ × Plane => ψ n.2) m := by
  have hd : DifferentiableAt ℝ ψ m.2 := hψ.differentiable (by simp) m.2
  have hcut := Axi.ringStreamProfile_cutoff R (χ := fun _ : ℝ => (1 : ℝ)) (ψ := ψ) (m := m)
    (differentiableAt_const _) hd
  simp only [one_mul, deriv_const', mul_zero, sub_zero] at hcut
  exact hcut.symm

private def trainDeltaStream (p : UnforcedLeray.Cons.C03.Concrete.Params) (x : ℝ × Plane) : ℝ :=
  p.train.ψ x.1 x.2 - p.train.ψ 0 x.2

private def trainDeltaMerid (p : UnforcedLeray.Cons.C03.Concrete.Params) : ℝ × Plane → Axi.Merid :=
  Axi.ringStreamProfile p.R (trainDeltaStream p)

private def trainDeltaBu (p : UnforcedLeray.Cons.C03.Concrete.Params) : ℝ × Plane → Axi.Merid :=
  trainDeltaMerid p ∘ sqAgeMap

private theorem trainDeltaMerid_slice_eq (p : UnforcedLeray.Cons.C03.Concrete.Params)
    (hΔΨ_cd : ContDiffOn ℝ ∞ (trainDeltaStream p) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs0 : 0 < s) (w : Plane) :
    trainDeltaMerid p (s, w) =
      (-(fderiv ℝ (fun w' => trainDeltaStream p (s, w')) w (0, 1))) • Axi.m0 +
        (fderiv ℝ (fun w' => trainDeltaStream p (s, w')) w (1, 0) +
          p.R⁻¹ * (trainDeltaStream p (s, w) - 2 * s * Axi.dS (trainDeltaStream p) (s, w) -
            w.2 * fderiv ℝ (fun w' => trainDeltaStream p (s, w')) w (0, 1))) • Axi.m1 := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hsw_mem : (s, w) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hs0, trivial⟩
  have hd : DifferentiableAt ℝ (trainDeltaStream p) (s, w) :=
    (hΔΨ_cd.contDiffAt (hopen.mem_nhds hsw_mem)).differentiableAt (by simp)
  have hcomp : HasFDerivAt (fun w' : Plane => trainDeltaStream p (s, w'))
      ((fderiv ℝ (trainDeltaStream p) (s, w)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) w :=
    hd.hasFDerivAt.comp w (hasFDerivAt_prodMk_right s w)
  have h10 : fderiv ℝ (fun w' => trainDeltaStream p (s, w')) w (1, 0) =
      Axi.dQ (trainDeltaStream p) (s, w) := by
    rw [hcomp.fderiv]; rfl
  have h01 : fderiv ℝ (fun w' => trainDeltaStream p (s, w')) w (0, 1) =
      Axi.dEta (trainDeltaStream p) (s, w) := by
    rw [hcomp.fderiv]; rfl
  rw [h10, h01]
  rfl

private theorem trainDeltaMerid_jet_bounds {dm dp : ℝ}
    {p : UnforcedLeray.Cons.C03.Concrete.Params} {d : ℝ} (hreg : BgRegime p d dm dp)
    {CS : ℕ → ℝ} (hCS0 : ∀ i : ℕ, 0 ≤ CS i)
    (hCS : ∀ i : ℕ, ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i (fun y : ℝ × Plane => p.train.ψ y.1 y.2) x‖ ≤ CS i)
    (hψ0_jet : ∀ i : ℕ, ∀ w : Plane, (1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ i (p.train.ψ 0) w‖ ≤ CS i) :
    ContDiffOn ℝ ∞ (trainDeltaStream p) (Ioi 0 ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (trainDeltaMerid p) (Ioi 0 ×ˢ univ) ∧
    (∀ i : ℕ, ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖ ≤ 2 * CS i) ∧
    ∃ B_mer : ℝ, 0 ≤ B_mer ∧ ∀ l ≤ 2, ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 5 * ‖iteratedFDeriv ℝ l (trainDeltaMerid p) x‖ ≤ B_mer := by
  let Ψ : ℝ × Plane → ℝ := fun x => p.train.ψ x.1 x.2
  have hΨ : ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ univ) := hreg.train_stream_smooth
  have hR1 : 1 ≤ p.R := RawAndInletL4.one_le_R_of hreg
  let Ψ₀_ext : ℝ × Plane → ℝ := fun x => p.train.ψ 0 x.2
  have hψ0_cd : ContDiff ℝ ∞ (p.train.ψ 0) := contDiff_psi_slice p.train le_rfl
  have hΨ₀_cd : ContDiff ℝ ∞ Ψ₀_ext := hψ0_cd.comp contDiff_snd
  have hΔΨ_eq : trainDeltaStream p = fun x => Ψ x - Ψ₀_ext x := rfl
  have hΔΨ_cd : ContDiffOn ℝ ∞ (trainDeltaStream p) (Ioi 0 ×ˢ univ) :=
    hΨ.sub hΨ₀_cd.contDiffOn
  have hbΔ_cd : ContDiffOn ℝ ∞ (trainDeltaMerid p) (Ioi 0 ×ˢ univ) :=
    (PartIIIb.Concrete.ringProfileMeridJet p.R (trainDeltaStream p) hΔΨ_cd).1
  have hΔΨ_jet : ∀ i : ℕ, ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖ ≤ 2 * CS i := by
    intro i x hx0 hx1
    have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
    have hx_mem : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hx0, trivial⟩
    have hc1 : ContDiffAt ℝ i Ψ x :=
      (hΨ.contDiffAt (hopen.mem_nhds hx_mem)).of_le (by exact_mod_cast le_top)
    have hc2 : ContDiffAt ℝ i Ψ₀_ext x := hΨ₀_cd.contDiffAt.of_le (by exact_mod_cast le_top)
    have hsub : iteratedFDeriv ℝ i (trainDeltaStream p) x =
        iteratedFDeriv ℝ i Ψ x - iteratedFDeriv ℝ i Ψ₀_ext x := by
      rw [hΔΨ_eq]; exact iteratedFDeriv_sub_apply hc1 hc2
    have hΨ₀_bd : ‖iteratedFDeriv ℝ i Ψ₀_ext x‖ ≤ ‖iteratedFDeriv ℝ i (p.train.ψ 0) x.2‖ := by
      have heq : Ψ₀_ext = (p.train.ψ 0) ∘ ContinuousLinearMap.snd ℝ ℝ Plane := rfl
      rw [heq, (ContinuousLinearMap.snd ℝ ℝ Plane).iteratedFDeriv_comp_right hψ0_cd x
        (by exact_mod_cast le_top)]
      have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ i (p.train.ψ 0) x.2) (fun _ : Fin i => ContinuousLinearMap.snd ℝ ℝ Plane)
      have hsnd_le : ‖ContinuousLinearMap.snd ℝ ℝ Plane‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
          simp [Prod.norm_def]
      have hprod : ∏ _j : Fin i, ‖ContinuousLinearMap.snd ℝ ℝ Plane‖ ≤ 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hsnd_le
      calc _ ≤ ‖iteratedFDeriv ℝ i (p.train.ψ 0) x.2‖ * 1 :=
            h1.trans (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
        _ = _ := mul_one _
    rw [hsub]
    have hw : 0 ≤ (1 + |x.2.2|) ^ 6 := by positivity
    calc (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i Ψ x - iteratedFDeriv ℝ i Ψ₀_ext x‖
        ≤ (1 + |x.2.2|) ^ 6 * (‖iteratedFDeriv ℝ i Ψ x‖ + ‖iteratedFDeriv ℝ i (p.train.ψ 0) x.2‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl hΨ₀_bd)) hw
      _ = (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i Ψ x‖ +
            (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i (p.train.ψ 0) x.2‖ := by ring
      _ ≤ CS i + CS i := add_le_add (hCS i x hx0 hx1) (hψ0_jet i x.2)
      _ = 2 * CS i := by ring
  choose CP hCP0 hCP using fun l => PartIIa.ringProfileMeridJet_unif l
  obtain ⟨S_Δ, hS_Δ_def⟩ : ∃ x : ℝ, x = ∑ i ∈ Finset.range 4, 2 * CS i := ⟨_, rfl⟩
  have hS_Δ0 : 0 ≤ S_Δ := by
    rw [hS_Δ_def]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num) (hCS0 i)
  obtain ⟨B_mer, hB_mer_def⟩ : ∃ x : ℝ, x = (CP 0 + CP 1 + CP 2) * 2 * S_Δ := ⟨_, rfl⟩
  have hB_mer0 : 0 ≤ B_mer := by
    rw [hB_mer_def]
    have := hCP0 0; have := hCP0 1; have := hCP0 2
    positivity
  refine ⟨hΔΨ_cd, hbΔ_cd, hΔΨ_jet, B_mer, hB_mer0, fun l hl x hx0 hx1 => ?_⟩
  have h1_raw := (hCP l p.R (trainDeltaStream p) hR1 hΔΨ_cd).2 x hx0
  have h1 : ‖iteratedFDeriv ℝ l (trainDeltaMerid p) x‖ ≤
      CP l * (1 + x.1) * ((1 + |x.2.2|) *
        ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖) := by
    refine h1_raw.trans ?_
    have habs : 1 + |x.1| + |x.2.2| ≤ (1 + x.1) * (1 + |x.2.2|) := by
      rw [abs_of_pos hx0]
      have ha : 0 ≤ |x.2.2| := abs_nonneg x.2.2
      nlinarith only [hx0, ha]
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hCP_nn : 0 ≤ CP l := hCP0 l
    calc CP l * (1 + |x.1| + |x.2.2|) *
          ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖
        ≤ CP l * ((1 + x.1) * (1 + |x.2.2|)) *
            ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hCP_nn) hsum0
      _ = CP l * (1 + x.1) * ((1 + |x.2.2|) *
            ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖) := by ring
  have hCP_le : CP l ≤ CP 0 + CP 1 + CP 2 := by
    have h0 := hCP0 0; have h1' := hCP0 1; have h2 := hCP0 2
    interval_cases l <;> linarith only [h0, h1', h2]
  have hs_le : 1 + x.1 ≤ 2 := by linarith only [hx1]
  have hsum_le : (1 + |x.2.2|) ^ 6 *
      ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖ ≤ S_Δ := by
    rw [hS_Δ_def, Finset.mul_sum]
    calc ∑ i ∈ Finset.range (l + 2), (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖
        ≤ ∑ i ∈ Finset.range 4, (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (by omega)) (fun _ _ _ => by positivity)
      _ ≤ ∑ i ∈ Finset.range 4, 2 * CS i :=
          Finset.sum_le_sum fun i _ => hΔΨ_jet i x hx0 hx1
  have hw5 : 0 ≤ (1 + |x.2.2|) ^ 5 := by positivity
  rw [hB_mer_def]
  calc (1 + |x.2.2|) ^ 5 * ‖iteratedFDeriv ℝ l (trainDeltaMerid p) x‖
      ≤ (1 + |x.2.2|) ^ 5 * (CP l * (1 + x.1) * ((1 + |x.2.2|) *
          ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖)) :=
        mul_le_mul_of_nonneg_left h1 hw5
    _ = CP l * (1 + x.1) * ((1 + |x.2.2|) ^ 6 *
          ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖) := by ring
    _ ≤ (CP 0 + CP 1 + CP 2) * 2 * S_Δ := by
        have hcp_sum0 : 0 ≤ CP 0 + CP 1 + CP 2 := by
          have := hCP0 0; have := hCP0 1; have := hCP0 2; positivity
        exact mul_le_mul (mul_le_mul hCP_le hs_le (by positivity) hcp_sum0) hsum_le
          (by positivity) (by positivity)

private theorem bu_jet_zero {p : UnforcedLeray.Cons.C03.Concrete.Params}
    (hR1 : 1 ≤ p.R)
    (hΔΨ_cd : ContDiffOn ℝ ∞ (trainDeltaStream p) (Ioi 0 ×ˢ univ))
    {CS : ℕ → ℝ} (hCS0 : ∀ i : ℕ, 0 ≤ CS i)
    (hΔΨ_jet : ∀ i : ℕ, ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖ ≤ 2 * CS i)
    (hinc_sub : ∀ k : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ w : Plane,
      (1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ k (fun w' => p.train.ψ s w' - p.train.ψ 0 w') w‖ ≤
        CS (k + 1) * s) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ (u : ℝ) (w : Plane), 0 < u → u ≤ 1 →
      ‖trainDeltaBu p (u, w)‖ ≤ K0 * u ^ 2 * ((1 + |w.2|) ^ 5)⁻¹ := by
  have hR0 : 0 < p.R := lt_of_lt_of_le one_pos hR1
  have hRinv_le : p.R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hm0_norm : ‖Axi.m0‖ ≤ 1 := by
    have h : ‖Axi.m0‖ = 1 := by simp [Axi.m0]
    exact h.le
  have hm1_norm : ‖Axi.m1‖ ≤ 1 := by
    have h : ‖Axi.m1‖ = 1 := by simp [Axi.m1]
    exact h.le
  obtain ⟨K0, hK0_def⟩ : ∃ x : ℝ, x = CS 1 + 3 * CS 2 + 4 * CS 1 := ⟨_, rfl⟩
  have hK0_nn : 0 ≤ K0 := by
    rw [hK0_def]; have := hCS0 1; have := hCS0 2; positivity
  refine ⟨K0, hK0_nn, fun u w hu0 hu1 => ?_⟩
  set s : ℝ := u ^ 2 with hs_def
  have hs0 : 0 < s := pow_pos hu0 2
  have hs1 : s ≤ 1 := pow_le_one₀ hu0.le hu1
  let gs : Plane → ℝ := fun w' => p.train.ψ s w' - p.train.ψ 0 w'
  have hgs_eq : (fun w' => trainDeltaStream p (s, w')) = gs := rfl
  have hbu_val : trainDeltaBu p (u, w) = trainDeltaMerid p (s, w) := rfl
  rw [hbu_val, trainDeltaMerid_slice_eq p hΔΨ_cd hs0 w, hgs_eq]
  have hb_g0 : (1 + |w.2|) ^ 6 * |gs w| ≤ CS 1 * s := by
    have h := hinc_sub 0 s hs0 hs1 w
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hb_g1 : (1 + |w.2|) ^ 6 * ‖fderiv ℝ gs w‖ ≤ CS 2 * s := by
    have h := hinc_sub 1 s hs0 hs1 w
    rwa [norm_iteratedFDeriv_one] at h
  have hw1 : (1 : ℝ) ≤ 1 + |w.2| := le_add_of_nonneg_right (abs_nonneg w.2)
  have hdQ_bd : (1 + |w.2|) ^ 5 * |fderiv ℝ gs w (1, 0)| ≤ CS 2 * s := by
    have h1 : |fderiv ℝ gs w (1, 0)| ≤ ‖fderiv ℝ gs w‖ := by
      simpa [Real.norm_eq_abs, Prod.norm_def] using (fderiv ℝ gs w).le_opNorm (1, 0)
    calc (1 + |w.2|) ^ 5 * |fderiv ℝ gs w (1, 0)|
        ≤ (1 + |w.2|) ^ 5 * (1 + |w.2|) * ‖fderiv ℝ gs w‖ := by
          calc (1 + |w.2|) ^ 5 * |fderiv ℝ gs w (1, 0)|
              ≤ (1 + |w.2|) ^ 5 * ‖fderiv ℝ gs w‖ := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ ≤ (1 + |w.2|) ^ 5 * (1 + |w.2|) * ‖fderiv ℝ gs w‖ :=
                mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hw1) (norm_nonneg _)
      _ = (1 + |w.2|) ^ 6 * ‖fderiv ℝ gs w‖ := by rw [← pow_succ]
      _ ≤ CS 2 * s := hb_g1
  have hdEta_bd6 : (1 + |w.2|) ^ 6 * |fderiv ℝ gs w (0, 1)| ≤ CS 2 * s := by
    have h1 : |fderiv ℝ gs w (0, 1)| ≤ ‖fderiv ℝ gs w‖ := by
      simpa [Real.norm_eq_abs, Prod.norm_def] using (fderiv ℝ gs w).le_opNorm (0, 1)
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans hb_g1
  have hdEta_bd5 : (1 + |w.2|) ^ 5 * |fderiv ℝ gs w (0, 1)| ≤ CS 2 * s := by
    calc (1 + |w.2|) ^ 5 * |fderiv ℝ gs w (0, 1)|
        ≤ (1 + |w.2|) ^ 5 * (1 + |w.2|) * |fderiv ℝ gs w (0, 1)| :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hw1) (abs_nonneg _)
      _ = (1 + |w.2|) ^ 6 * |fderiv ℝ gs w (0, 1)| := by rw [← pow_succ]
      _ ≤ CS 2 * s := hdEta_bd6
  have hwdEta_bd5 : (1 + |w.2|) ^ 5 * |w.2 * fderiv ℝ gs w (0, 1)| ≤ CS 2 * s := by
    rw [abs_mul]
    have hw_le : |w.2| ≤ 1 + |w.2| := le_add_of_nonneg_left zero_le_one
    calc (1 + |w.2|) ^ 5 * (|w.2| * |fderiv ℝ gs w (0, 1)|)
        ≤ (1 + |w.2|) ^ 5 * ((1 + |w.2|) * |fderiv ℝ gs w (0, 1)|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hw_le (abs_nonneg _)) (by positivity)
      _ = (1 + |w.2|) ^ 6 * |fderiv ℝ gs w (0, 1)| := by ring
      _ ≤ CS 2 * s := hdEta_bd6
  have hg0_bd5 : (1 + |w.2|) ^ 5 * |gs w| ≤ CS 1 * s := by
    calc (1 + |w.2|) ^ 5 * |gs w|
        ≤ (1 + |w.2|) ^ 5 * (1 + |w.2|) * |gs w| :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hw1) (abs_nonneg _)
      _ = (1 + |w.2|) ^ 6 * |gs w| := by rw [← pow_succ]
      _ ≤ CS 1 * s := hb_g0
  have hdS_bd5 : (1 + |w.2|) ^ 5 * |2 * s * Axi.dS (trainDeltaStream p) (s, w)| ≤ 4 * CS 1 * s := by
    have hdS_le : |Axi.dS (trainDeltaStream p) (s, w)| ≤
        ‖iteratedFDeriv ℝ 1 (trainDeltaStream p) (s, w)‖ := by
      rw [norm_iteratedFDeriv_one]
      simpa [Axi.dS, Real.norm_eq_abs, Prod.norm_def] using
        (fderiv ℝ (trainDeltaStream p) (s, w)).le_opNorm (1, (0, 0))
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hs0]
    calc (1 + |w.2|) ^ 5 * (2 * s * |Axi.dS (trainDeltaStream p) (s, w)|)
        = 2 * s * ((1 + |w.2|) ^ 5 * |Axi.dS (trainDeltaStream p) (s, w)|) := by ring
      _ ≤ 2 * s * ((1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ 1 (trainDeltaStream p) (s, w)‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (1 + |w.2|) ^ 5 * |Axi.dS (trainDeltaStream p) (s, w)|
              ≤ (1 + |w.2|) ^ 5 * ‖iteratedFDeriv ℝ 1 (trainDeltaStream p) (s, w)‖ :=
                mul_le_mul_of_nonneg_left hdS_le (by positivity)
            _ ≤ (1 + |w.2|) ^ 5 * (1 + |w.2|) * ‖iteratedFDeriv ℝ 1 (trainDeltaStream p) (s, w)‖ :=
                mul_le_mul_of_nonneg_right
                  (le_mul_of_one_le_right (by positivity) hw1) (norm_nonneg _)
            _ = (1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ 1 (trainDeltaStream p) (s, w)‖ := by
                rw [← pow_succ]
      _ ≤ 2 * s * (2 * CS 1) :=
          mul_le_mul_of_nonneg_left (hΔΨ_jet 1 (s, w) hs0 hs1) (by positivity)
      _ = 4 * CS 1 * s := by ring
  have hw_pos : 0 < (1 + |w.2|) ^ 5 := by positivity
  change ‖(-(fderiv ℝ gs w (0, 1))) • Axi.m0 +
      (fderiv ℝ gs w (1, 0) + p.R⁻¹ * (gs w - 2 * s * Axi.dS (trainDeltaStream p) (s, w) -
        w.2 * fderiv ℝ gs w (0, 1))) • Axi.m1‖ ≤ K0 * u ^ 2 * ((1 + |w.2|) ^ 5)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀' hw_pos]
  have htri : ‖(-(fderiv ℝ gs w (0, 1))) • Axi.m0 +
      (fderiv ℝ gs w (1, 0) + p.R⁻¹ * (gs w - 2 * s * Axi.dS (trainDeltaStream p) (s, w) -
        w.2 * fderiv ℝ gs w (0, 1))) • Axi.m1‖ ≤
      |fderiv ℝ gs w (0, 1)| + |fderiv ℝ gs w (1, 0)| +
        (|gs w| + |2 * s * Axi.dS (trainDeltaStream p) (s, w)| + |w.2 * fderiv ℝ gs w (0, 1)|) := by
    have n1 : ‖(-(fderiv ℝ gs w (0, 1))) • Axi.m0‖ ≤ |fderiv ℝ gs w (0, 1)| := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg _) hm0_norm
    have n2 : ‖(fderiv ℝ gs w (1, 0) + p.R⁻¹ * (gs w - 2 * s * Axi.dS (trainDeltaStream p) (s, w) -
        w.2 * fderiv ℝ gs w (0, 1))) • Axi.m1‖ ≤
        |fderiv ℝ gs w (1, 0)| +
          (|gs w| + |2 * s * Axi.dS (trainDeltaStream p) (s, w)| + |w.2 * fderiv ℝ gs w (0, 1)|) := by
      rw [norm_smul, Real.norm_eq_abs]
      refine (mul_le_of_le_one_right (abs_nonneg _) hm1_norm).trans ?_
      have ha1 := abs_add_le (fderiv ℝ gs w (1, 0))
        (p.R⁻¹ * (gs w - 2 * s * Axi.dS (trainDeltaStream p) (s, w) - w.2 * fderiv ℝ gs w (0, 1)))
      have ha2 : |p.R⁻¹ * (gs w - 2 * s * Axi.dS (trainDeltaStream p) (s, w) -
          w.2 * fderiv ℝ gs w (0, 1))| ≤
          |gs w| + |2 * s * Axi.dS (trainDeltaStream p) (s, w)| + |w.2 * fderiv ℝ gs w (0, 1)| := by
        rw [abs_mul, abs_of_pos (inv_pos.2 hR0)]
        refine (mul_le_of_le_one_left (abs_nonneg _) hRinv_le).trans ?_
        have s1 := abs_sub (gs w - 2 * s * Axi.dS (trainDeltaStream p) (s, w))
          (w.2 * fderiv ℝ gs w (0, 1))
        have s2 := abs_sub (gs w) (2 * s * Axi.dS (trainDeltaStream p) (s, w))
        linarith only [s1, s2]
      linarith only [ha1, ha2]
    have n12 := norm_add_le ((-(fderiv ℝ gs w (0, 1))) • Axi.m0)
      ((fderiv ℝ gs w (1, 0) + p.R⁻¹ * (gs w - 2 * s * Axi.dS (trainDeltaStream p) (s, w) -
        w.2 * fderiv ℝ gs w (0, 1))) • Axi.m1)
    linarith only [n12, n1, n2]
  calc (1 + |w.2|) ^ 5 * ‖(-(fderiv ℝ gs w (0, 1))) • Axi.m0 +
        (fderiv ℝ gs w (1, 0) + p.R⁻¹ * (gs w - 2 * s * Axi.dS (trainDeltaStream p) (s, w) -
          w.2 * fderiv ℝ gs w (0, 1))) • Axi.m1‖
      ≤ (1 + |w.2|) ^ 5 * (|fderiv ℝ gs w (0, 1)| + |fderiv ℝ gs w (1, 0)| +
          (|gs w| + |2 * s * Axi.dS (trainDeltaStream p) (s, w)| + |w.2 * fderiv ℝ gs w (0, 1)|)) :=
        mul_le_mul_of_nonneg_left htri hw_pos.le
    _ = (1 + |w.2|) ^ 5 * |fderiv ℝ gs w (0, 1)| +
          (1 + |w.2|) ^ 5 * |fderiv ℝ gs w (1, 0)| +
          (1 + |w.2|) ^ 5 * |gs w| +
          (1 + |w.2|) ^ 5 * |2 * s * Axi.dS (trainDeltaStream p) (s, w)| +
          (1 + |w.2|) ^ 5 * |w.2 * fderiv ℝ gs w (0, 1)| := by ring
    _ ≤ CS 2 * s + CS 2 * s + CS 1 * s + 4 * CS 1 * s + CS 2 * s := by
        linarith only [hdEta_bd5, hdQ_bd, hg0_bd5, hdS_bd5, hwdEta_bd5]
    _ = K0 * u ^ 2 := by rw [hK0_def, hs_def]; ring

private theorem bu_jet_one {p : UnforcedLeray.Cons.C03.Concrete.Params}
    (hR1 : 1 ≤ p.R)
    (hΔΨ_cd : ContDiffOn ℝ ∞ (trainDeltaStream p) (Ioi 0 ×ˢ univ))
    (hbΔ_cd : ContDiffOn ℝ ∞ (trainDeltaMerid p) (Ioi 0 ×ˢ univ))
    {CS : ℕ → ℝ} (hCS0 : ∀ i : ℕ, 0 ≤ CS i)
    (hΔΨ_jet : ∀ i : ℕ, ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i (trainDeltaStream p) x‖ ≤ 2 * CS i)
    (hinc_sub : ∀ k : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ w : Plane,
      (1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ k (fun w' => p.train.ψ s w' - p.train.ψ 0 w') w‖ ≤
        CS (k + 1) * s)
    {B_mer : ℝ} (hB_mer0 : 0 ≤ B_mer)
    (hbΔ_jet : ∀ l ≤ 2, ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 5 * ‖iteratedFDeriv ℝ l (trainDeltaMerid p) x‖ ≤ B_mer) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ (u : ℝ) (w : Plane), 0 < u → u ≤ 1 →
      ‖fderiv ℝ (trainDeltaBu p) (u, w)‖ ≤ K1 * u * ((1 + |w.2|) ^ 5)⁻¹ := by
  have hR0 : 0 < p.R := lt_of_lt_of_le one_pos hR1
  have hRinv_le : p.R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hm0_norm : ‖Axi.m0‖ ≤ 1 := by
    have h : ‖Axi.m0‖ = 1 := by simp [Axi.m0]
    exact h.le
  have hm1_norm : ‖Axi.m1‖ ≤ 1 := by
    have h : ‖Axi.m1‖ = 1 := by simp [Axi.m1]
    exact h.le
  obtain ⟨K1, hK1_def⟩ : ∃ x : ℝ, x = 2 * B_mer + (3 * CS 3 + 2 * CS 2 + 4 * CS 2) := ⟨_, rfl⟩
  have hK1_nn : 0 ≤ K1 := by
    rw [hK1_def]; have := hCS0 2; have := hCS0 3; positivity
  refine ⟨K1, hK1_nn, fun u w hu0 hu1 => ?_⟩
  set s : ℝ := u ^ 2 with hs_def
  have hs0 : 0 < s := pow_pos hu0 2
  have hs1 : s ≤ 1 := pow_le_one₀ hu0.le hu1
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hsw_mem : (s, w) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hs0, trivial⟩
  have hbΔ_diff : DifferentiableAt ℝ (trainDeltaMerid p) (s, w) :=
    (hbΔ_cd.contDiffAt (hopen.mem_nhds hsw_mem)).differentiableAt (by simp)
  have hcomp_fd : fderiv ℝ (trainDeltaBu p) (u, w) =
      (fderiv ℝ (trainDeltaMerid p) (s, w)).comp (fderiv ℝ sqAgeMap (u, w)) :=
    fderiv_comp (u, w) hbΔ_diff (contDiff_sqAgeMap.differentiable (by simp) (u, w))
  rw [hcomp_fd]
  let gs : Plane → ℝ := fun w' => p.train.ψ s w' - p.train.ψ 0 w'
  have hgs_cd : ContDiff ℝ ∞ gs :=
    (contDiff_psi_slice p.train hs0.le).sub (contDiff_psi_slice p.train le_rfl)
  have hΔΨ_at : ContDiffAt ℝ ∞ (trainDeltaStream p) (s, w) :=
    hΔΨ_cd.contDiffAt (hopen.mem_nhds hsw_mem)
  have hd2_ΔΨ : DifferentiableAt ℝ (fderiv ℝ (trainDeltaStream p)) (s, w) :=
    (hΔΨ_at.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd_at_dS : DifferentiableAt ℝ (Axi.dS (trainDeltaStream p)) (s, w) := by
    unfold Axi.dS
    exact hd2_ΔΨ.clm_apply (differentiableAt_const _)
  have hdS_slice_diff :
      DifferentiableAt ℝ (fun w' : Plane => Axi.dS (trainDeltaStream p) (s, w')) w :=
    hd_at_dS.comp w ((differentiableAt_const s).prodMk differentiableAt_id)
  have hdS_slice_norm : ‖fderiv ℝ (fun w' : Plane => Axi.dS (trainDeltaStream p) (s, w')) w‖ ≤
      ‖iteratedFDeriv ℝ 2 (trainDeltaStream p) (s, w)‖ := by
    have hc1 : fderiv ℝ (fun w' : Plane => Axi.dS (trainDeltaStream p) (s, w')) w =
        (fderiv ℝ (Axi.dS (trainDeltaStream p)) (s, w)).comp (ContinuousLinearMap.inr ℝ ℝ Plane) :=
      (hd_at_dS.hasFDerivAt.comp w (hasFDerivAt_prodMk_right s w)).fderiv
    have hc2 : HasFDerivAt (Axi.dS (trainDeltaStream p))
        ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : Plane))).comp
          (fderiv ℝ (fderiv ℝ (trainDeltaStream p)) (s, w))) (s, w) := by
      unfold Axi.dS
      exact ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : Plane))).hasFDerivAt).comp (s, w)
        hd2_ΔΨ.hasFDerivAt
    rw [hc1, hc2.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun dw => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    have h1 := (fderiv ℝ (fderiv ℝ (trainDeltaStream p)) (s, w) (0, dw)).le_opNorm
      ((1 : ℝ), (0 : Plane))
    have h2 := (fderiv ℝ (fderiv ℝ (trainDeltaStream p)) (s, w)).le_opNorm (0, dw)
    have h10 : ‖((1 : ℝ), (0 : Plane))‖ = 1 := by simp [Prod.norm_def]
    have h0dw : ‖((0 : ℝ), dw)‖ = ‖dw‖ := by simp [Prod.norm_def]
    have hfd2 : ‖fderiv ℝ (fderiv ℝ (trainDeltaStream p)) (s, w)‖ =
        ‖iteratedFDeriv ℝ 2 (trainDeltaStream p) (s, w)‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    rw [h10, mul_one] at h1
    rw [h0dw, hfd2] at h2
    exact h1.trans h2
  let gq : Plane → ℝ := fun w' => fderiv ℝ gs w' (1, 0)
  let geta : Plane → ℝ := fun w' => fderiv ℝ gs w' (0, 1)
  have hgq_diff : DifferentiableAt ℝ gq w :=
    ((hgs_cd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) w
  have hgeta_diff : DifferentiableAt ℝ geta w :=
    ((hgs_cd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) w
  have hgs_diff : DifferentiableAt ℝ gs w := hgs_cd.differentiable (by simp) w
  have hgq_fd_le : ‖fderiv ℝ gq w‖ ≤ ‖iteratedFDeriv ℝ 2 gs w‖ := by
    have hd2 : DifferentiableAt ℝ (fderiv ℝ gs) w :=
      (hgs_cd.fderiv_right (m := ∞) (by simp)).differentiable (by simp) w
    have hc : HasFDerivAt gq
        ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).comp (fderiv ℝ (fderiv ℝ gs) w)) w :=
      ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).hasFDerivAt).comp w hd2.hasFDerivAt
    rw [hc.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun dw => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    have h1 := (fderiv ℝ (fderiv ℝ gs) w dw).le_opNorm ((1 : ℝ), (0 : ℝ))
    have h2 := (fderiv ℝ (fderiv ℝ gs) w).le_opNorm dw
    have h10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    have hfd2 : ‖fderiv ℝ (fderiv ℝ gs) w‖ = ‖iteratedFDeriv ℝ 2 gs w‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    rw [h10, mul_one] at h1
    rw [hfd2] at h2
    exact h1.trans h2
  have hgeta_fd_le : ‖fderiv ℝ geta w‖ ≤ ‖iteratedFDeriv ℝ 2 gs w‖ := by
    have hd2 : DifferentiableAt ℝ (fderiv ℝ gs) w :=
      (hgs_cd.fderiv_right (m := ∞) (by simp)).differentiable (by simp) w
    have hc : HasFDerivAt geta
        ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).comp (fderiv ℝ (fderiv ℝ gs) w)) w :=
      ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).hasFDerivAt).comp w hd2.hasFDerivAt
    rw [hc.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun dw => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    have h1 := (fderiv ℝ (fderiv ℝ gs) w dw).le_opNorm ((0 : ℝ), (1 : ℝ))
    have h2 := (fderiv ℝ (fderiv ℝ gs) w).le_opNorm dw
    have h01 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    have hfd2 : ‖fderiv ℝ (fderiv ℝ gs) w‖ = ‖iteratedFDeriv ℝ 2 gs w‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    rw [h01, mul_one] at h1
    rw [hfd2] at h2
    exact h1.trans h2
  have hw_slice : (fun w' : Plane => trainDeltaMerid p (s, w')) =
      fun w' : Plane => (-(geta w')) • Axi.m0 +
        (gq w' + p.R⁻¹ * (gs w' - 2 * s * Axi.dS (trainDeltaStream p) (s, w') -
          w'.2 * geta w')) • Axi.m1 :=
    funext (trainDeltaMerid_slice_eq p hΔΨ_cd hs0)
  have hslice_fd : ‖fderiv ℝ (fun w' : Plane => trainDeltaMerid p (s, w')) w‖ ≤
      (3 * CS 3 + 2 * CS 2 + 4 * CS 2) * s * ((1 + |w.2|) ^ 5)⁻¹ := by
    have hdA : HasFDerivAt (fun w' : Plane => (-(geta w')) • Axi.m0)
        ((-(fderiv ℝ geta w)).smulRight Axi.m0) w :=
      hgeta_diff.hasFDerivAt.neg.smul_const Axi.m0
    have hd_wgeta : HasFDerivAt (fun w' : Plane => w'.2 * geta w')
        (w.2 • fderiv ℝ geta w + geta w • ContinuousLinearMap.snd ℝ ℝ ℝ) w :=
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := w)).mul hgeta_diff.hasFDerivAt
    have hd_inner : HasFDerivAt
        (fun w' : Plane => gq w' + p.R⁻¹ *
          (gs w' - 2 * s * Axi.dS (trainDeltaStream p) (s, w') - w'.2 * geta w'))
        (fderiv ℝ gq w + p.R⁻¹ • (fderiv ℝ gs w -
          (2 * s) • fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w -
          (w.2 • fderiv ℝ geta w + geta w • ContinuousLinearMap.snd ℝ ℝ ℝ))) w :=
      hgq_diff.hasFDerivAt.add (((hgs_diff.hasFDerivAt.sub
        (hdS_slice_diff.hasFDerivAt.const_smul (2 * s))).sub hd_wgeta).const_smul p.R⁻¹)
    have htot_hd : HasFDerivAt
        (fun w' : Plane => (-(geta w')) • Axi.m0 +
          (gq w' + p.R⁻¹ * (gs w' - 2 * s * Axi.dS (trainDeltaStream p) (s, w') -
            w'.2 * geta w')) • Axi.m1)
        ((-(fderiv ℝ geta w)).smulRight Axi.m0 +
          (fderiv ℝ gq w + p.R⁻¹ • (fderiv ℝ gs w -
            (2 * s) • fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w -
            (w.2 • fderiv ℝ geta w + geta w • ContinuousLinearMap.snd ℝ ℝ ℝ))).smulRight Axi.m1) w :=
      hdA.add (hd_inner.smul_const Axi.m1)
    rw [hw_slice, htot_hd.fderiv]
    have hw_pos : 0 < (1 + |w.2|) ^ 5 := by positivity
    have hw1 : (1 : ℝ) ≤ 1 + |w.2| := le_add_of_nonneg_right (abs_nonneg w.2)
    have hb_g1 : (1 + |w.2|) ^ 6 * ‖fderiv ℝ gs w‖ ≤ CS 2 * s := by
      have h := hinc_sub 1 s hs0 hs1 w
      rwa [norm_iteratedFDeriv_one] at h
    have hb_g2 : (1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ 2 gs w‖ ≤ CS 3 * s :=
      hinc_sub 2 s hs0 hs1 w
    have hb_dS2 : (1 + |w.2|) ^ 6 *
        ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖ ≤ 2 * CS 2 :=
      (mul_le_mul_of_nonneg_left hdS_slice_norm (by positivity)).trans (hΔΨ_jet 2 (s, w) hs0 hs1)
    refine ContinuousLinearMap.opNorm_le_bound _ (by
      have := hCS0 2; have := hCS0 3; positivity) fun dw => ?_
    have hrhs_eq : (3 * CS 3 + 2 * CS 2 + 4 * CS 2) * s * ((1 + |w.2|) ^ 5)⁻¹ * ‖dw‖ =
        ((3 * CS 3 + 2 * CS 2 + 4 * CS 2) * s * ‖dw‖) / (1 + |w.2|) ^ 5 := by
      rw [← div_eq_mul_inv, div_mul_eq_mul_div]
    rw [hrhs_eq, le_div_iff₀' hw_pos]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      neg_apply, smul_apply, sub_apply, ContinuousLinearMap.coe_snd', smul_eq_mul]
    have nA : ‖(-(fderiv ℝ geta w dw)) • Axi.m0‖ ≤ ‖iteratedFDeriv ℝ 2 gs w‖ * ‖dw‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg]
      refine (mul_le_of_le_one_right (abs_nonneg _) hm0_norm).trans ?_
      exact ((fderiv ℝ geta w).le_opNorm dw).trans
        (mul_le_mul_of_nonneg_right hgeta_fd_le (norm_nonneg dw))
    have nBq : |fderiv ℝ gq w dw| ≤ ‖iteratedFDeriv ℝ 2 gs w‖ * ‖dw‖ :=
      ((fderiv ℝ gq w).le_opNorm dw).trans
        (mul_le_mul_of_nonneg_right hgq_fd_le (norm_nonneg dw))
    have nBgs : |fderiv ℝ gs w dw| ≤ ‖fderiv ℝ gs w‖ * ‖dw‖ := (fderiv ℝ gs w).le_opNorm dw
    have nBdS : |2 * s * fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w dw| ≤
        2 * s * ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖ * ‖dw‖ := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * s), mul_assoc (2 * s)]
      exact mul_le_mul_of_nonneg_left
        ((fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w).le_opNorm dw)
        (by positivity)
    have nBwe : |w.2 * fderiv ℝ geta w dw| ≤
        (1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖ * ‖dw‖ := by
      rw [abs_mul]
      have hw_le : |w.2| ≤ 1 + |w.2| := le_add_of_nonneg_left zero_le_one
      have h1 : |fderiv ℝ geta w dw| ≤ ‖iteratedFDeriv ℝ 2 gs w‖ * ‖dw‖ :=
        ((fderiv ℝ geta w).le_opNorm dw).trans
          (mul_le_mul_of_nonneg_right hgeta_fd_le (norm_nonneg dw))
      calc |w.2| * |fderiv ℝ geta w dw|
          ≤ (1 + |w.2|) * (‖iteratedFDeriv ℝ 2 gs w‖ * ‖dw‖) :=
            mul_le_mul hw_le h1 (abs_nonneg _) (by positivity)
        _ = (1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖ * ‖dw‖ := by ring
    have nBge : |geta w * dw.2| ≤ ‖fderiv ℝ gs w‖ * ‖dw‖ := by
      rw [abs_mul]
      have h1 : |geta w| ≤ ‖fderiv ℝ gs w‖ := by
        simpa [geta, Real.norm_eq_abs, Prod.norm_def] using (fderiv ℝ gs w).le_opNorm (0, 1)
      have h2 : |dw.2| ≤ ‖dw‖ := le_max_right _ _
      exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    have nB : ‖(fderiv ℝ gq w dw + p.R⁻¹ * (fderiv ℝ gs w dw -
        2 * s * fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w dw -
          (w.2 * fderiv ℝ geta w dw + geta w * dw.2))) • Axi.m1‖ ≤
        (‖iteratedFDeriv ℝ 2 gs w‖ + 2 * ‖fderiv ℝ gs w‖ +
          2 * s * ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖ +
          (1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖) * ‖dw‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      refine (mul_le_of_le_one_right (abs_nonneg _) hm1_norm).trans ?_
      have a1 := abs_add_le (fderiv ℝ gq w dw)
        (p.R⁻¹ * (fderiv ℝ gs w dw -
          2 * s * fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w dw -
          (w.2 * fderiv ℝ geta w dw + geta w * dw.2)))
      have a2 : |p.R⁻¹ * (fderiv ℝ gs w dw -
          2 * s * fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w dw -
            (w.2 * fderiv ℝ geta w dw + geta w * dw.2))| ≤
          |fderiv ℝ gs w dw| +
            |2 * s * fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w dw| +
            (|w.2 * fderiv ℝ geta w dw| + |geta w * dw.2|) := by
        rw [abs_mul, abs_of_pos (inv_pos.2 hR0)]
        refine (mul_le_of_le_one_left (abs_nonneg _) hRinv_le).trans ?_
        have s1 := abs_sub (fderiv ℝ gs w dw -
          2 * s * fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w dw)
          (w.2 * fderiv ℝ geta w dw + geta w * dw.2)
        have s2 := abs_sub (fderiv ℝ gs w dw)
          (2 * s * fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w dw)
        have s3 := abs_add_le (w.2 * fderiv ℝ geta w dw) (geta w * dw.2)
        linarith only [s1, s2, s3]
      linarith only [a1, a2, nBq, nBgs, nBdS, nBwe, nBge]
    have htot_pt : ‖(-(fderiv ℝ geta w dw)) • Axi.m0 +
        (fderiv ℝ gq w dw + p.R⁻¹ * (fderiv ℝ gs w dw -
          2 * s * fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w dw -
            (w.2 * fderiv ℝ geta w dw + geta w * dw.2))) • Axi.m1‖ ≤
        (2 * ‖iteratedFDeriv ℝ 2 gs w‖ + 2 * ‖fderiv ℝ gs w‖ +
          2 * s * ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖ +
          (1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖) * ‖dw‖ := by
      have n_tri := norm_add_le ((-(fderiv ℝ geta w dw)) • Axi.m0)
        ((fderiv ℝ gq w dw + p.R⁻¹ * (fderiv ℝ gs w dw -
          2 * s * fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w dw -
            (w.2 * fderiv ℝ geta w dw + geta w * dw.2))) • Axi.m1)
      linarith only [n_tri, nA, nB]
    refine (mul_le_mul_of_nonneg_left htot_pt hw_pos.le).trans ?_
    have t1 : (1 + |w.2|) ^ 5 * ‖iteratedFDeriv ℝ 2 gs w‖ ≤ CS 3 * s := by
      calc (1 + |w.2|) ^ 5 * ‖iteratedFDeriv ℝ 2 gs w‖
          ≤ (1 + |w.2|) ^ 5 * (1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖ :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hw_pos.le hw1) (norm_nonneg _)
        _ = (1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ 2 gs w‖ := by rw [← pow_succ]
        _ ≤ CS 3 * s := hb_g2
    have t2 : (1 + |w.2|) ^ 5 * ‖fderiv ℝ gs w‖ ≤ CS 2 * s := by
      calc (1 + |w.2|) ^ 5 * ‖fderiv ℝ gs w‖
          ≤ (1 + |w.2|) ^ 5 * (1 + |w.2|) * ‖fderiv ℝ gs w‖ :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hw_pos.le hw1) (norm_nonneg _)
        _ = (1 + |w.2|) ^ 6 * ‖fderiv ℝ gs w‖ := by rw [← pow_succ]
        _ ≤ CS 2 * s := hb_g1
    have t3 : (1 + |w.2|) ^ 5 *
        (2 * s * ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖) ≤
        4 * CS 2 * s := by
      calc (1 + |w.2|) ^ 5 *
            (2 * s * ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖)
          = 2 * s * ((1 + |w.2|) ^ 5 *
              ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖) := by ring
        _ ≤ 2 * s * ((1 + |w.2|) ^ 6 *
              ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc (1 + |w.2|) ^ 5 * ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖
                ≤ (1 + |w.2|) ^ 5 * (1 + |w.2|) *
                    ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖ :=
                  mul_le_mul_of_nonneg_right
                    (le_mul_of_one_le_right hw_pos.le hw1) (norm_nonneg _)
              _ = (1 + |w.2|) ^ 6 *
                    ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖ := by
                  rw [← pow_succ]
        _ ≤ 2 * s * (2 * CS 2) := mul_le_mul_of_nonneg_left hb_dS2 (by positivity)
        _ = 4 * CS 2 * s := by ring
    have t4 : (1 + |w.2|) ^ 5 * ((1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖) ≤ CS 3 * s := by
      calc (1 + |w.2|) ^ 5 * ((1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖)
          = (1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ 2 gs w‖ := by ring
        _ ≤ CS 3 * s := hb_g2
    have hcomb : (1 + |w.2|) ^ 5 *
        (2 * ‖iteratedFDeriv ℝ 2 gs w‖ + 2 * ‖fderiv ℝ gs w‖ +
          2 * s * ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖ +
          (1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖) ≤
        (3 * CS 3 + 2 * CS 2 + 4 * CS 2) * s := by
      linarith only [t1, t2, t3, t4]
    calc (1 + |w.2|) ^ 5 *
          ((2 * ‖iteratedFDeriv ℝ 2 gs w‖ + 2 * ‖fderiv ℝ gs w‖ +
            2 * s * ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖ +
            (1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖) * ‖dw‖)
        = ((1 + |w.2|) ^ 5 *
            (2 * ‖iteratedFDeriv ℝ 2 gs w‖ + 2 * ‖fderiv ℝ gs w‖ +
              2 * s * ‖fderiv ℝ (fun w' => Axi.dS (trainDeltaStream p) (s, w')) w‖ +
              (1 + |w.2|) * ‖iteratedFDeriv ℝ 2 gs w‖)) * ‖dw‖ := by ring
      _ ≤ ((3 * CS 3 + 2 * CS 2 + 4 * CS 2) * s) * ‖dw‖ :=
          mul_le_mul_of_nonneg_right hcomb (norm_nonneg dw)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, fderiv_sqAgeMap_apply]
  have hv_split : ((2 * u * v.1, v.2) : ℝ × Plane) =
      (2 * u * v.1) • ((1 : ℝ), (0 : Plane)) + ((0 : ℝ), v.2) := by
    ext <;> simp
  have hinr_eq : fderiv ℝ (trainDeltaMerid p) (s, w) (0, v.2) =
      fderiv ℝ (fun w' => trainDeltaMerid p (s, w')) w v.2 := by
    have hc : HasFDerivAt (fun w' : Plane => trainDeltaMerid p (s, w'))
        ((fderiv ℝ (trainDeltaMerid p) (s, w)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) w :=
      hbΔ_diff.hasFDerivAt.comp w (hasFDerivAt_prodMk_right s w)
    rw [hc.fderiv]; rfl
  rw [hv_split, map_add, map_smul, hinr_eq]
  have h10_le : ‖fderiv ℝ (trainDeltaMerid p) (s, w) (1, 0)‖ ≤ B_mer * ((1 + |w.2|) ^ 5)⁻¹ := by
    have h1 : ‖fderiv ℝ (trainDeltaMerid p) (s, w) (1, 0)‖ ≤
        ‖iteratedFDeriv ℝ 1 (trainDeltaMerid p) (s, w)‖ := by
      rw [norm_iteratedFDeriv_one]
      simpa [Prod.norm_def] using (fderiv ℝ (trainDeltaMerid p) (s, w)).le_opNorm (1, 0)
    have hw_pos : 0 < (1 + |w.2|) ^ 5 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀' hw_pos]
    exact (mul_le_mul_of_nonneg_left h1 hw_pos.le).trans (hbΔ_jet 1 (by norm_num) (s, w) hs0 hs1)
  have hv1 : |v.1| ≤ ‖v‖ := le_max_left _ _
  have hv2 : ‖v.2‖ ≤ ‖v‖ := le_max_right _ _
  have hs_le_u : s ≤ u := pow_le_of_le_one hu0.le hu1 (by norm_num)
  have p1 : ‖(2 * u * v.1) • fderiv ℝ (trainDeltaMerid p) (s, w) (1, 0)‖ ≤
      2 * B_mer * u * ((1 + |w.2|) ^ 5)⁻¹ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hu0]
    calc 2 * u * |v.1| * ‖fderiv ℝ (trainDeltaMerid p) (s, w) (1, 0)‖
        ≤ 2 * u * ‖v‖ * (B_mer * ((1 + |w.2|) ^ 5)⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hv1 (by positivity)) h10_le
            (norm_nonneg _) (by positivity)
      _ = 2 * B_mer * u * ((1 + |w.2|) ^ 5)⁻¹ * ‖v‖ := by ring
  have p2 : ‖fderiv ℝ (fun w' => trainDeltaMerid p (s, w')) w v.2‖ ≤
      (3 * CS 3 + 2 * CS 2 + 4 * CS 2) * u * ((1 + |w.2|) ^ 5)⁻¹ * ‖v‖ := by
    have hcoef0 : 0 ≤ 3 * CS 3 + 2 * CS 2 + 4 * CS 2 := by
      have := hCS0 2; have := hCS0 3; positivity
    calc ‖fderiv ℝ (fun w' => trainDeltaMerid p (s, w')) w v.2‖
        ≤ ‖fderiv ℝ (fun w' => trainDeltaMerid p (s, w')) w‖ * ‖v.2‖ :=
          (fderiv ℝ (fun w' => trainDeltaMerid p (s, w')) w).le_opNorm v.2
      _ ≤ ((3 * CS 3 + 2 * CS 2 + 4 * CS 2) * s * ((1 + |w.2|) ^ 5)⁻¹) * ‖v‖ :=
          mul_le_mul hslice_fd hv2 (norm_nonneg _) (by positivity)
      _ ≤ ((3 * CS 3 + 2 * CS 2 + 4 * CS 2) * u * ((1 + |w.2|) ^ 5)⁻¹) * ‖v‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hs_le_u hcoef0) (by positivity)
      _ = (3 * CS 3 + 2 * CS 2 + 4 * CS 2) * u * ((1 + |w.2|) ^ 5)⁻¹ * ‖v‖ := by ring
  exact (norm_add_le _ _).trans (by
    calc _ ≤ 2 * B_mer * u * ((1 + |w.2|) ^ 5)⁻¹ * ‖v‖ +
          (3 * CS 3 + 2 * CS 2 + 4 * CS 2) * u * ((1 + |w.2|) ^ 5)⁻¹ * ‖v‖ := add_le_add p1 p2
      _ = K1 * u * ((1 + |w.2|) ^ 5)⁻¹ * ‖v‖ := by rw [hK1_def]; ring)

private theorem bu_jet_two {p : UnforcedLeray.Cons.C03.Concrete.Params}
    (hbΔ_cd : ContDiffOn ℝ ∞ (trainDeltaMerid p) (Ioi 0 ×ˢ univ))
    {B_mer : ℝ} (hB_mer0 : 0 ≤ B_mer)
    (hbΔ_jet : ∀ l ≤ 2, ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 5 * ‖iteratedFDeriv ℝ l (trainDeltaMerid p) x‖ ≤ B_mer) :
    ContDiffOn ℝ ∞ (trainDeltaBu p) (Ioi 0 ×ˢ univ) ∧
    ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ (u : ℝ) (w : Plane), 0 < u → u ≤ 1 →
      ‖iteratedFDeriv ℝ 2 (trainDeltaBu p) (u, w)‖ ≤ K2 * ((1 + |w.2|) ^ 5)⁻¹ := by
  have hmaps_sq : MapsTo sqAgeMap (Ioi (0 : ℝ) ×ˢ (univ : Set Plane))
      (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
    fun x hx => ⟨show (0 : ℝ) < (sqAgeMap x).1 from pow_pos hx.1 2, trivial⟩
  have hbu_cd : ContDiffOn ℝ ∞ (trainDeltaBu p) (Ioi 0 ×ˢ univ) :=
    hbΔ_cd.comp contDiff_sqAgeMap.contDiffOn hmaps_sq
  obtain ⟨K2, hK2_def⟩ : ∃ x : ℝ, x = 8 * B_mer := ⟨_, rfl⟩
  have hK2_nn : 0 ≤ K2 := by rw [hK2_def]; positivity
  refine ⟨hbu_cd, K2, hK2_nn, fun u w hu0 hu1 => ?_⟩
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hx : (u, w) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hu0, trivial⟩
  have hs0 : 0 < u ^ 2 := pow_pos hu0 2
  have hs1 : u ^ 2 ≤ 1 := pow_le_one₀ hu0.le hu1
  have hbound0 : ∀ i, i ≤ 2 →
      ‖iteratedFDerivWithin ℝ i (trainDeltaMerid p) (Ioi 0 ×ˢ univ) (sqAgeMap (u, w))‖ ≤
        B_mer * ((1 + |w.2|) ^ 5)⁻¹ := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hopen (hmaps_sq hx)]
    have hw_pos : 0 < (1 + |w.2|) ^ 5 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀' hw_pos]
    exact hbΔ_jet i hi (u ^ 2, w) hs0 hs1
  have hD : ∀ i, 1 ≤ i → i ≤ 2 →
      ‖iteratedFDerivWithin ℝ i sqAgeMap (Ioi 0 ×ˢ univ) (u, w)‖ ≤ (2 : ℝ) ^ i := by
    intro i hi1 hi2
    rw [iteratedFDerivWithin_of_isOpen i hopen hx]
    interval_cases i
    · rw [norm_iteratedFDeriv_one, pow_one]
      exact norm_fderiv_sqAgeMap_le hu0.le hu1
    · calc ‖iteratedFDeriv ℝ 2 sqAgeMap (u, w)‖ ≤ 2 := norm_iteratedFDeriv_two_sqAgeMap_le (u, w)
        _ ≤ 2 ^ 2 := by norm_num
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ)
    (g := trainDeltaMerid p) (f := sqAgeMap)
    (n := 2) (s := Ioi 0 ×ˢ univ) (t := Ioi 0 ×ˢ univ) (x := (u, w)) (N := ∞)
    hbΔ_cd contDiff_sqAgeMap.contDiffOn (by simp)
    hopen.uniqueDiffOn hopen.uniqueDiffOn hmaps_sq hx hbound0 hD
  rw [← iteratedFDerivWithin_of_isOpen 2 hopen hx]
  have heq : ((2 : ℕ).factorial : ℝ) * (B_mer * ((1 + |w.2|) ^ 5)⁻¹) * (2 : ℝ) ^ 2 =
      K2 * ((1 + |w.2|) ^ 5)⁻¹ := by
    rw [hK2_def]
    norm_num [Nat.factorial]
    ring
  exact key.trans_eq heq

private theorem bu_jet_bounds {dm dp : ℝ} {p : UnforcedLeray.Cons.C03.Concrete.Params} {d : ℝ}
    (hreg : BgRegime p d dm dp) {C10 : ℝ} (hC10_nn : 0 ≤ C10)
    (hb10 : ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) * ‖iteratedFDeriv ℝ 0 (fun y : ℝ × Plane => p.train.ψ y.1 y.2) x‖ ≤ C10)
    {CS : ℕ → ℝ} (hCS0 : ∀ i : ℕ, 0 ≤ CS i)
    (hCS : ∀ i : ℕ, ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i (fun y : ℝ × Plane => p.train.ψ y.1 y.2) x‖ ≤ CS i) :
    ContDiffOn ℝ ∞ (trainDeltaMerid p) (Ioi 0 ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (trainDeltaBu p) (Ioi 0 ×ˢ univ) ∧
    ∃ K0 K1 K2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧
      (∀ (u : ℝ) (w : Plane), 0 < u → u ≤ 1 →
        ‖trainDeltaBu p (u, w)‖ ≤ K0 * u ^ 2 * ((1 + |w.2|) ^ 5)⁻¹) ∧
      (∀ (u : ℝ) (w : Plane), 0 < u → u ≤ 1 →
        ‖fderiv ℝ (trainDeltaBu p) (u, w)‖ ≤ K1 * u * ((1 + |w.2|) ^ 5)⁻¹) ∧
      (∀ (u : ℝ) (w : Plane), 0 < u → u ≤ 1 →
        ‖iteratedFDeriv ℝ 2 (trainDeltaBu p) (u, w)‖ ≤ K2 * ((1 + |w.2|) ^ 5)⁻¹) := by
  have hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hreg.train_stream_smooth
  have hR1 : 1 ≤ p.R := RawAndInletL4.one_le_R_of hreg
  have hinc : ∀ k : ℕ, (∀ w : Plane, (1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ k (p.train.ψ 0) w‖ ≤ CS k) ∧
      (∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ w : Plane,
        (1 + |w.2|) ^ 6 * ‖iteratedFDeriv ℝ k (fun w' => p.train.ψ s w' - p.train.ψ 0 w') w‖ ≤
          CS (k + 1) * s) :=
    fun k => psi_zero_and_sub_wtd_jet p.train hΨ hC10_nn (hCS0 k) (hCS0 (k + 1)) hb10
      (hCS k) (hCS (k + 1))
  obtain ⟨hΔΨ_cd, hbΔ_cd, hΔΨ_jet, B_mer, hB_mer0, hbΔ_jet⟩ :=
    trainDeltaMerid_jet_bounds hreg hCS0 hCS (fun i => (hinc i).1)
  obtain ⟨K0, hK0_nn, hbu_0⟩ := bu_jet_zero hR1 hΔΨ_cd hCS0 hΔΨ_jet (fun k => (hinc k).2)
  obtain ⟨K1, hK1_nn, hbu_1⟩ :=
    bu_jet_one hR1 hΔΨ_cd hbΔ_cd hCS0 hΔΨ_jet (fun k => (hinc k).2) hB_mer0 hbΔ_jet
  obtain ⟨hbu_cd, K2, hK2_nn, hbu_2⟩ := bu_jet_two hbΔ_cd hB_mer0 hbΔ_jet
  exact ⟨hbΔ_cd, hbu_cd, K0, K1, K2, hK0_nn, hK1_nn, hK2_nn, hbu_0, hbu_1, hbu_2⟩

/-- Far-field (`Axi.age p.R y ≤ 1`) cubic decay `(1 + ‖y‖)³ ‖D^j(p.raw τ - N_v b₀ τ)(y)‖ ≤ B`
for `j ≤ 2`, where `b₀ m = datumProfile p.ε (p.train.ψ 0) m.2`. -/
theorem raw_sub_train0_far_decay3 :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (dm dp : ℝ) (p : UnforcedLeray.Cons.C03.Concrete.Params) (d : ℝ),
      BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ j : ℕ, j ≤ 2 → ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : ℝ) (y : Space),
        y ∉ Axi.axis → Axi.age p.R y ≤ 1 →
        (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (fun z =>
          p.raw τ z - Axi.Nv p.R
            (fun m => UnforcedLeray.Cons.C03.Concrete.datumProfile p.ε (p.train.ψ 0) m.2) τ z) y‖ ≤
          B := by
  obtain ⟨νS, hνS, HS⟩ := trainStreamWtdBdd_uncond 2 (by norm_num)
  refine ⟨νS, hνS, fun dm dp p d hreg hν j hj => ?_⟩
  have hν0 : 0 < p.ν := p.ν_pos
  have hc : p.c = UnforcedLeray.Short.PartI.trainPeriod 2 p.ν := by
    rw [hreg.c_eq]
    unfold UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν0.le, Real.rpow_two]
  have htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train := hreg.train_buc
  let Ψ : ℝ × Plane → ℝ := fun x => p.train.ψ x.1 x.2
  have hΨ : ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ univ) := hreg.train_stream_smooth
  have hR1 : 1 ≤ p.R := RawAndInletL4.one_le_R_of hreg
  have hR0 : 0 < p.R := lt_of_lt_of_le one_pos hR1
  have hεR : p.ε = p.R⁻¹ := (inv_inv p.ε).symm
  obtain ⟨C10_raw, hC10_raw⟩ := HS p.ν p.c hν0 hν hc p.train htr 1 0 1
  have hb10 : ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) * ‖iteratedFDeriv ℝ 0 Ψ x‖ ≤ max C10_raw 0 :=
    fun x hx0 hx1 => by simpa only [pow_one] using (hC10_raw x hx0 hx1).trans (le_max_left _ _)
  have hS6 : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ 6 * ‖iteratedFDeriv ℝ i Ψ x‖ ≤ C := by
    intro i
    obtain ⟨Ci, hCi⟩ := HS p.ν p.c hν0 hν hc p.train htr 6 i 1
    exact ⟨max Ci 0, le_max_right _ _, fun x hx0 hx1 => (hCi x hx0 hx1).trans (le_max_left _ _)⟩
  choose CS hCS0 hCS using hS6
  obtain ⟨hbΔ_cd, hbu_cd, K0, K1, K2, hK0_nn, hK1_nn, hK2_nn, hbu_0, hbu_1, hbu_2⟩ :=
    bu_jet_bounds hreg (le_max_right C10_raw 0) hb10 hCS0 hCS
  let Ψ₀_ext : ℝ × Plane → ℝ := fun x => p.train.ψ 0 x.2
  have hψ0_cd : ContDiff ℝ ∞ (p.train.ψ 0) := contDiff_psi_slice p.train le_rfl
  have hΨ₀_cd : ContDiff ℝ ∞ Ψ₀_ext := hψ0_cd.comp contDiff_snd
  -- Compose `trainDeltaBu p` with `uChart p.R τ` and multiply by `√age` and `frameL`
  obtain ⟨CU1, hCU1_1, hU1⟩ := uChart_jet_le 1 le_rfl
  obtain ⟨CU2, _hCU2_1, hU2⟩ := uChart_jet_le 2 (by norm_num)
  obtain ⟨CU, hCU_def⟩ : ∃ x : ℝ, x = max CU1 CU2 := ⟨_, rfl⟩
  have hCU1 : 1 ≤ CU := hCU_def ▸ le_trans hCU1_1 (le_max_left _ _)
  have hCU1_le : CU1 ≤ CU := hCU_def ▸ le_max_left _ _
  have hCU2_le : CU2 ≤ CU := hCU_def ▸ le_max_right _ _
  choose Csf hCsf0 hSF using sqrtFrameJet_sqrt_age
  obtain ⟨Cq, hCq_def⟩ : ∃ x : ℝ, x = Csf 0 + Csf 1 + Csf 2 := ⟨_, rfl⟩
  have hCq0 : 0 < Cq := by
    rw [hCq_def]; have := hCsf0 0; have := hCsf0 1; have := hCsf0 2; positivity
  obtain ⟨Kcomp, hKcomp_def⟩ :
      ∃ x : ℝ, x = K0 + K1 * CU + 2 * (K0 + K1 + K2) * CU ^ 2 := ⟨_, rfl⟩
  have hKcomp0 : 0 ≤ Kcomp := by
    rw [hKcomp_def]; positivity
  obtain ⟨C_nv, hC_nv_def⟩ :
      ∃ x : ℝ, x = (((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * Kcomp := ⟨_, rfl⟩
  have hC_nv0 : 0 ≤ C_nv := by
    rw [hC_nv_def]; positivity
  refine ⟨C_nv * (1 + 1 + p.R) ^ 3, by positivity, fun τ y hy hs1 => ?_⟩
  have hs0 : 0 < Axi.age p.R y := PartIIIb.Concrete.age_pos_of hR0 hy
  -- Identify `p.raw τ - Nv ...` near `y` with `Axi.Nv p.R (trainDeltaMerid p) τ`
  have hev_diff : (fun z => p.raw τ z - Axi.Nv p.R
        (fun m => UnforcedLeray.Cons.C03.Concrete.datumProfile p.ε (p.train.ψ 0) m.2) τ z) =ᶠ[𝓝 y]
      Axi.Nv p.R (trainDeltaMerid p) τ := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
    have hz_age : 0 < (Axi.chart p.R τ z).1 := PartIIIb.Concrete.age_pos_of hR0 hz
    have e_raw : p.raw τ z = Axi.Nv p.R (Axi.ringStreamProfile p.R Ψ) τ z := by
      have hprof : UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ (Axi.chart p.R τ z) =
          Axi.ringStreamProfile p.R Ψ (Axi.chart p.R τ z) := by
        rw [hεR]
        exact rawStreamProfile p.ν p.c p.R p.train hR0 hreg.train_stream_smooth _ hz_age
      rw [p.raw_eq_off_axis τ z hz]
      unfold Axi.Nv
      change √(Axi.age p.R z) •
        (Axi.frameL z) (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ (Axi.chart p.R τ z)) = _
      rw [hprof]
    have e_dat : UnforcedLeray.Cons.C03.Concrete.datumProfile p.ε (p.train.ψ 0)
        (Axi.chart p.R τ z).2 = Axi.ringStreamProfile p.R Ψ₀_ext (Axi.chart p.R τ z) := by
      rw [hεR]
      exact datumProfile_eq_ringStreamProfile_snd hψ0_cd (Axi.chart p.R τ z)
    have e_sub_prof : Axi.ringStreamProfile p.R Ψ (Axi.chart p.R τ z) -
        Axi.ringStreamProfile p.R Ψ₀_ext (Axi.chart p.R τ z) =
        trainDeltaMerid p (Axi.chart p.R τ z) := by
      have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
      have hz_mem : Axi.chart p.R τ z ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hz_age, trivial⟩
      have hd1 : DifferentiableAt ℝ Ψ (Axi.chart p.R τ z) :=
        (hΨ.contDiffAt (hopen.mem_nhds hz_mem)).differentiableAt (by simp)
      have hd2 : DifferentiableAt ℝ Ψ₀_ext (Axi.chart p.R τ z) :=
        hΨ₀_cd.differentiable (by simp) _
      have hfd : fderiv ℝ (trainDeltaStream p) (Axi.chart p.R τ z) =
          fderiv ℝ Ψ (Axi.chart p.R τ z) - fderiv ℝ Ψ₀_ext (Axi.chart p.R τ z) :=
        (hd1.hasFDerivAt.sub hd2.hasFDerivAt).fderiv
      ext k
      fin_cases k <;>
        simp only [trainDeltaMerid, trainDeltaStream, Ψ, Ψ₀_ext,
          Axi.ringStreamProfile, Axi.dEta, Axi.dQ, Axi.dS, Axi.m0, Axi.m1,
          hfd, sub_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
        ring
    rw [e_raw]
    unfold Axi.Nv
    dsimp only
    rw [e_dat, ← smul_sub, ← map_sub, e_sub_prof]
  rw [(hev_diff.iteratedFDeriv ℝ j).eq_of_nhds]
  -- Bound `iteratedFDeriv ℝ m (trainDeltaMerid p ∘ chart) y` for `m ≤ j ≤ 2` via `trainDeltaBu p ∘ uChart`
  have hopen_ax : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hyc : y ∈ (Axi.axisᶜ : Set Space) := hy
  have hev_bu : (fun z => trainDeltaMerid p (Axi.chart p.R τ z)) =ᶠ[𝓝 y]
      (trainDeltaBu p ∘ uChart p.R τ) := by
    filter_upwards [hopen_ax.mem_nhds hyc] with z hz
    have hz0 : 0 < Axi.age p.R z := PartIIIb.Concrete.age_pos_of hR0 hz
    simp only [Function.comp_apply, trainDeltaBu, sqAgeMap, uChart, Axi.chart, Real.sq_sqrt hz0.le]
  obtain ⟨u, hu⟩ : ∃ x : ℝ, x = √(Axi.age p.R y) := ⟨_, rfl⟩
  have hu0 : 0 < u := hu ▸ Real.sqrt_pos.2 hs0
  have hu1 : u ≤ 1 := hu ▸ Real.sqrt_le_one.2 hs1
  obtain ⟨η, hη⟩ : ∃ x : ℝ, x = |Axi.trans p.R y| := ⟨_, rfl⟩
  have hη_nn : 0 ≤ η := hη ▸ abs_nonneg _
  have hη1 : 1 ≤ 1 + η := le_add_of_nonneg_right hη_nn
  have hmaps_uc : MapsTo (uChart p.R τ) Axi.axisᶜ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
    fun z hz =>
      ⟨show (0 : ℝ) < (uChart p.R τ z).1 from
        Real.sqrt_pos.2 (PartIIIb.Concrete.age_pos_of hR0 hz), trivial⟩
  have hK0_le_Kcomp : K0 ≤ Kcomp := by
    rw [hKcomp_def]
    have t1 : 0 ≤ K1 * CU := by positivity
    have t2 : 0 ≤ 2 * (K0 + K1 + K2) * CU ^ 2 := by positivity
    linarith only [t1, t2]
  have hK1CU_le_Kcomp : K1 * CU ≤ Kcomp := by
    rw [hKcomp_def]
    have t2 : 0 ≤ 2 * (K0 + K1 + K2) * CU ^ 2 := by positivity
    linarith only [hK0_nn, t2]
  have hK2_le_Kcomp : 2 * (K0 + K1 + K2) * CU ^ 2 ≤ Kcomp := by
    rw [hKcomp_def]
    have t1 : 0 ≤ K1 * CU := by positivity
    linarith only [hK0_nn, t1]
  have hcomp_bd : ∀ m ≤ j,
      ‖iteratedFDerivWithin ℝ m (fun z => trainDeltaMerid p (Axi.chart p.R τ z)) Axi.axisᶜ y‖ ≤
        Kcomp * u ^ 2 * ((1 + η) ^ 3)⁻¹ := by
    intro m hm
    rw [iteratedFDerivWithin_of_isOpen m hopen_ax hyc, (hev_bu.iteratedFDeriv ℝ m).eq_of_nhds]
    have hm2 : m ≤ 2 := hm.trans hj
    have hw35 : ((1 + η) ^ 5)⁻¹ ≤ ((1 + η) ^ 3)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ hη1 (by norm_num))
    have hw43 : (1 + η) * ((1 + η) ^ 5)⁻¹ ≤ ((1 + η) ^ 3)⁻¹ := by
      have hw45 : (1 + η) * ((1 + η) ^ 5)⁻¹ = ((1 + η) ^ 4)⁻¹ := by
        have hp : 0 < 1 + η := by positivity
        field_simp
      rw [hw45]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hη1 (by norm_num))
    have hw23 : (1 + η) ^ 2 * ((1 + η) ^ 5)⁻¹ = ((1 + η) ^ 3)⁻¹ := by
      have hp : 0 < 1 + η := by positivity
      field_simp
    have huc_eq : uChart p.R τ y = (u, (Axi.phase p.R τ y, Axi.trans p.R y)) := by
      simp only [uChart, hu]
    interval_cases m
    · rw [norm_iteratedFDeriv_zero, Function.comp_apply, huc_eq]
      have h0 := hbu_0 u (Axi.phase p.R τ y, Axi.trans p.R y) hu0 hu1
      rw [← hη] at h0
      have h1 : K0 * u ^ 2 * ((1 + η) ^ 5)⁻¹ ≤ K0 * u ^ 2 * ((1 + η) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_left hw35 (by positivity)
      refine h0.trans (h1.trans ?_)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK0_le_Kcomp (sq_nonneg u)) (by positivity)
    · rw [norm_iteratedFDeriv_one]
      have hopen_t : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
      have hbu_d : DifferentiableAt ℝ (trainDeltaBu p) (uChart p.R τ y) :=
        (hbu_cd.contDiffAt (hopen_t.mem_nhds (hmaps_uc hyc))).differentiableAt (by simp)
      have huc_d : DifferentiableAt ℝ (uChart p.R τ) y :=
        ((contDiffOn_uChart hR0.ne' τ).contDiffAt (hopen_ax.mem_nhds hyc)).differentiableAt (by simp)
      rw [fderiv_comp y hbu_d huc_d]
      have b_out : ‖fderiv ℝ (trainDeltaBu p) (uChart p.R τ y)‖ ≤ K1 * u * ((1 + η) ^ 5)⁻¹ := by
        rw [huc_eq]
        have h := hbu_1 u (Axi.phase p.R τ y, Axi.trans p.R y) hu0 hu1
        rwa [← hη] at h
      have b_in : ‖fderiv ℝ (uChart p.R τ) y‖ ≤ CU * (1 + η) * u := by
        rw [← norm_iteratedFDeriv_one]
        have h := hU1 p.R τ hR1 y hy hs1
        rw [pow_one, ← hu, ← hη] at h
        exact h.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCU1_le (by positivity)) hu0.le)
      calc ‖(fderiv ℝ (trainDeltaBu p) (uChart p.R τ y)).comp (fderiv ℝ (uChart p.R τ) y)‖
          ≤ ‖fderiv ℝ (trainDeltaBu p) (uChart p.R τ y)‖ * ‖fderiv ℝ (uChart p.R τ) y‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K1 * u * ((1 + η) ^ 5)⁻¹) * (CU * (1 + η) * u) :=
            mul_le_mul b_out b_in (norm_nonneg _) (by positivity)
        _ = K1 * CU * u ^ 2 * ((1 + η) * ((1 + η) ^ 5)⁻¹) := by ring
        _ ≤ K1 * CU * u ^ 2 * ((1 + η) ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_left hw43 (by positivity)
        _ ≤ Kcomp * u ^ 2 * ((1 + η) ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hK1CU_le_Kcomp (sq_nonneg u)) (by positivity)
    · have hopen_t : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
      obtain ⟨Sbu, hSbu_def⟩ : ∃ x : ℝ, x = (K0 + K1 + K2) * ((1 + η) ^ 5)⁻¹ := ⟨_, rfl⟩
      have hbound0 : ∀ i, i ≤ 2 →
          ‖iteratedFDerivWithin ℝ i (trainDeltaBu p) (Ioi 0 ×ˢ univ) (uChart p.R τ y)‖ ≤ Sbu := by
        intro i hi
        rw [iteratedFDerivWithin_of_isOpen i hopen_t (hmaps_uc hyc), hSbu_def, huc_eq]
        interval_cases i
        · rw [norm_iteratedFDeriv_zero]
          have h := hbu_0 u (Axi.phase p.R τ y, Axi.trans p.R y) hu0 hu1
          rw [← hη] at h
          have hu2_le1 : u ^ 2 ≤ 1 := pow_le_one₀ hu0.le hu1
          have hk0 : K0 * u ^ 2 ≤ K0 + K1 + K2 := by
            calc K0 * u ^ 2 ≤ K0 * 1 := mul_le_mul_of_nonneg_left hu2_le1 hK0_nn
              _ ≤ K0 + K1 + K2 := by linarith only [hK1_nn, hK2_nn]
          exact h.trans (mul_le_mul_of_nonneg_right hk0 (by positivity))
        · rw [norm_iteratedFDeriv_one]
          have h := hbu_1 u (Axi.phase p.R τ y, Axi.trans p.R y) hu0 hu1
          rw [← hη] at h
          have hk1 : K1 * u ≤ K0 + K1 + K2 := by
            calc K1 * u ≤ K1 * 1 := mul_le_mul_of_nonneg_left hu1 hK1_nn
              _ ≤ K0 + K1 + K2 := by linarith only [hK0_nn, hK2_nn]
          exact h.trans (mul_le_mul_of_nonneg_right hk1 (by positivity))
        · have h := hbu_2 u (Axi.phase p.R τ y, Axi.trans p.R y) hu0 hu1
          rw [← hη] at h
          have hk2 : K2 ≤ K0 + K1 + K2 := by linarith only [hK0_nn, hK1_nn]
          exact h.trans (mul_le_mul_of_nonneg_right hk2 (by positivity))
      obtain ⟨Buc, hBuc_def⟩ : ∃ x : ℝ, x = CU * (1 + η) * u := ⟨_, rfl⟩
      have hW1 : 1 ≤ CU * (1 + η) := one_le_mul_of_one_le_of_one_le hCU1 hη1
      have hD : ∀ i, 1 ≤ i → i ≤ 2 →
          ‖iteratedFDerivWithin ℝ i (uChart p.R τ) Axi.axisᶜ y‖ ≤ Buc ^ i := by
        intro i hi1 hi2
        rw [iteratedFDerivWithin_of_isOpen i hopen_ax hyc, hBuc_def]
        interval_cases i
        · rw [pow_one]
          have h := hU1 p.R τ hR1 y hy hs1
          rw [pow_one, ← hu, ← hη] at h
          exact h.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCU1_le (by positivity)) hu0.le)
        · have h := hU2 p.R τ hR1 y hy hs1
          rw [← hu, ← hη] at h
          have hle1 : CU2 * (1 + η) * u ^ 2 ≤ CU * (1 + η) * u ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCU2_le (by positivity)) (sq_nonneg u)
          have hle2 : CU * (1 + η) * u ^ 2 ≤ (CU * (1 + η) * u) ^ 2 := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right (le_self_pow₀ hW1 (by norm_num)) (sq_nonneg u)
          exact h.trans (hle1.trans hle2)
      have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ)
        (g := trainDeltaBu p) (f := uChart p.R τ)
        (n := 2) (s := Axi.axisᶜ) (t := Ioi 0 ×ˢ univ) (x := y) (N := ∞)
        hbu_cd (contDiffOn_uChart hR0.ne' τ) (by simp)
        hopen_t.uniqueDiffOn hopen_ax.uniqueDiffOn hmaps_uc hyc hbound0 hD
      rw [← iteratedFDerivWithin_of_isOpen 2 hopen_ax hyc]
      refine key.trans ?_
      have heq : ((2 : ℕ).factorial : ℝ) * Sbu * Buc ^ 2 =
          2 * (K0 + K1 + K2) * CU ^ 2 * u ^ 2 * ((1 + η) ^ 2 * ((1 + η) ^ 5)⁻¹) := by
        rw [hSbu_def, hBuc_def]
        norm_num [Nat.factorial]
        ring
      rw [heq, hw23]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK2_le_Kcomp (sq_nonneg u)) (by positivity)
  -- Assemble `Nv p.R (trainDeltaMerid p) τ` via `RingLiftOffAxisAux.clm_bound` and `smul_bound`
  have hmaps_ch : MapsTo (Axi.chart p.R τ) Axi.axisᶜ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
    fun z hz =>
      ⟨show (0 : ℝ) < (Axi.chart p.R τ z).1 from PartIIIb.Concrete.age_pos_of hR0 hz, trivial⟩
  have hbc : ContDiffOn ℝ ∞ (fun z => trainDeltaMerid p (Axi.chart p.R τ z)) Axi.axisᶜ :=
    hbΔ_cd.comp (ChartJetsAux.contDiffOn_chart hR0.ne' τ) hmaps_ch
  have hCsf_le : ∀ i ≤ j, Csf i ≤ Cq := by
    intro i hi
    have hi2 : i ≤ 2 := hi.trans hj
    rw [hCq_def]
    have h0 := (hCsf0 0).le; have h1 := (hCsf0 1).le; have h2 := (hCsf0 2).le
    interval_cases i <;> linarith only [h0, h1, h2]
  have hA_sf : ∀ i ≤ j, ‖iteratedFDerivWithin ℝ i (fun z => √(Axi.age p.R z)) Axi.axisᶜ y‖ ≤
      Cq * u := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hopen_ax hyc]
    have b := (hSF i p.R hR1 y hy).1
    rw [← hu] at b
    have hpow : u ^ (i + 1) ≤ u := pow_le_of_le_one hu0.le hu1 (Nat.succ_ne_zero i)
    exact b.trans ((mul_le_mul_of_nonneg_left hpow (hCsf0 i).le).trans
      (mul_le_mul_of_nonneg_right (hCsf_le i hi) hu0.le))
  have hB_sf : ∀ i ≤ j, ‖iteratedFDerivWithin ℝ i Axi.frameL Axi.axisᶜ y‖ ≤ Cq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hopen_ax hyc]
    have b := (hSF i p.R hR1 y hy).2
    rw [← hu] at b
    have hpow : u ^ i ≤ 1 := pow_le_one₀ hu0.le hu1
    calc _ ≤ Csf i * 1 := b.trans (mul_le_mul_of_nonneg_left hpow (hCsf0 i).le)
      _ = Csf i := mul_one _
      _ ≤ Cq := hCsf_le i hi
  obtain ⟨Bcomp, hBcomp_def⟩ : ∃ x : ℝ, x = Kcomp * u ^ 2 * ((1 + η) ^ 3)⁻¹ := ⟨_, rfl⟩
  have hBcomp0 : 0 ≤ Bcomp := by rw [hBcomp_def]; positivity
  have hGc : ∀ m ≤ j, ‖iteratedFDerivWithin ℝ m
      (fun z => Axi.frameL z (trainDeltaMerid p (Axi.chart p.R τ z))) Axi.axisᶜ y‖ ≤
      ((j : ℝ) + 1) * 2 ^ j * Cq * Bcomp := by
    intro m hm
    have h := RingLiftOffAxisAux.clm_bound (f := Axi.frameL)
      (g := fun z => trainDeltaMerid p (Axi.chart p.R τ z)) (n := m) (A := Cq) (B := Bcomp)
      ChartJetsAux.contDiffOn_frameL hbc hopen_ax.uniqueDiffOn hyc
      (fun i hi => hB_sf i (hi.trans hm))
      (fun i hi => hBcomp_def ▸ hcomp_bd i (hi.trans hm))
    refine h.trans ?_
    have hmono : ((m : ℝ) + 1) * 2 ^ m ≤ ((j : ℝ) + 1) * 2 ^ j := by
      have h1 : (m : ℝ) ≤ j := by exact_mod_cast hm
      have h2 : (2 : ℝ) ^ m ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hm
      exact mul_le_mul (by linarith only [h1]) h2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hCq0.le) hBcomp0
  have hSmul := RingLiftOffAxisAux.smul_bound (f := fun z => √(Axi.age p.R z))
    (g := fun z => Axi.frameL z (trainDeltaMerid p (Axi.chart p.R τ z))) (n := j)
    (A := Cq * u) (B := ((j : ℝ) + 1) * 2 ^ j * Cq * Bcomp)
    (ChartJetsAux.contDiffOn_sqrt_age hR0.ne') (ChartJetsAux.contDiffOn_frameL.clm_apply hbc)
    hopen_ax.uniqueDiffOn hyc hA_sf hGc
  have hNv_jet : ‖iteratedFDeriv ℝ j (Axi.Nv p.R (trainDeltaMerid p) τ) y‖ ≤
      C_nv * u ^ 3 * ((1 + η) ^ 3)⁻¹ := by
    rw [← iteratedFDerivWithin_of_isOpen j hopen_ax hyc, ChartJetsAux.Nv_eq_fun]
    have heq_rhs : ((j : ℝ) + 1) * 2 ^ j * (Cq * u) *
        (((j : ℝ) + 1) * 2 ^ j * Cq * Bcomp) = C_nv * u ^ 3 * ((1 + η) ^ 3)⁻¹ := by
      rw [hC_nv_def, hBcomp_def]
      ring
    exact hSmul.trans_eq heq_rhs
  have hgeom := RawAndInletIteratedDriftSub.one_add_norm_pow_mul_sqrt_age_pow_le 3
    hR0 zero_le_one hy hs1
  rw [← hu, ← hη] at hgeom
  have hp_eta : (1 + η) ^ 3 ≠ 0 := by positivity
  calc (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (Axi.Nv p.R (trainDeltaMerid p) τ) y‖
      ≤ (1 + ‖y‖) ^ 3 * (C_nv * u ^ 3 * ((1 + η) ^ 3)⁻¹) :=
        mul_le_mul_of_nonneg_left hNv_jet (by positivity)
    _ = C_nv * ((1 + ‖y‖) ^ 3 * u ^ 3) * ((1 + η) ^ 3)⁻¹ := by ring
    _ ≤ C_nv * ((1 + 1 + p.R) ^ 3 * (1 + η) ^ 3) * ((1 + η) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom hC_nv0) (by positivity)
    _ = C_nv * (1 + 1 + p.R) ^ 3 * ((1 + η) ^ 3 * ((1 + η) ^ 3)⁻¹) := by ring
    _ = C_nv * (1 + 1 + p.R) ^ 3 := by rw [mul_inv_cancel₀ hp_eta, mul_one]

end UnforcedLeray.Short.IIb.RawHeatAux
