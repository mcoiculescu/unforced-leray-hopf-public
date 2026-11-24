import UnforcedLeray.Short.PartIIb.Sub.PartIIb_B3_2_1
import UnforcedLeray.Units.B0418.Continuity
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartII-b:B3/2/1/2`: `StressColsContinuousH2` (`Tasks/HeatRemainderH2/StressCont.lean`)

Source of record: `the November 2 reference manuscript`, lines 2607-2612:
from `D^j U ∈ C_per L⁴` (`j ≤ 2`), deduce `𝕋 = U ⊗ U ∈ C_per H²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

namespace StressContAux

open UnforcedLeray.B0412 UnforcedLeray.Blueprint UnforcedLeray.SobolevGraph

local instance fact_one_le_four_sc : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

private theorem four_ne_top : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num

private theorem sliceFamily_memLp_four {V : ℝ → SpatialField}
    (hV : IsUniformSmoothL4SliceFamily V) (τ : ℝ) :
    MemLp (V τ) 4 volume := by
  obtain ⟨M, hM⟩ := hV.l4_bounded 0
  have heq : eLpNorm (fun y => iteratedFDeriv ℝ 0 (V τ) y) 4 volume =
      eLpNorm (V τ) 4 volume :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_iteratedFDeriv_zero)
  have h0 : eLpNorm (V τ) 4 volume ≤ ENNReal.ofReal M := heq ▸ hM τ
  exact ⟨(HigherPhaseSub.sliceFamily_contDiff_infty hV τ).continuous.aestronglyMeasurable,
    lt_of_le_of_lt h0 ENNReal.ofReal_lt_top⟩

private theorem contDiff_uncurry_dirSpatialJet {V : ℝ → SpatialField}
    (hV : ContDiff ℝ ∞ (fun p : ℝ × Space => V p.1 p.2)) :
    ∀ ws : List Space, ContDiff ℝ ∞ (fun p : ℝ × Space => dirSpatialJet (V p.1) ws p.2)
  | [] => hV
  | w :: ws => by
      have ih := contDiff_uncurry_dirSpatialJet hV ws
      have h_eq : (fun p : ℝ × Space => dirSpatialJet (V p.1) (w :: ws) p.2) =
          fun p : ℝ × Space =>
            fderiv ℝ (fun q : ℝ × Space => dirSpatialJet (V q.1) ws q.2) p (0, w) := by
        funext ⟨τ, y⟩
        have hd : DifferentiableAt ℝ (fun q : ℝ × Space => dirSpatialJet (V q.1) ws q.2) (τ, y) :=
          (contDiff_infty_iff_fderiv.1 ih).1 (τ, y)
        have hcomp : HasFDerivAt (fun y' : Space => dirSpatialJet (V τ) ws y')
            ((fderiv ℝ (fun q : ℝ × Space => dirSpatialJet (V q.1) ws q.2) (τ, y)).comp
              (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
          hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
        simp only [dirSpatialJet_cons, hcomp.fderiv, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inr_apply]
      rw [h_eq]
      exact (contDiff_infty_iff_fderiv.1 ih).2.clm_apply contDiff_const

private theorem continuous_comovingPullback_deriv {U U₁ : ℝ → SpatialField}
    (hU_smooth : ContDiff ℝ ∞ (fun p : ℝ × Space => U p.1 p.2))
    (hU : ∀ τ : ℝ, ContDiff ℝ ∞ (U τ))
    (hU₁ : ∀ τ : ℝ, ContDiff ℝ ∞ (U₁ τ))
    (hDeriv : HasComovingJetDeriv U U₁) (ws : List Space) :
    Continuous (fun p : ℝ × Space =>
      dirSpatialJet (JointSmoothSub.comovingPullback U₁ p.1) ws p.2) := by
  have hPb_smooth : ContDiff ℝ ∞ (fun p : ℝ × Space =>
      JointSmoothSub.comovingPullback U p.1 p.2) := by
    change ContDiff ℝ ∞ (fun p : ℝ × Space => U p.1 (Real.exp (-p.1 / 2) • p.2))
    exact hU_smooth.comp (contDiff_fst.prodMk
      (((contDiff_fst.neg.div_const (2 : ℝ)).exp).smul contDiff_snd))
  have hG_smooth := contDiff_uncurry_dirSpatialJet hPb_smooth ws
  let G_unc : ℝ × Space → Space :=
    fun p => dirSpatialJet (JointSmoothSub.comovingPullback U p.1) ws p.2
  have h_eq : (fun p : ℝ × Space =>
        dirSpatialJet (JointSmoothSub.comovingPullback U₁ p.1) ws p.2) =
      fun p : ℝ × Space => fderiv ℝ G_unc p (1, 0) := by
    funext ⟨τ, x⟩
    have hd : DifferentiableAt ℝ G_unc (τ, x) :=
      (contDiff_infty_iff_fderiv.1 hG_smooth).1 (τ, x)
    have h1 : HasDerivAt (fun τ' : ℝ => G_unc (τ', x)) (fderiv ℝ G_unc (τ, x) (1, 0)) τ := by
      have hc := hd.hasFDerivAt.comp_hasDerivAt τ
        ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ x))
      have hval : (fderiv ℝ G_unc (τ, x)) ((1 : ℝ), (0 : Space)) =
          (fderiv ℝ G_unc (τ, x)) ((1 : ℝ), (0 : Space)) := rfl
      exact hc
    have h2 : HasDerivAt (fun τ' : ℝ => G_unc (τ', x))
        (dirSpatialJet (JointSmoothSub.comovingPullback U₁ τ) ws x) τ :=
      JointSmoothSub.hasDerivAt_comovingPullback_dirSpatialJet hU hU₁ hDeriv ws τ x
    exact h2.unique h1
  rw [h_eq]
  exact ((contDiff_infty_iff_fderiv.1 hG_smooth).2.clm_apply contDiff_const).continuous

private theorem eLpNorm_comovingPullback_jet_le {V : ℝ → SpatialField}
    (hV : IsUniformSmoothL4SliceFamily V) (ws : List Space) (τ₀ : ℝ) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ s : ℝ, |s - τ₀| ≤ 1 →
      eLpNorm (dirSpatialJet (JointSmoothSub.comovingPullback V s) ws) 4 volume ≤ K := by
  have hVws := HigherPhaseSub.sliceFamily_dirSpatialJet hV ws
  obtain ⟨M, hM⟩ := hVws.l4_bounded 0
  let B : ℝ := max M 0
  let E₁ : ℝ := Real.exp ((|τ₀| + 1) / 2) ^ ws.length
  let E₂ : ℝ := Real.exp (3 * (|τ₀| + 1) / 2)
  let K : ℝ≥0∞ := ENNReal.ofReal E₁ * ((ENNReal.ofReal E₂) ^ (1 / (4 : ℝ≥0∞)).toReal *
    ENNReal.ofReal B)
  have hK_ne : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top)
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  refine ⟨K, hK_ne, fun s hs => ?_⟩
  have hs_lb : -s ≤ |τ₀| + 1 := by
    have h1 := (abs_le.1 hs).1
    have h2 := neg_le_abs τ₀
    linarith
  have hs_ub : s ≤ |τ₀| + 1 := by
    have h1 := (abs_le.1 hs).2
    have h2 := le_abs_self τ₀
    linarith
  have hfun : dirSpatialJet (JointSmoothSub.comovingPullback V s) ws =
      (Real.exp (-s / 2) ^ ws.length) •
        fun x => dirSpatialJet (V s) ws (Real.exp (-s / 2) • x) :=
    funext (JointSmoothSub.dirSpatialJet_comp_smul
      (HigherPhaseSub.sliceFamily_contDiff_infty hV s) (Real.exp (-s / 2)) ws)
  rw [hfun, eLpNorm_const_smul,
    B0418.eLpNorm_comp_dilation four_ne_top (Real.exp_pos (-s / 2)).ne']
  have hc1 : ‖Real.exp (-s / 2) ^ ws.length‖ₑ ≤ ENNReal.ofReal E₁ := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (pow_nonneg (Real.exp_nonneg _) _)]
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (Real.exp_nonneg _)
      (Real.exp_le_exp.2 (by linarith)) ws.length
  have hc2 : (ENNReal.ofReal |(Real.exp (-s / 2) ^ 3)⁻¹|) ^ (1 / (4 : ℝ≥0∞)).toReal ≤
      (ENNReal.ofReal E₂) ^ (1 / (4 : ℝ≥0∞)).toReal := by
    gcongr
    rw [abs_of_pos (inv_pos.2 (pow_pos (Real.exp_pos _) 3))]
    have hexp3 : (Real.exp (-s / 2) ^ 3)⁻¹ = Real.exp (3 * s / 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    rw [hexp3]
    exact Real.exp_le_exp.2 (by linarith)
  have hc3 : eLpNorm (dirSpatialJet (V s) ws) 4 volume ≤ ENNReal.ofReal B := by
    have heq : eLpNorm (fun y => iteratedFDeriv ℝ 0 (dirSpatialJet (V s) ws) y) 4 volume =
        eLpNorm (dirSpatialJet (V s) ws) 4 volume :=
      eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_iteratedFDeriv_zero)
    exact heq ▸ (hM s).trans (ENNReal.ofReal_le_ofReal (le_max_left M 0))
  exact mul_le_mul hc1 (mul_le_mul hc2 hc3 zero_le zero_le) zero_le zero_le

private theorem tendsto_eLpNorm_comovingPullback_sub {U U₁ : ℝ → SpatialField}
    (hU_smooth : ContDiff ℝ ∞ (fun p : ℝ × Space => U p.1 p.2))
    (hU : IsUniformSmoothL4SliceFamily U)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hDeriv : HasComovingJetDeriv U U₁) (ws : List Space) (τ₀ : ℝ) :
    Tendsto (fun τ : ℝ =>
      eLpNorm (dirSpatialJet (JointSmoothSub.comovingPullback U τ) ws -
        dirSpatialJet (JointSmoothSub.comovingPullback U τ₀) ws) 4 volume)
      (𝓝 τ₀) (𝓝 0) := by
  let G : ℝ → SpatialField := fun τ => dirSpatialJet (JointSmoothSub.comovingPullback U τ) ws
  let G' : ℝ → SpatialField := fun τ => dirSpatialJet (JointSmoothSub.comovingPullback U₁ τ) ws
  have hU_inf := HigherPhaseSub.sliceFamily_contDiff_infty hU
  have hU₁_inf := HigherPhaseSub.sliceFamily_contDiff_infty hU₁
  have hG'_cont : Continuous (fun p : ℝ × Space => G' p.1 p.2) :=
    continuous_comovingPullback_deriv hU_smooth hU_inf hU₁_inf hDeriv ws
  obtain ⟨K, hK_ne, hK⟩ := eLpNorm_comovingPullback_jet_le hU₁ ws τ₀
  have h_bound : ∀ᶠ τ : ℝ in 𝓝 τ₀, eLpNorm (G τ - G τ₀) 4 volume ≤
      K * ENNReal.ofReal |τ - τ₀| := by
    filter_upwards [Metric.closedBall_mem_nhds τ₀ zero_lt_one] with τ hτ
    have hτ1 : |τ - τ₀| ≤ 1 := by rwa [Metric.mem_closedBall, Real.dist_eq] at hτ
    have hpt : ∀ x : Space, ‖(G τ - G τ₀) x‖ₑ ≤ ‖∫⁻ s in uIoc τ₀ τ, ‖G' s x‖ₑ‖ₑ := by
      intro x
      rw [enorm_eq_self, Pi.sub_apply]
      have hFTC : ∫ s in τ₀..τ, G' s x = G τ x - G τ₀ x :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun s _ => JointSmoothSub.hasDerivAt_comovingPullback_dirSpatialJet
            hU_inf hU₁_inf hDeriv ws s x)
          ((hG'_cont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable τ₀ τ)
      rw [← hFTC]
      rcases le_total τ₀ τ with hle | hge
      · rw [intervalIntegral.integral_of_le hle, uIoc_of_le hle]
        exact enorm_integral_le_lintegral_enorm _
      · rw [intervalIntegral.integral_of_ge hge, uIoc_of_ge hge, enorm_neg]
        exact enorm_integral_le_lintegral_enorm _
    have hmeas : AEMeasurable (Function.uncurry fun (x : Space) (s : ℝ) => ‖G' s x‖ₑ)
        ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (uIoc τ₀ τ))) :=
      (hG'_cont.comp (continuous_snd.prodMk continuous_fst)).enorm.measurable.aemeasurable
    have hMink : eLpNorm (fun x : Space => ∫⁻ s in uIoc τ₀ τ, ‖G' s x‖ₑ) 4 volume ≤
        ∫⁻ s in uIoc τ₀ τ, eLpNorm (fun x : Space => ‖G' s x‖ₑ) 4 volume :=
      NonUniqueEuler.Conv.eLpNorm_lintegral_le hmeas (by norm_num) four_ne_top
    have h_uIoc : ∀ s ∈ uIoc τ₀ τ, |s - τ₀| ≤ 1 := by
      intro s hs
      rcases le_total τ₀ τ with hle | hge
      · rw [uIoc_of_le hle] at hs
        have h1 := (abs_le.1 hτ1).2
        rw [abs_le]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      · rw [uIoc_of_ge hge] at hs
        have h1 := (abs_le.1 hτ1).1
        rw [abs_le]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    calc eLpNorm (G τ - G τ₀) 4 volume
        ≤ eLpNorm (fun x : Space => ∫⁻ s in uIoc τ₀ τ, ‖G' s x‖ₑ) 4 volume :=
          eLpNorm_mono_enorm hpt
      _ ≤ ∫⁻ s in uIoc τ₀ τ, eLpNorm (fun x : Space => ‖G' s x‖ₑ) 4 volume := hMink
      _ ≤ ∫⁻ _s in uIoc τ₀ τ, K := by
          refine setLIntegral_mono measurable_const fun s hs => ?_
          rw [eLpNorm_enorm]
          exact hK s (h_uIoc s hs)
      _ = K * ENNReal.ofReal |τ - τ₀| := by
          rw [setLIntegral_const, Real.volume_uIoc, abs_sub_comm]
  have hlim : Tendsto (fun τ : ℝ => K * ENNReal.ofReal |τ - τ₀|) (𝓝 τ₀) (𝓝 0) := by
    have h0 : Tendsto (fun τ : ℝ => ENNReal.ofReal |τ - τ₀|) (𝓝 τ₀) (𝓝 0) := by
      have hc : Continuous (fun τ : ℝ => ENNReal.ofReal |τ - τ₀|) :=
        ENNReal.continuous_ofReal.comp (continuous_id.sub continuous_const).abs
      simpa using hc.tendsto τ₀
    have hm := ENNReal.Tendsto.const_mul h0 (Or.inr hK_ne)
    rwa [mul_zero] at hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) h_bound

private theorem continuous_dirSpatialJet_toLp {U U₁ : ℝ → SpatialField}
    (hU_smooth : ContDiff ℝ ∞ (fun p : ℝ × Space => U p.1 p.2))
    (hU : IsUniformSmoothL4SliceFamily U)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hDeriv : HasComovingJetDeriv U U₁) (ws : List Space) :
    let hmem : ∀ τ : ℝ, MemLp (dirSpatialJet (U τ) ws) 4 volume :=
      fun τ => sliceFamily_memLp_four (HigherPhaseSub.sliceFamily_dirSpatialJet hU ws) τ
    Continuous (fun τ : ℝ => (hmem τ).toLp (dirSpatialJet (U τ) ws)) := by
  intro hmem
  rw [continuous_iff_continuousAt]
  intro τ₀
  let F : ℝ → SpatialField := fun τ => dirSpatialJet (U τ) ws
  let G : ℝ → SpatialField := fun τ => dirSpatialJet (JointSmoothSub.comovingPullback U τ) ws
  let c : ℝ → ℝ := fun τ => Real.exp (τ / 2)
  let k : ℕ := ws.length
  have hU_inf := HigherPhaseSub.sliceFamily_contDiff_infty hU
  have hFG : ∀ τ : ℝ, F τ = fun y => (c τ ^ k) • G τ (c τ • y) := by
    intro τ
    funext y
    have h1 := JointSmoothSub.dirSpatialJet_comp_smul (hU_inf τ) (Real.exp (-τ / 2)) ws (c τ • y)
    have hsmul : Real.exp (-τ / 2) • (c τ • y) = y := by
      dsimp [c]
      rw [← mul_smul, ← Real.exp_add]
      have : -τ / 2 + τ / 2 = 0 := by ring
      rw [this, Real.exp_zero, one_smul]
    have hG_eq : G τ (c τ • y) = (Real.exp (-τ / 2) ^ k) • F τ y := by
      change dirSpatialJet (fun x' => U τ (Real.exp (-τ / 2) • x')) ws (c τ • y) =
        (Real.exp (-τ / 2) ^ ws.length) • dirSpatialJet (U τ) ws y
      rw [h1, hsmul]
    change F τ y = (c τ ^ k) • G τ (c τ • y)
    rw [hG_eq, smul_smul, ← mul_pow]
    have hmul : c τ * Real.exp (-τ / 2) = 1 := by
      dsimp [c]
      rw [← Real.exp_add]
      have : τ / 2 + -τ / 2 = 0 := by ring
      rw [this, Real.exp_zero]
    rw [hmul, one_pow, one_smul]
  have hG_mem : ∀ τ : ℝ, MemLp (G τ) 4 volume := by
    intro τ
    have heq : G τ = (Real.exp (-τ / 2) ^ k) • fun x => F τ (Real.exp (-τ / 2) • x) :=
      funext (JointSmoothSub.dirSpatialJet_comp_smul (hU_inf τ) (Real.exp (-τ / 2)) ws)
    rw [heq]
    exact (SpatialScaling.memLp_comp_dilation (hmem τ) (Real.exp_pos (-τ / 2)).ne').const_smul _
  -- Split `F τ - F τ₀ = D₁ τ + (D₂ τ + D₃ τ)`
  let D₁ : ℝ → SpatialField := fun τ y => (c τ ^ k) • (G τ (c τ • y) - G τ₀ (c τ • y))
  let D₂ : ℝ → SpatialField := fun τ y => (c τ ^ k - c τ₀ ^ k) • G τ₀ (c τ • y)
  let D₃ : ℝ → SpatialField := fun τ y => (c τ₀ ^ k) • (G τ₀ (c τ • y) - G τ₀ (c τ₀ • y))
  have hsplit : ∀ τ : ℝ, F τ - F τ₀ = D₁ τ + (D₂ τ + D₃ τ) := by
    intro τ
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, hFG τ, hFG τ₀, D₁, D₂, D₃, sub_smul, smul_sub]
    abel
  -- `D₁ τ → 0` in `L⁴`
  have hD₁ : Tendsto (fun τ : ℝ => eLpNorm (D₁ τ) 4 volume) (𝓝 τ₀) (𝓝 0) := by
    let C₁ : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((|τ₀| + 1) / 2) ^ k) *
      (ENNReal.ofReal (Real.exp (3 * (|τ₀| + 1) / 2))) ^ (1 / (4 : ℝ≥0∞)).toReal
    have hC₁_ne : C₁ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
    have h_le : ∀ᶠ τ : ℝ in 𝓝 τ₀, eLpNorm (D₁ τ) 4 volume ≤
        C₁ * eLpNorm (G τ - G τ₀) 4 volume := by
      filter_upwards [Metric.closedBall_mem_nhds τ₀ zero_lt_one] with τ hτ
      have hτ1 : |τ - τ₀| ≤ 1 := by rwa [Metric.mem_closedBall, Real.dist_eq] at hτ
      have hτ_ub : τ ≤ |τ₀| + 1 := by
        have := (abs_le.1 hτ1).2
        have := le_abs_self τ₀
        linarith
      have hτ_lb : -τ ≤ |τ₀| + 1 := by
        have := (abs_le.1 hτ1).1
        have := neg_le_abs τ₀
        linarith
      change eLpNorm ((c τ ^ k) • fun y => (G τ - G τ₀) (c τ • y)) 4 volume ≤ _
      rw [eLpNorm_const_smul, B0418.eLpNorm_comp_dilation four_ne_top (Real.exp_pos (τ / 2)).ne',
        ← mul_assoc]
      refine mul_le_mul ?_ le_rfl zero_le zero_le
      refine mul_le_mul ?_ ?_ zero_le zero_le
      · rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (pow_nonneg (Real.exp_nonneg _) _)]
        apply ENNReal.ofReal_le_ofReal
        exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.2 (by linarith)) k
      · gcongr
        rw [abs_of_pos (inv_pos.2 (pow_pos (Real.exp_pos _) 3))]
        have hexp3 : (c τ ^ 3)⁻¹ = Real.exp (3 * (-τ) / 2) := by
          dsimp [c]
          rw [← Real.exp_nat_mul, ← Real.exp_neg]
          congr 1; push_cast; ring
        rw [hexp3]
        exact Real.exp_le_exp.2 (by linarith)
    have hG_lim := tendsto_eLpNorm_comovingPullback_sub hU_smooth hU hU₁ hDeriv ws τ₀
    have hCG_lim : Tendsto (fun τ => C₁ * eLpNorm (G τ - G τ₀) 4 volume) (𝓝 τ₀) (𝓝 0) := by
      have hm := ENNReal.Tendsto.const_mul hG_lim (Or.inr hC₁_ne)
      rwa [mul_zero] at hm
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCG_lim
      (Eventually.of_forall fun _ => zero_le) h_le
  -- `D₂ τ → 0` in `L⁴`
  have hD₂ : Tendsto (fun τ : ℝ => eLpNorm (D₂ τ) 4 volume) (𝓝 τ₀) (𝓝 0) := by
    let C₂ : ℝ≥0∞ := (ENNReal.ofReal (Real.exp (3 * (|τ₀| + 1) / 2))) ^
      (1 / (4 : ℝ≥0∞)).toReal * eLpNorm (G τ₀) 4 volume
    have hC₂_ne : C₂ ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
        (hG_mem τ₀).eLpNorm_ne_top
    have h_le : ∀ᶠ τ : ℝ in 𝓝 τ₀, eLpNorm (D₂ τ) 4 volume ≤
        ENNReal.ofReal |c τ ^ k - c τ₀ ^ k| * C₂ := by
      filter_upwards [Metric.closedBall_mem_nhds τ₀ zero_lt_one] with τ hτ
      have hτ1 : |τ - τ₀| ≤ 1 := by rwa [Metric.mem_closedBall, Real.dist_eq] at hτ
      have hτ_lb : -τ ≤ |τ₀| + 1 := by
        have := (abs_le.1 hτ1).1
        have := neg_le_abs τ₀
        linarith
      change eLpNorm ((c τ ^ k - c τ₀ ^ k) • fun y => G τ₀ (c τ • y)) 4 volume ≤ _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
        B0418.eLpNorm_comp_dilation four_ne_top (Real.exp_pos (τ / 2)).ne']
      refine mul_le_mul le_rfl (mul_le_mul ?_ le_rfl zero_le zero_le) zero_le zero_le
      gcongr
      rw [abs_of_pos (inv_pos.2 (pow_pos (Real.exp_pos _) 3))]
      have hexp3 : (c τ ^ 3)⁻¹ = Real.exp (3 * (-τ) / 2) := by
        dsimp [c]
        rw [← Real.exp_nat_mul, ← Real.exp_neg]
        congr 1; push_cast; ring
      rw [hexp3]
      exact Real.exp_le_exp.2 (by linarith)
    have hc_cont : Continuous (fun τ : ℝ => ENNReal.ofReal |c τ ^ k - c τ₀ ^ k|) :=
      ENNReal.continuous_ofReal.comp
        ((((Real.continuous_exp.comp (continuous_id.div_const (2 : ℝ))).pow k).sub
          continuous_const).abs)
    have hc_lim : Tendsto (fun τ : ℝ => ENNReal.ofReal |c τ ^ k - c τ₀ ^ k| * C₂)
        (𝓝 τ₀) (𝓝 0) := by
      have h0 : Tendsto (fun τ : ℝ => ENNReal.ofReal |c τ ^ k - c τ₀ ^ k|) (𝓝 τ₀) (𝓝 0) := by
        simpa [c] using hc_cont.tendsto τ₀
      have hm := ENNReal.Tendsto.mul_const h0 (Or.inr hC₂_ne)
      rwa [zero_mul] at hm
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc_lim
      (Eventually.of_forall fun _ => zero_le) h_le
  -- `D₃ τ → 0` in `L⁴` via `B0418.tendsto_dilation`
  have hD₃ : Tendsto (fun τ : ℝ => eLpNorm (D₃ τ) 4 volume) (𝓝 τ₀) (𝓝 0) := by
    let φ₀ : SpatialField := fun y => G τ₀ (c τ₀ • y)
    have hφ₀ : MemLp φ₀ 4 volume :=
      SpatialScaling.memLp_comp_dilation (hG_mem τ₀) (Real.exp_pos (τ₀ / 2)).ne'
    have hdil := B0418.tendsto_dilation (p := 4) (by norm_num) four_ne_top hφ₀
    have hb_lim : Tendsto (fun τ : ℝ => Real.exp ((τ - τ₀) / 2)) (𝓝 τ₀) (𝓝 1) := by
      have hc_b : Continuous (fun τ : ℝ => Real.exp ((τ - τ₀) / 2)) :=
        Real.continuous_exp.comp ((continuous_id.sub continuous_const).div_const (2 : ℝ))
      simpa using hc_b.tendsto τ₀
    have hcomp := hdil.comp hb_lim
    have heq : ∀ τ : ℝ, eLpNorm (D₃ τ) 4 volume =
        ‖c τ₀ ^ k‖ₑ * eLpNorm (fun y => φ₀ (Real.exp ((τ - τ₀) / 2) • y) - φ₀ y) 4 volume := by
      intro τ
      have hfun : D₃ τ = (c τ₀ ^ k) • fun y => φ₀ (Real.exp ((τ - τ₀) / 2) • y) - φ₀ y := by
        funext y
        dsimp [D₃, φ₀, c]
        congr 2
        rw [← mul_smul, ← Real.exp_add]
        congr 2
        ring
      rw [hfun, eLpNorm_const_smul]
    simp_rw [heq]
    have hmul := ENNReal.Tendsto.const_mul hcomp (Or.inr (enorm_ne_top (x := c τ₀ ^ k)))
    rwa [mul_zero] at hmul
  -- Combine `D₁ + (D₂ + D₃)` and convert to `Lp` continuity
  have hF_lim : Tendsto (fun τ : ℝ => eLpNorm (F τ - F τ₀) 4 volume) (𝓝 τ₀) (𝓝 0) := by
    have h_tri : ∀ τ : ℝ, eLpNorm (F τ - F τ₀) 4 volume ≤
        eLpNorm (D₁ τ) 4 volume + (eLpNorm (D₂ τ) 4 volume + eLpNorm (D₃ τ) 4 volume) := by
      intro τ
      have hm1 : AEStronglyMeasurable (D₁ τ) volume := by
        have hd1 : D₁ τ = (c τ ^ k) •
            ((fun y => G τ (c τ • y)) - fun y => G τ₀ (c τ • y)) := rfl
        rw [hd1]
        exact (((SpatialScaling.memLp_comp_dilation (hG_mem τ) (Real.exp_pos (τ / 2)).ne').sub
          (SpatialScaling.memLp_comp_dilation (hG_mem τ₀) (Real.exp_pos (τ / 2)).ne')).const_smul
            (c τ ^ k)).aestronglyMeasurable
      have hm2 : AEStronglyMeasurable (D₂ τ) volume := by
        have hd2 : D₂ τ = (c τ ^ k - c τ₀ ^ k) • fun y => G τ₀ (c τ • y) := rfl
        rw [hd2]
        exact ((SpatialScaling.memLp_comp_dilation (hG_mem τ₀) (Real.exp_pos (τ / 2)).ne').const_smul
          (c τ ^ k - c τ₀ ^ k)).aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (D₃ τ) volume := by
        have hd3 : D₃ τ = (c τ₀ ^ k) •
            ((fun y => G τ₀ (c τ • y)) - fun y => G τ₀ (c τ₀ • y)) := rfl
        rw [hd3]
        exact (((SpatialScaling.memLp_comp_dilation (hG_mem τ₀) (Real.exp_pos (τ / 2)).ne').sub
          (SpatialScaling.memLp_comp_dilation (hG_mem τ₀) (Real.exp_pos (τ₀ / 2)).ne')).const_smul
            (c τ₀ ^ k)).aestronglyMeasurable
      rw [hsplit τ]
      exact (eLpNorm_add_le hm1 (hm2.add hm3) (by norm_num)).trans
        (add_le_add le_rfl (eLpNorm_add_le hm2 hm3 (by norm_num)))
    have hsum_lim : Tendsto (fun τ : ℝ =>
        eLpNorm (D₁ τ) 4 volume + (eLpNorm (D₂ τ) 4 volume + eLpNorm (D₃ τ) 4 volume))
        (𝓝 τ₀) (𝓝 0) := by
      have hs := hD₁.add (hD₂.add hD₃)
      simpa only [add_zero] using hs
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum_lim
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall h_tri)
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  change Tendsto (fun τ : ℝ => dist ((hmem τ).toLp (F τ)) ((hmem τ₀).toLp (F τ₀))) (𝓝 τ₀) (𝓝 0)
  have hdist : ∀ τ : ℝ, dist ((hmem τ).toLp (F τ)) ((hmem τ₀).toLp (F τ₀)) =
      (eLpNorm (F τ - F τ₀) 4 volume).toReal := by
    intro τ
    rw [Lp.dist_def, eLpNorm_congr_ae ((hmem τ).coeFn_toLp.sub (hmem τ₀).coeFn_toLp)]
  simp_rw [hdist]
  have htoReal : Tendsto ENNReal.toReal (𝓝 (0 : ℝ≥0∞)) (𝓝 (0 : ℝ≥0∞).toReal) :=
    ENNReal.tendsto_toReal ENNReal.zero_ne_top
  rw [ENNReal.toReal_zero] at htoReal
  exact htoReal.comp hF_lim

private theorem eLpNorm_coord_smul_le {A B : SpatialField}
    (hA : AEStronglyMeasurable A volume) (hB : AEStronglyMeasurable B volume) (m : Fin 3) :
    eLpNorm (fun y : Space => (A y m) • B y) 2 volume ≤
      eLpNorm A 4 volume * eLpNorm B 4 volume := by
  have holder : ENNReal.HolderTriple 4 4 2 := by
    apply ENNReal.HolderTriple.of_toReal
    norm_num [Real.holderTriple_iff]
  have h1 := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    hA.norm hB.norm (fun x y : ℝ => x * y) (1 : ℝ≥0)
    (Eventually.of_forall fun y => by
      rw [norm_mul, NNReal.coe_one, one_mul])
    (hpqr := holder)
  rw [ENNReal.coe_one, one_mul, eLpNorm_norm, eLpNorm_norm] at h1
  refine (eLpNorm_mono_real fun y => ?_).trans h1
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (A y) m)
    (norm_nonneg _)

private theorem continuous_toL2_coord_smul {A B : ℝ → SpatialField}
    (hAc : ∀ τ : ℝ, Continuous (A τ)) (hBc : ∀ τ : ℝ, Continuous (B τ))
    (hA : ∀ τ : ℝ, MemLp (A τ) 4 volume) (hB : ∀ τ : ℝ, MemLp (B τ) 4 volume)
    (hA_cont : Continuous (fun τ : ℝ => (hA τ).toLp (A τ)))
    (hB_cont : Continuous (fun τ : ℝ => (hB τ).toLp (B τ)))
    (m : Fin 3) :
    Continuous (fun τ : ℝ => toL2 (fun y : Space => (A τ y m) • B τ y)) := by
  let P : ℝ → SpatialField := fun τ y => (A τ y m) • B τ y
  have hP_cont : ∀ τ : ℝ, Continuous (P τ) := fun τ =>
    ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp (hAc τ)).smul (hBc τ)
  have hP_mem : ∀ τ : ℝ, MemLp (P τ) 2 volume := fun τ => by
    have hbd : eLpNorm (P τ) 2 volume ≤ eLpNorm (A τ) 4 volume * eLpNorm (B τ) 4 volume :=
      eLpNorm_coord_smul_le (hAc τ).aestronglyMeasurable (hBc τ).aestronglyMeasurable m
    exact ⟨(hP_cont τ).aestronglyMeasurable,
      lt_of_le_of_lt hbd (ENNReal.mul_lt_top (hA τ).2 (hB τ).2)⟩
  rw [continuous_iff_continuousAt]
  intro τ₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hdist_le : ∀ τ : ℝ, dist (toL2 (P τ)) (toL2 (P τ₀)) ≤
      dist ((hA τ).toLp (A τ)) ((hA τ₀).toLp (A τ₀)) * ‖(hB τ).toLp (B τ)‖ +
        ‖(hA τ₀).toLp (A τ₀)‖ * dist ((hB τ).toLp (B τ)) ((hB τ₀).toLp (B τ₀)) := by
    intro τ
    rw [Lp.dist_def, eLpNorm_congr_ae (coeFn_toL2 (hP_mem τ) |>.sub (coeFn_toL2 (hP_mem τ₀)))]
    let P₁ : SpatialField := fun y => ((A τ - A τ₀) y m) • B τ y
    let P₂ : SpatialField := fun y => (A τ₀ y m) • (B τ - B τ₀) y
    have hdecomp : P τ - P τ₀ = P₁ + P₂ := by
      funext y
      simp only [P, P₁, P₂, Pi.sub_apply, Pi.add_apply, PiLp.sub_apply, sub_smul, smul_sub]
      abel
    have hm1 : AEStronglyMeasurable P₁ volume :=
      (((EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp
        ((hAc τ).sub (hAc τ₀))).smul (hBc τ)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable P₂ volume :=
      (((EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp
        (hAc τ₀)).smul ((hBc τ).sub (hBc τ₀))).aestronglyMeasurable
    have hb1 := eLpNorm_coord_smul_le ((hAc τ).sub (hAc τ₀)).aestronglyMeasurable
      (hBc τ).aestronglyMeasurable m
    have hb2 := eLpNorm_coord_smul_le (hAc τ₀).aestronglyMeasurable
      ((hBc τ).sub (hBc τ₀)).aestronglyMeasurable m
    have hfin1 : eLpNorm (A τ - A τ₀) 4 volume * eLpNorm (B τ) 4 volume ≠ ⊤ :=
      ENNReal.mul_ne_top ((hA τ).sub (hA τ₀)).eLpNorm_ne_top (hB τ).eLpNorm_ne_top
    have hfin2 : eLpNorm (A τ₀) 4 volume * eLpNorm (B τ - B τ₀) 4 volume ≠ ⊤ :=
      ENNReal.mul_ne_top (hA τ₀).eLpNorm_ne_top ((hB τ).sub (hB τ₀)).eLpNorm_ne_top
    have he : eLpNorm (P τ - P τ₀) 2 volume ≤
        eLpNorm (A τ - A τ₀) 4 volume * eLpNorm (B τ) 4 volume +
          eLpNorm (A τ₀) 4 volume * eLpNorm (B τ - B τ₀) 4 volume := by
      rw [hdecomp]
      exact (eLpNorm_add_le hm1 hm2 (by norm_num)).trans (add_le_add hb1 hb2)
    have hto := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩) he
    rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_mul] at hto
    have hdA : dist ((hA τ).toLp (A τ)) ((hA τ₀).toLp (A τ₀)) =
        (eLpNorm (A τ - A τ₀) 4 volume).toReal := by
      rw [Lp.dist_def, eLpNorm_congr_ae ((hA τ).coeFn_toLp.sub (hA τ₀).coeFn_toLp)]
    have hdB : dist ((hB τ).toLp (B τ)) ((hB τ₀).toLp (B τ₀)) =
        (eLpNorm (B τ - B τ₀) 4 volume).toReal := by
      rw [Lp.dist_def, eLpNorm_congr_ae ((hB τ).coeFn_toLp.sub (hB τ₀).coeFn_toLp)]
    have hnB : ‖(hB τ).toLp (B τ)‖ = (eLpNorm (B τ) 4 volume).toReal := Lp.norm_toLp _ _
    have hnA : ‖(hA τ₀).toLp (A τ₀)‖ = (eLpNorm (A τ₀) 4 volume).toReal := Lp.norm_toLp _ _
    rwa [hdA, hdB, hnB, hnA]
  have hA0 : Tendsto (fun τ => dist ((hA τ).toLp (A τ)) ((hA τ₀).toLp (A τ₀))) (𝓝 τ₀) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 hA_cont.continuousAt
  have hB0 : Tendsto (fun τ => dist ((hB τ).toLp (B τ)) ((hB τ₀).toLp (B τ₀))) (𝓝 τ₀) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 hB_cont.continuousAt
  have hBn : Tendsto (fun τ => ‖(hB τ).toLp (B τ)‖) (𝓝 τ₀) (𝓝 ‖(hB τ₀).toLp (B τ₀)‖) :=
    (continuous_norm.comp hB_cont).continuousAt
  have hrhs : Tendsto (fun τ =>
      dist ((hA τ).toLp (A τ)) ((hA τ₀).toLp (A τ₀)) * ‖(hB τ).toLp (B τ)‖ +
        ‖(hA τ₀).toLp (A τ₀)‖ * dist ((hB τ).toLp (B τ)) ((hB τ₀).toLp (B τ₀)))
      (𝓝 τ₀) (𝓝 0) := by
    simpa using (hA0.mul hBn).add (hB0.const_mul _)
  exact squeeze_zero (fun _ => dist_nonneg) hdist_le hrhs

end StressContAux

theorem stressColsContinuousH2_proof : UnforcedLeray.Short.IIb.StressColsContinuousH2 := by
  intro U hU_smooth hU ⟨U₁, hU₁, hDeriv⟩ C hf h0 h1 h2
  have : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  open UnforcedLeray.Blueprint UnforcedLeray.SobolevGraph in
  refine continuous_pi fun m => ?_
  rw [← continuousOn_univ, H2.continuousOn_iff_components]
  simp_rw [continuousOn_univ]
  have hJet_cont_fn : ∀ (ws : List Space) (τ : ℝ), Continuous (dirSpatialJet (U τ) ws) :=
    fun ws τ => (JointSmoothSub.contDiff_infty_dirSpatialJet
      (HigherPhaseSub.sliceFamily_contDiff_infty hU τ) ws).continuous
  let hmem : ∀ (ws : List Space) (τ : ℝ), MemLp (dirSpatialJet (U τ) ws) 4 volume :=
    fun ws τ => StressContAux.sliceFamily_memLp_four
      (HigherPhaseSub.sliceFamily_dirSpatialJet hU ws) τ
  have hLp_cont : ∀ ws : List Space,
      Continuous (fun τ : ℝ => (hmem ws τ).toLp (dirSpatialJet (U τ) ws)) :=
    fun ws => StressContAux.continuous_dirSpatialJet_toLp hU_smooth hU hU₁ hDeriv ws
  have hProd_cont : ∀ ws₁ ws₂ : List Space,
      Continuous (fun τ : ℝ =>
        toL2 (fun y : Space => (dirSpatialJet (U τ) ws₁ y m) • dirSpatialJet (U τ) ws₂ y)) :=
    fun ws₁ ws₂ => StressContAux.continuous_toL2_coord_smul
      (hJet_cont_fn ws₁) (hJet_cont_fn ws₂) (hmem ws₁) (hmem ws₂)
      (hLp_cont ws₁) (hLp_cont ws₂) m
  have hProd_mem : ∀ (ws₁ ws₂ : List Space) (τ : ℝ),
      MemLp (fun y : Space => (dirSpatialJet (U τ) ws₁ y m) • dirSpatialJet (U τ) ws₂ y)
        2 volume := by
    intro ws₁ ws₂ τ
    have hbd := StressContAux.eLpNorm_coord_smul_le
      (hJet_cont_fn ws₁ τ).aestronglyMeasurable (hJet_cont_fn ws₂ τ).aestronglyMeasurable m
    exact ⟨(((EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp
        (hJet_cont_fn ws₁ τ)).smul (hJet_cont_fn ws₂ τ)).aestronglyMeasurable,
      lt_of_le_of_lt hbd (ENNReal.mul_lt_top (hmem ws₁ τ).2 (hmem ws₂ τ).2)⟩
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · -- `.value`
    have heq : (fun τ : ℝ => (B3RemH2Sub.stressColH2 (U τ) (hf τ) (h0 τ) (h1 τ) (h2 τ) m).value) =
        fun τ : ℝ => toL2 (fun y => (dirSpatialJet (U τ) [] y m) • dirSpatialJet (U τ) [] y) :=
      rfl
    rw [heq]
    exact hProd_cont [] []
  · -- `.first i`
    let wᵢ : List Space := [coordinateVector i]
    have heq : (fun τ : ℝ =>
          (B3RemH2Sub.stressColH2 (U τ) (hf τ) (h0 τ) (h1 τ) (h2 τ) m).first i) =
        fun τ : ℝ =>
          toL2 (fun y => (dirSpatialJet (U τ) wᵢ y m) • dirSpatialJet (U τ) [] y) +
            toL2 (fun y => (dirSpatialJet (U τ) [] y m) • dirSpatialJet (U τ) wᵢ y) := by
      funext τ
      change toL2 (L10.dpart (B3RemH2Sub.stressCol (U τ) m) i) = _
      have hf1 : ContDiff ℝ 1 (U τ) := (hf τ).of_le (by norm_num)
      have hfn : L10.dpart (B3RemH2Sub.stressCol (U τ) m) i =
          (fun y => (dirSpatialJet (U τ) wᵢ y m) • dirSpatialJet (U τ) [] y) +
            fun y => (dirSpatialJet (U τ) [] y m) • dirSpatialJet (U τ) wᵢ y :=
        funext (B3RemH2Sub.dpart_stressCol hf1 m i)
      rw [hfn, L10.toL2_add' (hProd_mem wᵢ [] τ) (hProd_mem [] wᵢ τ)]
    rw [heq]
    exact (hProd_cont wᵢ []).add (hProd_cont [] wᵢ)
  · -- `.second i j`
    let wᵢ : List Space := [coordinateVector i]
    let wⱼ : List Space := [coordinateVector j]
    let wⱼᵢ : List Space := [coordinateVector j, coordinateVector i]
    have heq : (fun τ : ℝ =>
          (B3RemH2Sub.stressColH2 (U τ) (hf τ) (h0 τ) (h1 τ) (h2 τ) m).second i j) =
        fun τ : ℝ =>
          ((toL2 (fun y => (dirSpatialJet (U τ) wⱼᵢ y m) • dirSpatialJet (U τ) [] y) +
              toL2 (fun y => (dirSpatialJet (U τ) wᵢ y m) • dirSpatialJet (U τ) wⱼ y)) +
            toL2 (fun y => (dirSpatialJet (U τ) wⱼ y m) • dirSpatialJet (U τ) wᵢ y)) +
          toL2 (fun y => (dirSpatialJet (U τ) [] y m) • dirSpatialJet (U τ) wⱼᵢ y) := by
      funext τ
      change toL2 (L10.dpart (L10.dpart (B3RemH2Sub.stressCol (U τ) m) i) j) = _
      let p1 : SpatialField := fun y => (dirSpatialJet (U τ) wⱼᵢ y m) • dirSpatialJet (U τ) [] y
      let p2 : SpatialField := fun y => (dirSpatialJet (U τ) wᵢ y m) • dirSpatialJet (U τ) wⱼ y
      let p3 : SpatialField := fun y => (dirSpatialJet (U τ) wⱼ y m) • dirSpatialJet (U τ) wᵢ y
      let p4 : SpatialField := fun y => (dirSpatialJet (U τ) [] y m) • dirSpatialJet (U τ) wⱼᵢ y
      have hfn : L10.dpart (L10.dpart (B3RemH2Sub.stressCol (U τ) m) i) j =
          ((p1 + p2) + p3) + p4 :=
        funext (B3RemH2Sub.dpart_dpart_stressCol (hf τ) m i j)
      have m1 := hProd_mem wⱼᵢ [] τ
      have m2 := hProd_mem wᵢ wⱼ τ
      have m3 := hProd_mem wⱼ wᵢ τ
      have m4 := hProd_mem [] wⱼᵢ τ
      rw [hfn, L10.toL2_add' ((m1.add m2).add m3) m4,
        L10.toL2_add' (m1.add m2) m3, L10.toL2_add' m1 m2]
    rw [heq]
    exact (((hProd_cont wⱼᵢ []).add (hProd_cont wᵢ wⱼ)).add (hProd_cont wⱼ wᵢ)).add
      (hProd_cont [] wⱼᵢ)

end UnforcedLeray.Short.IIb

end
