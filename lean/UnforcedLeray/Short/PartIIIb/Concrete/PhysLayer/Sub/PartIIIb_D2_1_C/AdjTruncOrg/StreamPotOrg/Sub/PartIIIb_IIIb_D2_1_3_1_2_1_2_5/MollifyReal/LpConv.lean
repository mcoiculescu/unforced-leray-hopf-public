import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.MollifyReal.LpMem

/-!
# `L^p` convergence of mollification (`mollifyLpReal_holds : MollifyLp`)

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
Plan: for continuous compactly supported `g` the mollifications converge uniformly with supports
in a fixed ball, hence in `L^p`; general `f ∈ L^p` is approximated by such `g` in `L^p` and
the convolution is a contraction on `L^p` (`mollify_eLpNorm_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- A sequence with `u n ≤ ofReal η * K` eventually, for every `η > 0`, tends to `0`. -/
theorem mlr_tendsto_zero_of_ofReal_mul_le {u : ℕ → ℝ≥0∞} {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, u n ≤ ENNReal.ofReal η * K) :
    Tendsto u atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Eventually.of_forall fun n => le_top
  have hid : Tendsto (fun η : ℝ => η) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h1 : Tendsto (fun η : ℝ => ENNReal.ofReal η) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hid
  have hg : Tendsto (fun η : ℝ => ENNReal.ofReal η * K) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hK)
    simpa using this
  have hev : ∀ᶠ η in 𝓝[>] (0:ℝ), ENNReal.ofReal η * K < ε := hg.eventually (gt_mem_nhds hε)
  obtain ⟨η, hηlt, hηpos⟩ := (hev.and eventually_mem_nhdsWithin).exists
  exact (h η (Set.mem_Ioi.1 hηpos)).mono fun n hn => hn.trans hηlt.le

/-- Mollification of a field with compact support vanishes outside the ball of radius `R+1`
when the field vanishes outside the ball of radius `R`. -/
theorem mlr_mollify_eq_zero_of_far {ρ : ℕ → Space → ℝ} (hρ : IsMollifierFamily ρ)
    {g : Space → CVec3} {R : ℝ} (hR : ∀ y : Space, R < ‖y‖ → g y = 0) (n : ℕ)
    {x : Space} (hx : R + 1 < ‖x‖) : mollify (ρ n) g x = 0 := by
  unfold mollify
  apply integral_eq_zero_of_ae
  refine Eventually.of_forall fun z => ?_
  by_cases hz : ρ n z = 0
  · simp [hz]
  · have hzn : ‖z‖ ≤ 1 / ((n:ℝ) + 1) := (hρ n).2.2.2.2 z hz
    have hn1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hxz : R < ‖x - z‖ := by linarith [norm_sub_norm_le x z]
    simp [hR _ hxz]

/-- Pointwise integral form of `mollify ρ g - g` for continuous `g`, `ρ` with `∫ ρ = 1`. -/
theorem mlr_mollify_sub_eq_integral {ρ : Space → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρint : ∫ z : Space, ρ z = 1) {g : Space → CVec3}
    (hgc : Continuous g) (x : Space) :
    mollify ρ g x - g x = ∫ z : Space, ρ z • (g (x - z) - g x) := by
  have hi1 : Integrable (fun z : Space => ρ z • g (x - z)) volume := by
    have hloc : LocallyIntegrable (fun z : Space => g (x - z)) volume :=
      (hgc.comp (continuous_const.sub continuous_id)).locallyIntegrable
    exact LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hloc hρc hρs
  have hρi : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
  have hi2 : Integrable (fun z : Space => ρ z • g x) volume := hρi.smul_const (g x)
  have h1 : ∫ z : Space, ρ z • g (x - z) = mollify ρ g x := rfl
  have h2 : ∫ z : Space, ρ z • g x = g x := by
    rw [integral_smul_const, hρint, one_smul]
  calc mollify ρ g x - g x
      = (∫ z : Space, ρ z • g (x - z)) - ∫ z : Space, ρ z • g x := by rw [h1, h2]
    _ = ∫ z : Space, (ρ z • g (x - z) - ρ z • g x) := (integral_sub hi1 hi2).symm
    _ = ∫ z : Space, ρ z • (g (x - z) - g x) := by
        congr 1
        funext z
        simp [smul_sub]

/-- The integrand `z ↦ ρ z • f (x - z)` is integrable for `f` locally integrable and `ρ`
continuous with compact support. -/
theorem mlr_integrable_smul_translate {ρ : Space → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) {f : Space → CVec3} (hf : LocallyIntegrable f volume) (x : Space) :
    Integrable (fun z : Space => ρ z • f (x - z)) volume := by
  set K := tsupport ρ with hKdef
  have hK : IsCompact K := hρs
  have hS : IsCompact ((fun z : Space => x - z) '' K) :=
    hK.image (continuous_const.sub continuous_id)
  set F : Space → CVec3 := ((fun z : Space => x - z) '' K).indicator f with hFdef
  have hFint : Integrable F volume :=
    (hf.integrableOn_isCompact hS).integrable_indicator hS.measurableSet
  have hcomp : Integrable (fun z : Space => F (x - z)) volume :=
    (Measure.measurePreserving_sub_left volume x).integrable_comp_of_integrable hFint
  have heq : (fun z : Space => ρ z • f (x - z)) = (fun z : Space => ρ z • F (x - z)) := by
    funext z
    by_cases hz : z ∈ K
    · have hmem : x - z ∈ (fun z : Space => x - z) '' K := ⟨z, hz, rfl⟩
      simp [hFdef, Set.indicator_of_mem hmem]
    · have h0 : ρ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [h0]
  rw [heq]
  exact LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hcomp.locallyIntegrable hρc hρs

/-- Linearity of mollification in the field, for locally integrable fields. -/
theorem mlr_mollify_sub_apply {ρ : Space → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    {f g : Space → CVec3} (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (x : Space) :
    mollify ρ (f - g) x = mollify ρ f x - mollify ρ g x := by
  unfold mollify
  rw [← integral_sub (mlr_integrable_smul_translate hρc hρs hf x)
    (mlr_integrable_smul_translate hρc hρs hg x)]
  congr 1
  funext z
  simp [Pi.sub_apply, smul_sub]

/-- Uniform approximation: for `g` continuous with compact support, the mollifications are
within `δ` of `g` uniformly, for all large `n`. -/
theorem mlr_mollify_dist_le {ρ : ℕ → Space → ℝ} (hρ : IsMollifierFamily ρ) {g : Space → CVec3}
    (hgc : Continuous g) (hgs : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x : Space, dist (mollify (ρ n) g x) (g x) ≤ δ := by
  obtain ⟨η, hη, hηg⟩ :=
    Metric.uniformContinuous_iff.1 (hgs.uniformContinuous_of_continuous hgc) δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  refine ⟨N, fun n hn x => ?_⟩
  have hnN : 1 / ((n:ℝ) + 1) < η := by
    have h1 : (N:ℝ) ≤ n := by exact_mod_cast hn
    calc 1 / ((n:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
      _ < η := hN
  have hint : ∫ z : Space, ρ n z = 1 := (hρ n).2.2.2.1
  have hρc : Continuous (ρ n) := (hρ n).1.continuous
  have hρs : HasCompactSupport (ρ n) := (hρ n).2.1
  have hρi : Integrable (ρ n) volume := hρc.integrable_of_hasCompactSupport hρs
  rw [dist_eq_norm, mlr_mollify_sub_eq_integral hρc hρs hint hgc x]
  calc ‖∫ z : Space, ρ n z • (g (x - z) - g x)‖ ≤ ∫ z : Space, ρ n z * δ := by
        refine norm_integral_le_of_norm_le (hρi.mul_const δ) (ae_of_all _ fun z => ?_)
        by_cases hz : ρ n z = 0
        · simp [hz]
        · have hpos : 0 ≤ ρ n z := (hρ n).2.2.1 z
          rw [norm_smul, Real.norm_of_nonneg hpos]
          refine mul_le_mul_of_nonneg_left ?_ hpos
          have hzn : ‖z‖ ≤ 1 / ((n:ℝ) + 1) := (hρ n).2.2.2.2 z hz
          have hd : dist (x - z) x < η := by
            rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
            exact lt_of_le_of_lt hzn hnN
          rw [← dist_eq_norm]
          exact (hηg hd).le
    _ = δ := by rw [integral_mul_const, hint, one_mul]

/-- For `g` continuous with compact support, `mollify (ρ n) g - g → 0` in `L^p`. -/
theorem mlr_mollify_eLpNorm_sub_tendsto {ρ : ℕ → Space → ℝ} (hρ : IsMollifierFamily ρ)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) {g : Space → CVec3} (hgc : Continuous g)
    (hgs : HasCompactSupport g) :
    Tendsto (fun n => eLpNorm (mollify (ρ n) g - g) p volume) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y : Space, R < ‖y‖ → g y = 0 := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hgs.isCompact.isBounded
    refine ⟨C, fun y hy => image_eq_zero_of_notMem_tsupport (fun hmem => ?_)⟩
    exact absurd (hC y hmem) (not_le.2 hy)
  set s : Set Space := Metric.closedBall 0 (R + 1) with hsdef
  have hs : MeasurableSet s := measurableSet_closedBall
  have hVfin : volume s ≠ ⊤ := measure_closedBall_lt_top.ne
  have hKtop : volume s ^ (1 / p.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 ENNReal.toReal_nonneg) hVfin
  refine mlr_tendsto_zero_of_ofReal_mul_le hKtop fun η hη => ?_
  obtain ⟨N, hN⟩ := mlr_mollify_dist_le hρ hgc hgs hη
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsupp_g : Function.support g ⊆ s := by
    intro x hx
    simp only [hsdef, Metric.mem_closedBall, dist_zero_right]
    by_contra h
    push Not at h
    exact Function.mem_support.1 hx (hR x (by linarith))
  have hsupp_m : Function.support (mollify (ρ n) g) ⊆ s := by
    intro x hx
    simp only [hsdef, Metric.mem_closedBall, dist_zero_right]
    by_contra h
    push Not at h
    exact Function.mem_support.1 hx (mlr_mollify_eq_zero_of_far hρ hR n (by linarith))
  exact eLpNorm_sub_le_of_dist_bdd volume hp hs hη.le (fun x => hN n hn x) hsupp_m hsupp_g

theorem mollifyLpReal_holds : MollifyLp := by
  unfold MollifyLp
  intro ρ hρ p hp1 hpt f hf
  refine ⟨fun n => (mollify_eLpNorm_le (hρ n).1 (hρ n).2.1 (hρ n).2.2.1 (hρ n).2.2.2.1 hp1 hpt hf).1, ?_⟩
  refine mlr_tendsto_zero_of_ofReal_mul_le (K := 3) ENNReal.ofNat_ne_top fun η hη => ?_
  obtain ⟨g, hgs, hfg, hgc, hgL⟩ :=
    MemLp.exists_hasCompactSupport_eLpNorm_sub_le hpt hf (ENNReal.ofReal_pos.2 hη).ne'
  have hA := mlr_mollify_eLpNorm_sub_tendsto hρ hpt hgc hgs
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hA (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)]
    with n hn
  show eLpNorm (mollify (ρ n) f - f) p volume ≤ ENNReal.ofReal η * 3
  have hfL : LocallyIntegrable f volume := hf.locallyIntegrable hp1
  have hgLoc : LocallyIntegrable g volume := hgL.locallyIntegrable hp1
  have hρc : Continuous (ρ n) := (hρ n).1.continuous
  have hρs : HasCompactSupport (ρ n) := (hρ n).2.1
  have hid : mollify (ρ n) f - f
      = (mollify (ρ n) (f - g) - (f - g)) + (mollify (ρ n) g - g) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, mlr_mollify_sub_apply hρc hρs hfL hgLoc]
    abel
  have hfgM : MemLp (f - g) p volume := hf.sub hgL
  have hMA := mollify_eLpNorm_le (hρ n).1 (hρ n).2.1 (hρ n).2.2.1 (hρ n).2.2.2.1 hp1 hpt hfgM
  have hMg := (mollify_eLpNorm_le (hρ n).1 (hρ n).2.1 (hρ n).2.2.1 (hρ n).2.2.2.1 hp1 hpt hgL).1
  have hAm : AEStronglyMeasurable (mollify (ρ n) (f - g) - (f - g)) volume :=
    hMA.1.aestronglyMeasurable.sub hfgM.aestronglyMeasurable
  have hBm : AEStronglyMeasurable (mollify (ρ n) g - g) volume :=
    hMg.aestronglyMeasurable.sub hgL.aestronglyMeasurable
  have hA_le : eLpNorm (mollify (ρ n) (f - g) - (f - g)) p volume
      ≤ ENNReal.ofReal η + ENNReal.ofReal η := by
    calc eLpNorm (mollify (ρ n) (f - g) - (f - g)) p volume
        ≤ eLpNorm (mollify (ρ n) (f - g)) p volume + eLpNorm (f - g) p volume :=
          eLpNorm_sub_le hMA.1.aestronglyMeasurable hfgM.aestronglyMeasurable hp1
      _ ≤ ENNReal.ofReal η + ENNReal.ofReal η := add_le_add (hMA.2.trans hfg) hfg
  have hsum : eLpNorm (mollify (ρ n) f - f) p volume
      ≤ eLpNorm (mollify (ρ n) (f - g) - (f - g)) p volume
        + eLpNorm (mollify (ρ n) g - g) p volume := by
    rw [hid]
    exact eLpNorm_add_le hAm hBm hp1
  calc eLpNorm (mollify (ρ n) f - f) p volume
      ≤ eLpNorm (mollify (ρ n) (f - g) - (f - g)) p volume
        + eLpNorm (mollify (ρ n) g - g) p volume := hsum
    _ ≤ (ENNReal.ofReal η + ENNReal.ofReal η) + ENNReal.ofReal η := add_le_add hA_le hn
    _ = ENNReal.ofReal η * 3 := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
