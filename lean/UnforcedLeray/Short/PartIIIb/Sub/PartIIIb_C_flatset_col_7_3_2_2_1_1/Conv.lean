import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_1.Weight

/-!
# Convergence on the class `s^{3/4} φ` (tex lines 1650-1656)

For `φ` continuous with compact support and `ψ = s^{3/4} φ`, the identity
`‖D_a ψ - ψ‖_H = ‖a^{3/4} φ(a s, ·) - φ‖_{L²(cellMeasure c)}` (weight `s^{-3/4}` of
`Weight.lean`) reduces `D_{e^{-s}} ψ → ψ` to a dominated-convergence statement
(`tendsto_eLpNorm_profile_dil`, same proof pattern as `B0223.tendsto_eLpNorm_dil_sub`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.DilStrong

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure cell)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0224 (dilH coeFn_dilH dil_congr_ae eLpNorm_two_eq)
open UnforcedLeray.Short.PartIIIb.Concrete.DilWeight

theorem tendsto_eLpNorm_profile_dil {c : ℝ} {g : Profile → MeridC} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun a : ℝ => eLpNorm (fun p : Profile => a ^ (3 / 4 : ℝ) • g (a * p.1, p.2) - g p)
      2 (cellMeasure c)) (𝓝 1) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Profile)
  have hzero : ∀ z : Profile, |R| < ‖z‖ → g z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hR (subset_tsupport g hne)
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith [le_abs_self R]
  have hcoord : ∀ z : Profile, ‖z.1‖ ≤ ‖z‖ ∧ ‖z.2.1‖ ≤ ‖z‖ ∧ ‖z.2.2‖ ≤ ‖z‖ :=
    fun z => ⟨norm_fst_le z, (norm_fst_le z.2).trans (norm_snd_le z),
      (norm_snd_le z.2).trans (norm_snd_le z)⟩
  have key : ∀ z : Profile, g z ≠ 0 → ‖z‖ ≤ |R| := fun z hz =>
    not_lt.1 (fun h => hz (hzero z h))
  set K : Set Profile := Metric.closedBall (0 : ℝ) (2 * |R|) ×ˢ
    (Metric.closedBall (0 : ℝ) (2 * |R|) ×ˢ Metric.closedBall (0 : ℝ) (2 * |R|)) with hK
  have hKm : MeasurableSet K :=
    measurableSet_closedBall.prod (measurableSet_closedBall.prod measurableSet_closedBall)
  have hKf : cellMeasure c K < ∞ := by
    show (volume.restrict (cell c)) K < ∞
    refine lt_of_le_of_lt (Measure.restrict_apply_le _ _) ?_
    rw [hK, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_closedBall_lt_top
      (ENNReal.mul_lt_top measure_closedBall_lt_top measure_closedBall_lt_top)
  have hmemK : ∀ p : Profile, ‖p.1‖ ≤ 2 * |R| → ‖p.2.1‖ ≤ 2 * |R| → ‖p.2.2‖ ≤ 2 * |R| →
      p ∈ K := by
    intro p h1 h2 h3
    rw [hK]
    exact ⟨Metric.mem_closedBall.2 (by simpa using h1),
      Metric.mem_closedBall.2 (by simpa using h2), Metric.mem_closedBall.2 (by simpa using h3)⟩
  have hout : ∀ a : ℝ, 1 / 2 < a → ∀ p : Profile, p ∉ K → g p = 0 ∧ g (a * p.1, p.2) = 0 := by
    intro a ha p hp
    constructor
    · by_contra hne
      apply hp
      have h1 := key p hne
      have h2 := hcoord p
      exact hmemK p (by linarith [abs_nonneg R]) (by linarith [abs_nonneg R])
        (by linarith [abs_nonneg R])
    · by_contra hne
      apply hp
      have h1 := key _ hne
      have h2 : ‖a * p.1‖ ≤ |R| := (norm_fst_le (a * p.1, p.2)).trans h1
      have h3 : ‖a * p.1‖ = a * ‖p.1‖ := by
        rw [norm_mul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ a)]
      have h4 : ‖p.1‖ ≤ 2 * |R| := by
        nlinarith [norm_nonneg p.1, abs_nonneg R]
      have h5 : ‖p.2‖ ≤ |R| := (norm_snd_le (a * p.1, p.2)).trans h1
      exact hmemK p h4 ((norm_fst_le p.2).trans (by linarith [abs_nonneg R]))
        ((norm_snd_le p.2).trans (by linarith [abs_nonneg R]))
  have hnear : ∀ᶠ a : ℝ in 𝓝 1, 1 / 2 < a ∧ a < 2 :=
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)).and (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have hlim : Tendsto (fun a : ℝ => ∫⁻ p : Profile,
      ‖a ^ (3 / 4 : ℝ) • g (a * p.1, p.2) - g p‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(cellMeasure c))
      (𝓝 1) (𝓝 (∫⁻ _p : Profile, (0 : ℝ≥0∞) ∂(cellMeasure c))) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (K.indicator fun _ => (ENNReal.ofReal (3 * M)) ^ (2 : ℝ≥0∞).toReal) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun a => ?_
      have hq : Continuous fun p : Profile => (a * p.1, p.2) :=
        (continuous_const.mul continuous_fst).prodMk continuous_snd
      have hc : Continuous fun p : Profile => a ^ (3 / 4 : ℝ) • g (a * p.1, p.2) - g p :=
        ((hg.comp hq).const_smul (a ^ (3 / 4 : ℝ))).sub hg
      exact hc.enorm.measurable.pow_const _
    · filter_upwards [hnear] with a ha
      refine Eventually.of_forall fun p => ?_
      by_cases hp : p ∈ K
      · rw [Set.indicator_of_mem hp]
        gcongr
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        have hb32 : a ^ (3 / 4 : ℝ) ≤ 2 := by
          calc a ^ (3 / 4 : ℝ) ≤ 2 ^ (3 / 4 : ℝ) :=
                Real.rpow_le_rpow (by linarith [ha.1]) ha.2.le (by norm_num)
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        calc ‖a ^ (3 / 4 : ℝ) • g (a * p.1, p.2) - g p‖
            ≤ ‖a ^ (3 / 4 : ℝ) • g (a * p.1, p.2)‖ + ‖g p‖ := norm_sub_le _ _
          _ = a ^ (3 / 4 : ℝ) * ‖g (a * p.1, p.2)‖ + ‖g p‖ := by
              rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [ha.1]) _)]
          _ ≤ 2 * M + M :=
              add_le_add (mul_le_mul hb32 (hM _) (norm_nonneg _) (by norm_num)) (hM _)
          _ = 3 * M := by ring
      · rw [Set.indicator_of_notMem hp]
        obtain ⟨h1, h2⟩ := hout a ha.1 p hp
        rw [h1, h2, smul_zero, sub_zero, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    · rw [lintegral_indicator hKm, setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hKf.ne
    · refine Eventually.of_forall fun p => ?_
      have h1 : Tendsto (fun a : ℝ => a ^ (3 / 4 : ℝ) • g (a * p.1, p.2) - g p) (𝓝 1) (𝓝 0) := by
        have hc : Continuous fun a : ℝ => a ^ (3 / 4 : ℝ) • g (a * p.1, p.2) - g p :=
          ((Real.continuous_rpow_const (by norm_num)).smul (hg.comp
            ((continuous_id.mul continuous_const).prodMk continuous_const))).sub continuous_const
        have := hc.tendsto 1
        simpa using this
      have h2 := (continuous_enorm.tendsto (0 : MeridC)).comp h1
      rw [enorm_zero] at h2
      have h3 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      exact h3
  rw [lintegral_zero] at hlim
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h4

theorem scaled_profile_measurable {a : ℝ} {phi : Profile → MeridC} (hcont : Continuous phi) :
    StronglyMeasurable (fun p : Profile => (a * p.1) ^ (3 / 4 : ℝ) • phi (a * p.1, p.2) -
      p.1 ^ (3 / 4 : ℝ) • phi p) := by
  have hm1 : Measurable fun p : Profile => (a * p.1) ^ (3 / 4 : ℝ) :=
    ((measurable_fst.const_mul a)).pow_const _
  have hm2 : Measurable fun p : Profile => phi (a * p.1, p.2) :=
    hcont.measurable.comp ((measurable_fst.const_mul a).prodMk measurable_snd)
  have hm3 : Measurable fun p : Profile => p.1 ^ (3 / 4 : ℝ) := measurable_fst.pow_const _
  exact (hm1.stronglyMeasurable.smul hm2.stronglyMeasurable).sub
    (hm3.stronglyMeasurable.smul hcont.measurable.stronglyMeasurable)

theorem dilH_sub_norm {c : ℝ} (phi : Profile → MeridC) (hcont : Continuous phi)
    (hψ : MemLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p) 2 (measureH c)) {a : ℝ}
    (ha : 0 < a) :
    ‖dilH ha (hψ.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p)) -
        hψ.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p)‖ =
      (eLpNorm (fun p : Profile => a ^ (3 / 4 : ℝ) • phi (a * p.1, p.2) - phi p) 2
        (cellMeasure c)).toReal := by
  have hWsm : StronglyMeasurable (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p) :=
    (measurable_fst.pow_const _).stronglyMeasurable.smul hcont.measurable.stronglyMeasurable
  have hae : ⇑(dilH ha (hψ.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p)) -
      hψ.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p)) =ᵐ[measureH c]
      fun p : Profile => (a * p.1) ^ (3 / 4 : ℝ) • phi (a * p.1, p.2) -
        p.1 ^ (3 / 4 : ℝ) • phi p := by
    filter_upwards [Lp.coeFn_sub (dilH ha (hψ.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p)))
        (hψ.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p)),
      coeFn_dilH ha (hψ.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p)),
      dil_congr_ae ha (Lp.stronglyMeasurable (hψ.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p)))
        hWsm (MemLp.coeFn_toLp hψ),
      MemLp.coeFn_toLp hψ] with p h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4]
    rfl
  rw [Lp.norm_def]
  congr 1
  refine (eLpNorm_congr_ae hae).trans ?_
  refine (eLpNorm_measureH_eq_weighted (scaled_profile_measurable (a := a) hcont)).trans ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)] with p hp
  exact scale_identity (show 0 < p.1 from hp.1) ha _ _

theorem dilGoodConv_holds (c : ℝ) (hc : 0 < c) : UnforcedLeray.Short.PartIIIb.Concrete.DilStrong.DilGoodConv c := by
  intro phi hcont hsupp hψ
  have hlim := tendsto_eLpNorm_profile_dil (c := c) hcont hsupp
  have hreal : Tendsto (fun a : ℝ => (eLpNorm (fun p : Profile => a ^ (3 / 4 : ℝ) •
      phi (a * p.1, p.2) - phi p) 2 (cellMeasure c)).toReal) (𝓝 1) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    rw [ENNReal.toReal_zero] at this
    exact this
  have hexp : Tendsto (fun s : ℝ => Real.exp (-s)) (nhdsWithin 0 (Set.Ici 0)) (𝓝 1) := by
    have h : Tendsto (fun s : ℝ => Real.exp (-s)) (𝓝 0) (𝓝 (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).tendsto (0 : ℝ)
    rw [neg_zero, Real.exp_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine Tendsto.congr (fun s => ?_) (hreal.comp hexp)
  exact (dilH_sub_norm phi hcont hψ (Real.exp_pos (-s))).symm

end UnforcedLeray.Short.PartIIIb.Concrete.DilStrong
