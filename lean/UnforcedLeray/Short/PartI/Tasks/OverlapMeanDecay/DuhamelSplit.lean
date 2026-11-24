import UnforcedLeray.Short.PartI.Sub.PartI_T15
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay.DuhamelSplit.OverlapBounds
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartI:T15/1` — 1D Heat Duhamel Split at `T / 2` (`overlap_mean_duhamel_split`)

Source of record: `the November 2 reference manuscript`, lines 415–425.

Proves `overlap_mean_duhamel_split : OverlapMeanDuhamelSplit` by combining:
1. The pointwise `j`-th derivative Duhamel split at `T / 2`
   (`DuhamelSplit.iteratedDeriv_b_duhamel_split` from `DuhamelSplit/OverlapBounds.lean`),
2. Minkowski's integral inequality on `Ioc 0 (T / 2)` and `Ioc (T / 2) T` in `L²(ℝ)` and `L^∞(ℝ)`,
3. The 1D Gaussian heat smoothing bound `Heat.eLpNorm_iteratedDeriv_lineHeat` on `[T / 2, T]` and
   the `L^p` contraction bound `Heat.eLpNorm_lineHeat_le` on `(0, T / 2]`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

namespace DuhamelSplit

open UnforcedLeray.Heat

/-! ### 1. Pointwise-to-`L^∞` and Minkowski helpers -/

/-- For a continuous function `ψ : ℝ → ℝ`, `‖ψ x‖ₑ ≤ eLpNorm ψ ⊤ volume` for every `x : ℝ`. -/
private theorem enorm_le_eLpNorm_top_of_continuous {ψ : ℝ → ℝ} (hψ : Continuous ψ) (x : ℝ) :
    ‖ψ x‖ₑ ≤ eLpNorm ψ ⊤ volume := by
  rw [eLpNorm_exponent_top, eLpNormEssSup]
  by_contra! hlt
  have hopen : IsOpen {y : ℝ | essSup (fun z => ‖ψ z‖ₑ) volume < ‖ψ y‖ₑ} :=
    isOpen_Ioi.preimage hψ.enorm
  have hne : ({y : ℝ | essSup (fun z => ‖ψ z‖ₑ) volume < ‖ψ y‖ₑ}).Nonempty := ⟨x, hlt⟩
  have hpos : volume {y : ℝ | essSup (fun z => ‖ψ z‖ₑ) volume < ‖ψ y‖ₑ} ≠ 0 :=
    hopen.measure_ne_zero volume hne
  have hae : ∀ᵐ y ∂volume, ‖ψ y‖ₑ ≤ essSup (fun z => ‖ψ z‖ₑ) volume := ae_le_essSup
  rw [ae_iff] at hae
  exact hpos (by simpa [not_le] using hae)

/-- Minkowski's integral inequality in `L^∞(ℝ)` for a family with a.e. continuous slices. -/
private theorem eLpNorm_setIntegral_top_le {F : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hcont : ∀ᵐ t ∂(volume.restrict s), Continuous (fun Y => F Y t)) :
    eLpNorm (fun Y => ∫ t in s, F Y t) ⊤ volume ≤
      ∫⁻ t in s, eLpNorm (fun Y => F Y t) ⊤ volume := by
  rw [eLpNorm_exponent_top]
  refine essSup_le_of_ae_le _ (Eventually.of_forall fun Y => ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine lintegral_mono_ae ?_
  filter_upwards [hcont] with t ht
  exact enorm_le_eLpNorm_top_of_continuous ht Y

/-- Triangle inequality for a 3-term split `f Y = -f₁ Y - e * f₂ Y - e * f₃ Y` in `L^p(ℝ)`. -/
private theorem eLpNorm_three_split_le {f f₁ f₂ f₃ : ℝ → ℝ} {e : ℝ} (he : 0 ≤ e)
    (hf_eq : ∀ Y : ℝ, f Y = -f₁ Y - e * f₂ Y - e * f₃ Y)
    (hf₁ : AEStronglyMeasurable f₁ volume)
    (hf₂ : AEStronglyMeasurable f₂ volume)
    (hf₃ : AEStronglyMeasurable f₃ volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm f p volume ≤
      eLpNorm f₁ p volume + ENNReal.ofReal e * eLpNorm f₂ p volume +
        ENNReal.ofReal e * eLpNorm f₃ p volume := by
  have hfun : f = (-f₁ + -(e • f₂)) + -(e • f₃) := by
    funext Y
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hf_eq Y]
    ring
  rw [hfun]
  have h12 : AEStronglyMeasurable (-f₁ + -(e • f₂)) volume :=
    hf₁.neg.add (hf₂.const_smul e).neg
  have h3 : AEStronglyMeasurable (-(e • f₃)) volume := (hf₃.const_smul e).neg
  calc eLpNorm ((-f₁ + -(e • f₂)) + -(e • f₃)) p volume
      ≤ eLpNorm (-f₁ + -(e • f₂)) p volume + eLpNorm (-(e • f₃)) p volume :=
        eLpNorm_add_le h12 h3 hp
    _ ≤ (eLpNorm (-f₁) p volume + eLpNorm (-(e • f₂)) p volume) +
          eLpNorm (-(e • f₃)) p volume := by
        gcongr
        exact eLpNorm_add_le hf₁.neg (hf₂.const_smul e).neg hp
    _ = eLpNorm f₁ p volume + ENNReal.ofReal e * eLpNorm f₂ p volume +
          ENNReal.ofReal e * eLpNorm f₃ p volume := by
        rw [eLpNorm_neg, eLpNorm_neg, eLpNorm_neg, eLpNorm_const_smul, eLpNorm_const_smul,
          Real.enorm_of_nonneg he]

/-! ### 2. Scalar rate and 1D heat smoothing bounds on `[T / 2, T]` -/

private noncomputable def heatSplitConst (j : ℕ) : ℝ :=
  max 1 (max |Gaussian.derivLpConst 1 (j + 1) 2| |Gaussian.derivLpConst 1 (j + 1) ⊤|) *
    4 ^ (1 + (j : ℝ) / 2)

private theorem heatSplitConst_pos (j : ℕ) : 0 < heatSplitConst j := by
  unfold heatSplitConst
  have h1 : (0 : ℝ) < max 1
      (max |Gaussian.derivLpConst 1 (j + 1) 2| |Gaussian.derivLpConst 1 (j + 1) ⊤|) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

private theorem rpow_theta_le_one_add_T (j : ℕ) {T θ α : ℝ} (hT : 1 ≤ T) (hθ : T / 2 ≤ θ)
    (hα_nonpos : α ≤ 0) (hα_low : -(1 + (j : ℝ) / 2) ≤ α) :
    θ ^ α ≤ 4 ^ (1 + (j : ℝ) / 2) * (1 + T) ^ α := by
  have h1T_pos : 0 < 1 + T := by linarith
  have hq_pos : 0 < (1 + T) / 4 := by positivity
  have hq_le : (1 + T) / 4 ≤ θ := by linarith
  have h1 : θ ^ α ≤ ((1 + T) / 4) ^ α :=
    Real.rpow_le_rpow_of_nonpos hq_pos hq_le hα_nonpos
  have h2 : ((1 + T) / 4) ^ α = (4 : ℝ) ^ (-α) * (1 + T) ^ α := by
    rw [div_eq_mul_inv, Real.mul_rpow h1T_pos.le (by positivity),
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      mul_comm]
  have h3 : (4 : ℝ) ^ (-α) ≤ (4 : ℝ) ^ (1 + (j : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) (by linarith)
  calc θ ^ α
      ≤ ((1 + T) / 4) ^ α := h1
    _ = (4 : ℝ) ^ (-α) * (1 + T) ^ α := h2
    _ ≤ (4 : ℝ) ^ (1 + (j : ℝ) / 2) * (1 + T) ^ α :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg h1T_pos.le _)

/-- Smooth `L¹ → L²` 1D heat derivative bound for `θ ≥ T / 2` and `T ≥ 1`. -/
private theorem eLpNorm_iteratedDeriv_lineHeat_two_le (j : ℕ) {T θ : ℝ} (hT : 1 ≤ T)
    (hθ : T / 2 ≤ θ) {f : ℝ → ℝ} (hf_cd : ContDiff ℝ ∞ f) :
    eLpNorm (iteratedDeriv (j + 1) (lineHeat θ f)) 2 volume ≤
      ENNReal.ofReal (heatSplitConst j * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) *
        eLpNorm f 1 volume := by
  set α : ℝ := -1 - (j : ℝ) / 2 + 1 / 4
  have hT_pos : 0 < 1 + T := by linarith
  have hC_pos : 0 < heatSplitConst j * (1 + T) ^ α :=
    mul_pos (heatSplitConst_pos j) (Real.rpow_pos_of_pos hT_pos α)
  by_cases hf_top : eLpNorm f 1 volume = ⊤
  · rw [hf_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hC_pos).ne']
    exact le_top
  · have hint : Integrable f volume :=
      memLp_one_iff_integrable.1 ⟨hf_cd.continuous.aestronglyMeasurable, lt_top_iff_ne_top.2 hf_top⟩
    have hθ_pos : 0 < θ := by linarith
    have hmain := Heat.eLpNorm_iteratedDeriv_lineHeat hθ_pos hint (j + 1) (p := 2) (by norm_num)
    have hexp : -((j + 1 : ℕ) : ℝ) / 2 - (1 : ℝ) / 2 * (1 - (1 / (2 : ℝ≥0∞)).toReal) = α := by
      have hto : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
      rw [hto]
      dsimp [α]
      push_cast
      ring
    rw [hexp, mul_comm (eLpNorm f 1 volume)] at hmain
    refine hmain.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
    have hα_nonpos : α ≤ 0 := by
      dsimp [α]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hα_low : -(1 + (j : ℝ) / 2) ≤ α := by
      dsimp [α]
      linarith
    have hθ_pow := rpow_theta_le_one_add_T j hT hθ hα_nonpos hα_low
    have hconst : Gaussian.derivLpConst 1 (j + 1) 2 ≤
        max 1 (max |Gaussian.derivLpConst 1 (j + 1) 2| |Gaussian.derivLpConst 1 (j + 1) ⊤|) :=
      (le_abs_self _).trans ((le_max_left _ _).trans (le_max_right _ _))
    calc Gaussian.derivLpConst 1 (j + 1) 2 * θ ^ α
        ≤ max 1 (max |Gaussian.derivLpConst 1 (j + 1) 2| |Gaussian.derivLpConst 1 (j + 1) ⊤|) *
            (4 ^ (1 + (j : ℝ) / 2) * (1 + T) ^ α) :=
          mul_le_mul hconst hθ_pow (Real.rpow_nonneg hθ_pos.le _) (by positivity)
      _ = heatSplitConst j * (1 + T) ^ α := by unfold heatSplitConst; ring

/-- Smooth `L¹ → L^∞` 1D heat derivative bound for `θ ≥ T / 2` and `T ≥ 1`. -/
private theorem eLpNorm_iteratedDeriv_lineHeat_top_le (j : ℕ) {T θ : ℝ} (hT : 1 ≤ T)
    (hθ : T / 2 ≤ θ) {f : ℝ → ℝ} (hf_cd : ContDiff ℝ ∞ f) :
    eLpNorm (iteratedDeriv (j + 1) (lineHeat θ f)) ⊤ volume ≤
      ENNReal.ofReal (heatSplitConst j * (1 + T) ^ (-1 - (j : ℝ) / 2)) *
        eLpNorm f 1 volume := by
  set α : ℝ := -1 - (j : ℝ) / 2
  have hT_pos : 0 < 1 + T := by linarith
  have hC_pos : 0 < heatSplitConst j * (1 + T) ^ α :=
    mul_pos (heatSplitConst_pos j) (Real.rpow_pos_of_pos hT_pos α)
  by_cases hf_top : eLpNorm f 1 volume = ⊤
  · rw [hf_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hC_pos).ne']
    exact le_top
  · have hint : Integrable f volume :=
      memLp_one_iff_integrable.1 ⟨hf_cd.continuous.aestronglyMeasurable, lt_top_iff_ne_top.2 hf_top⟩
    have hθ_pos : 0 < θ := by linarith
    have hmain := Heat.eLpNorm_iteratedDeriv_lineHeat hθ_pos hint (j + 1) (p := ⊤) le_top
    have hexp : -((j + 1 : ℕ) : ℝ) / 2 - (1 : ℝ) / 2 * (1 - (1 / (⊤ : ℝ≥0∞)).toReal) = α := by
      simp only [ENNReal.div_top, ENNReal.toReal_zero]
      dsimp [α]
      push_cast
      ring
    rw [hexp, mul_comm (eLpNorm f 1 volume)] at hmain
    refine hmain.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
    have hα_nonpos : α ≤ 0 := by
      dsimp [α]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hα_low : -(1 + (j : ℝ) / 2) ≤ α := by
      dsimp [α]
      linarith
    have hθ_pow := rpow_theta_le_one_add_T j hT hθ hα_nonpos hα_low
    have hconst : Gaussian.derivLpConst 1 (j + 1) ⊤ ≤
        max 1 (max |Gaussian.derivLpConst 1 (j + 1) 2| |Gaussian.derivLpConst 1 (j + 1) ⊤|) :=
      (le_abs_self _).trans ((le_max_right _ _).trans (le_max_right _ _))
    calc Gaussian.derivLpConst 1 (j + 1) ⊤ * θ ^ α
        ≤ max 1 (max |Gaussian.derivLpConst 1 (j + 1) 2| |Gaussian.derivLpConst 1 (j + 1) ⊤|) *
            (4 ^ (1 + (j : ℝ) / 2) * (1 + T) ^ α) :=
          mul_le_mul hconst hθ_pow (Real.rpow_nonneg hθ_pos.le _) (by positivity)
      _ = heatSplitConst j * (1 + T) ^ α := by unfold heatSplitConst; ring

end DuhamelSplit

/-! ### 3. Main Theorem `overlap_mean_duhamel_split` -/

/-- **1D Heat Duhamel Split at `T / 2`** (`PartI:T15/1`, `shorter-proof.tex` lines 415–425). -/
theorem overlap_mean_duhamel_split : OverlapMeanDuhamelSplit := by
  intro j
  refine ⟨DuhamelSplit.heatSplitConst j, DuhamelSplit.heatSplitConst_pos j, ?_⟩
  intro ν c hν hc tr htr T hT
  dsimp only
  set U := overlapField ν c tr.v T
  set b : ℝ → ℝ := fun Y => hmean 1 U Y 0
  set S₀ : ℝ → ℝ := overlapMeanStream tr 0
  set g : ℝ → ℝ → ℝ := overlapStressProfile tr
  set early : ℝ≥0∞ :=
    eLpNorm S₀ 1 volume + ENNReal.ofReal (eC ν c) * ∫⁻ t in Ioc 0 (T / 2), eLpNorm (g t) 1 volume
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have heC_pos : 0 < eC ν c := by unfold eC; positivity
  obtain ⟨M, _hM0, hS_bd, _hSt_bd, hg_bd⟩ :=
    DuhamelSplit.exists_overlap_duhamel_bounds hν hc tr htr hT0.le (j + 2)
  have hS₀_cd : ContDiff ℝ ∞ S₀ :=
    DuhamelSplit.contDiff_overlapMeanStream_slice hν hc tr htr le_rfl
  have hg_slice : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (g t) :=
    fun t ht => DuhamelSplit.contDiff_overlapStressProfile_slice hν hc tr htr ht.1
  have hg_open := DuhamelSplit.contDiffOn_overlapStressProfile_open hν hc tr htr
  have hg_Ioi : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hg_open.mono (prod_mono
      (Ioi_subset_Ici_self.trans (DuhamelSplit.Ici_subset_overlapTimeIoi hν hc)) Subset.rfl)
  -- The three pieces of the Duhamel split at `T / 2`
  let f₁ : ℝ → ℝ := iteratedDeriv (j + 1) (Heat.lineHeat T S₀)
  let F_early : ℝ → ℝ → ℝ := fun Y t => iteratedDeriv (j + 1) (Heat.lineHeat (T - t) (g t)) Y
  let F_late : ℝ → ℝ → ℝ := fun Y t => Heat.lineHeat (T - t) (iteratedDeriv (j + 1) (g t)) Y
  let f₂ : ℝ → ℝ := fun Y => ∫ t in Ioc 0 (T / 2), F_early Y t
  let f₃ : ℝ → ℝ := fun Y => ∫ t in Ioc (T / 2) T, F_late Y t
  have hsplit_pt : ∀ Y : ℝ,
      iteratedDeriv j b Y = -f₁ Y - eC ν c * f₂ Y - eC ν c * f₃ Y :=
    fun Y => DuhamelSplit.iteratedDeriv_b_duhamel_split hν hc tr htr hT j Y
  -- Joint measurability and slice continuity of the three pieces
  have hf₁_cont : Continuous f₁ := by
    have hcomm := DuhamelSplit.iteratedDeriv_lineHeat_data hT0 hS₀_cd (j + 1)
      (fun m hm x => hS_bd 0 ⟨le_rfl, hT0.le⟩ m (hm.trans (by omega)) x)
    change Continuous (iteratedDeriv (j + 1) (Heat.lineHeat T S₀))
    rw [hcomm]
    exact DuhamelSplit.continuous_lineHeat_of_contDiff hT0
      (DuhamelSplit.contDiff_iteratedDeriv_of_top hS₀_cd (j + 1))
      (fun x => hS_bd 0 ⟨le_rfl, hT0.le⟩ (j + 1) (by omega) x)
      (fun x => by
        rw [← iteratedDeriv_succ]
        exact hS_bd 0 ⟨le_rfl, hT0.le⟩ (j + 2) le_rfl x)
  have hF_early_meas : AEStronglyMeasurable (Function.uncurry F_early)
      (volume.prod (volume.restrict (Ioc 0 (T / 2)))) :=
    DuhamelSplit.aestronglyMeasurable_iteratedDeriv_lineHeat_Ioc (by linarith : T / 2 < T)
      hg_Ioi (j + 1) (fun t ht k hk x =>
        hg_bd t ⟨ht.1.le, ht.2.trans (by linarith)⟩ k (hk.trans (by omega)) x)
  have hF_late_meas : AEStronglyMeasurable (Function.uncurry F_late)
      (volume.prod (volume.restrict (Ioc (T / 2) T))) :=
    DuhamelSplit.aestronglyMeasurable_lineHeat_iteratedDeriv_Ioc (by linarith : 0 ≤ T / 2)
      hg_Ioi (j + 1)
  have hf₁_meas : AEStronglyMeasurable f₁ volume := hf₁_cont.aestronglyMeasurable
  have hf₂_meas : AEStronglyMeasurable f₂ volume := hF_early_meas.integral_prod_right'
  have hf₃_meas : AEStronglyMeasurable f₃ volume := hF_late_meas.integral_prod_right'
  have hF_early_cont : ∀ᵐ t ∂(volume.restrict (Ioc 0 (T / 2))),
      Continuous (fun Y => F_early Y t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht_Icc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.trans (by linarith)⟩
    have hθ : 0 < T - t := by linarith [ht.2]
    have hg_cd : ContDiff ℝ ∞ (g t) := hg_slice t ht_Icc
    have hcomm := DuhamelSplit.iteratedDeriv_lineHeat_data hθ hg_cd (j + 1)
      (fun m hm x => hg_bd t ht_Icc m (hm.trans (by omega)) x)
    change Continuous (iteratedDeriv (j + 1) (Heat.lineHeat (T - t) (g t)))
    rw [hcomm]
    exact DuhamelSplit.continuous_lineHeat_of_contDiff hθ
      (DuhamelSplit.contDiff_iteratedDeriv_of_top hg_cd (j + 1))
      (fun x => hg_bd t ht_Icc (j + 1) (by omega) x)
      (fun x => by
        rw [← iteratedDeriv_succ]
        exact hg_bd t ht_Icc (j + 2) le_rfl x)
  have hF_late_cont : ∀ᵐ t ∂(volume.restrict (Ioc (T / 2) T)),
      Continuous (fun Y => F_late Y t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume T)] with t ht ht_ne
    have ht_Icc : t ∈ Icc 0 T := ⟨(by linarith [ht.1]), ht.2⟩
    have hθ : 0 < T - t := sub_pos.2 (lt_of_le_of_ne ht.2 ht_ne)
    have hg_cd : ContDiff ℝ ∞ (g t) := hg_slice t ht_Icc
    exact DuhamelSplit.continuous_lineHeat_of_contDiff hθ
      (DuhamelSplit.contDiff_iteratedDeriv_of_top hg_cd (j + 1))
      (fun x => hg_bd t ht_Icc (j + 1) (by omega) x)
      (fun x => by
        rw [← iteratedDeriv_succ]
        exact hg_bd t ht_Icc (j + 2) le_rfl x)
  -- Late contraction bounds for `p = 2` and `p = ⊤`
  have hlate_bound : ∀ p : ℝ≥0∞, 1 ≤ p →
      ∫⁻ t in Ioc (T / 2) T, eLpNorm (fun Y => F_late Y t) p volume ≤
        ∫⁻ t in Ioc (T / 2) T, eLpNorm (iteratedDeriv (j + 1) (g t)) p volume := by
    intro p hp
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume T)] with t ht ht_ne
    have ht_Icc : t ∈ Icc 0 T := ⟨(by linarith [ht.1]), ht.2⟩
    have hθ : 0 < T - t := sub_pos.2 (lt_of_le_of_ne ht.2 ht_ne)
    have hg_meas : AEStronglyMeasurable (iteratedDeriv (j + 1) (g t)) volume :=
      (DuhamelSplit.contDiff_iteratedDeriv_of_top (hg_slice t ht_Icc) (j + 1)).continuous.aestronglyMeasurable
    exact Heat.eLpNorm_lineHeat_le hθ hg_meas hp
  refine ⟨?_, ?_⟩
  · -- `L²` Duhamel split bound
    set C_two : ℝ≥0∞ :=
      ENNReal.ofReal (DuhamelSplit.heatSplitConst j * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4))
    have htri := DuhamelSplit.eLpNorm_three_split_le heC_pos.le hsplit_pt
      hf₁_meas hf₂_meas hf₃_meas (p := 2) (by norm_num)
    have hinit : eLpNorm f₁ 2 volume ≤ C_two * eLpNorm S₀ 1 volume :=
      DuhamelSplit.eLpNorm_iteratedDeriv_lineHeat_two_le j hT (by linarith) hS₀_cd
    have hearly_mink : eLpNorm f₂ 2 volume ≤
        ∫⁻ t in Ioc 0 (T / 2), eLpNorm (fun Y => F_early Y t) 2 volume :=
      NonUniqueEuler.Conv.eLpNorm_integral_le hF_early_meas (by norm_num) (by simp)
    have hearly_int : ∫⁻ t in Ioc 0 (T / 2), eLpNorm (fun Y => F_early Y t) 2 volume ≤
        C_two * ∫⁻ t in Ioc 0 (T / 2), eLpNorm (g t) 1 volume := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
      have ht_Icc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.trans (by linarith)⟩
      exact DuhamelSplit.eLpNorm_iteratedDeriv_lineHeat_two_le j hT (by linarith [ht.2])
        (hg_slice t ht_Icc)
    have hlate_mink : eLpNorm f₃ 2 volume ≤
        ∫⁻ t in Ioc (T / 2) T, eLpNorm (iteratedDeriv (j + 1) (g t)) 2 volume :=
      (NonUniqueEuler.Conv.eLpNorm_integral_le hF_late_meas (by norm_num) (by simp)).trans
        (hlate_bound 2 (by norm_num))
    calc eLpNorm (iteratedDeriv j b) 2 volume
        ≤ eLpNorm f₁ 2 volume + ENNReal.ofReal (eC ν c) * eLpNorm f₂ 2 volume +
            ENNReal.ofReal (eC ν c) * eLpNorm f₃ 2 volume := htri
      _ ≤ C_two * eLpNorm S₀ 1 volume +
            ENNReal.ofReal (eC ν c) * (C_two * ∫⁻ t in Ioc 0 (T / 2), eLpNorm (g t) 1 volume) +
            ENNReal.ofReal (eC ν c) *
              ∫⁻ t in Ioc (T / 2) T, eLpNorm (iteratedDeriv (j + 1) (g t)) 2 volume := by
          gcongr
          exact hearly_mink.trans hearly_int
      _ = C_two * early +
            ENNReal.ofReal (eC ν c) *
              ∫⁻ t in Ioc (T / 2) T, eLpNorm (iteratedDeriv (j + 1) (g t)) 2 volume := by
          dsimp [early]
          rw [mul_add, mul_left_comm]
  · -- `L^∞` Duhamel split bound
    set C_top : ℝ≥0∞ :=
      ENNReal.ofReal (DuhamelSplit.heatSplitConst j * (1 + T) ^ (-1 - (j : ℝ) / 2))
    have htri := DuhamelSplit.eLpNorm_three_split_le heC_pos.le hsplit_pt
      hf₁_meas hf₂_meas hf₃_meas (p := ⊤) le_top
    have hinit : eLpNorm f₁ ⊤ volume ≤ C_top * eLpNorm S₀ 1 volume :=
      DuhamelSplit.eLpNorm_iteratedDeriv_lineHeat_top_le j hT (by linarith) hS₀_cd
    have hearly_mink : eLpNorm f₂ ⊤ volume ≤
        ∫⁻ t in Ioc 0 (T / 2), eLpNorm (fun Y => F_early Y t) ⊤ volume :=
      DuhamelSplit.eLpNorm_setIntegral_top_le hF_early_cont
    have hearly_int : ∫⁻ t in Ioc 0 (T / 2), eLpNorm (fun Y => F_early Y t) ⊤ volume ≤
        C_top * ∫⁻ t in Ioc 0 (T / 2), eLpNorm (g t) 1 volume := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
      have ht_Icc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.trans (by linarith)⟩
      exact DuhamelSplit.eLpNorm_iteratedDeriv_lineHeat_top_le j hT (by linarith [ht.2])
        (hg_slice t ht_Icc)
    have hlate_mink : eLpNorm f₃ ⊤ volume ≤
        ∫⁻ t in Ioc (T / 2) T, eLpNorm (iteratedDeriv (j + 1) (g t)) ⊤ volume :=
      (DuhamelSplit.eLpNorm_setIntegral_top_le hF_late_cont).trans (hlate_bound ⊤ le_top)
    calc eLpNorm (iteratedDeriv j b) ⊤ volume
        ≤ eLpNorm f₁ ⊤ volume + ENNReal.ofReal (eC ν c) * eLpNorm f₂ ⊤ volume +
            ENNReal.ofReal (eC ν c) * eLpNorm f₃ ⊤ volume := htri
      _ ≤ C_top * eLpNorm S₀ 1 volume +
            ENNReal.ofReal (eC ν c) * (C_top * ∫⁻ t in Ioc 0 (T / 2), eLpNorm (g t) 1 volume) +
            ENNReal.ofReal (eC ν c) *
              ∫⁻ t in Ioc (T / 2) T, eLpNorm (iteratedDeriv (j + 1) (g t)) ⊤ volume := by
          gcongr
          exact hearly_mink.trans hearly_int
      _ = C_top * early +
            ENNReal.ofReal (eC ν c) *
              ∫⁻ t in Ioc (T / 2) T, eLpNorm (iteratedDeriv (j + 1) (g t)) ⊤ volume := by
          dsimp [early]
          rw [mul_add, mul_left_comm]

end UnforcedLeray.Short.PartI
