import UnforcedLeray.Units.B0223.Ops
import UnforcedLeray.Analysis.SpatialScaling
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# B0223 helper: the normalized spatial dilation on the periodic `L²`

Blueprint unit B0223 (label `eq:st18-t00116`), `paper/main.tex` lines 3348–3354.

For `a > 0`, `dilN a F(x, τ) = a^{3/2} F(a x, τ)` is a unitary of `L²(ℝ³ × ℝ/Pℤ)`
(`dx ↦ a^{-3} dx`); the dilation part `F ↦ e^{t/2} F(e^{t/2} ·)` of `S_ε(t)` is
`e^{t/2} e^{-3t/4} dilN (e^{t/2}) = e^{-t/4} dilN (e^{t/2})`, the source of the bound `e^{-t/4}`
(blueprint proof outline). This file proves:

* `dilN` is a complex linear isometry (`norm_dilN_apply`), `dilN 1 = 1`, `dilN a dilN b = dilN (ab)`;
* `heatC_dilN`: `e^{θΔ}(dilN a F) = dilN a (e^{a²θΔ} F)` (Gaussian dilation identity);
* `transC_dilN`: dilations commute with the phase translation;
* `tendsto_dilN`: strong continuity `dilN b F → F` as `b → 1` (density of continuous compactly
  supported fields and dominated convergence; adapted from the draft
  `Units/B0418/Continuity.lean`, `tendsto_dilation`, on `ℝ³`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0220 (WeightedComp)

namespace UnforcedLeray.B0223

variable {P : ℝ} [Fact (0 < P)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-! ### Complex linear weighted compositions -/

section Upgrade

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

theorem wc_toLI_smul (W : WeightedComp μ ν E F)
    (hW : ∀ x (c : ℂ) (v : E), W.L x (c • v) = c • W.L x v) (c : ℂ) (f : Lp E 2 ν) :
    W.toLI (c • f) = c • W.toLI f := by
  refine Lp.ext ?_
  have h1 := W.coeFn_toLI (c • f)
  have h2 := W.compFun_congr (Lp.coeFn_smul c f)
  have h3 := Lp.coeFn_smul c (W.toLI f)
  have h4 := W.coeFn_toLI f
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, Pi.smul_apply, hx4]
  simp only [WeightedComp.compFun, Pi.smul_apply, hW]

/-- A weighted composition whose pointwise maps are complex linear is a complex linear
isometry of `L²`. -/
def wcToLIC (W : WeightedComp μ ν E F)
    (hW : ∀ x (c : ℂ) (v : E), W.L x (c • v) = c • W.L x v) : Lp E 2 ν →ₗᵢ[ℂ] Lp F 2 μ where
  toFun := W.toLI
  map_add' := W.toLI.map_add
  map_smul' := wc_toLI_smul W hW
  norm_map' := W.toLI.norm_map

theorem wcToLIC_apply (W : WeightedComp μ ν E F)
    (hW : ∀ x (c : ℂ) (v : E), W.L x (c • v) = c • W.L x v) (f : Lp E 2 ν) :
    wcToLIC W hW f = W.toLI f := rfl

end Upgrade

/-! ### The normalized dilation -/

theorem map_dil {a : ℝ} (ha : 0 < a) :
    (volume : Measure (PSpace P)).map (fun z => (a • z.1, z.2)) =
      ENNReal.ofReal |(a ^ 3)⁻¹| • volume := by
  rw [volume_pspace]
  have h := Measure.map_prod_map (volume : Measure Space) (volume : Measure (AddCircle P))
    (measurable_const_smul a) measurable_id
  change Measure.map (Prod.map (fun x : Space => a • x) id) _ = _
  rw [← h, Measure.map_id, SpatialScaling.map_dilation ha.ne', Measure.prod_smul_left]

/-- The normalized dilation `F ↦ a^{3/2} F(a ·, ·)` as a weighted composition. -/
def dilWC {a : ℝ} (ha : 0 < a) :
    WeightedComp (volume : Measure (PSpace P)) (volume : Measure (PSpace P)) E E where
  T z := (a • z.1, z.2)
  L _ := a ^ (3 / 2 : ℝ) • LinearMap.id
  ρ _ := a ^ (3 / 2 : ℝ)
  measurable_T := (measurable_fst.const_smul a).prodMk measurable_snd
  measurable_ρ := measurable_const
  measurable_L := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact measurable_snd.const_smul _
  nonneg_ρ _ := by positivity
  norm_L _ v := by
    rw [LinearMap.smul_apply, LinearMap.id_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
  map_eq := by
    have hρ : (a ^ (3 / 2 : ℝ)) ^ 2 = a ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
      norm_num
    have hd : (fun _ : PSpace P => ENNReal.ofReal ((a ^ (3 / 2 : ℝ)) ^ 2)) =
        fun _ => ENNReal.ofReal (a ^ 3) := by
      rw [hρ]
    rw [hd, withDensity_const, Measure.map_smul, map_dil ha, smul_smul,
      ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_smul]

theorem dilWC_smul {a : ℝ} (ha : 0 < a) (x : PSpace P) (c : ℂ) (v : E) :
    (dilWC (P := P) (E := E) ha).L x (c • v) = c • (dilWC (P := P) (E := E) ha).L x v := by
  simp only [dilWC, LinearMap.smul_apply, LinearMap.id_apply]
  exact smul_comm _ _ _

/-- **The normalized dilation** `dilN a F (x, τ) = a^{3/2} F(a x, τ)`, a unitary for `a > 0`
(the identity for `a ≤ 0`, a convention never used). -/
def dilN (a : ℝ) : X E P →L[ℂ] X E P :=
  if ha : 0 < a then (wcToLIC (dilWC ha) (dilWC_smul ha)).toContinuousLinearMap
  else ContinuousLinearMap.id ℂ _

theorem dilN_of_pos {a : ℝ} (ha : 0 < a) (u : X E P) :
    dilN a u = (dilWC (P := P) (E := E) ha).toLI u := by
  simp only [dilN, ha, ↓reduceDIte]
  rfl

/-- Composition with a representative. -/
theorem dilN_ae {a : ℝ} (ha : 0 < a) {u : X E P} {f : PSpace P → E}
    (hf : (u : PSpace P → E) =ᵐ[volume] f) :
    (dilN a u : PSpace P → E) =ᵐ[volume] fun z => a ^ (3 / 2 : ℝ) • f (a • z.1, z.2) := by
  rw [dilN_of_pos ha]
  refine ((dilWC ha).coeFn_toLI u).trans (((dilWC ha).compFun_congr hf).trans ?_)
  exact Eventually.of_forall fun z => rfl

theorem coeFn_dilN {a : ℝ} (ha : 0 < a) (u : X E P) :
    (dilN a u : PSpace P → E) =ᵐ[volume] fun z => a ^ (3 / 2 : ℝ) • u (a • z.1, z.2) :=
  dilN_ae ha (Eventually.of_forall fun _ => rfl)

theorem norm_dilN_apply (a : ℝ) (u : X E P) : ‖dilN a u‖ = ‖u‖ := by
  by_cases ha : 0 < a
  · rw [dilN_of_pos ha]
    exact (dilWC ha).toLI.norm_map u
  · simp only [dilN, ha, ↓reduceDIte, ContinuousLinearMap.id_apply]

theorem norm_dilN_le (a : ℝ) : ‖(dilN a : X E P →L[ℂ] X E P)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul, norm_dilN_apply]

theorem dilN_one (u : X E P) : dilN 1 u = u := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dilN one_pos u] with z hz
  rw [hz, Real.one_rpow, one_smul, one_smul]

theorem dilN_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : X E P) :
    dilN a (dilN b u) = dilN (a * b) u := by
  refine Lp.ext ?_
  filter_upwards [dilN_ae ha (coeFn_dilN hb u), coeFn_dilN (mul_pos ha hb) u] with z hz1 hz2
  rw [hz1, hz2, smul_smul, smul_smul, Real.mul_rpow ha.le hb.le, mul_comm b a]

/-- **Gaussian dilation identity**: `e^{θΔ}[a^{3/2} v(a ·, τ)](x) = a^{3/2} (e^{a²θΔ} v)(a x, τ)`. -/
theorem heatConv_dil {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (v : PSpace P → E) (z : PSpace P) :
    Heat.heatConv (ιx P) θ (fun w => a ^ (3 / 2 : ℝ) • v (a • w.1, w.2)) z =
      a ^ (3 / 2 : ℝ) • Heat.heatConv (ιx P) (a ^ 2 * θ) v (a • z.1, z.2) := by
  simp only [Heat.heatConv, ιx_apply, Prod.fst_sub, Prod.snd_sub, sub_zero, Prod.mk_sub_mk]
  set F : Euc 3 → E := fun w => gaussKernel 3 (a ^ 2 * θ) w • v (a • z.1 - w, z.2) with hF
  have hJac := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euc 3)) F a (hR := ha.le)
  rw [Gaussian.finrank_euc] at hJac
  have hscale : ∀ y : Euc 3, gaussKernel 3 θ y = a ^ 3 * gaussKernel 3 (a ^ 2 * θ) (a • y) := by
    intro y
    rw [Gaussian.gaussKernel_scale ha hθ, ← mul_assoc, Real.rpow_neg ha.le, Real.rpow_natCast,
      mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]
  have hpt : ∀ y : Euc 3, gaussKernel 3 θ y • (a ^ (3 / 2 : ℝ) • v (a • (z.1 - y), z.2)) =
      (a ^ (3 / 2 : ℝ) * a ^ 3) • F (a • y) := by
    intro y
    simp only [hF, hscale y, smul_smul, smul_sub]
    congr 1
    ring
  calc ∫ y : Euc 3, gaussKernel 3 θ y • (a ^ (3 / 2 : ℝ) • v (a • (z.1 - y), z.2))
      = ∫ y : Euc 3, (a ^ (3 / 2 : ℝ) * a ^ 3) • F (a • y) := by simp_rw [hpt]
    _ = (a ^ (3 / 2 : ℝ) * a ^ 3) • ∫ y : Euc 3, F (a • y) := integral_smul _ _
    _ = (a ^ (3 / 2 : ℝ) * a ^ 3) • ((a ^ 3)⁻¹ • ∫ w : Euc 3, F w) := by rw [hJac]
    _ = a ^ (3 / 2 : ℝ) • ∫ w : Euc 3, F w := by
        rw [smul_smul, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), mul_one]

/-- **`e^{θΔ} dilN a = dilN a e^{a²θΔ}`** for `a > 0`. -/
theorem heatC_dilN {a : ℝ} (ha : 0 < a) (θ : ℝ) (u : X E P) :
    heatC θ (dilN a u) = dilN a (heatC (a ^ 2 * θ) u) := by
  by_cases hθ : 0 < θ
  · refine Lp.ext ?_
    have h1 := heatC_rep hθ (dilN a u)
    have h2 := Heat.heatConv_congr_ae (ιx P) continuous_ιx.measurable θ (coeFn_dilN ha u)
    have h3 := dilN_ae ha (heatC_rep (by positivity : 0 < a ^ 2 * θ) u)
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    rw [hz1, hz2, hz3]
    exact heatConv_dil ha hθ _ z
  · have hθ' : a ^ 2 * θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hθ)
    rw [heatC_of_nonpos (not_lt.mp hθ), heatC_of_nonpos hθ']

/-- Dilations commute with the phase translation. -/
theorem transC_dilN {a : ℝ} (ha : 0 < a) (t : ℝ) (u : X E P) :
    transC t (dilN a u) = dilN a (transC t u) := by
  refine Lp.ext ?_
  have h1 := coeFn_transC t (dilN a u)
  have h2 : (fun z => (dilN a u : PSpace P → E) (shiftT P t z)) =ᵐ[volume]
      fun z => a ^ (3 / 2 : ℝ) • u (a • (shiftT P t z).1, (shiftT P t z).2) :=
    (mp_shiftT t).quasiMeasurePreserving.ae_eq_comp (coeFn_dilN ha u)
  have h3 := dilN_ae ha (coeFn_transC t u)
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [hz1, hz2, hz3]
  simp only [shiftT_apply]

/-! ### Strong continuity of the dilation group -/

theorem tendsto_eLpNorm_dil_sub {g : PSpace P → E} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun b : ℝ => eLpNorm (fun z => b ^ (3 / 2 : ℝ) • g (b • z.1, z.2) - g z) 2 volume)
      (𝓝 1) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : PSpace P)
  have hzero : ∀ z : PSpace P, |R| < ‖z.1‖ → g z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hR (subset_tsupport g hne)
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 := norm_fst_le z
    have h3 := le_abs_self R
    linarith
  have hnear : ∀ᶠ b : ℝ in 𝓝 1, 1 / 2 < b ∧ b < 2 :=
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)).and (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  set K : Set (PSpace P) := Metric.closedBall (0 : Space) (2 * |R|) ×ˢ univ with hK
  have hKm : MeasurableSet K := measurableSet_closedBall.prod MeasurableSet.univ
  have hKf : volume K < ∞ := by
    rw [hK, volume_pspace, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_closedBall_lt_top (measure_lt_top _ _)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have hlim : Tendsto (fun b : ℝ => ∫⁻ z, ‖b ^ (3 / 2 : ℝ) • g (b • z.1, z.2) - g z‖ₑ ^
      (2 : ℝ≥0∞).toReal) (𝓝 1) (𝓝 (∫⁻ _z : PSpace P, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (K.indicator fun _ => (ENNReal.ofReal (5 * M)) ^ (2 : ℝ≥0∞).toReal) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun b => ?_
      have hc : Continuous fun z : PSpace P => b ^ (3 / 2 : ℝ) • g (b • z.1, z.2) - g z :=
        (continuous_const.smul (hg.comp ((continuous_fst.const_smul b).prodMk
          continuous_snd))).sub hg
      exact hc.enorm.measurable.pow_const _
    · filter_upwards [hnear] with b hb
      refine Eventually.of_forall fun z => ?_
      by_cases hz : ‖z.1‖ ≤ 2 * |R|
      · rw [Set.indicator_of_mem (show z ∈ K from ⟨by simpa using hz, trivial⟩)]
        gcongr
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        have hb32 : b ^ (3 / 2 : ℝ) ≤ 4 := by
          calc b ^ (3 / 2 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) :=
                Real.rpow_le_rpow (by linarith) hb.2.le (by norm_num)
            _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 4 := by norm_num
        calc ‖b ^ (3 / 2 : ℝ) • g (b • z.1, z.2) - g z‖
            ≤ ‖b ^ (3 / 2 : ℝ) • g (b • z.1, z.2)‖ + ‖g z‖ := norm_sub_le _ _
          _ = b ^ (3 / 2 : ℝ) * ‖g (b • z.1, z.2)‖ + ‖g z‖ := by
              rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [hb.1]) _)]
          _ ≤ 4 * M + M :=
              add_le_add (mul_le_mul hb32 (hM _) (norm_nonneg _) (by norm_num)) (hM _)
          _ = 5 * M := by ring
      · rw [Set.indicator_of_notMem (show z ∉ K from fun h => hz (by simpa using h.1))]
        have h1 : |R| < ‖(b • z.1, z.2).1‖ := by
          simp only [norm_smul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ b)]
          nlinarith [abs_nonneg R, hb.1, not_le.mp hz]
        have h2 : |R| < ‖z.1‖ := by nlinarith [abs_nonneg R, not_le.mp hz]
        rw [hzero _ h1, hzero _ h2, smul_zero, sub_zero, enorm_zero,
          ENNReal.zero_rpow_of_pos (by norm_num)]
    · rw [lintegral_indicator hKm, setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hKf.ne
    · refine Eventually.of_forall fun z => ?_
      have h1 : Tendsto (fun b : ℝ => b ^ (3 / 2 : ℝ) • g (b • z.1, z.2) - g z) (𝓝 1) (𝓝 0) := by
        have hc : Continuous fun b : ℝ => b ^ (3 / 2 : ℝ) • g (b • z.1, z.2) - g z :=
          ((Real.continuous_rpow_const (by norm_num)).smul (hg.comp
            ((continuous_id.smul continuous_const).prodMk continuous_const))).sub continuous_const
        have := hc.tendsto 1
        simpa using this
      have h2 := (continuous_enorm.tendsto (0 : E)).comp h1
      rw [enorm_zero] at h2
      have h3 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      exact h3
  rw [lintegral_zero] at hlim
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h4

/-- **Strong continuity of the dilations**: `dilN b F → F` in `L²` as `b → 1`. -/
theorem tendsto_dilN (u : X E P) : Tendsto (fun b => dilN b u) (𝓝 1) (𝓝 u) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨g, hgc, hgu, hgcont, hgm⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top
      (ε := ENNReal.ofReal (ε / 4)) (by simpa using hε)
  set gL : X E P := hgm.toLp g with hgL
  have hu : ‖u - gL‖ ≤ ε / 4 := by
    rw [Lp.norm_def, eLpNorm_congr_ae ((Lp.coeFn_sub u gL).trans
      (EventuallyEq.sub EventuallyEq.rfl hgm.coeFn_toLp))]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hgu
  have hT := tendsto_eLpNorm_dil_sub hgcont hgc
  have hev := (ENNReal.tendsto_nhds_zero.mp hT) (ENNReal.ofReal (ε / 4))
    (by simpa using hε)
  have hpos : ∀ᶠ b : ℝ in 𝓝 1, 0 < b := lt_mem_nhds one_pos
  filter_upwards [hev, hpos] with b hb hb0
  have hg : ‖dilN b gL - gL‖ ≤ ε / 4 := by
    have hae : ((dilN b gL - gL : X E P) : PSpace P → E) =ᵐ[volume]
        fun z => b ^ (3 / 2 : ℝ) • g (b • z.1, z.2) - g z := by
      filter_upwards [Lp.coeFn_sub (dilN b gL) gL, dilN_ae hb0 hgm.coeFn_toLp,
        hgm.coeFn_toLp] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hb
  have hdec : dilN b u - u = dilN b (u - gL) + (dilN b gL - gL) + (gL - u) := by
    rw [map_sub]
    abel
  rw [dist_eq_norm, hdec]
  have h1 : ‖dilN b (u - gL)‖ = ‖u - gL‖ := norm_dilN_apply b _
  have h2 : ‖gL - u‖ = ‖u - gL‖ := norm_sub_rev _ _
  calc ‖dilN b (u - gL) + (dilN b gL - gL) + (gL - u)‖
      ≤ ‖dilN b (u - gL)‖ + ‖dilN b gL - gL‖ + ‖gL - u‖ := norm_add₃_le
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by rw [h1, h2]; gcongr
    _ < ε := by linarith

end UnforcedLeray.B0223
