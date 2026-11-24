import UnforcedLeray.Lib.PlanarSpectralB.XGSpectrum

/-!


Source of record: `the November 2 reference manuscript`, lines 809-889
(transfer of rootspaces to the actual weighted spaces).

This generalizes the `M = 2` embedding `xgEmb` of `Lib/PlanarSpectralB/XGSpectrum.lean`
(`profileMeasure_two_le`, `xgEmbLin`, `norm_xgEmbLin_le`, `xgEmb_injective`, `xgEmb_L0`).

Route: `(1 + r²)^M ≤ e^{4M²+1} e^{r²/4}` gives `profileMeasure M ≤ e^{4M²+1} • xGMeasure`
(`profileMeasure_le_xGMeasure_smul`). The rest mirrors `xgEmb`; the reverse absolute continuity
`xGMeasure ≪ profileMeasure M` comes from `ac_profileMeasure`, which holds for every `M`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartI

theorem xgEmbM_nonneg {M : ℝ} (hM : 1 < M) : 0 ≤ M := by linarith

/-- `(1 + r²)^M ≤ e^{4M²+1} e^{r²/4}` for `M ≥ 0`. Proof: with `s = √(1 + r²)`,
`log(1 + r²) = 2 log s ≤ 2(s - 1)`, and `2M(s - 1) - (s² - 1)/4 ≤ 4M² + 1`. -/
theorem rpow_one_add_sq_le_exp_quarter {M : ℝ} (hM : 0 ≤ M) (r : ℝ) :
    (1 + r ^ 2) ^ M ≤ Real.exp (4 * M ^ 2 + 1) * Real.exp (r ^ 2 / 4) := by
  have hy0 : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have hs0 : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 hy0
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt hy0.le
  have hlog : Real.log (1 + r ^ 2) ≤ 2 * (Real.sqrt (1 + r ^ 2) - 1) := by
    have h1 : Real.log (Real.sqrt (1 + r ^ 2)) ≤ Real.sqrt (1 + r ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log (1 + r ^ 2) = 2 * Real.log (Real.sqrt (1 + r ^ 2)) := by
      rw [Real.log_sqrt hy0.le]; ring
    linarith
  rw [Real.rpow_def_of_pos hy0, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h3 : Real.log (1 + r ^ 2) * M ≤ 2 * (Real.sqrt (1 + r ^ 2) - 1) * M :=
    mul_le_mul_of_nonneg_right hlog hM
  nlinarith [sq_nonneg (Real.sqrt (1 + r ^ 2) / 2 - 2 * M), hs2, hM]

/-- The profile measure of weight `M ≥ 0` is at most `e^{4M²+1}` times the `X_G` measure. -/
theorem profileMeasure_le_xGMeasure_smul {M : ℝ} (hM : 0 ≤ M) :
    Planar.profileMeasure M ≤ ENNReal.ofReal (Real.exp (4 * M ^ 2 + 1)) • B0010.xGMeasure := by
  rw [Planar.profileMeasure, B0010.xGMeasure,
    ← withDensity_smul' (ENNReal.ofReal (Real.exp (4 * M ^ 2 + 1))) _ ENNReal.ofReal_ne_top]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  rw [Pi.smul_apply, smul_eq_mul, B0010.xGDensity_eq]
  rw [show ((Real.toNNReal (4 * π * Real.exp (r ^ 2 / 4) * r) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (4 * π * Real.exp (r ^ 2 / 4) * r) from rfl]
  rw [← ENNReal.ofReal_mul (Real.exp_pos (4 * M ^ 2 + 1)).le]
  apply ENNReal.ofReal_le_ofReal
  have h1 := rpow_one_add_sq_le_exp_quarter hM r
  have key : 2 * π * r * (1 + r ^ 2) ^ M ≤
      2 * π * r * (Real.exp (4 * M ^ 2 + 1) * Real.exp (r ^ 2 / 4)) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg (by positivity) hr0.le)
  have hc : 0 ≤ Real.exp (4 * M ^ 2 + 1) * Real.exp (r ^ 2 / 4) * r * π :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hr0.le)
      Real.pi_pos.le
  nlinarith [key, hc]

theorem profileMeasure_ac_xGMeasure {M : ℝ} (hM : 0 ≤ M) :
    Planar.profileMeasure M ≪ B0010.xGMeasure :=
  Measure.absolutelyContinuous_of_le_smul (profileMeasure_le_xGMeasure_smul hM)

theorem xGMeasure_ac_profileMeasure (M : ℝ) :
    B0010.xGMeasure ≪ Planar.profileMeasure M :=
  B0012.xG_ac.trans (Planar.ac_profileMeasure M)

theorem memLp_xgEmbM {M : ℝ} (hM : 0 ≤ M) (f : B0010.XG) :
    MemLp (⇑f) 2 (Planar.profileMeasure M) :=
  (Lp.memLp f).of_measure_le_smul ENNReal.ofReal_ne_top (profileMeasure_le_xGMeasure_smul hM)

/-- The embedding constant `(e^{4M²+1})^{1/2}`. -/
def xgEmbNormConstM (M : ℝ) : ℝ :=
  ((ENNReal.ofReal (Real.exp (4 * M ^ 2 + 1))) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal

/-- The embedding `X_G → L²_M` as a linear map (same profile). -/
def xgEmbLinM {M : ℝ} (hM : 1 < M) : B0010.XG →ₗ[ℂ] Planar.ProfL2 M where
  toFun f := (memLp_xgEmbM (xgEmbM_nonneg hM) f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_xgEmbM (xgEmbM_nonneg hM) (f + g)).coeFn_toLp,
      (memLp_xgEmbM (xgEmbM_nonneg hM) f).coeFn_toLp,
      (memLp_xgEmbM (xgEmbM_nonneg hM) g).coeFn_toLp,
      Lp.coeFn_add ((memLp_xgEmbM (xgEmbM_nonneg hM) f).toLp _)
        ((memLp_xgEmbM (xgEmbM_nonneg hM) g).toLp _),
      (profileMeasure_ac_xGMeasure (xgEmbM_nonneg hM)).ae_le (Lp.coeFn_add f g)] with r h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]
  map_smul' a f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(memLp_xgEmbM (xgEmbM_nonneg hM) (a • f)).coeFn_toLp,
      (memLp_xgEmbM (xgEmbM_nonneg hM) f).coeFn_toLp,
      Lp.coeFn_smul a ((memLp_xgEmbM (xgEmbM_nonneg hM) f).toLp _),
      (profileMeasure_ac_xGMeasure (xgEmbM_nonneg hM)).ae_le (Lp.coeFn_smul a f)] with r h1 h2 h3 h4
    rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply]

theorem norm_xgEmbLinM_le {M : ℝ} (hM : 1 < M) (f : B0010.XG) :
    ‖xgEmbLinM hM f‖ ≤ xgEmbNormConstM M * ‖f‖ := by
  have h := eLpNorm_le_of_measure_le_smul (profileMeasure_le_xGMeasure_smul (xgEmbM_nonneg hM))
    (f := ⇑f) (p := 2)
  rw [smul_eq_mul] at h
  have hK : (ENNReal.ofReal (Real.exp (4 * M ^ 2 + 1))) ^ ((1 / (2 : ℝ≥0∞)).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  change ‖(memLp_xgEmbM (xgEmbM_nonneg hM) f).toLp _‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def, xgEmbNormConstM, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hK (Lp.eLpNorm_ne_top f)) h

/-- **The embedding** `X_G → L²_M` (`f ↦ f` on the profile), bounded. -/
def xgEmbM {M : ℝ} (hM : 1 < M) : B0010.XG →L[ℂ] Planar.ProfL2 M :=
  (xgEmbLinM hM).mkContinuous (xgEmbNormConstM M) (norm_xgEmbLinM_le hM)

theorem coeFn_xgEmbM {M : ℝ} (hM : 1 < M) (f : B0010.XG) :
    ⇑(xgEmbM hM f) =ᵐ[Planar.profileMeasure M] ⇑f :=
  (memLp_xgEmbM (xgEmbM_nonneg hM) f).coeFn_toLp

theorem xgEmbM_injective {M : ℝ} (hM : 1 < M) {f : B0010.XG} (h : xgEmbM hM f = 0) :
    f = 0 := by
  have h1 : ⇑f =ᵐ[Planar.profileMeasure M] (0 : ℝ → ℂ) := by
    filter_upwards [coeFn_xgEmbM hM f, Lp.coeFn_zero ℂ 2 (Planar.profileMeasure M)] with r h1 h2
    rw [← h1, h, h2]
  apply Lp.ext
  filter_upwards [(xGMeasure_ac_profileMeasure M).ae_le h1,
    Lp.coeFn_zero ℂ 2 B0010.xGMeasure] with r h1 h2
  rw [h1, h2]

/-- The embedding intertwines `L₀` with the sector-two generator `𝓛_2` (general `M`). -/
theorem xgEmbM_L0 {M : ℝ} (hM : 1 < M) (f : B0010.XG) :
    xgEmbM hM (Planar.L0 f) = Planar.Lsec hM 2 (xgEmbM hM f) := by
  have h2 : (2 : ℤ).natAbs = 2 := rfl
  apply Lp.ext
  filter_upwards [coeFn_xgEmbM hM (Planar.L0 f),
    (profileMeasure_ac_xGMeasure (xgEmbM_nonneg hM)).ae_le (Planar.coeFn_L0 f),
    Planar.coeFn_Lsec hM 2 (xgEmbM hM f), coeFn_xgEmbM hM f] with r h1 h3 h4 h5
  rw [h1, h3, h4, h5, h2, Planar.greenN_congr 2 (coeFn_xgEmbM hM f)]
  push_cast
  ring

/-- **Task PartI:S01.** For `M > 1` there is a bounded linear `e : X_G → L²_M` which is the
identity on profiles, is injective, and intertwines `L₀` with the sector-two generator
`𝓛_2 = Planar.Lsec hM 2` (source lines 809-889). -/
theorem exists_xgEmbM {M : ℝ} (hM : 1 < M) : ∃ e : B0010.XG →L[ℂ] Planar.ProfL2 M,
    (∀ f, ⇑(e f) =ᵐ[Planar.profileMeasure M] ⇑f) ∧ (∀ f, e f = 0 → f = 0) ∧
      ∀ f, e (Planar.L0 f) = Planar.Lsec hM 2 (e f) :=
  ⟨xgEmbM hM, coeFn_xgEmbM hM, fun _ h => xgEmbM_injective hM h, fun f => xgEmbM_L0 hM f⟩

end UnforcedLeray.Short.PartI
