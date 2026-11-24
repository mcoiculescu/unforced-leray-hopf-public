import UnforcedLeray.Units.B0285.Defs

/-!
# B0285, the spatial Hölder step

Unit B0285 of `paper/main.tex` (tex lines 4663–4669); blueprint unit B0285. For each age the
localized coefficients of the train give, by spatial Hölder with `1/2 = 1/r + 1/p`
(`r = 22/3`, `p = 11/4`),
`‖curl(B_v b)‖_{X_c} ≤ P (‖D²b‖_p + ‖Db‖_p + ‖b‖_p)`, `P = 2 c^{1/p} K`,
where `K = coeffNorm c m v` is the weighted `L^r` norm of the 2-jet of `v`; the factor
`c^{1/p}` converts the unnormalized cell measure `dq dη` of `X_c` to the normalized measure
`dq/c dη` of `‖·‖_p` (tex line 4734: "conversions between these spatial conventions cost fixed
powers of `c`, absorbed into `P`").

The bridge `eLpNorm_cellμ_eq` identifies the two cell conventions (B0284's `(0, c] × ℝ` with
`dq/c dη`, and `Cyl.cell c = [-c/2, c/2) × ℝ` with `dq dη`) on periodic fields.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal ContDiff

namespace UnforcedLeray.B0285

open UnforcedLeray.GaussianVortex (Plane)

/-! ## 1. The two cell conventions -/

/-- The cell `(0, c] × ℝ` of B0284 and the centred cell `[-c/2, c/2) × ℝ` carry the same
lower integrals of a `c`-periodic function. -/
theorem setLIntegral_cell_eq {c : ℝ} (hc : 0 < c) {G : Plane → ℝ≥0∞}
    (hG : B0284.IsQPeriodic c G) :
    ∫⁻ z in B0284.cell c, G z = ∫⁻ z in Cyl.cell c, G z := by
  have hae : (B0284.cell c : Set Plane) =ᵐ[volume] (Ico 0 (0 + c) ×ˢ (univ : Set ℝ)) := by
    filter_upwards [Sob.ae_fst_ne 0, Sob.ae_fst_ne c] with z h0 hc'
    show (z ∈ Ioc 0 c ×ˢ (univ : Set ℝ)) = (z ∈ Ico 0 (0 + c) ×ˢ (univ : Set ℝ))
    rw [zero_add]
    refine propext ⟨fun h => ⟨⟨h.1.1.le, lt_of_le_of_ne h.1.2 hc'⟩, trivial⟩,
      fun h => ⟨⟨lt_of_le_of_ne h.1.1 (Ne.symm h0), h.1.2.le⟩, trivial⟩⟩
  rw [setLIntegral_congr hae]
  exact Cyl.lintegral_strip_eq_cell hc hG 0

/-- `‖f‖_{L^p(cell, dq dη)} = c^{1/p} ‖f‖_{L^p(dq/c dη)}` for a `c`-periodic field. -/
theorem eLpNorm_cellμ_eq {E : Type*} [NormedAddCommGroup E] {c : ℝ} (hc : 0 < c)
    {f : Plane → E} (hf : B0284.IsQPeriodic c f) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) (Cyl.cellμ c) =
      ENNReal.ofReal (c ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) (B0284.cellMeasure c) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp [hp]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  have hG : B0284.IsQPeriodic c (fun z => ‖f z‖ₑ ^ p) := fun z => by simp only [hf z]
  have hkey : ENNReal.ofReal (c ^ (1 / p)) * (((c.toNNReal)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (1 / p) = 1 := by
    rw [← Real.toNNReal_inv,
      show (((c⁻¹).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal c⁻¹ from rfl,
      ENNReal.ofReal_rpow_of_pos (inv_pos.2 hc), ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
      ← Real.mul_rpow hc.le (inv_nonneg.2 hc.le), mul_inv_cancel₀ hc.ne', Real.one_rpow,
      ENNReal.ofReal_one]
  rw [B0284.cellMeasure, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
    setLIntegral_cell_eq hc hG,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p), ← mul_assoc, hkey, one_mul]
  rfl

/-! ## 2. The `X_c` norm and the weighted Hölder inequality -/

/-- `‖ω‖_{X_c} = ‖ρc^{m/2} ω‖_{L²(cell)}`. -/
theorem XcNorm_eq (c m : ℝ) (om : Plane → ℝ) :
    XcNorm c m om = eLpNorm (fun z => wt m z * om z) 2 (Cyl.cellμ c) := by
  unfold XcNorm
  rw [Cyl.eLpNorm_wμc_eq]
  refine eLpNorm_congr_norm_ae (Eventually.of_forall fun z => ?_)
  rw [← Complex.ofReal_mul, Complex.norm_real]
  rfl

/-- **Spatial Hölder** with `1/2 = 1/r + 1/p`:
`‖ρc^{m/2} A B‖_{L²} ≤ ‖ρc^{m/2} A‖_{L^r} ‖B‖_{L^p}` on the cell. -/
theorem eLpNorm_wt_mul_le {c m : ℝ} {A B : Plane → ℝ}
    (hA : AEStronglyMeasurable A (Cyl.cellμ c)) (hB : AEStronglyMeasurable B (Cyl.cellμ c)) :
    eLpNorm (fun z => wt m z * A z * B z) 2 (Cyl.cellμ c) ≤
      eLpNorm (fun z => wt m z * A z) (ENNReal.ofReal rB) (Cyl.cellμ c) *
        eLpNorm B (ENNReal.ofReal pB) (Cyl.cellμ c) := by
  have hwA : AEStronglyMeasurable (fun z => wt m z * A z) (Cyl.cellμ c) :=
    (continuous_wt m).aestronglyMeasurable.mul hA
  have h := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal rB) (q := ENNReal.ofReal pB)
    (r := 2) hB hwA
  exact h

/-! ## 3. Jets in the normalized norm -/

theorem eLpNorm_norm_cellμ_le {c : ℝ} (hc : 0 < c) {f : Plane → Plane}
    (hf : B0284.IsQPeriodic c f) :
    eLpNorm (fun z => ‖f z‖) (ENNReal.ofReal pB) (Cyl.cellμ c) =
      ENNReal.ofReal (c ^ (1 / pB)) * spNorm c f := by
  rw [eLpNorm_norm, eLpNorm_cellμ_eq hc hf pB_pos]
  rfl

theorem aestronglyMeasurable_jet1 {μ : Measure Plane} {D : Fin 2 → Plane → Plane}
    (hD : ∀ j, AEStronglyMeasurable (D j) μ) : AEStronglyMeasurable (jet1 D) μ := by
  have : jet1 D = fun z => ‖D 0 z‖ + ‖D 1 z‖ := by
    funext z; simp [jet1, Fin.sum_univ_two]
  rw [this]
  exact (hD 0).norm.add (hD 1).norm

theorem aestronglyMeasurable_jet2 {μ : Measure Plane} {D : Fin 2 → Fin 2 → Plane → Plane}
    (hD : ∀ j k, AEStronglyMeasurable (D j k) μ) : AEStronglyMeasurable (jet2 D) μ := by
  have : jet2 D = fun z => ‖D 0 0 z‖ + ‖D 0 1 z‖ + (‖D 1 0 z‖ + ‖D 1 1 z‖) := by
    funext z; simp [jet2, Fin.sum_univ_two]
  rw [this]
  exact ((hD 0 0).norm.add (hD 0 1).norm).add ((hD 1 0).norm.add (hD 1 1).norm)

theorem eLpNorm_jet1_le {c : ℝ} (hc : 0 < c) {D : Fin 2 → Plane → Plane}
    (hper : ∀ j, B0284.IsQPeriodic c (D j)) (hD : ∀ j, AEStronglyMeasurable (D j) (Cyl.cellμ c)) :
    eLpNorm (jet1 D) (ENNReal.ofReal pB) (Cyl.cellμ c) ≤
      ENNReal.ofReal (c ^ (1 / pB)) * spNorm1 c D := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal pB := ENNReal.one_le_ofReal.2 one_lt_pB.le
  have : jet1 D = (fun z => ‖D 0 z‖) + fun z => ‖D 1 z‖ := by
    funext z; simp [jet1, Fin.sum_univ_two]
  rw [this]
  refine (eLpNorm_add_le (hD 0).norm (hD 1).norm hp1).trans (le_of_eq ?_)
  rw [eLpNorm_norm_cellμ_le hc (hper 0), eLpNorm_norm_cellμ_le hc (hper 1), spNorm1,
    Fin.sum_univ_two, mul_add]

theorem eLpNorm_jet2_le {c : ℝ} (hc : 0 < c) {D : Fin 2 → Fin 2 → Plane → Plane}
    (hper : ∀ j k, B0284.IsQPeriodic c (D j k))
    (hD : ∀ j k, AEStronglyMeasurable (D j k) (Cyl.cellμ c)) :
    eLpNorm (jet2 D) (ENNReal.ofReal pB) (Cyl.cellμ c) ≤
      ENNReal.ofReal (c ^ (1 / pB)) * spNorm2 c D := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal pB := ENNReal.one_le_ofReal.2 one_lt_pB.le
  have : jet2 D = ((fun z => ‖D 0 0 z‖) + fun z => ‖D 0 1 z‖) +
      ((fun z => ‖D 1 0 z‖) + fun z => ‖D 1 1 z‖) := by
    funext z; simp [jet2, Fin.sum_univ_two]
  rw [this]
  refine (eLpNorm_add_le ((hD 0 0).norm.add (hD 0 1).norm) ((hD 1 0).norm.add (hD 1 1).norm)
    hp1).trans ?_
  refine (add_le_add (eLpNorm_add_le (hD 0 0).norm (hD 0 1).norm hp1)
    (eLpNorm_add_le (hD 1 0).norm (hD 1 1).norm hp1)).trans (le_of_eq ?_)
  rw [eLpNorm_norm_cellμ_le hc (hper 0 0), eLpNorm_norm_cellμ_le hc (hper 0 1),
    eLpNorm_norm_cellμ_le hc (hper 1 0), eLpNorm_norm_cellμ_le hc (hper 1 1), spNorm2]
  simp only [Fin.sum_univ_two]
  ring

/-! ## 4. Continuity of the coefficient jets -/

theorem continuous_dV {V : Plane → Plane} (hV : ContDiff ℝ 2 V) (k : Fin 2) :
    Continuous (dV V k) :=
  (hV.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem contDiff_dV {V : Plane → Plane} (hV : ContDiff ℝ 2 V) (k : Fin 2) :
    ContDiff ℝ 1 (dV V k) :=
  (hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem continuous_d2V {V : Plane → Plane} (hV : ContDiff ℝ 2 V) (j k : Fin 2) :
    Continuous (d2V V j k) :=
  ((contDiff_dV hV k).continuous_fderiv (by norm_num)).clm_apply continuous_const

/-! ## 5. The pointwise-in-age source bound -/

theorem le_two_mul_self (a : ℝ≥0∞) : a ≤ 2 * a := by
  calc a = 1 * a := (one_mul a).symm
    _ ≤ 2 * a := by gcongr; norm_num

/-- **Curl source bound** (tex lines 4663–4669): for a `C²` coefficient field `V` and a
periodic field `b` with measurable jets `Db j = ∂_j b`, `D2b j k = ∂_j∂_k b`,
`‖curl(B_V b)‖_{X_c} ≤ P (‖D²b‖_p + ‖Db‖_p + ‖b‖_p)` with `P = 2 c^{1/p} K`,
`K = coeffNorm c m V` (`srcConst`). No measurability of `curlSource` is needed and no
finiteness is assumed (both sides are in `[0,∞]`). -/
theorem XcNorm_curlSource_le {c m : ℝ} (hc : 0 < c) {V b : Plane → Plane}
    {Db : Fin 2 → Plane → Plane} {D2b : Fin 2 → Fin 2 → Plane → Plane}
    (hV : ContDiff ℝ 2 V)
    (hbper : B0284.IsQPeriodic c b) (hDbper : ∀ j, B0284.IsQPeriodic c (Db j))
    (hD2bper : ∀ j k, B0284.IsQPeriodic c (D2b j k))
    (hbm : AEStronglyMeasurable b (Cyl.cellμ c))
    (hDbm : ∀ j, AEStronglyMeasurable (Db j) (Cyl.cellμ c))
    (hD2bm : ∀ j k, AEStronglyMeasurable (D2b j k) (Cyl.cellμ c)) :
    XcNorm c m (curlSource V b Db D2b) ≤
      srcConst c (coeffNorm c m V) * (spNorm2 c D2b + spNorm1 c Db + spNorm c b) := by
  set μ := Cyl.cellμ c
  set P := ENNReal.ofReal pB
  set R := ENNReal.ofReal rB
  have hV0 : AEStronglyMeasurable (fun z => ‖V z‖) μ := hV.continuous.norm.aestronglyMeasurable
  have hV1 : AEStronglyMeasurable (jet1 (dV V)) μ :=
    aestronglyMeasurable_jet1 fun k => (continuous_dV hV k).aestronglyMeasurable
  have hV2 : AEStronglyMeasurable (jet2 (d2V V)) μ :=
    aestronglyMeasurable_jet2 fun j k => (continuous_d2V hV j k).aestronglyMeasurable
  have hb0 : AEStronglyMeasurable (fun z => ‖b z‖) μ := hbm.norm
  have hb1 : AEStronglyMeasurable (jet1 Db) μ := aestronglyMeasurable_jet1 hDbm
  have hb2 : AEStronglyMeasurable (jet2 D2b) μ := aestronglyMeasurable_jet2 hD2bm
  have hw := (continuous_wt m).aestronglyMeasurable (μ := μ)
  set f1 : Plane → ℝ := fun z => wt m z * ‖V z‖ * jet2 D2b z
  set f2 : Plane → ℝ := fun z => wt m z * jet1 (dV V) z * jet1 Db z
  set f3 : Plane → ℝ := fun z => wt m z * jet2 (d2V V) z * ‖b z‖
  have hf1 : AEStronglyMeasurable f1 μ := (hw.mul hV0).mul hb2
  have hf2 : AEStronglyMeasurable f2 μ := (hw.mul hV1).mul hb1
  have hf3 : AEStronglyMeasurable f3 μ := (hw.mul hV2).mul hb0
  -- pointwise domination
  have hdom : ∀ z, ‖wt m z * curlSource V b Db D2b z‖ ≤ ‖(f1 + (2 : ℝ) • f2 + f3) z‖ := by
    intro z
    have h := abs_curlSource_le V b Db D2b z
    have hw0 := wt_nonneg m z
    have hnn : 0 ≤ f1 z + 2 * f2 z + f3 z := by
      simp only [f1, f2, f3]
      have := jet1_nonneg (dV V) z
      have := jet1_nonneg Db z
      have := jet2_nonneg D2b z
      have := jet2_nonneg (d2V V) z
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [abs_of_nonneg hnn]
    calc wt m z * |curlSource V b Db D2b z|
        ≤ wt m z * (‖V z‖ * jet2 D2b z + 2 * (jet1 (dV V) z * jet1 Db z) +
          jet2 (d2V V) z * ‖b z‖) := mul_le_mul_of_nonneg_left h hw0
      _ = f1 z + 2 * f2 z + f3 z := by simp only [f1, f2, f3]; ring
  have hp1 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hstep1 : XcNorm c m (curlSource V b Db D2b) ≤
      eLpNorm f1 2 μ + 2 * eLpNorm f2 2 μ + eLpNorm f3 2 μ := by
    rw [XcNorm_eq]
    refine (eLpNorm_mono hdom).trans ?_
    refine (eLpNorm_add_le (hf1.add (hf2.const_smul 2)) hf3 hp1).trans ?_
    refine add_le_add ((eLpNorm_add_le hf1 (hf2.const_smul 2) hp1).trans (le_of_eq ?_)) le_rfl
    have h2e : ‖(2 : ℝ)‖ₑ = 2 := by
      rw [Real.enorm_eq_ofReal (by norm_num)]; exact ENNReal.ofReal_ofNat 2
    rw [eLpNorm_const_smul, h2e]
  -- Hölder on each term
  have h1 : eLpNorm f1 2 μ ≤ eLpNorm (fun z => wt m z * ‖V z‖) R μ *
      (ENNReal.ofReal (c ^ (1 / pB)) * spNorm2 c D2b) :=
    (eLpNorm_wt_mul_le hV0 hb2).trans (mul_le_mul_right (eLpNorm_jet2_le hc hD2bper hD2bm) _)
  have h2 : eLpNorm f2 2 μ ≤ eLpNorm (fun z => wt m z * jet1 (dV V) z) R μ *
      (ENNReal.ofReal (c ^ (1 / pB)) * spNorm1 c Db) :=
    (eLpNorm_wt_mul_le hV1 hb1).trans (mul_le_mul_right (eLpNorm_jet1_le hc hDbper hDbm) _)
  have h3 : eLpNorm f3 2 μ ≤ eLpNorm (fun z => wt m z * jet2 (d2V V) z) R μ *
      (ENNReal.ofReal (c ^ (1 / pB)) * spNorm c b) :=
    (eLpNorm_wt_mul_le hV2 hb0).trans
      (mul_le_mul_right (le_of_eq (eLpNorm_norm_cellμ_le hc hbper)) _)
  -- collect
  set A0 := eLpNorm (fun z => wt m z * ‖V z‖) R μ
  set A1 := eLpNorm (fun z => wt m z * jet1 (dV V) z) R μ
  set A2 := eLpNorm (fun z => wt m z * jet2 (d2V V) z) R μ
  set C := ENNReal.ofReal (c ^ (1 / pB))
  have hK : coeffNorm c m V = A0 + A1 + A2 := rfl
  have hA0 : A0 ≤ 2 * (A0 + A1 + A2) :=
    (le_self_add.trans le_self_add).trans (le_two_mul_self _)
  have hA1 : A1 ≤ A0 + A1 + A2 := le_self_add.trans' le_add_self
  have hA2 : A2 ≤ 2 * (A0 + A1 + A2) := le_add_self.trans (le_two_mul_self _)
  calc XcNorm c m (curlSource V b Db D2b)
      ≤ A0 * (C * spNorm2 c D2b) + 2 * (A1 * (C * spNorm1 c Db)) + A2 * (C * spNorm c b) :=
        hstep1.trans (add_le_add (add_le_add h1 (mul_le_mul_right h2 _)) h3)
    _ ≤ (2 * (A0 + A1 + A2)) * (C * spNorm2 c D2b) +
          2 * ((A0 + A1 + A2) * (C * spNorm1 c Db)) +
          (2 * (A0 + A1 + A2)) * (C * spNorm c b) := by
        gcongr
    _ = srcConst c (coeffNorm c m V) * (spNorm2 c D2b + spNorm1 c Db + spNorm c b) := by
        rw [hK, srcConst]; ring

end UnforcedLeray.B0285
