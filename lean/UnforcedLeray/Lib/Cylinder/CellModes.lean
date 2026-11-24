import UnforcedLeray.Lib.Cylinder.ModesWirtinger

/-!
# Cell forms of the `q`-mode estimates (INF13, target CY04, cell part)


§5 CY04 (`hasSum_cell_parseval`, `eLpNorm_qAvg_le`, `norm_sub_qAvg_le`,
`qAvg_contract_weighted`); blueprint units B0172 (Parseval in `q`, tex 2589-2598), B0158
(averaging cost `‖f̄‖_{L¹_η} ≤ c⁻¹ ‖f‖_{L¹(cell)}`, tex 2394-2404), B0176 (contraction of the
`q`-average in `⟨η⟩^m`-weighted norms, tex 2634-2656), B0566 (Wirtinger constant `c/(2π)`,
tex 9077-9085).

Cell norms are over the centred cell `cell c = [-c/2, c/2) × ℝ`, not divided by `c` (B0139,
tex 2042-2129).  All inequalities are stated in `ℝ≥0∞` (`lintegral`, `eLpNorm`), so no
integrability hypothesis is hidden in a Bochner junk value; the Parseval identity, an equality
of real numbers, assumes `f ∈ L²(cell)`.

* `hasSum_cell_parseval`: `∑_n c ∫ |f^(n)(η)|² dη = ∫_cell |f|²` for `f ∈ L²(cell)`;
* `enorm_qAvg_rpow_le`: Jensen on a slice, `|f̄(η)|^p ≤ c⁻¹ ∫_{-c/2}^{c/2} |f(q,η)|^p dq`,
  for every `f` and `1 ≤ p < ∞`;
* `eLpNorm_qAvg_le`: `‖f̄‖_{L^p_η} ≤ c^{-1/p} ‖f‖_{L^p(cell)}` (B0158 at `p = 1`);
* `eLpNorm_qAvg_contract_weighted`: `‖w(η) f̄‖_{L^p(cell)} ≤ ‖w(η) f‖_{L^p(cell)}` for a
  measurable weight depending on `η` only (B0176);
* `eLpNorm_sub_qAvg_le`: Wirtinger on the cell,
  `‖f - f̄‖_{L²(cell)} ≤ (c/2π) ‖∂_q f‖_{L²(cell)}` for a `C¹`, `c`-periodic `f`
  (classical form, as `qMode_partialQ`); `eLpNorm_le_of_qAvg_eq_zero` is the zero-mean case.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Complex
open scoped ENNReal

namespace UnforcedLeray.Cyl

/-! ### Measure-theoretic preliminaries -/

theorem restrict_Ioc_half_eq_Ico (c : ℝ) :
    (volume : Measure ℝ).restrict (Ioc (-c / 2) (c / 2)) =
      volume.restrict (Ico (-c / 2) (c / 2)) :=
  (Measure.restrict_congr_set Ico_ae_eq_Ioc).symm

theorem volume_Ico_half (c : ℝ) :
    volume (Ico (-c / 2) (c / 2)) = ENNReal.ofReal c := by
  rw [Real.volume_Ico]
  congr 1
  ring

theorem enorm_norm_sq' (z : ℂ) : ‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2 := by
  rw [enorm_pow, enorm_norm]

theorem ofReal_norm_sq (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
  rw [← enorm_norm_sq', Real.enorm_eq_ofReal (by positivity)]

theorem cellμ_eq_restrict (c : ℝ) : (volume : Measure Plane).restrict (cell c) = cellμ c := rfl

/-- `q`-modes as set integrals over the centred period. -/
theorem qMode_eq_setIntegral {c : ℝ} (hc : 0 < c) (n : ℤ) (f : Plane → ℂ) (η : ℝ) :
    qMode c hc n f η = (c⁻¹ : ℂ) * ∫ q in Ico (-c / 2) (c / 2),
      fourier (-n) (q : AddCircle (c / 2 - -c / 2)) * f (q, η) := by
  rw [qMode_eq_integral, intervalIntegral.integral_of_le (neg_half_lt_half hc).le,
    restrict_Ioc_half_eq_Ico]
  have h1 : (1 / (c / 2 - -c / 2) : ℝ) = c⁻¹ := by rw [half_sub_neg_half, one_div]
  rw [h1, Complex.real_smul]
  push_cast
  rfl

/-- `η ↦ f^(n)(η)` is a.e.-strongly measurable for `f` a.e.-strongly measurable on the cell. -/
theorem aestronglyMeasurable_qMode {c : ℝ} (hc : 0 < c) (n : ℤ) {f : Plane → ℂ}
    (hf : AEStronglyMeasurable f (cellμ c)) :
    AEStronglyMeasurable (qMode c hc n f) volume := by
  have hcont : Continuous fun q : ℝ => fourier (-n) (q : AddCircle (c / 2 - -c / 2)) :=
    (fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)
  have hg : AEStronglyMeasurable
      (fun z : Plane => fourier (-n) (z.1 : AddCircle (c / 2 - -c / 2)) * f z)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) := by
    rw [← cellμ_eq_prod]
    exact (hcont.comp continuous_fst).aestronglyMeasurable.mul hf
  have h2 := hg.prod_swap.integral_prod_right'
  have : qMode c hc n f = fun η => (c⁻¹ : ℂ) * ∫ q in Ico (-c / 2) (c / 2),
      fourier (-n) (q : AddCircle (c / 2 - -c / 2)) * f (q, η) := by
    funext η
    exact qMode_eq_setIntegral hc n f η
  rw [this]
  exact h2.const_mul _

/-- `η ↦ f̄(η)` is a.e.-strongly measurable for `f` a.e.-strongly measurable on the cell. -/
theorem aestronglyMeasurable_qAvg {c : ℝ} (hc : 0 < c) {f : Plane → ℂ}
    (hf : AEStronglyMeasurable f (cellμ c)) :
    AEStronglyMeasurable (qAvg c f) volume := by
  have h := aestronglyMeasurable_qMode hc 0 hf
  have : qMode c hc 0 f = qAvg c f := funext fun η => qMode_zero hc f η
  rwa [this] at h

/-- Almost every slice of an `L^p(cell)` function is in `L^p` of the period. -/
theorem ae_memLp_slice {c : ℝ} {f : Plane → ℂ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hf : MemLp f p (cellμ c)) :
    ∀ᵐ η ∂(volume : Measure ℝ),
      MemLp (fun q => f (q, η)) p (volume.restrict (Ico (-c / 2) (c / 2))) := by
  have hm := hf.1
  rw [cellμ_eq_prod] at hm
  have hfin := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp).1 hf.2
  rw [cellμ_eq_prod, lintegral_prod_symm _ (hm.enorm.pow_const _)] at hfin
  have hae := ae_lt_top' (hm.enorm.pow_const _).lintegral_prod_left' hfin.ne
  filter_upwards [hae, hm.prodMk_right] with η hη hmη
  exact ⟨hmη, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp).2 hη⟩

/-! ### Parseval on the cell -/

/-- Parseval on one slice, in `ℝ≥0∞`. -/
theorem tsum_enorm_sq_qMode {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (η : ℝ)
    (hL2 : MemLp (fun q => f (q, η)) 2 (volume.restrict (Ico (-c / 2) (c / 2)))) :
    ∑' n : ℤ, ‖qMode c hc n f η‖ₑ ^ 2 =
      ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ₑ ^ 2 := by
  have hL2' : MemLp (fun q => f (q, η)) 2 (volume.restrict (Ioc (-c / 2) (c / 2))) := by
    rwa [restrict_Ioc_half_eq_Ico]
  have hS := hasSum_sq_qMode hc η hL2'
  have hint : Integrable (fun q => ‖f (q, η)‖ ^ 2) (volume.restrict (Ico (-c / 2) (c / 2))) :=
    (memLp_two_iff_integrable_sq_norm hL2.1).1 hL2
  have hI : ENNReal.ofReal (∫ q in (-c / 2)..(c / 2), ‖f (q, η)‖ ^ 2) =
      ∫⁻ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ₑ ^ 2 := by
    rw [intervalIntegral.integral_of_le (neg_half_lt_half hc).le, restrict_Ioc_half_eq_Ico,
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun _ => by positivity)]
    exact lintegral_congr fun q => ofReal_norm_sq _
  rw [← hI, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), ← hS.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hS.summable]
  exact tsum_congr fun n => (ofReal_norm_sq _).symm

/-- **Parseval on the cell** (CY04 `hasSum_cell_parseval`; B0172, tex 2589-2598 "Parseval in
`q`"): for `f ∈ L²(cell c)`, `∑_n c ∫ |f^(n)(η)|² dη = ∫_{cell c} |f|²`. -/
theorem hasSum_cell_parseval {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : MemLp f 2 (cellμ c)) :
    HasSum (fun n : ℤ => c * ∫ η, ‖qMode c hc n f η‖ ^ 2) (∫ z in cell c, ‖f z‖ ^ 2) := by
  set A : ℤ → ℝ≥0∞ := fun n => ∫⁻ η, ‖qMode c hc n f η‖ₑ ^ 2 with hA
  set L : ℝ≥0∞ := ∫⁻ z in cell c, ‖f z‖ₑ ^ 2 with hL
  have hm : AEStronglyMeasurable f (cellμ c) := hf.1
  have hLfin : L ≠ ∞ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top).1 hf.2
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
    exact h.ne
  have hsum : ∑' n, A n = ENNReal.ofReal c⁻¹ * L := by
    simp only [A]
    rw [← lintegral_tsum fun n => (aestronglyMeasurable_qMode hc n hm).enorm.pow_const 2]
    have hae := ae_memLp_slice two_ne_zero ENNReal.ofNat_ne_top hf
    rw [lintegral_congr_ae (hae.mono fun η hη => tsum_enorm_sq_qMode hc η hη),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    have hm' := hm.enorm.pow_const 2
    rw [cellμ_eq_prod] at hm'
    rw [hL, cellμ_eq_restrict, cellμ_eq_prod, lintegral_prod_symm _ hm']
  have hsumfin : ∑' n, A n ≠ ∞ := by
    rw [hsum]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLfin
  have hAfin : ∀ n, A n ≠ ∞ := fun n => ne_top_of_le_ne_top hsumfin (ENNReal.le_tsum n)
  have hreal : ∀ n, ∫ η, ‖qMode c hc n f η‖ ^ 2 = (A n).toReal := by
    intro n
    have hmeas : AEStronglyMeasurable (fun η => ‖qMode c hc n f η‖ ^ 2) volume :=
      (aestronglyMeasurable_qMode hc n hm).norm.pow 2
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun η => sq_nonneg ‖qMode c hc n f η‖) hmeas]
    congr 1
    exact lintegral_congr fun η => ofReal_norm_sq _
  have hLreal : ∫ z in cell c, ‖f z‖ ^ 2 = L.toReal := by
    have hmeas : AEStronglyMeasurable (fun z => ‖f z‖ ^ 2) (volume.restrict (cell c)) :=
      hm.norm.pow 2
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => sq_nonneg ‖f z‖) hmeas]
    congr 1
    exact lintegral_congr fun z => ofReal_norm_sq _
  have hS : HasSum (fun n => (A n).toReal) (∑' n, A n).toReal := by
    rw [ENNReal.tsum_toReal_eq hAfin]
    exact (ENNReal.summable_toReal hsumfin).hasSum
  rw [hsum, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le)] at hS
  have h := hS.mul_left c
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h
  simp_rw [hreal, hLreal]
  exact h

/-! ### Jensen for the `q`-average -/

/-- The normalised period measure `c⁻¹ dq` on `[-c/2, c/2)`. -/
def perAvg (c : ℝ) : Measure ℝ := ENNReal.ofReal c⁻¹ • volume.restrict (Ico (-c / 2) (c / 2))

theorem isProbabilityMeasure_perAvg {c : ℝ} (hc : 0 < c) : IsProbabilityMeasure (perAvg c) :=
  ⟨by rw [perAvg, Measure.smul_apply, Measure.restrict_apply_univ, volume_Ico_half c,
      smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne',
      ENNReal.ofReal_one]⟩

theorem qAvg_eq_integral_perAvg {c : ℝ} (hc : 0 < c) (f : Plane → ℂ) (η : ℝ) :
    qAvg c f η = ∫ q, f (q, η) ∂(perAvg c) := by
  rw [perAvg, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le), qAvg,
    Complex.real_smul]
  push_cast
  rfl

/-- **Jensen on a slice**: for every `f` and `1 ≤ p < ∞`,
`|f̄(η)|^p ≤ c⁻¹ ∫_{-c/2}^{c/2} |f(q,η)|^p dq` (in `ℝ≥0∞`). -/
theorem enorm_qAvg_rpow_le {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (f : Plane → ℂ) (η : ℝ) :
    ‖qAvg c f η‖ₑ ^ p.toReal ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ₑ ^ p.toReal := by
  have := isProbabilityMeasure_perAvg hc
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  by_cases hm : AEStronglyMeasurable (fun q => f (q, η)) (perAvg c)
  · have h1 : ‖qAvg c f η‖ₑ ≤ eLpNorm (fun q => f (q, η)) p (perAvg c) := by
      rw [qAvg_eq_integral_perAvg hc]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← eLpNorm_one_eq_lintegral_enorm]
      exact eLpNorm_le_eLpNorm_of_exponent_le hp1 hm
    have h2 := ENNReal.rpow_le_rpow h1 hpr.le
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, one_div,
      ENNReal.rpow_inv_rpow hpr.ne', perAvg, lintegral_smul_measure] at h2
    exact h2
  · have : qAvg c f η = 0 := by
      rw [qAvg_eq_integral_perAvg hc, integral_undef fun hi => hm hi.1]
    rw [this, enorm_zero, ENNReal.zero_rpow_of_pos hpr]
    simp

/-- A function of `η` alone integrates over the cell to `c` times its line integral
(one inequality, valid without measurability). -/
theorem lintegral_cell_snd_le {c : ℝ} (hc : 0 < c) (G : ℝ → ℝ≥0∞) :
    ∫⁻ z in cell c, G z.2 ≤ ENNReal.ofReal c * ∫⁻ η, G η := by
  rw [cellμ_eq_restrict, cellμ_eq_prod]
  refine (lintegral_prod_le _).trans_eq ?_
  change ∫⁻ _ in Ico (-c / 2) (c / 2), ∫⁻ η, G η = _
  rw [lintegral_const, Measure.restrict_apply_univ, volume_Ico_half c, mul_comm]

/-- Weighted Jensen on the cell, in `ℝ≥0∞`: for a measurable weight `w(η)`,
`∫_cell |w f̄|^p ≤ ∫_cell |w f|^p`. -/
theorem lintegral_cell_weight_qAvg_le {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) {w : ℝ → ℝ} (hw : Measurable w) {f : Plane → ℂ}
    (hf : AEStronglyMeasurable f (cellμ c)) :
    ∫⁻ z in cell c, ‖(w z.2 : ℂ) * qAvg c f z.2‖ₑ ^ p.toReal ≤
      ∫⁻ z in cell c, ‖(w z.2 : ℂ) * f z‖ₑ ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine (lintegral_cell_snd_le hc
    (fun η => ‖(w η : ℂ) * qAvg c f η‖ₑ ^ p.toReal)).trans ?_
  have hwf : AEStronglyMeasurable (fun z : Plane => (w z.2 : ℂ) * f z) (cellμ c) :=
    ((Complex.measurable_ofReal.comp (hw.comp measurable_snd)).aestronglyMeasurable).mul hf
  have hm' := hwf.enorm.pow_const p.toReal
  rw [cellμ_eq_prod] at hm'
  rw [cellμ_eq_restrict, cellμ_eq_prod, lintegral_prod_symm _ hm',
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun η => ?_
  simp only [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hpr.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpr.le enorm_ne_top)]
  calc ENNReal.ofReal c * (‖(w η : ℂ)‖ₑ ^ p.toReal * ‖qAvg c f η‖ₑ ^ p.toReal)
      ≤ ENNReal.ofReal c * (‖(w η : ℂ)‖ₑ ^ p.toReal * (ENNReal.ofReal c⁻¹ *
          ∫⁻ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ₑ ^ p.toReal)) := by
        gcongr
        exact enorm_qAvg_rpow_le hc hp1 hp f η
    _ = ‖(w η : ℂ)‖ₑ ^ p.toReal * ∫⁻ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ₑ ^ p.toReal := by
        calc _ = ‖(w η : ℂ)‖ₑ ^ p.toReal * ((ENNReal.ofReal c * ENNReal.ofReal c⁻¹) *
              ∫⁻ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ₑ ^ p.toReal) := by ring
          _ = _ := by
            rw [← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

/-- **Contraction of the `q`-average in weighted norms** (CY04 `qAvg_contract_weighted`;
B0176, tex 2634-2656): for `1 ≤ p < ∞` and a measurable weight `w(η)` (e.g. `⟨η⟩^m`),
`‖w f̄‖_{L^p(cell)} ≤ ‖w f‖_{L^p(cell)}`. -/
theorem eLpNorm_qAvg_contract_weighted {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) {w : ℝ → ℝ} (hw : Measurable w) {f : Plane → ℂ}
    (hf : AEStronglyMeasurable f (cellμ c)) :
    eLpNorm (fun z : Plane => (w z.2 : ℂ) * qAvg c f z.2) p (cellμ c) ≤
      eLpNorm (fun z : Plane => (w z.2 : ℂ) * f z) p (cellμ c) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  exact ENNReal.rpow_le_rpow (lintegral_cell_weight_qAvg_le hc hp1 hp hw hf)
    (by positivity)

/-- The unweighted contraction `‖f̄‖_{L^p(cell)} ≤ ‖f‖_{L^p(cell)}`. -/
theorem eLpNorm_qAvg_cell_le {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : Plane → ℂ} (hf : AEStronglyMeasurable f (cellμ c)) :
    eLpNorm (fun z : Plane => qAvg c f z.2) p (cellμ c) ≤ eLpNorm f p (cellμ c) := by
  have h := eLpNorm_qAvg_contract_weighted hc hp1 hp (w := fun _ => 1) measurable_const hf
  simpa using h

/-- **Averaging cost** (CY04 `eLpNorm_qAvg_le`; B0158, tex 2394-2404 at `p = 1`): for
`1 ≤ p < ∞`, `‖f̄‖_{L^p(dη)} ≤ c^{-1/p} ‖f‖_{L^p(cell)}`. -/
theorem eLpNorm_qAvg_le {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : Plane → ℂ} (hf : AEStronglyMeasurable f (cellμ c)) :
    eLpNorm (qAvg c f) p volume ≤
      ENNReal.ofReal (c ^ (-1 / p.toReal)) * eLpNorm f p (cellμ c) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hm' := hf.enorm.pow_const p.toReal
  rw [cellμ_eq_prod] at hm'
  have hI : ∫⁻ η, ‖qAvg c f η‖ₑ ^ p.toReal ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ z, ‖f z‖ₑ ^ p.toReal ∂(cellμ c) := by
    rw [cellμ_eq_prod, lintegral_prod_symm _ hm', ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun η => enorm_qAvg_rpow_le hc hp1 hp f η
  calc (∫⁻ η, ‖qAvg c f η‖ₑ ^ p.toReal) ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal c⁻¹ * ∫⁻ z, ‖f z‖ₑ ^ p.toReal ∂(cellμ c)) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hI (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hc.le) (by positivity),
          Real.inv_rpow hc.le, ← Real.rpow_neg hc.le, neg_div]

/-! ### Wirtinger on the cell -/

theorem lintegral_Ico_enorm_sq_eq {c : ℝ} (hc : 0 < c) {g : ℝ → ℂ} (hg : Continuous g) :
    ∫⁻ q in Ico (-c / 2) (c / 2), ‖g q‖ₑ ^ 2 =
      ENNReal.ofReal (∫ q in (-c / 2)..(c / 2), ‖g q‖ ^ 2) := by
  have hint : IntegrableOn (fun q => ‖g q‖ ^ 2) (Ico (-c / 2) (c / 2)) :=
    ((hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ico_subset_Icc_self
  rw [intervalIntegral.integral_of_le (neg_half_lt_half hc).le, restrict_Ioc_half_eq_Ico,
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => by positivity)]
  exact lintegral_congr fun q => (ofReal_norm_sq _).symm

/-- Wirtinger's inequality on the cell, in `ℝ≥0∞`. -/
theorem lintegral_cell_sub_qAvg_le {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsPeriodic c f) :
    ∫⁻ z in cell c, ‖f z - qAvg c f z.2‖ₑ ^ 2 ≤
      ENNReal.ofReal ((c / (2 * π)) ^ 2) * ∫⁻ z in cell c, ‖partialQ f z‖ₑ ^ 2 := by
  have hfc := hf.continuous
  have hpc := (C1_partial_of_contDiff hf).1
  have hA : AEStronglyMeasurable (qAvg c f) volume :=
    aestronglyMeasurable_qAvg hc hfc.aestronglyMeasurable
  have hB : AEStronglyMeasurable (fun z : Plane => f z - qAvg c f z.2)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) :=
    hfc.aestronglyMeasurable.sub hA.comp_snd
  have hD : AEMeasurable (fun z : Plane => ‖partialQ f z‖ₑ ^ 2)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) :=
    hpc.aestronglyMeasurable.enorm.pow_const 2
  rw [cellμ_eq_restrict, cellμ_eq_prod, lintegral_prod_symm _ (hB.enorm.pow_const 2),
    lintegral_prod_symm _ hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun η => ?_
  have hs1 : Continuous fun q : ℝ => f (q, η) - qAvg c f η :=
    (hfc.comp (continuous_id.prodMk continuous_const)).sub continuous_const
  have hs2 : Continuous fun q : ℝ => partialQ f (q, η) :=
    hpc.comp (continuous_id.prodMk continuous_const)
  rw [lintegral_Ico_enorm_sq_eq hc hs1, lintegral_Ico_enorm_sq_eq hc hs2,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (wirtinger_slice hc hf hper η)

theorem eLpNorm_two_eq_lintegral {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℂ) :
    eLpNorm g 2 μ = (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- **Wirtinger on the cell** (CY04 `norm_sub_qAvg_le`; B0566, tex 9077-9085, constant
`c/(2π)`): for a `C¹`, `c`-periodic `f`,
`‖f - f̄‖_{L²(cell)} ≤ (c/2π) ‖∂_q f‖_{L²(cell)}`. -/
theorem eLpNorm_sub_qAvg_le {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsPeriodic c f) :
    eLpNorm (fun z : Plane => f z - qAvg c f z.2) 2 (cellμ c) ≤
      ENNReal.ofReal (c / (2 * π)) * eLpNorm (partialQ f) 2 (cellμ c) := by
  rw [eLpNorm_two_eq_lintegral, eLpNorm_two_eq_lintegral]
  have h := lintegral_cell_sub_qAvg_le hc hf hper
  calc (∫⁻ z, ‖f z - qAvg c f z.2‖ₑ ^ 2 ∂(cellμ c)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((c / (2 * π)) ^ 2) *
          ∫⁻ z, ‖partialQ f z‖ₑ ^ 2 ∂(cellμ c)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = _ := by
        have hk : 0 ≤ c / (2 * π) := by positivity
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hk]

/-- The zero-mean case of Wirtinger on the cell: if `f̄ ≡ 0`, then
`‖f‖_{L²(cell)} ≤ (c/2π) ‖∂_q f‖_{L²(cell)}`. -/
theorem eLpNorm_le_of_qAvg_eq_zero {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsPeriodic c f) (hzero : ∀ η, qAvg c f η = 0) :
    eLpNorm f 2 (cellμ c) ≤ ENNReal.ofReal (c / (2 * π)) * eLpNorm (partialQ f) 2 (cellμ c) := by
  have h := eLpNorm_sub_qAvg_le hc hf hper
  simp only [hzero, sub_zero] at h
  exact h

end UnforcedLeray.Cyl
