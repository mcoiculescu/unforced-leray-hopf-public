import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.LimitBound

/-!
# Part III-a, helper of `PartIII-a:T18/3/1/2`: the defect `D2` and the integrated bounds

`D2 φₖ φ x = ∑ᵢ [(φₖᵢ - φᵢ)² + ∑ⱼ (∂ⱼφₖᵢ - ∂ⱼφᵢ)²](x)` is the integrand of the hypothesis
`hT` of `DivFreeCutoffDensity`. Its cell integral tends to `0`. On the box `T = [a, u] × cell`:

* the difference `Eφₖ - Eφ` of the extended integrands is integrable (`diff_integrableOn_T`);
* its integral is bounded by `3 t K² ∫_T q² + (1/(2t)) |[a,u]| ∫_cell D2` for every `t > 0`
  (`norm_diff_integral_T_le`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The defect integrand `∑ᵢ [(φₖᵢ - φᵢ)² + ∑ⱼ (∂ⱼφₖᵢ - ∂ⱼφᵢ)²]`. -/
def D2 (φk φ : ℝ × ℝ → Fin 2 → ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ i : Fin 2, ((φk x i - φ x i) ^ 2 +
    ∑ j : Fin 2, (B0579.pd j (fun y => φk y i) x - B0579.pd j (fun y => φ y i) x) ^ 2)

lemma D2_nonneg (φk φ : ℝ × ℝ → Fin 2 → ℝ) (x : ℝ × ℝ) : 0 ≤ D2 φk φ x :=
  Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)

lemma D2_continuous {c : ℝ} {φ φk : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsH1DivFreeTest c φ)
    (hk : IsFlatSpatialTest c φk) : Continuous (D2 φk φ) := by
  unfold D2
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.add (((hk.smooth i).continuous.sub (hφ.smooth i).continuous).pow 2) ?_
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_pd_of_contDiff (hk.smooth i) j).sub
      (continuous_pd_of_contDiff (hφ.smooth i) j)).pow 2

/-- The `x`-function `D2` integrated over the time-space box `[a, u] × cell`. -/
lemma integrableOn_snd_T {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : IntegrableOn f (B0579.cell c)) (a u : ℝ) :
    IntegrableOn (fun p : ℝ × (ℝ × ℝ) => f p.2) (Icc a u ×ˢ B0579.cell c) := by
  have h := Integrable.comp_snd (μ := volume.restrict (Icc a u)) hf
  rw [Measure.prod_restrict] at h
  rw [← Measure.volume_eq_prod ℝ (ℝ × ℝ)] at h
  exact h

/-- The space-time box integral of a function of `x` alone. -/
lemma setIntegral_snd_T (f : ℝ × ℝ → ℝ) (a u c : ℝ) :
    ∫ p in Icc a u ×ˢ B0579.cell c, f p.2 = volume.real (Icc a u) * ∫ x in B0579.cell c, f x := by
  have hvol : (volume : Measure (ℝ × (ℝ × ℝ))) =
      (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) := Measure.volume_eq_prod _ _
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
    (fun _ : ℝ => (1 : ℝ)) f (Icc a u) (B0579.cell c)
  rw [hvol]
  simp only [one_mul, setIntegral_const, smul_eq_mul, mul_one] at h
  exact h

/-- The defect integrands are eventually integrable (from `hT`, through the lintegral). -/
lemma eventually_D2_integrable {c : ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsH1DivFreeTest c φ)
    {φk : ℕ → ℝ × ℝ → Fin 2 → ℝ} (hk : ∀ k, IsFlatSpatialTest c (φk k))
    (hT : Tendsto (fun k => ∫⁻ x in B0579.cell c, ENNReal.ofReal (D2 (φk k) φ x)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, Integrable (D2 (φk k) φ) (volume.restrict (B0579.cell c)) := by
  filter_upwards [hT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))] with k hmem
  have hk1 : ∫⁻ x in B0579.cell c, ENNReal.ofReal (D2 (φk k) φ x) < 1 := Set.mem_Iio.1 hmem
  exact ⟨(D2_continuous hφ (hk k)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => D2_nonneg _ _ x)).2
      (lt_trans hk1 ENNReal.one_lt_top)⟩

/-- The defect integrals tend to `0`. -/
lemma tendsto_D2_integral {c : ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsH1DivFreeTest c φ)
    {φk : ℕ → ℝ × ℝ → Fin 2 → ℝ} (hk : ∀ k, IsFlatSpatialTest c (φk k))
    (hT : Tendsto (fun k => ∫⁻ x in B0579.cell c, ENNReal.ofReal (D2 (φk k) φ x)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in B0579.cell c, D2 (φk k) φ x) atTop (𝓝 0) := by
  have hconv : ∀ k, ∫ x in B0579.cell c, D2 (φk k) φ x =
      (∫⁻ x in B0579.cell c, ENNReal.ofReal (D2 (φk k) φ x)).toReal :=
    fun k => integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => D2_nonneg _ _ x)
      (D2_continuous hφ (hk k)).aestronglyMeasurable
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
  simp only [ENNReal.toReal_zero] at h2
  exact h2.congr fun k => (hconv k).symm

/-- The difference of the extended integrands of `φₖ` and `φ` is integrable on the box. -/
lemma diff_integrableOn_T {c ν : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hdat : FreeSolData c ν μ F b G) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {a u Cψ Cd : ℝ} (ha : 0 < a) (hCψ0 : 0 ≤ Cψ) (hCd0 : 0 ≤ Cd)
    (hCψ : ∀ x, ‖ψ x‖ ≤ Cψ) (hCd : ∀ x, ‖deriv ψ x‖ ≤ Cd)
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsH1DivFreeTest c φ)
    {φk : ℝ × ℝ → Fin 2 → ℝ} (hk : IsFlatSpatialTest c φk)
    (hD : Integrable (D2 φk φ) (volume.restrict (B0579.cell c))) :
    IntegrableOn (fun p => extWeakIntegrand ν μ F b G ψ φk p - extWeakIntegrand ν μ F b G ψ φ p)
      (Icc a u ×ˢ B0579.cell c) := by
  have hTm : MeasurableSet (Icc a u ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hmk : Measurable (extWeakIntegrand ν μ F b G ψ φk) :=
    measurable_extWeak hdat.sol.measurable hdat.sol.gradMeasurable hdat.meas hψ.continuous
      (hψ.continuous_deriv (by simp)) (fun i => (hk.smooth i).continuous)
      (fun i j => continuous_pd_of_contDiff (hk.smooth i) j)
  have hmφ : Measurable (extWeakIntegrand ν μ F b G ψ φ) :=
    measurable_extWeak hdat.sol.measurable hdat.sol.gradMeasurable hdat.meas hψ.continuous
      (hψ.continuous_deriv (by simp)) (fun i => (hφ.smooth i).continuous)
      (fun i j => continuous_pd_of_contDiff (hφ.smooth i) j)
  have hq := qNorm_sq_integrableOn (u := u) hdat ha
  have hD' := integrableOn_snd_T hD a u
  have hg : IntegrableOn (fun p : ℝ × (ℝ × ℝ) => 3 * 1 * Kconst ν μ a Cψ Cd ^ 2 * qNorm b G F p ^ 2 +
      1 / (2 * 1) * D2 φk φ p.2) (Icc a u ×ˢ B0579.cell c) :=
    (hq.const_mul _).add (hD'.const_mul _)
  refine Integrable.mono' hg ((hmk.sub hmφ).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' hTm).2 (Eventually.of_forall fun p hp => ?_)
  have hpa : a ≤ p.1 := (Set.mem_prod.1 hp).1.1
  have hb := extWeak_sub_bound ν μ F b G ha hCψ0 hCd0 hCψ hCd φk φ hpa one_pos
  exact hb.trans_eq (by unfold D2; ring)

/-- The integral of the difference over the box is bounded by the defect integral. -/
lemma norm_diff_integral_T_le {c ν : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hdat : FreeSolData c ν μ F b G) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {a u Cψ Cd : ℝ} (ha : 0 < a) (hCψ0 : 0 ≤ Cψ) (hCd0 : 0 ≤ Cd)
    (hCψ : ∀ x, ‖ψ x‖ ≤ Cψ) (hCd : ∀ x, ‖deriv ψ x‖ ≤ Cd)
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsH1DivFreeTest c φ)
    {φk : ℝ × ℝ → Fin 2 → ℝ} (hk : IsFlatSpatialTest c φk)
    (hD : Integrable (D2 φk φ) (volume.restrict (B0579.cell c))) {t : ℝ} (ht : 0 < t) :
    ‖∫ p in Icc a u ×ˢ B0579.cell c, (extWeakIntegrand ν μ F b G ψ φk p -
        extWeakIntegrand ν μ F b G ψ φ p)‖ ≤
      3 * t * Kconst ν μ a Cψ Cd ^ 2 * (∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) +
        1 / (2 * t) * (volume.real (Icc a u) * ∫ x in B0579.cell c, D2 φk φ x) := by
  have hTm : MeasurableSet (Icc a u ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hq := qNorm_sq_integrableOn (u := u) hdat ha
  have hD' := integrableOn_snd_T hD a u
  have hg : IntegrableOn (fun p : ℝ × (ℝ × ℝ) => 3 * t * Kconst ν μ a Cψ Cd ^ 2 * qNorm b G F p ^ 2 +
      1 / (2 * t) * D2 φk φ p.2) (Icc a u ×ˢ B0579.cell c) :=
    (hq.const_mul _).add (hD'.const_mul _)
  have hae : ∀ᵐ p ∂(volume.restrict (Icc a u ×ˢ B0579.cell c)),
      ‖extWeakIntegrand ν μ F b G ψ φk p - extWeakIntegrand ν μ F b G ψ φ p‖ ≤
        3 * t * Kconst ν μ a Cψ Cd ^ 2 * qNorm b G F p ^ 2 + 1 / (2 * t) * D2 φk φ p.2 := by
    refine (ae_restrict_iff' hTm).2 (Eventually.of_forall fun p hp => ?_)
    have hpa : a ≤ p.1 := (Set.mem_prod.1 hp).1.1
    have hb := extWeak_sub_bound ν μ F b G ha hCψ0 hCd0 hCψ hCd φk φ hpa ht
    exact hb.trans_eq (by unfold D2; ring)
  calc ‖∫ p in Icc a u ×ˢ B0579.cell c, (extWeakIntegrand ν μ F b G ψ φk p -
        extWeakIntegrand ν μ F b G ψ φ p)‖
      ≤ ∫ p in Icc a u ×ˢ B0579.cell c, (3 * t * Kconst ν μ a Cψ Cd ^ 2 * qNorm b G F p ^ 2 +
          1 / (2 * t) * D2 φk φ p.2) :=
        norm_integral_le_of_norm_le hg hae
    _ = 3 * t * Kconst ν μ a Cψ Cd ^ 2 * (∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) +
        1 / (2 * t) * (volume.real (Icc a u) * ∫ x in B0579.cell c, D2 φk φ x) := by
        rw [integral_add (hq.const_mul _) (hD'.const_mul _), integral_const_mul, integral_const_mul,
          setIntegral_snd_T (D2 φk φ) a u c]

end UnforcedLeray.Short.IIIa
