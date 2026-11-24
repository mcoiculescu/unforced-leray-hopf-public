import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T18
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Weights
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8.FlatPoly
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique

/-!
# Cross-exponent uniqueness of the flat response (`PartII-b:T18/1` helper)

Source of record: `the November 2 reference manuscript`, lines 1923-1938, 1992-2004.

Proves that if `F₁ ∈ H_{r₁}` and `F₂ ∈ H_{r₂}` agree `dm c`-a.e., then their flat responses
`b0₁` (in `InFlatClass c r₁`) and `b0₂` (in `InFlatClass c r₂`) agree Lebesgue-a.e. on `{s > 0}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.HrOpHelp

/-- Pointwise a.e. convergence of `cylMoll (mollBump n) D` to `D` with respect to `Cyl.avgμ c`. -/
theorem ae_tendsto_cylMoll {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {D : ℝ × ℝ → CMerid}
    (hD : CylLp c r D) :
    ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c),
      Tendsto (fun n => cylMoll (mollBump n) D z) atTop (𝓝 (D z)) := by
  have hli := cylLocInt c r hc hr D hD
  have hv : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      Tendsto (fun n => cylMoll (mollBump n) D z) atTop (𝓝 (D z)) := by
    have := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := mollBump) (l := atTop) (K := 2) (μ := (volume : Measure (ℝ × ℝ)))
      (g := D) ?_ ?_ hli
    · filter_upwards [this] with z hz
      simpa [cylMoll, convolution_def] using hz
    · show Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0)
      exact Tendsto.div_atTop tendsto_const_nhds
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    · refine Eventually.of_forall fun n => ?_
      show 2 / ((n : ℝ) + 2) ≤ 2 * (1 / ((n : ℝ) + 2))
      rw [mul_one_div]
  have hac : UnforcedLeray.Cyl.avgμ c ≪ (volume : Measure (ℝ × ℝ)) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _
  exact hac.ae_le hv

/-- Boundedness and `MemLp` at `r₁` imply `MemLp` at `r₂ ≥ r₁`. -/
theorem memLp_of_le_of_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r₁ r₂ : ℝ} (hr₁ : 1 < r₁) (hr12 : r₁ ≤ r₂) {E : α → CMerid}
    (hE₁ : MemLp E (ENNReal.ofReal r₁) μ) (hM : ∃ M : ℝ, ∀ z (i : Fin 2), ‖E z i‖ ≤ M) :
    MemLp E (ENNReal.ofReal r₂) μ := by
  obtain ⟨M, hMb⟩ := hM
  set B : ℝ := 2 * max M 0
  have hB0 : 0 ≤ B := by positivity
  have hEnorm : ∀ z, ‖E z‖ ≤ B := by
    intro z
    have h0 : ‖E z 0‖ ≤ max M 0 := (hMb z 0).trans (le_max_left _ _)
    have h1 : ‖E z 1‖ ≤ max M 0 := (hMb z 1).trans (le_max_left _ _)
    have heq : E z = E z 0 • EuclideanSpace.single 0 (1 : ℂ) +
        E z 1 • EuclideanSpace.single 1 (1 : ℂ) := by
      ext i; fin_cases i <;> simp
    have hle : ‖E z‖ ≤ ‖E z 0‖ + ‖E z 1‖ := by
      rw [heq]
      refine (norm_add_le _ _).trans ?_
      simp [norm_smul]
    linarith
  have hr₁0 : 0 < r₁ := by linarith
  have hr₂0 : 0 < r₂ := by linarith
  have hp₁0 : ENNReal.ofReal r₁ ≠ 0 := (ENNReal.ofReal_pos.2 hr₁0).ne'
  have hp₁t : ENNReal.ofReal r₁ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp₂0 : ENNReal.ofReal r₂ ≠ 0 := (ENNReal.ofReal_pos.2 hr₂0).ne'
  have hp₂t : ENNReal.ofReal r₂ ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨hE₁.1, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₂0 hp₂t,
    ENNReal.toReal_ofReal hr₂0.le]
  have hfin₁ : ∫⁻ z, ‖E z‖ₑ ^ r₁ ∂μ < ⊤ := by
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₁0 hp₁t).1 hE₁.2
    rwa [ENNReal.toReal_ofReal hr₁0.le] at this
  have hpt : ∀ z, ‖E z‖ₑ ^ r₂ ≤ (ENNReal.ofReal B) ^ (r₂ - r₁) * ‖E z‖ₑ ^ r₁ := by
    intro z
    rcases eq_or_ne ‖E z‖ₑ 0 with hz | hz
    · rw [hz, ENNReal.zero_rpow_of_pos hr₂0]
      exact zero_le
    · have hadd := ENNReal.rpow_add (r₂ - r₁) r₁ hz ENNReal.coe_ne_top
      rw [sub_add_cancel] at hadd
      rw [hadd]
      refine mul_le_mul_of_nonneg_right ?_ zero_le
      refine ENNReal.rpow_le_rpow ?_ (sub_nonneg.2 hr12)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hEnorm z)
  calc ∫⁻ z, ‖E z‖ₑ ^ r₂ ∂μ
      ≤ ∫⁻ z, (ENNReal.ofReal B) ^ (r₂ - r₁) * ‖E z‖ₑ ^ r₁ ∂μ := lintegral_mono hpt
    _ = (ENNReal.ofReal B) ^ (r₂ - r₁) * ∫⁻ z, ‖E z‖ₑ ^ r₁ ∂μ :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hr12) ENNReal.ofReal_ne_top)
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.2 hr12) ENNReal.ofReal_ne_top) hfin₁

/-- Auxiliary `r₁ ≤ r₂` case for cross-exponent cylinder Helmholtz uniqueness. -/
theorem isCylHelmholtz_unique_le {c r₁ r₂ : ℝ} (hc : 0 < c) (hr₁ : 1 < r₁) (hr12 : r₁ ≤ r₂)
    {f g₁ g₂ : ℝ × ℝ → CMerid}
    (h₁ : IsCylHelmholtz c r₁ f g₁) (h₂ : IsCylHelmholtz c r₂ f g₂) :
    g₁ =ᵐ[UnforcedLeray.Cyl.avgμ c] g₂ := by
  have hr₂ : 1 < r₂ := lt_of_lt_of_le hr₁ hr12
  set μ := UnforcedLeray.Cyl.avgμ c
  have hmoll_eq : ∀ n : ℕ,
      cylMoll (mollBump n) g₁ =ᵐ[μ] cylMoll (mollBump n) g₂ := by
    intro n
    set ρ := mollBump n
    set E₁ := cylMoll ρ g₁
    set E₂ := cylMoll ρ g₂
    obtain ⟨hper₁, _⟩ := cylMollSmoothPeriodic c r₁ hc hr₁ g₁ h₁.1 ρ
    obtain ⟨hper₂, _⟩ := cylMollSmoothPeriodic c r₂ hc hr₂ g₂ h₂.1 ρ
    have hmem₁_r₁ := cylMollMemLp c r₁ hc hr₁ g₁ h₁.1 ρ
    have hmem₁ : MemLp E₁ (ENNReal.ofReal r₂) μ :=
      memLp_of_le_of_bounded hr₁ hr12 hmem₁_r₁ (cylMollBounded c r₁ hc hr₁ g₁ h₁.1 ρ)
    have hmem₂ : MemLp E₂ (ENNReal.ofReal r₂) μ :=
      cylMollMemLp c r₂ hc hr₂ g₂ h₂.1 ρ
    have hLp₁ : CylLp c r₂ E₁ := ⟨hper₁, hmem₁⟩
    have hLp₂ : CylLp c r₂ E₂ := ⟨hper₂, hmem₂⟩
    have hLp_sub : CylLp c r₂ (E₁ - E₂) := cylLp_sub hLp₁ hLp₂
    have hdiv₁ : CylWeakDiv c E₁ :=
      cylMollWeakDiv c r₁ hc hr₁ g₁ h₁.1 (fun φ hφ => (h₁.2.1 φ hφ).2) ρ
    have hdiv₂ : CylWeakDiv c E₂ :=
      cylMollWeakDiv c r₂ hc hr₂ g₂ h₂.1 (fun φ hφ => (h₂.2.1 φ hφ).2) ρ
    have hdiv_sub : CylWeakDiv c (E₁ - E₂) := by
      intro φ hφ
      obtain ⟨hwc, ⟨M, hwb⟩, ⟨L, hws⟩⟩ := cylTest_weights hc hφ
      have i₁' := cylPair_integrable hc hr₂ hwc hwb hws hmem₁
      have i₂' := cylPair_integrable hc hr₂ hwc hwb hws hmem₂
      have heq_pair : ∀ H : ℝ × ℝ → CMerid,
          (fun z => H z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + H z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) =
          cylPair (testWeights φ) H := by
        intro H; funext z; simp [cylPair, testWeights, Fin.sum_univ_two]
      have i₁ : Integrable (fun z => E₁ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
          E₁ z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) μ := by
        rw [heq_pair]; exact i₁'
      have i₂ : Integrable (fun z => E₂ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
          E₂ z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) μ := by
        rw [heq_pair]; exact i₂'
      have hsub : ∫ z, ((E₁ - E₂) z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
          (E₁ - E₂) z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) ∂μ =
          (∫ z, (E₁ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + E₁ z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) ∂μ) -
          ∫ z, (E₂ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + E₂ z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) ∂μ := by
        rw [← integral_sub i₁ i₂]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [Pi.sub_apply, PiLp.sub_apply]; ring
      rw [hsub, hdiv₁ φ hφ, hdiv₂ φ hφ, sub_self]
    have hsol_sub : CylWeakSol c (E₁ - E₂) := by
      intro Ψ hΨ
      obtain ⟨hwc, ⟨M, hwb⟩, ⟨L, hws⟩⟩ := cylSol_weights hc hΨ
      have iE₁ : Integrable (fun z => ∑ i : Fin 2, E₁ z i * (Ψ z i : ℂ)) μ :=
        cylPair_integrable hc hr₂ hwc hwb hws hmem₁
      have iE₂ : Integrable (fun z => ∑ i : Fin 2, E₂ z i * (Ψ z i : ℂ)) μ :=
        cylPair_integrable hc hr₂ hwc hwb hws hmem₂
      have hsub : ∫ z, ∑ i : Fin 2, (E₁ - E₂) z i * (Ψ z i : ℂ) ∂μ =
          (∫ z, ∑ i : Fin 2, E₁ z i * (Ψ z i : ℂ) ∂μ) -
          ∫ z, ∑ i : Fin 2, E₂ z i * (Ψ z i : ℂ) ∂μ := by
        rw [← integral_sub iE₁ iE₂]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [Fin.sum_univ_two, Pi.sub_apply, PiLp.sub_apply]; ring
      rw [hsub, cylMollSwapSol c r₁ hc hr₁ g₁ h₁.1 ρ Ψ hΨ,
        cylMollSwapSol c r₂ hc hr₂ g₂ h₂.1 ρ Ψ hΨ]
      set Ψ' : ℝ × ℝ → Fin 2 → ℝ := fun z i => testMoll ρ (fun w => Ψ w i) z
      have hΨ' : CylSolTest c Ψ' := solTestMollIsSolTest c ρ Ψ hΨ
      obtain ⟨hwc', ⟨M', hwb'⟩, ⟨L', hws'⟩⟩ := cylSol_weights hc hΨ'
      have ig₁ : Integrable (fun u => ∑ i : Fin 2, g₁ u i * (Ψ' u i : ℂ)) μ :=
        cylPair_integrable hc hr₁ hwc' hwb' hws' h₁.1.2
      have ig₂ : Integrable (fun u => ∑ i : Fin 2, g₂ u i * (Ψ' u i : ℂ)) μ :=
        cylPair_integrable hc hr₂ hwc' hwb' hws' h₂.1.2
      obtain ⟨i₁', hsol₁⟩ := h₁.2.2 Ψ' hΨ'
      obtain ⟨i₂', hsol₂⟩ := h₂.2.2 Ψ' hΨ'
      have hdiff : (∫ u, ∑ i : Fin 2, g₁ u i * (Ψ' u i : ℂ) ∂μ) -
          (∫ u, ∑ i : Fin 2, g₂ u i * (Ψ' u i : ℂ) ∂μ) =
          (∫ u, ∑ i : Fin 2, (f u i - g₂ u i) * (Ψ' u i : ℂ) ∂μ) -
          (∫ u, ∑ i : Fin 2, (f u i - g₁ u i) * (Ψ' u i : ℂ) ∂μ) := by
        rw [← integral_sub ig₁ ig₂, ← integral_sub i₂' i₁']
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [Fin.sum_univ_two]; ring
      rw [hdiff, hsol₂, hsol₁, sub_self]
    have h0 := cylHelmholtzUnique c r₂ hc hr₂ (E₁ - E₂) hLp_sub hdiv_sub hsol_sub
    filter_upwards [h0] with z hz
    have hz' : E₁ z - E₂ z = 0 := by simpa using hz
    exact sub_eq_zero.1 hz'
  have hall := ae_all_iff.2 hmoll_eq
  filter_upwards [hall, ae_tendsto_cylMoll hc hr₁ h₁.1, ae_tendsto_cylMoll hc hr₂ h₂.1]
    with z hz ht₁ ht₂
  have hseq : (fun n => cylMoll (mollBump n) g₁ z) = fun n => cylMoll (mollBump n) g₂ z :=
    funext hz
  rw [hseq] at ht₁
  exact tendsto_nhds_unique ht₁ ht₂

/-- Cross-exponent cylinder Helmholtz uniqueness. -/
theorem isCylHelmholtz_unique_cross {c r₁ r₂ : ℝ} (hc : 0 < c) (hr₁ : 1 < r₁) (hr₂ : 1 < r₂)
    {f g₁ g₂ : ℝ × ℝ → CMerid}
    (h₁ : IsCylHelmholtz c r₁ f g₁) (h₂ : IsCylHelmholtz c r₂ f g₂) :
    g₁ =ᵐ[UnforcedLeray.Cyl.avgμ c] g₂ := by
  rcases le_total r₁ r₂ with hr12 | hr21
  · exact isCylHelmholtz_unique_le hc hr₁ hr12 h₁ h₂
  · exact (isCylHelmholtz_unique_le hc hr₂ hr21 h₂ h₁).symm

/-- Given `G ∈ H_r` with `WeakSolenoidal G` and `PerpPlanarSol (F - G)`, `flatDuhamel ν μ G`
belongs to `InFlatClass c r` and is a flat response to `F`. -/
theorem flatDuhamel_inFlatClass_and_resp {c ν r : ℝ} {μ : ℂ} {F G : CProf}
    (hc : 0 < c) (hν : 0 < ν) (hr1 : 1 < r) (hr3 : r < 3)
    (ha : 0 < μ.re + (3 / r - 1) / 2)
    (hGH : InHr c r G) (hGs : WeakSolenoidal G) (hGp : PerpPlanarSol (F - G)) :
    InFlatClass c r (flatDuhamel ν μ G) ∧ IsFlatResponse ν μ F (flatDuhamel ν μ G) := by
  obtain ⟨M, C, Ci, hM, hC, hCi, hWK⟩ := windowBound_explicit r hr1 hr3
  set K := 2 * flatK0Fn M C Ci μ
  have hK : 0 < K := mul_pos (by norm_num) (flatK0Fn_pos hM hC hCi μ)
  have hbm := duhamelMeasurable r hr1 hr3 μ ha ν c hν hc G hGH
  have hbn := duhamelBound r hr1 hr3 μ ha ν c hν hc G hGH
  have hbper := duhamelPeriodic ν μ c G hc hGH.periodic
  have hbH : InHr c r (flatDuhamel ν μ G) :=
    ⟨hbper, hbm, lt_of_le_of_lt hbn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGH.finite)⟩
  have hbs := duhamelSolenoidal r hr1 hr3 μ ha ν c hν hc G hGH hGs hbH
  have hresp : IsFlatResponse ν μ F (flatDuhamel ν μ G) := by
    refine ⟨hbs, fun Ψ hΨ => ?_⟩
    obtain ⟨hi1, hi2, he⟩ := duhamelEquation r hr1 hr3 μ ha ν c hν hc G hGH hbH Ψ hΨ
    obtain ⟨hj1, hj2⟩ := hGp Ψ hΨ
    have hsplit := cdot_eq_add_sub F G Ψ
    refine ⟨hi1, ?_, ?_⟩
    · rw [hsplit]
      exact hi2.add hj1
    · rw [hsplit, integral_add hi2 hj1, hj2, add_zero]
      exact he
  have hfull := duhamelFullEq r hr1 hr3 μ ha ν c hν hc G hGH hbH
  set b := flatDuhamel ν μ G
  have hPfin : ENNReal.ofReal (4 * K) * (hNorm c r G + hNorm c r b) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hGH.finite, hbH.finite⟩)
  obtain ⟨S, Q, E, hw⟩ := hWK μ ν c hν hc G b hGH hbH hfull
  obtain ⟨Sb, hSbw, hSbp, hSbm, hSbe⟩ := weakGlue vS fw_vS_smooth c b S
    (fun a ha' => (hw a ha').1) (fun a ha' => (hw a ha').2.2.2.1)
  obtain ⟨Qb, hQbw, hQbp, hQbm, hQbe⟩ := weakGlue vQ0 fw_vQ0_smooth c b Q
    (fun a ha' => (hw a ha').2.1) (fun a ha' => (hw a ha').2.2.2.2.1)
  obtain ⟨Eb, hEbw, hEbp, hEbm, hEbe⟩ := weakGlue vEta fw_vEta_smooth c b E
    (fun a ha' => (hw a ha').2.2.1) (fun a ha' => (hw a ha').2.2.2.2.2.1)
  have hpos : ∀ k : ℤ, (0 : ℝ) < (2 : ℝ) ^ k := fun k => zpow_pos (by norm_num) k
  have hSk : ∀ k : ℤ, ENNReal.ofReal 1 * hNormOn c r (winOpen ((2 : ℝ) ^ k)) Sb ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [ENNReal.ofReal_one, one_mul, fw_hNormOn_congr (hSbe _ (hpos k))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.1
  have hSn : hNorm c r Sb ≤ ENNReal.ofReal (4 * K) * (hNorm c r G + hNorm c r b) := by
    have h := dyadicSummation r c hr1.le hc Sb G b 1 K zero_le_one hK.le
      (hSbm.mono_ac (fw_hMeas_ac c r)) hGH.meas hbH.meas hSk
    rwa [ENNReal.ofReal_one, one_mul] at h
  have hQk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c r (winOpen ((2 : ℝ) ^ k)) (sqrtS Qb) ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hQbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.1
  have hQn : ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Qb) ≤
      ENNReal.ofReal (4 * K) * (hNorm c r G + hNorm c r b) :=
    dyadicSummation r c hr1.le hc (sqrtS Qb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c r))) hGH.meas hbH.meas hQk
  have hEk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c r (winOpen ((2 : ℝ) ^ k)) (sqrtS Eb) ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hEbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2
  have hEn : ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Eb) ≤
      ENNReal.ofReal (4 * K) * (hNorm c r G + hNorm c r b) :=
    dyadicSummation r c hr1.le hc (sqrtS Eb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c r))) hGH.meas hbH.meas hEk
  have hsq0 : ENNReal.ofReal (Real.sqrt ν) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hν)).ne'
  have hQfin : hNorm c r (sqrtS Qb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hQn hPfin).ne hsq0
  have hEfin : hNorm c r (sqrtS Eb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hEn hPfin).ne hsq0
  refine ⟨⟨hbH, Sb, Qb, Eb, hSbw, hQbw, hEbw,
    ⟨hSbp, hSbm.mono_ac (fw_hMeas_ac c r), lt_of_le_of_lt hSn hPfin⟩,
    ⟨qPeriodic_sqrtS hQbp, aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c r)), hQfin⟩,
    ⟨qPeriodic_sqrtS hEbp, aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c r)), hEfin⟩⟩,
    hresp⟩

/-- Lebesgue-a.e. agreement on `{s > 0}` implies `hMeas c r`-a.e. agreement. -/
theorem ae_hMeas_of_ae_pos {c r : ℝ} (hc : 0 < c) {f g : CProf}
    (h : ∀ᵐ x : Coord, 0 < x.1 → f x = g x) : f =ᵐ[hMeas c r] g := by
  show ∀ᵐ x ∂(Axi.ageμ c (r / 2 - 5 / 2)), f x = g x
  rw [ageμ_eq_withDensity hc (r / 2 - 5 / 2), ae_withDensity_iff (measurable_dens c _)]
  filter_upwards [h] with x hx hxd
  have hm : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c := by
    by_contra hnot
    exact hxd (by simp [dens, Set.indicator_of_notMem hnot])
  exact hx hm.1

/-- Cross-exponent flat Leray lift: if `F ∈ H_{r₁} ∩ H_{r₂}`, there is a single profile `G`
which is a flat Leray projection of `F` in both `H_{r₁}` and `H_{r₂}`. -/
theorem flatLerayLift_common {c r₁ r₂ : ℝ} (hc : 0 < c)
    (hr₁1 : 1 < r₁) (hr₂1 : 1 < r₂)
    {F : CProf} (hF₁ : InHr c r₁ F) (hF₂ : InHr c r₂ F) :
    ∃ G : CProf, InHr c r₁ G ∧ InHr c r₂ G ∧ WeakSolenoidal G ∧ PerpPlanarSol (F - G) := by
  obtain ⟨C₁, hC₁, hCL₁⟩ := cylinderHelmholtzLr r₁ hr₁1
  obtain ⟨C₂, hC₂, hCL₂⟩ := cylinderHelmholtzLr r₂ hr₂1
  obtain ⟨P₁, hPb₁, hPl₁⟩ := hCL₁ c hc
  obtain ⟨P₂, hPb₂, hPl₂⟩ := hCL₂ c hc
  obtain ⟨F', hF's, hF'p, hFa₁, hFa'⟩ := LerayLiftSub.slicePeriodicRep_proof c r₁ hc F hF₁
  have hFa_pos : ∀ᵐ x : Coord, 0 < x.1 → F' x = F x := by
    filter_upwards [hFa'] with x hx hpos
    exact (hx hpos).symm
  have hF'eq₁ : hNorm c r₁ F' = hNorm c r₁ F :=
    eLpNorm_congr_ae (hFa₁.mono fun _ hx => hx.symm)
  have hF'fin₁ : hNorm c r₁ F' < ⊤ := by rw [hF'eq₁]; exact hF₁.finite
  have hFa₂ : F' =ᵐ[hMeas c r₂] F := ae_hMeas_of_ae_pos hc hFa_pos
  have hF'eq₂ : hNorm c r₂ F' = hNorm c r₂ F :=
    eLpNorm_congr_ae hFa₂
  have hF'fin₂ : hNorm c r₂ F' < ⊤ := by rw [hF'eq₂]; exact hF₂.finite
  obtain ⟨G₁, hGs₁, hGper₁, hGjoint₁⟩ :=
    sliceJointHelmholtz_proof c r₁ C₁ P₁ hc hr₁1 hC₁ hPb₁ hPl₁ F' hF's hF'p hF'fin₁
  obtain ⟨G₂, hGs₂, hGper₂, hGjoint₂⟩ :=
    sliceJointHelmholtz_proof c r₂ C₂ P₂ hc hr₂1 hC₂ hPb₂ hPl₂ F' hF's hF'p hF'fin₂
  have hCyl₁ := sliceCylLpAe_proof c r₁ hc hr₁1 F' hF's hF'p hF'fin₁
  have hCyl₂ := sliceCylLpAe_proof c r₂ hc hr₂1 F' hF's hF'p hF'fin₂
  have hbound₁ : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      eLpNorm (fun z => G₁ (s, z)) (ENNReal.ofReal r₁) (UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal C₁ *
          eLpNorm (fun z => F' (s, z)) (ENNReal.ofReal r₁) (UnforcedLeray.Cyl.avgμ c) := by
    filter_upwards [hGjoint₁, hCyl₁] with s hs hcs
    exact (eLpNorm_congr_ae hs).trans_le (hPb₁ _ hcs).2
  have hGnorm₁ : hNorm c r₁ G₁ ≤ ENNReal.ofReal C₁ * hNorm c r₁ F' :=
    sliceNormBound_proof c r₁ C₁ G₁ F' hc (by linarith) hC₁.le hGs₁ hF's hbound₁
  have hGfin₁ : hNorm c r₁ G₁ < ⊤ :=
    lt_of_le_of_lt hGnorm₁ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF'fin₁)
  have hGH₁ : InHr c r₁ G₁ :=
    { periodic := Eventually.of_forall fun x => hGper₁ x.1 x.2
      meas := hGs₁.aestronglyMeasurable
      finite := hGfin₁ }
  have hbound₂ : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      eLpNorm (fun z => G₁ (s, z)) (ENNReal.ofReal r₂) (UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal C₂ *
          eLpNorm (fun z => F' (s, z)) (ENNReal.ofReal r₂) (UnforcedLeray.Cyl.avgμ c) := by
    filter_upwards [hGjoint₁, hGjoint₂, hCyl₁, hCyl₂] with s hs₁ hs₂ hcs₁ hcs₂
    have hP12 : P₁ (fun z => F' (s, z)) =ᵐ[UnforcedLeray.Cyl.avgμ c] P₂ (fun z => F' (s, z)) :=
      isCylHelmholtz_unique_cross hc hr₁1 hr₂1 (hPb₁ _ hcs₁).1 (hPb₂ _ hcs₂).1
    have hG1P2 : (fun z => G₁ (s, z)) =ᵐ[UnforcedLeray.Cyl.avgμ c] P₂ (fun z => F' (s, z)) :=
      hs₁.trans hP12
    exact (eLpNorm_congr_ae hG1P2).trans_le (hPb₂ _ hcs₂).2
  have hGnorm₂ : hNorm c r₂ G₁ ≤ ENNReal.ofReal C₂ * hNorm c r₂ F' :=
    sliceNormBound_proof c r₂ C₂ G₁ F' hc (by linarith) hC₂.le hGs₁ hF's hbound₂
  have hGfin₂ : hNorm c r₂ G₁ < ⊤ :=
    lt_of_le_of_lt hGnorm₂ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF'fin₂)
  have hGH₂ : InHr c r₂ G₁ :=
    { periodic := Eventually.of_forall fun x => hGper₁ x.1 x.2
      meas := hGs₁.aestronglyMeasurable
      finite := hGfin₂ }
  have hGw : WeakSolenoidal G₁ := by
    apply sliceWeakSolenoidal_proof c r₁ G₁ hc hr₁1 hGs₁ hGper₁ hGH₁
    filter_upwards [hGjoint₁, hCyl₁] with s hs hcs
    intro Φ hΦ
    have hcyl := (hPb₁ _ hcs).1.2.1 Φ hΦ
    have hae : (fun z => G₁ (s, z) 0 * (fderiv ℝ Φ z (1, 0) : ℂ) +
          G₁ (s, z) 1 * (fderiv ℝ Φ z (0, 1) : ℂ)) =ᵐ[UnforcedLeray.Cyl.avgμ c]
        (fun z => P₁ (fun w => F' (s, w)) z 0 * (fderiv ℝ Φ z (1, 0) : ℂ) +
          P₁ (fun w => F' (s, w)) z 1 * (fderiv ℝ Φ z (0, 1) : ℂ)) :=
      hs.mono fun z hz => by
        have hz' : G₁ (s, z) = P₁ (fun w => F' (s, w)) z := hz
        dsimp only
        rw [hz']
    exact ⟨hcyl.1.congr hae.symm, by rw [integral_congr_ae hae]; exact hcyl.2⟩
  have hPp : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, CylSolTest c Ψ →
      Integrable (fun z => ∑ i : Fin 2, (F' (s, z) i - G₁ (s, z) i) * (Ψ z i : ℂ))
          (UnforcedLeray.Cyl.avgμ c) ∧
        ∫ z, ∑ i : Fin 2, (F' (s, z) i - G₁ (s, z) i) * (Ψ z i : ℂ)
          ∂(UnforcedLeray.Cyl.avgμ c) = 0 := by
    filter_upwards [hGjoint₁, hCyl₁] with s hs hcs
    intro Ψ hΨ
    have hcyl := (hPb₁ _ hcs).1.2.2 Ψ hΨ
    have hae : (fun z => ∑ i : Fin 2, (F' (s, z) i - G₁ (s, z) i) * (Ψ z i : ℂ)) =ᵐ[UnforcedLeray.Cyl.avgμ c]
        (fun z => ∑ i : Fin 2, (F' (s, z) i - P₁ (fun w => F' (s, w)) z i) * (Ψ z i : ℂ)) :=
      hs.mono fun z hz => by
        have hz' : G₁ (s, z) = P₁ (fun w => F' (s, w)) z := hz
        dsimp only
        rw [hz']
    exact ⟨hcyl.1.congr hae.symm, by rw [integral_congr_ae hae]; exact hcyl.2⟩
  have hGp : PerpPlanarSol (F - G₁) :=
    slicePerpPlanar_proof c r₁ F F' G₁ hc hr₁1 hF₁ hF's hF'p hFa' hGH₁ hGs₁ hGper₁ hPp
  exact ⟨G₁, hGH₁, hGH₂, hGw, hGp⟩

/-- Cross-exponent uniqueness of the flat response profile on `{s > 0}`. -/
theorem flatResponse_unique_cross {c ν r₁ r₂ : ℝ} {μ : ℂ} {F₁ F₂ b0₁ b0₂ : CProf}
    (hc : 0 < c) (hν : 0 < ν)
    (hr₁1 : 1 < r₁) (hr₁3 : r₁ < 3) (hr₂1 : 1 < r₂) (hr₂3 : r₂ < 3)
    (hμ₁ : 0 < μ.re + (3 / r₁ - 1) / 2) (hμ₂ : 0 < μ.re + (3 / r₂ - 1) / 2)
    (hF₁ : InHr c r₁ F₁) (hF₂ : InHr c r₂ F₂) (hFF : F₁ =ᵐ[dm c] F₂)
    (hbc₁ : InFlatClass c r₁ b0₁) (hb0₁ : IsFlatResponse ν μ F₁ b0₁)
    (hbc₂ : InFlatClass c r₂ b0₂) (hb0₂ : IsFlatResponse ν μ F₂ b0₂) :
    ∀ᵐ x : Coord, 0 < x.1 → b0₁ x = b0₂ x := by
  have hFF_pos : ∀ᵐ x : Coord, 0 < x.1 → F₁ x = F₂ x :=
    CongrHelp.ae_volume_of_ageμ hc hF₁.periodic hF₂.periodic hFF
  have hFF_r₂ : F₁ =ᵐ[hMeas c r₂] F₂ := ae_hMeas_of_ae_pos hc hFF_pos
  have hF₁_r₂ : InHr c r₂ F₁ :=
    { periodic := hF₁.periodic
      meas := hF₂.meas.congr hFF_r₂.symm
      finite := by
        unfold hNorm
        rw [eLpNorm_congr_ae hFF_r₂]
        exact hF₂.finite }
  have hb0₂' : IsFlatResponse ν μ F₁ b0₂ := by
    refine ⟨hb0₂.1, fun Ψ hΨ => ?_⟩
    obtain ⟨hi1, hi2, he⟩ := hb0₂.2 Ψ hΨ
    have hae_cdot : cdot F₁ Ψ =ᵐ[volume] cdot F₂ Ψ := by
      filter_upwards [hFF_pos] with x hx
      by_cases hpos : 0 < x.1
      · simp only [cdot, hx hpos]
      · have hΨ0 : Ψ x 0 = 0 := by
          by_contra hne
          exact hpos ((hΨ.smooth 0).supp (subset_tsupport (fun y => Ψ y 0) hne)).1
        have hΨ1 : Ψ x 1 = 0 := by
          by_contra hne
          exact hpos ((hΨ.smooth 1).supp (subset_tsupport (fun y => Ψ y 1) hne)).1
        simp [cdot, Fin.sum_univ_two, hΨ0, hΨ1]
    exact ⟨hi1, hi2.congr hae_cdot.symm, by rw [integral_congr_ae hae_cdot]; exact he⟩
  obtain ⟨G, hGH₁, hGH₂, hGs, hGp⟩ := flatLerayLift_common hc hr₁1 hr₂1 hF₁ hF₁_r₂
  obtain ⟨hbc_du₁, hresp_du₁⟩ :=
    flatDuhamel_inFlatClass_and_resp hc hν hr₁1 hr₁3 hμ₁ hGH₁ hGs hGp
  obtain ⟨hbc_du₂, hresp_du₂⟩ :=
    flatDuhamel_inFlatClass_and_resp hc hν hr₂1 hr₂3 hμ₂ hGH₂ hGs hGp
  set b := flatDuhamel ν μ G
  have h0₁ : b0₁ - b =ᵐ[hMeas c r₁] 0 :=
    flat_unique hc hν hr₁1 hr₁3 hμ₁ (b0₁ - b) (flatClassSub c r₁ b0₁ b hbc₁ hbc_du₁)
      (flatResponseSub ν μ F₁ b0₁ b hb0₁ hresp_du₁)
  have h0₂ : b0₂ - b =ᵐ[hMeas c r₂] 0 :=
    flat_unique hc hν hr₂1 hr₂3 hμ₂ (b0₂ - b) (flatClassSub c r₂ b0₂ b hbc₂ hbc_du₂)
      (flatResponseSub ν μ F₁ b0₂ b hb0₂' hresp_du₂)
  have hbb₁ : b0₁ =ᵐ[hMeas c r₁] b := by
    filter_upwards [h0₁] with x hx
    exact sub_eq_zero.mp hx
  have hbb₂ : b0₂ =ᵐ[hMeas c r₂] b := by
    filter_upwards [h0₂] with x hx
    exact sub_eq_zero.mp hx
  have hae₁ : ∀ᵐ x : Coord, 0 < x.1 → b0₁ x = b x :=
    CongrHelp.ae_volume_of_ageμ hc hbc₁.inHr.periodic hbc_du₁.inHr.periodic hbb₁
  have hae₂ : ∀ᵐ x : Coord, 0 < x.1 → b0₂ x = b x :=
    CongrHelp.ae_volume_of_ageμ hc hbc₂.inHr.periodic hbc_du₂.inHr.periodic hbb₂
  filter_upwards [hae₁, hae₂] with x hx₁ hx₂ hpos
  exact (hx₁ hpos).trans (hx₂ hpos).symm

end UnforcedLeray.Short.IIb.HrOpHelp

end
