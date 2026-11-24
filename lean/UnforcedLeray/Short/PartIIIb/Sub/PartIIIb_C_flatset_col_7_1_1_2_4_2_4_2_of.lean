import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# `SFCCausalHeatDiff` from the regular datum and the heat bounds (decomposition of
`PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2`)

Source `the November 2 reference manuscript`
3426-3430, 1650-1656.  Differentiation under the `σ`-integral: dominated by
`C (s-σ)^{-1/2}`, via `hasFDerivAt_integral_of_dominated_loc_of_deriv_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Regular datum (source 1650-1656, 1684-1689): for a lift `f'` of a smooth force, `P₀ f'` agrees
`measureH`-ae with a continuous bounded `q`-periodic `G` vanishing for `σ < s₀ > 0`, and for a.e.
`σ > 0` the heat of the periodized `sfcGp` equals the heat of `σ⁻¹ G(σ, ·)` at every time `θ > 0`
(heat only sees the a.e.-class of the datum in `z`; Fubini on `measureH`-null sets; only
`θ = ν (s - σ) > 0` is used, source 3426-3430). -/
def SFCDatumReg : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (g : Hsp c) (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
    IsSmoothForce c g → SFCLift g f' →
      ∃ G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC,
        Continuous G ∧
        (∀ σ q η, G (σ, (q + c, η)) = G (σ, (q, η))) ∧
        (∃ M : ℝ, ∀ p, ‖G p‖ ≤ M) ∧
        (∃ s0 : ℝ, 0 < s0 ∧ ∀ p : UnforcedLeray.B0220.Profile, p.1 < s0 → G p = 0) ∧
        ∀ᵐ σ ∂(volume : Measure ℝ), 0 < σ → ∀ θ : ℝ, 0 < θ →
          UnforcedLeray.B0224.planeHeat θ
              (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) =
            UnforcedLeray.B0224.planeHeat θ (fun z => (((σ : ℝ) : ℂ)⁻¹) • G (σ, z))

/-- Heat bounds on the plane (source 3426-3430, Gaussian kernel: `L¹` norm of `∇` is `~ θ^{-1/2}`):
there is `K` such that for `θ > 0` and bounded continuous `u`, `planeHeat θ u` is differentiable,
`|planeHeat θ u| ≤ M`, and `‖D planeHeat θ u (x)‖ ≤ K θ^{-1/2} M`. -/
def SFCHeatBounds : Prop :=
  ∃ K : ℝ, ∀ θ : ℝ, 0 < θ → ∀ u : ℝ × ℝ → UnforcedLeray.B0223.MeridC, Continuous u →
    ∀ M : ℝ, (∀ y, ‖u y‖ ≤ M) → ∀ x : ℝ × ℝ,
      DifferentiableAt ℝ (UnforcedLeray.B0224.planeHeat θ u) x ∧
      ‖UnforcedLeray.B0224.planeHeat θ u x‖ ≤ M ∧
      ‖fderiv ℝ (UnforcedLeray.B0224.planeHeat θ u) x‖ ≤ K * θ ^ (-(1 / 2 : ℝ)) * M

/-- Parametric measurability (source 3426-3430): for continuous bounded `G` vanishing for `σ < s₀`,
`ν > 0`, the maps `σ ↦ e^{ν(s-σ)Δ}(σ⁻¹ G σ)(y)` and `σ ↦ D_y e^{ν(s-σ)Δ}(σ⁻¹ G σ)` are
a.e.-strongly measurable on `(0, s]`. -/
def SFCHeatParamMeas : Prop :=
  ∀ (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC), Continuous G →
    ∀ (M s0 s ν : ℝ), (∀ p, ‖G p‖ ≤ M) → 0 < s0 →
      (∀ p : UnforcedLeray.B0220.Profile, p.1 < s0 → G p = 0) → 0 < ν → ∀ y : ℝ × ℝ,
      AEStronglyMeasurable (fun σ : ℝ => UnforcedLeray.B0224.planeHeat (ν * (s - σ))
          (fun z => (((σ : ℝ) : ℂ)⁻¹) • G (σ, z)) y) (volume.restrict (Ioc 0 s)) ∧
      AEStronglyMeasurable (fun σ : ℝ => fderiv ℝ (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
          (fun z => (((σ : ℝ) : ℂ)⁻¹) • G (σ, z))) y) (volume.restrict (Ioc 0 s))


open UnforcedLeray.B0224 UnforcedLeray.B0223 in
theorem sfcCausalHeatDiff_of (hDat : SFCDatumReg) (hHeat : SFCHeatBounds)
    (hMeas : SFCHeatParamMeas) : SFCCausalHeatDiff := by
  intro c ν μ hc R0 g hctx f' hlift s hs x i j
  obtain ⟨hν, -, -, hsm⟩ := hctx
  obtain ⟨G, hGc, -, ⟨M, hM⟩, ⟨s0, hs0, hGz⟩, hbr⟩ := hDat c hc g f' hsm hlift
  obtain ⟨K0, hK0⟩ := hHeat
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0, 0, 0))
  set K : ℝ := max K0 0 with hK
  have hKnn : 0 ≤ K := le_max_right _ _
  -- the scaled datum and its bound
  set u : ℝ → ℝ × ℝ → MeridC := fun σ z => (((σ : ℝ) : ℂ)⁻¹) • G (σ, z) with hu
  set Mσ : ℝ → ℝ := fun σ => if s0 ≤ σ then M / s0 else 0 with hMσ
  have hMσnn : ∀ σ, 0 ≤ Mσ σ := fun σ => by
    simp only [hMσ]; split_ifs
    · exact div_nonneg hM0 hs0.le
    · exact le_rfl
  have huc : ∀ σ, Continuous (u σ) := fun σ =>
    ((hGc.comp (Continuous.prodMk continuous_const continuous_id)).const_smul (((σ : ℝ) : ℂ)⁻¹) :
      Continuous fun z : ℝ × ℝ => (((σ : ℝ) : ℂ)⁻¹) • G (σ, z))
  have hub : ∀ σ, 0 < σ → ∀ z, ‖u σ z‖ ≤ Mσ σ := by
    intro σ hσ z
    simp only [hu, hMσ]
    split_ifs with h
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hσ.le]
      calc σ⁻¹ * ‖G (σ, z)‖ ≤ σ⁻¹ * M := by gcongr; exact hM _
        _ ≤ s0⁻¹ * M := by gcongr
        _ = M / s0 := by ring
    · rw [hGz (σ, z) (not_le.1 h)]; simp
  -- coefficient
  set coef : ℝ → ℂ := fun σ => ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) with hcoef
  have hcoefm : Measurable coef := by
    simp only [hcoef]; fun_prop
  set Cμ : ℝ := 1 + (s0 / s) ^ μ with hCμ
  have hcoefb : ∀ σ, s0 ≤ σ → σ ≤ s → ‖coef σ‖ ≤ Cμ := by
    intro σ h1 h2
    have hσ : 0 < σ := hs0.trans_le h1
    simp only [hcoef]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hσ hs)]
    simp only [Complex.ofReal_re]
    rcases le_or_gt 0 μ with hμ | hμ
    · have : (σ / s) ^ μ ≤ 1 := Real.rpow_le_one (div_pos hσ hs).le ((div_le_one hs).2 h2) hμ
      have h0 : 0 ≤ (s0 / s) ^ μ := Real.rpow_nonneg (div_pos hs0 hs).le _
      linarith
    · have : (σ / s) ^ μ ≤ (s0 / s) ^ μ :=
        Real.rpow_le_rpow_of_nonpos (div_pos hs0 hs) (by gcongr) hμ.le
      linarith
  have hCμnn : 0 ≤ Cμ := by
    have : 0 ≤ (s0 / s) ^ μ := Real.rpow_nonneg (div_pos hs0 hs).le _
    simp only [hCμ]; linarith
  -- per-σ heat facts
  set ν0 : Measure ℝ := volume.restrict (Ioc 0 s) with hν0
  have hheat : ∀ σ, σ ∈ Ioo 0 s → ∀ y : ℝ × ℝ,
      DifferentiableAt ℝ (planeHeat (ν * (s - σ)) (u σ)) y ∧
      ‖planeHeat (ν * (s - σ)) (u σ) y‖ ≤ Mσ σ ∧
      ‖fderiv ℝ (planeHeat (ν * (s - σ)) (u σ)) y‖ ≤
        K * (ν * (s - σ)) ^ (-(1 / 2 : ℝ)) * Mσ σ := by
    intro σ hσ y
    have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσ.2)
    obtain ⟨h1, h2, h3⟩ := hK0 _ hθ (u σ) (huc σ) (Mσ σ) (hub σ hσ.1) y
    refine ⟨h1, h2, h3.trans ?_⟩
    have : 0 ≤ (ν * (s - σ)) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hθ.le _
    have := mul_le_mul_of_nonneg_right (le_max_left K0 0) this
    exact mul_le_mul_of_nonneg_right this (hMσnn σ)
  have hae : ∀ᵐ σ ∂ν0, σ ∈ Ioo 0 s := by
    have h1 : ∀ᵐ σ ∂ν0, σ ∈ Ioc 0 s := ae_restrict_mem measurableSet_Ioc
    have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ s := by
      rw [ae_iff]; simp
    have h3 : ∀ᵐ σ ∂ν0, σ ≠ s := ae_restrict_of_ae hne
    filter_upwards [h1, h3] with σ h1 h3
    exact ⟨h1.1, lt_of_le_of_ne h1.2 h3⟩
  -- the E-valued integrand
  set FE : ℝ × ℝ → ℝ → MeridC := fun y σ => coef σ • planeHeat (ν * (s - σ)) (u σ) y with hFE
  set πC : MeridC →L[ℂ] ℂ := EuclideanSpace.proj i with hπC
  set πR : MeridC →L[ℝ] ℂ := πC.restrictScalars ℝ with hπR
  have hπR1 : ‖πR‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simpa [hπR, hπC] using PiLp.norm_apply_le v i
  have hconst : Integrable (fun _ : ℝ => Cμ * (M / s0)) ν0 := by
    simp only [hν0]
    exact integrable_const _
  have hFEmeas : ∀ y, AEStronglyMeasurable (FE y) ν0 := fun y =>
    (hcoefm.aestronglyMeasurable).smul (hMeas G hGc M s0 s ν hM hs0 hGz hν y).1
  have hFEint : ∀ y, Integrable (FE y) ν0 := by
    intro y
    refine Integrable.mono' hconst (hFEmeas y) ?_
    filter_upwards [hae] with σ hσ
    rw [hFE]; simp only [norm_smul]
    have h1 := (hheat σ hσ y).2.1
    by_cases hc0 : s0 ≤ σ
    · calc ‖coef σ‖ * ‖planeHeat (ν * (s - σ)) (u σ) y‖ ≤ Cμ * Mσ σ :=
            mul_le_mul (hcoefb σ hc0 hσ.2.le) h1 (norm_nonneg _) hCμnn
        _ = Cμ * (M / s0) := by simp [hMσ, hc0]
    · have : Mσ σ = 0 := by simp [hMσ, hc0]
      rw [this] at h1
      have h2 : ‖planeHeat (ν * (s - σ)) (u σ) y‖ = 0 := le_antisymm h1 (norm_nonneg _)
      rw [h2, mul_zero]
      exact mul_nonneg hCμnn (div_nonneg hM0 hs0.le)
  -- scalar integrand, derivative, bound
  set F : ℝ × ℝ → ℝ → ℂ := fun y σ => πC (FE y σ) with hF
  set F' : ℝ × ℝ → ℝ → (ℝ × ℝ) →L[ℝ] ℂ := fun y σ =>
    coef σ • πR.comp (fderiv ℝ (planeHeat (ν * (s - σ)) (u σ)) y) with hF'
  set r : ℝ := -(1 / 2 : ℝ) with hr
  set bound : ℝ → ℝ := fun σ => Cμ * (K * (ν * (s - σ)) ^ r * (M / s0)) with hbound
  have hint0 : Integrable (fun σ : ℝ => (s - σ) ^ r) ν0 := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := s) (b := 0) (r := r)
      (by rw [hr]; norm_num)).comp_sub_left s
    simp only [sub_self, sub_zero] at h
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le).1 h
  have hbound_int : Integrable bound ν0 := by
    refine (hint0.const_mul (Cμ * (K * ν ^ r * (M / s0)))).congr ?_
    filter_upwards [hae] with σ hσ
    simp only [hbound]
    rw [Real.mul_rpow hν.le (sub_pos.2 hσ.2).le]
    ring
  have hF'meas : AEStronglyMeasurable (F' x) ν0 :=
    (hcoefm.aestronglyMeasurable).smul
      ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) MeridC ℂ πR).continuous.comp_aestronglyMeasurable
        (hMeas G hGc M s0 s ν hM hs0 hGz hν x).2)
  have hbd : ∀ᵐ σ ∂ν0, ∀ y ∈ Metric.ball x 1, ‖F' y σ‖ ≤ bound σ := by
    filter_upwards [hae] with σ hσ y _
    have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσ.2)
    have hD := (hheat σ hσ y).2.2
    have h1 : ‖F' y σ‖ ≤ ‖coef σ‖ * ‖fderiv ℝ (planeHeat (ν * (s - σ)) (u σ)) y‖ := by
      simp only [hF']
      rw [norm_smul]
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by simpa using mul_le_mul_of_nonneg_right hπR1 (norm_nonneg _))
    refine h1.trans ?_
    have hKr : 0 ≤ K * (ν * (s - σ)) ^ r := mul_nonneg hKnn (Real.rpow_nonneg hθ.le _)
    by_cases hc0 : s0 ≤ σ
    · calc ‖coef σ‖ * ‖fderiv ℝ (planeHeat (ν * (s - σ)) (u σ)) y‖
          ≤ ‖coef σ‖ * (K * (ν * (s - σ)) ^ r * Mσ σ) := by gcongr
        _ ≤ Cμ * (K * (ν * (s - σ)) ^ r * (M / s0)) := by
          have : Mσ σ = M / s0 := by simp [hMσ, hc0]
          rw [this]
          exact mul_le_mul_of_nonneg_right (hcoefb σ hc0 hσ.2.le) (mul_nonneg hKr (div_nonneg hM0 hs0.le))
    · have : Mσ σ = 0 := by simp [hMσ, hc0]
      rw [this] at hD
      have h0 : ‖fderiv ℝ (planeHeat (ν * (s - σ)) (u σ)) y‖ = 0 :=
        le_antisymm (by simpa using hD) (norm_nonneg _)
      rw [h0, mul_zero]
      exact mul_nonneg hCμnn (mul_nonneg hKr (div_nonneg hM0 hs0.le))
  have hdiff : ∀ᵐ σ ∂ν0, ∀ y ∈ Metric.ball x 1, HasFDerivAt (fun y => F y σ) (F' y σ) y := by
    filter_upwards [hae] with σ hσ y _
    have hd := (hheat σ hσ y).1.hasFDerivAt
    have h2 := (πR.hasFDerivAt.comp y hd).const_smul (coef σ)
    have hfun : (fun y => F y σ) = fun y => coef σ • πR (planeHeat (ν * (s - σ)) (u σ) y) := by
      funext y
      simp [hF, hFE, hπR, map_smul]
    rw [hfun]
    exact h2
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := ν0) (x₀ := x) (bound := bound) (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun y => πC.continuous.comp_aestronglyMeasurable (hFEmeas y))
    (πC.integrable_comp (hFEint x)) hF'meas hbd hbound_int hdiff
  have hint' : Integrable (F' x) ν0 := by
    refine Integrable.mono' hbound_int hF'meas ?_
    filter_upwards [hbd] with σ h using h x (Metric.mem_ball_self one_pos)
  -- identify the target function
  have hbr' : ∀ᵐ σ ∂ν0, 0 < σ → ∀ θ : ℝ, 0 < θ →
      planeHeat θ (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) =
        planeHeat θ (u σ) := ae_restrict_of_ae hbr
  have hfun : (fun y : ℝ × ℝ => (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (s, y)) i)
      = fun y => ∫ σ, F y σ ∂ν0 := by
    funext y
    have h1 : UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (s, y) = ∫ σ, FE y σ ∂ν0 := by
      unfold UnforcedLeray.B0225.causalHeat
      rw [intervalIntegral.integral_of_le hs.le]
      refine integral_congr_ae ?_
      filter_upwards [hae, hbr'] with σ hσ hb
      simp only [hFE, hcoef, hu]
      rw [hb hσ.1 _ (mul_pos hν (sub_pos.2 hσ.2))]
    rw [h1]
    have := πC.integral_comp_comm (hFEint y)
    simp only [hF]
    rw [this]
    simp [hπC]
  rw [hfun, hderiv.fderiv, ContinuousLinearMap.integral_apply hint']
  rw [intervalIntegral.integral_of_le hs.le]
  refine integral_congr_ae ?_
  filter_upwards [hae, hbr'] with σ hσ hb
  have hfe : (fun y : ℝ × ℝ => (planeHeat (ν * (s - σ))
      (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) y) i) =
      fun y => πR (planeHeat (ν * (s - σ)) (u σ) y) := by
    funext y; rw [hb hσ.1 _ (mul_pos hν (sub_pos.2 hσ.2))]; rfl
  have hfd : fderiv ℝ (fun y : ℝ × ℝ => πR (planeHeat (ν * (s - σ)) (u σ) y)) x =
      πR.comp (fderiv ℝ (planeHeat (ν * (s - σ)) (u σ)) x) :=
    (πR.hasFDerivAt.comp x (hheat σ hσ x).1.hasFDerivAt).fderiv
  rw [hfe, hfd]
  simp [hF', hcoef]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
