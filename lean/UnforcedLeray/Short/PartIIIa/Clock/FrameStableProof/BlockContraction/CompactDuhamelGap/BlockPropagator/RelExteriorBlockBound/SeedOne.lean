import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org
import UnforcedLeray.Lib.PlanarSectors.NUE.ParsevalPolarSum
import UnforcedLeray.Lib.PlanarSectors.NUE.PolarAngularAverage
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# `C₀ ≥ 1` from the seed-complement decay hypothesis (helper for `RelExteriorBlockBound`)

Source of record: `the November 2 reference manuscript` (SP), lines 2926-2935
(`eq:short-seed-complement`) and 2979-2980.

At `t = 0` the hypothesis `SeedCtx` bounds the complement projection `Q = I - 𝒫` by `C₀`. A radial
zero-mean test function `φ = ψ - ¼ ψ(·/2)` (`ψ(z) = s(1 - |z|²)`) has vanishing angular sectors
`±2`, hence `𝒫φ = 0` and `Qφ = φ ≠ 0`, so `C₀ ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.IIIa

namespace RelExteriorSub

/-- Radial bump `ψ(z) = s(1 - |z|²)`. -/
def seedOneψ (z : ℂ) : ℝ := Real.smoothTransition (1 - ‖z‖ ^ 2)

/-- Radial zero-mean test function `φ = ψ - ¼ ψ(·/2)`. -/
def seedOneφ (z : ℂ) : ℂ := ((seedOneψ z : ℝ) : ℂ) - (1 / 4 : ℂ) * ((seedOneψ ((1 / 2 : ℝ) • z) : ℝ) : ℂ)

theorem contDiff_seedOneψ : ContDiff ℝ ∞ seedOneψ :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem contDiff_seedOneφ : ContDiff ℝ ∞ seedOneφ := by
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => ((seedOneψ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_seedOneψ
  have h2 : ContDiff ℝ ∞ (fun z : ℂ => ((seedOneψ ((1 / 2 : ℝ) • z) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_seedOneψ.comp (contDiff_id.const_smul (1 / 2 : ℝ)))
  exact h1.sub (contDiff_const.mul h2)

theorem seedOneψ_eq_zero {z : ℂ} (hz : 1 ≤ ‖z‖) : seedOneψ z = 0 := by
  unfold seedOneψ
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg z]

theorem hasCompactSupport_seedOneφ : HasCompactSupport seedOneφ := by
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) 2) (isCompact_closedBall _ _)
    fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  have h1 : seedOneψ z = 0 := seedOneψ_eq_zero (by linarith)
  have h2 : seedOneψ ((1 / 2 : ℝ) • z) = 0 := by
    apply seedOneψ_eq_zero
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith
  simp only [seedOneφ, h1, h2, Complex.ofReal_zero, mul_zero, sub_zero]

theorem seedOneφ_rot (θ : ℝ) (x : ℂ) : seedOneφ (Planar.NUE.rot θ x) = seedOneφ x := by
  simp [seedOneφ, seedOneψ, Planar.NUE.Polar.norm_rot]

theorem integral_seedOneφ : ∫ z, seedOneφ z = 0 := by
  have hc : Continuous fun z : ℂ => ((seedOneψ z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp contDiff_seedOneψ.continuous
  have hsupp : HasCompactSupport fun z : ℂ => ((seedOneψ z : ℝ) : ℂ) := by
    refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) 1) (isCompact_closedBall _ _)
      fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    simp [seedOneψ_eq_zero hz.le]
  have hi1 : Integrable (fun z : ℂ => ((seedOneψ z : ℝ) : ℂ)) volume :=
    hc.integrable_of_hasCompactSupport hsupp
  have hc2 : Continuous fun z : ℂ => ((seedOneψ ((1 / 2 : ℝ) • z) : ℝ) : ℂ) :=
    hc.comp (continuous_const_smul _)
  have hsupp2 : HasCompactSupport fun z : ℂ => ((seedOneψ ((1 / 2 : ℝ) • z) : ℝ) : ℂ) := by
    refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) 2) (isCompact_closedBall _ _)
      fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    have : seedOneψ ((1 / 2 : ℝ) • z) = 0 := by
      apply seedOneψ_eq_zero
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      linarith
    simp only [this, Complex.ofReal_zero]
  have hi2 : Integrable (fun z : ℂ => (1 / 4 : ℂ) * ((seedOneψ ((1 / 2 : ℝ) • z) : ℝ) : ℂ))
      volume :=
    (hc2.integrable_of_hasCompactSupport hsupp2).const_mul _
  have hsc := Measure.integral_comp_smul (volume : Measure ℂ)
    (fun z : ℂ => ((seedOneψ z : ℝ) : ℂ)) (1 / 2 : ℝ)
  rw [Complex.finrank_real_complex] at hsc
  have h4 : |((1 / 2 : ℝ) ^ 2)⁻¹| = 4 := by norm_num
  rw [h4] at hsc
  unfold seedOneφ
  rw [integral_sub hi1 hi2, integral_const_mul, hsc]
  rw [Complex.real_smul]
  push_cast
  ring

theorem seedOneφ_zero : seedOneφ 0 = 3 / 4 := by
  simp [seedOneφ, seedOneψ, Real.smoothTransition.one]
  norm_num

/-- The seed projection of an a.e. radial function vanishes. -/
theorem seedProjFun_eq_zero_of_ae_radial (hprof : ℝ → ℂ) {f : ℂ → ℂ}
    (hf : f =ᵐ[volume] seedOneφ) : PartI.seedProjFun hprof f = fun _ => 0 := by
  have hae := Planar.NUE.Ang.ParsevalH.ae_angularSector_eq hf
  have hsec : ∀ (ℓ : ℤ), ℓ ≠ 0 → ∀ r, Planar.NUE.Polar.angularSector seedOneφ ℓ r = 0 :=
    fun ℓ hℓ r => Planar.NUE.Polar.angularSector_eq_zero_of_rot_invariant seedOneφ_rot hℓ r
  have h2 : PartI.seedEll hprof (Planar.NUE.Polar.angularSector f 2) = 0 := by
    unfold PartI.seedEll
    have : ∫ r in Ioi (0 : ℝ), hprof r * Planar.NUE.Polar.angularSector f 2 r /
        (Blueprint.Planar.strainK r : ℂ) * (r : ℂ) = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℂ)) ?_, integral_zero]
      filter_upwards [hae] with r hr
      rw [hr 2, hsec 2 (by norm_num) r]
      simp
    rw [this, mul_zero]
  have h3 : PartI.seedEll hprof
      (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)) = 0 := by
    unfold PartI.seedEll
    have : ∫ r in Ioi (0 : ℝ), hprof r * conj (Planar.NUE.Polar.angularSector f (-2) r) /
        (Blueprint.Planar.strainK r : ℂ) * (r : ℂ) = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℂ)) ?_, integral_zero]
      filter_upwards [hae] with r hr
      rw [hr (-2), hsec (-2) (by norm_num) r]
      simp
    rw [this, mul_zero]
  funext y
  unfold PartI.seedProjFun
  rw [h2, h3]
  simp

/-- **`C₀ ≥ 1`** from the seed-complement decay hypothesis at `t = 0`. -/
theorem one_le_of_seedCtx {κ : PlanarFrameKernels} {P : PlanarData} {m C₀ h : ℝ} (hm : 1 < m)
    (hS : BlockPropagatorInteriorSub.OrgSplit.SeedCtx κ P m C₀ h) : 1 ≤ C₀ := by
  obtain ⟨lam, h_prof, hh, ℓ, -, -, -, -, hdec⟩ := hS
  have hmem : B0008.MemHjM 0 m seedOneφ :=
    B0008.memHjM_of_testFn 0 m ⟨contDiff_seedOneφ, hasCompactSupport_seedOneφ, subset_univ _⟩
  set F : B0008.HjM 0 m := B0008.HjM.ofMemHjM hmem with hFdef
  have hFval : (F.value : ℂ → ℂ) =ᵐ[volume] seedOneφ := B0008.HjM.value_ofMemHjM hmem
  have hFX : F ∈ B0008.XjM 0 m := by
    rw [B0008.mem_XjM_iff hm F, integral_congr_ae hFval]
    exact integral_seedOneφ
  set f : B0008.XjM 0 m := ⟨F, hFX⟩ with hfdef
  have hxf : PartI.xValue f =ᵐ[volume] seedOneφ := hFval
  obtain ⟨u, g, hu, hg, hb⟩ := hdec hm 0 le_rfl f
  have hproj := seedProjFun_eq_zero_of_ae_radial h_prof hxf
  rw [Planar.eulerGroupW_zero] at hg
  have hgf : PartI.xValue g =ᵐ[volume] PartI.xValue f := by
    filter_upwards [hg, hu] with y h1 h2
    rw [h1, ContinuousLinearMap.one_apply, h2, hproj, sub_zero]
  have hval : (g : B0008.HjM 0 m).value = (f : B0008.HjM 0 m).value :=
    Lp.ext ((B0008.wMeasure_ac m).ae_le hgf)
  have hgf' : g = f := Subtype.ext (B0008.HjM.value_injective hval)
  have hfpos : 0 < ‖f‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    have hF0 : F = 0 := by
      have := congrArg Subtype.val h0
      simpa [hfdef] using this
    have hv0 : (F.value : ℂ → ℂ) =ᵐ[volume] (0 : ℂ → ℂ) := by
      rw [hF0, B0008.HjM.value_zero]
      exact (B0008.volume_ac m).ae_le (Lp.coeFn_zero _ _ _)
    have hφ0 : seedOneφ =ᵐ[volume] (0 : ℂ → ℂ) := hFval.symm.trans hv0
    have hφeq : seedOneφ = 0 :=
      (Continuous.ae_eq_iff_eq volume contDiff_seedOneφ.continuous continuous_const).1 hφ0
    have := congrFun hφeq 0
    rw [seedOneφ_zero] at this
    norm_num at this
  rw [hgf'] at hb
  simp only [mul_zero, Real.exp_zero, one_mul, mul_one] at hb
  nlinarith

end RelExteriorSub

end UnforcedLeray.Short.IIIa
