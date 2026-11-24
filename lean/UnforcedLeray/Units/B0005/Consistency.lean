import UnforcedLeray.Units.B0005.Bridge
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# B0005, part 4: the distributional `𝒯₀` extends the classical `𝒯₀ = ∂_τ - ½ y·∇`

Blueprint unit B0005 (tex 140–142). In the phase model "`𝒯₀ f = b` in distributions" is
`HasT0 f b`, tested through `PhaseSpace.driftT = -∂_τ + ½ y·∇ + 3/2`. This file checks that
`driftT` is the transpose of `𝒯₀` on smooth periodic fields: for a phase test `Φ`, viewed as an
element of `𝒴_q`, the classical `𝒯₀ Φ = T0op Φ` is its distributional `𝒯₀`
(`hasT0_testElem`). The proof integrates by parts once in the phase (periodicity,
`integral_slab_dτ`) and once in space (`∫ (y·∇h + 3h) = 0` for compactly supported `h`,
`integral_radial_add`).

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

/-! ### Test elements of `𝒴_q` -/

section TestElem

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem testElem_ae {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest 𝒯 Φ) :
    ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioc (0 : ℝ) 𝒯)),
      ((testElem 𝒯 q Φ (t : AddCircle 𝒯)) : Space → CVec3) =ᵐ[volume] fun y => Φ (t, y) := by
  have hs := hΦ.isSliceTest q
  have h1 : (testElem 𝒯 q Φ : AddCircle 𝒯 → Lp CVec3 q (volume : Measure Space))
      =ᵐ[AddCircle.haarAddCircle] circleSlice hs := by
    rw [testElem_of hs]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 q (volume : Measure Space)) (p := q) (𝕜 := ℂ)
      AddCircle.haarAddCircle (circleSlice hs)
  have h2 := (measurePreserving_phase 𝒯).quasiMeasurePreserving.ae_eq_comp h1
  have hne : (ENNReal.ofReal 𝒯)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have h3 := (Measure.ae_ennreal_smul_measure_iff hne).mp h2
  filter_upwards [h3] with t ht
  have ht' : testElem 𝒯 q Φ (t : AddCircle 𝒯) = sliceMap hs.2 t := ht.trans (circleSlice_coe hs t)
  rw [ht']
  exact MemLp.coeFn_toLp _

theorem phasePair_testElem {Ψ Φ : ℝ × Space → CVec3} (hΨ : IsPhaseTest 𝒯 Ψ)
    (hΦ : IsPhaseTest 𝒯 Φ) :
    phasePair 𝒯 q Ψ (testElem 𝒯 q Φ) =
      (𝒯⁻¹ : ℝ) • ∫ t in Ioc (0 : ℝ) 𝒯, ∫ y, dotL (Ψ (t, y)) (Φ (t, y)) := by
  rw [phasePair_eq_periodIntegral hΨ, zero_add]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [testElem_ae (q := q) hΦ] with t ht
  exact integral_congr_ae (by filter_upwards [ht] with y hy; rw [hy])

end TestElem

/-! ### Integrals over the period slab -/

section Slab

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)]

omit hT in
theorem integrable_slab {G : ℝ × Space → ℂ} (hG : Continuous G) {R : ℝ}
    (hR : ∀ t y, R < ‖y‖ → G (t, y) = 0) :
    Integrable G ((volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space)) := by
  rw [← IsY2.slab_eq 𝒯]
  have hK : IntegrableOn G (Icc (0 : ℝ) 𝒯 ×ˢ Metric.closedBall (0 : Space) R) :=
    hG.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))
  refine hK.of_forall_diff_eq_zero (measurableSet_Ioc.prod MeasurableSet.univ) ?_
  rintro ⟨t, y⟩ ⟨⟨ht, -⟩, hnot⟩
  refine hR t y ?_
  by_contra hy
  exact hnot ⟨Ioc_subset_Icc_self ht, by
    simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.mp hy⟩

/-- `∫∫_{(0,𝒯]×ℝ³} ∂_τ H = 0` for a periodic `H`. -/
theorem integral_slab_dτ {H : ℝ × Space → ℂ} (hH : IsPhaseTest 𝒯 H) :
    ∫ z, dτ H z ∂((volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space)) = 0 := by
  obtain ⟨R, hR⟩ := hH.dτ.bounded_support
  have hint := integrable_slab (𝒯 := 𝒯) hH.dτ.continuous hR
  rw [integral_prod_symm _ hint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  show ∫ x in Ioc (0 : ℝ) 𝒯, dτ H (x, y) = 0
  have hd : Differentiable ℝ H := hH.smooth.differentiable (by simp)
  have hderiv : ∀ t, HasDerivAt (fun s => H (s, y)) (dτ H (t, y)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact (hd (t, y)).hasFDerivAt.comp_hasDerivAt t h1
  rw [← intervalIntegral.integral_of_le hT.out.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((hH.dτ.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)]
  have := hH.periodic 0 y
  rw [zero_add] at this
  simp [this]

/-- `∫ (y·∇h + 3h) dy = 0` for a smooth compactly supported `h : ℝ³ → ℂ`. -/
theorem integral_radial_add {h : Space → ℂ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ∫ y, (∑ j : Fin 3, (y j : ℂ) * fderiv ℝ h y (coordinateVector j) + 3 * h y) = 0 := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have hcont : ∀ j : Fin 3, Continuous fun y => fderiv ℝ h y (coordinateVector j) := fun j =>
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcoord : ∀ j : Fin 3, Continuous fun y : Space => (y j : ℂ) := fun j =>
    Complex.continuous_ofReal.comp (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous
  have hcd : ∀ j : Fin 3, HasCompactSupport fun y => fderiv ℝ h y (coordinateVector j) :=
    fun j => hc.fderiv_apply (𝕜 := ℝ) _
  have hfd : ∀ (j : Fin 3) (x : Space),
      fderiv ℝ (fun y : Space => (y j : ℂ)) x (coordinateVector j) = 1 := by
    intro j x
    have hL : (fun y : Space => (y j : ℂ)) =
        fun y => (Complex.ofRealCLM.comp (EuclideanSpace.proj j : Space →L[ℝ] ℝ)) y := rfl
    rw [hL, ContinuousLinearMap.fderiv]
    simp [coordinateVector]
  have hfdiff : ∀ j : Fin 3, Differentiable ℝ fun y : Space => (y j : ℂ) := fun j =>
    (Complex.ofRealCLM.comp (EuclideanSpace.proj j : Space →L[ℝ] ℝ)).differentiable
  have hibp : ∀ j : Fin 3, ∫ y, (y j : ℂ) * fderiv ℝ h y (coordinateVector j) = -∫ y, h y := by
    intro j
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun y : Space => (y j : ℂ)) (g := h) (v := coordinateVector j)
      (by simp only [hfd, one_mul]; exact hh.continuous.integrable_of_hasCompactSupport hc)
      (((hcoord j).mul (hcont j)).integrable_of_hasCompactSupport (hcd j).mul_left)
      (((hcoord j).mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun x _ => hfdiff j x) (fun x _ => hd x)
    simpa [hfd] using this
  have hi : ∀ j : Fin 3, Integrable fun y : Space => (y j : ℂ) * fderiv ℝ h y (coordinateVector j) :=
    fun j => ((hcoord j).mul (hcont j)).integrable_of_hasCompactSupport (hcd j).mul_left
  have hhi : Integrable h := hh.continuous.integrable_of_hasCompactSupport hc
  rw [integral_add (integrable_finsetSum _ fun j _ => hi j) (hhi.const_mul 3),
    integral_finsetSum _ fun j _ => hi j, integral_const_mul]
  simp only [hibp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

omit hT in
/-- `∫∫_{(0,𝒯]×ℝ³} (y·∇H + 3H) = 0`. -/
theorem integral_slab_radial {H : ℝ × Space → ℂ} (hH : IsPhaseTest 𝒯 H) :
    ∫ z, (radialT H z + (3 : ℂ) * H z)
      ∂((volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space)) = 0 := by
  obtain ⟨R₁, hR₁⟩ := hH.radialT.bounded_support
  obtain ⟨R₂, hR₂⟩ := hH.bounded_support
  have hint : Integrable (fun z => radialT H z + (3 : ℂ) * H z)
      ((volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space)) :=
    (integrable_slab hH.radialT.continuous hR₁).add
      ((integrable_slab hH.continuous hR₂).const_mul _)
  rw [integral_prod _ hint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  have hd : Differentiable ℝ H := hH.smooth.differentiable (by simp)
  have hsl : ContDiff ℝ ∞ (fun y => H (t, y)) :=
    hH.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun y => H (t, y)) :=
    hasCompactSupport_of_bound (R := R₂) fun y hy => hR₂ t y hy
  have hpt : ∀ y, radialT H (t, y) + (3 : ℂ) * H (t, y) =
      ∑ j : Fin 3, (y j : ℂ) * fderiv ℝ (fun x => H (t, x)) y (coordinateVector j) +
        3 * H (t, y) := by
    intro y
    simp only [radialT, dy, fderiv_slice_space (hd (t, y)), ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, Complex.real_smul]
  simp only [hpt]
  exact integral_radial_add hsl hc

omit hT in
/-- `∫∫_{(0,𝒯]×ℝ³} ∂ⱼ K = 0` for a test `K` of bounded support. -/
theorem integral_slab_dy {K : ℝ × Space → ℂ} (hK : IsPhaseTest 𝒯 K) (j : Fin 3) :
    ∫ z, dy j K z ∂((volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space)) = 0 := by
  obtain ⟨R₁, hR₁⟩ := (hK.dy j).bounded_support
  obtain ⟨R₂, hR₂⟩ := hK.bounded_support
  rw [integral_prod _ (integrable_slab (hK.dy j).continuous hR₁)]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  show ∫ y, dy j K (t, y) = 0
  have hd : Differentiable ℝ K := hK.smooth.differentiable (by simp)
  have hsl : ContDiff ℝ ∞ (fun y => K (t, y)) := hK.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun y => K (t, y)) :=
    hasCompactSupport_of_bound (R := R₂) fun y hy => hR₂ t y hy
  have hpt : ∀ y, dy j K (t, y) = fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) := by
    intro y
    simp only [dy, fderiv_slice_space (hd (t, y)), ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
  simp only [hpt]
  have hcd : HasCompactSupport fun y => fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) :=
    hc.fderiv_apply (𝕜 := ℝ) _
  have hcont : Continuous fun y => fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) :=
    (hsl.continuous_fderiv (by simp)).clm_apply continuous_const
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Space => (1 : ℂ)) (g := fun x => K (t, x)) (v := coordinateVector j)
    (by simp) (by simpa using hcont.integrable_of_hasCompactSupport hcd)
    (by simpa using hsl.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hsl.differentiable (by simp)) x)
  simpa using this

end Slab

/-! ### The product rule for the bilinear dot product -/

section Product

/-- `dotL` as a real-bilinear map. -/
def dotR : CVec3 →L[ℝ] CVec3 →L[ℝ] ℂ := dotL.bilinearRestrictScalars ℝ

theorem fderiv_dotL {Ψ Φ : ℝ × Space → CVec3} (hΨ : Differentiable ℝ Ψ) (hΦ : Differentiable ℝ Φ)
    (p v : ℝ × Space) :
    fderiv ℝ (fun z => dotL (Ψ z) (Φ z)) p v =
      dotL (fderiv ℝ Ψ p v) (Φ p) + dotL (Ψ p) (fderiv ℝ Φ p v) := by
  have e : (fun z => dotL (Ψ z) (Φ z)) = fun z => dotR (Ψ z) (Φ z) := rfl
  rw [e, dotR.fderiv_of_bilinear (hΨ p) (hΦ p)]
  simp [dotR, ContinuousLinearMap.precompR, add_comm]

theorem isPhaseTest_dotL {P : ℝ} {Ψ Φ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ)
    (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (fun z => dotL (Ψ z) (Φ z)) where
  smooth := by
    have := dotR.isBoundedBilinearMap.contDiff.comp (hΨ.smooth.prodMk hΦ.smooth)
    exact this
  periodic := fun τ y => by simp only [hΨ.periodic τ y, hΦ.periodic τ y]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΨ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

end Product

/-! ### The distributional `𝒯₀` of a smooth periodic field -/

section Main

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **Consistency of `𝒯₀`** (tex 140): for a smooth `𝒯`-periodic field `Φ` of bounded support,
the classical `𝒯₀ Φ = ∂_τ Φ - ½ y·∇Φ` is its distributional `𝒯₀` in `𝒴_q`. -/
theorem hasT0_testElem {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest 𝒯 Φ) :
    HasT0 (testElem 𝒯 q Φ) (testElem 𝒯 q (T0op Φ)) := by
  intro Ψ hΨ
  rw [phasePair_testElem hΨ.driftT hΦ, phasePair_testElem hΨ (IsPhaseTest.T0op hΦ)]
  congr 1
  set μ := (volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space) with hμ
  set H : ℝ × Space → ℂ := fun z => dotL (Ψ z) (Φ z) with hHdef
  have hH : IsPhaseTest 𝒯 H := isPhaseTest_dotL hΨ hΦ
  have hΨd : Differentiable ℝ Ψ := hΨ.smooth.differentiable (by simp)
  have hΦd : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hconv : ∀ {A B : ℝ × Space → CVec3}, IsPhaseTest 𝒯 A → IsPhaseTest 𝒯 B →
      ∫ t in Ioc (0 : ℝ) 𝒯, ∫ y, dotL (A (t, y)) (B (t, y)) = ∫ z, dotL (A z) (B z) ∂μ := by
    intro A B hA hB
    obtain ⟨R, hR⟩ := (isPhaseTest_dotL hA hB).bounded_support
    exact (integral_prod _ (integrable_slab (isPhaseTest_dotL hA hB).continuous hR)).symm
  rw [hconv hΨ.driftT hΦ, hconv hΨ (IsPhaseTest.T0op hΦ), ← sub_eq_zero]
  have hdτ : ∀ z, dτ H z = dotL (dτ Ψ z) (Φ z) + dotL (Ψ z) (dτ Φ z) :=
    fun z => fderiv_dotL hΨd hΦd z _
  have hrad : ∀ z, radialT H z = dotL (radialT Ψ z) (Φ z) + dotL (Ψ z) (radialT Φ z) := by
    intro z
    have hd' : ∀ v, fderiv ℝ H z v = dotL (fderiv ℝ Ψ z v) (Φ z) + dotL (Ψ z) (fderiv ℝ Φ z v) :=
      fun v => fderiv_dotL hΨd hΦd z v
    simp only [radialT, dy, hd', map_sum, ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_add,
      Finset.sum_add_distrib]
  have hpt : ∀ z, dotL (driftT Ψ z) (Φ z) - dotL (Ψ z) (T0op Φ z) =
      -dτ H z + (1 / 2 : ℂ) * (radialT H z + (3 : ℂ) * H z) := by
    intro z
    rw [hdτ, hrad]
    simp only [driftT, T0op, map_add, map_neg, map_sub, ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, Complex.real_smul, hHdef]
    push_cast
    ring
  obtain ⟨R₁, hR₁⟩ := (isPhaseTest_dotL hΨ.driftT hΦ).bounded_support
  obtain ⟨R₂, hR₂⟩ := (isPhaseTest_dotL hΨ (IsPhaseTest.T0op hΦ)).bounded_support
  obtain ⟨R₃, hR₃⟩ := hH.dτ.bounded_support
  obtain ⟨R₄, hR₄⟩ := hH.radialT.bounded_support
  obtain ⟨R₅, hR₅⟩ := hH.bounded_support
  have i1 := integrable_slab (𝒯 := 𝒯) (isPhaseTest_dotL hΨ.driftT hΦ).continuous hR₁
  have i2 := integrable_slab (𝒯 := 𝒯) (isPhaseTest_dotL hΨ (IsPhaseTest.T0op hΦ)).continuous hR₂
  have i3 := integrable_slab (𝒯 := 𝒯) hH.dτ.continuous hR₃
  have i4 : Integrable (fun z => radialT H z + (3 : ℂ) * H z) μ :=
    (integrable_slab hH.radialT.continuous hR₄).add ((integrable_slab hH.continuous hR₅).const_mul _)
  rw [← integral_sub i1 i2]
  simp only [hpt]
  have i3' : Integrable (fun z => -dτ H z) μ := i3.neg
  have i4' : Integrable (fun z => (1 / 2 : ℂ) * (radialT H z + (3 : ℂ) * H z)) μ :=
    i4.const_mul _
  rw [integral_add i3' i4', integral_neg, integral_const_mul, integral_slab_dτ hH,
    integral_slab_radial hH]
  simp

/-- **Consistency of `Δ`**: for a smooth `𝒯`-periodic field `Φ` of bounded support, the
classical `hΔΦ` is its distributional `hΔ` in `𝒴_q`. -/
theorem hasHLap_testElem {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest 𝒯 Φ) (h : ℝ) :
    HasHLap h (testElem 𝒯 q Φ) (testElem 𝒯 q (nuLapT h Φ)) := by
  intro Ψ hΨ
  have hhΦ : IsPhaseTest 𝒯 (nuLapT h Φ) := hΦ.lapT.const_smul h
  have hhΨ : IsPhaseTest 𝒯 (nuLapT h Ψ) := hΨ.lapT.const_smul h
  rw [phasePair_testElem hhΨ hΦ, phasePair_testElem hΨ hhΦ]
  congr 1
  set μ := (volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space) with hμ
  have hconv : ∀ {A B : ℝ × Space → CVec3}, IsPhaseTest 𝒯 A → IsPhaseTest 𝒯 B →
      ∫ t in Ioc (0 : ℝ) 𝒯, ∫ y, dotL (A (t, y)) (B (t, y)) = ∫ z, dotL (A z) (B z) ∂μ := by
    intro A B hA hB
    obtain ⟨R, hR⟩ := (isPhaseTest_dotL hA hB).bounded_support
    exact (integral_prod _ (integrable_slab (isPhaseTest_dotL hA hB).continuous hR)).symm
  rw [hconv hhΨ hΦ, hconv hΨ hhΦ, ← sub_eq_zero]
  have hΨd : Differentiable ℝ Ψ := hΨ.smooth.differentiable (by simp)
  have hΦd : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  set K : Fin 3 → ℝ × Space → ℂ := fun j z => dotL (dy j Ψ z) (Φ z) - dotL (Ψ z) (dy j Φ z)
    with hKdef
  have hK : ∀ j, IsPhaseTest 𝒯 (K j) := fun j =>
    (isPhaseTest_dotL (hΨ.dy j) hΦ).sub (isPhaseTest_dotL hΨ (hΦ.dy j))
  have hdK : ∀ j z, dy j (K j) z = dotL (dy j (dy j Ψ) z) (Φ z) - dotL (Ψ z) (dy j (dy j Φ) z) := by
    intro j z
    have hdΨ : Differentiable ℝ (dy j Ψ) := (hΨ.dy j).smooth.differentiable (by simp)
    have hdΦ : Differentiable ℝ (dy j Φ) := (hΦ.dy j).smooth.differentiable (by simp)
    have h1 : DifferentiableAt ℝ (fun z => dotL (dy j Ψ z) (Φ z)) z :=
      ((isPhaseTest_dotL (hΨ.dy j) hΦ).smooth.differentiable (by simp)) z
    have h2 : DifferentiableAt ℝ (fun z => dotL (Ψ z) (dy j Φ z)) z :=
      ((isPhaseTest_dotL hΨ (hΦ.dy j)).smooth.differentiable (by simp)) z
    have e1 := fderiv_dotL hdΨ hΦd z (0, coordinateVector j)
    have e2 := fderiv_dotL hΨd hdΦ z (0, coordinateVector j)
    show fderiv ℝ (fun z => dotL (dy j Ψ z) (Φ z) - dotL (Ψ z) (dy j Φ z)) z
      (0, coordinateVector j) = _
    rw [fderiv_fun_sub h1 h2, ContinuousLinearMap.sub_apply, e1, e2]
    simp only [dy]
    ring
  have hpt : ∀ z, dotL (nuLapT h Ψ z) (Φ z) - dotL (Ψ z) (nuLapT h Φ z) =
      (h : ℂ) * ∑ j : Fin 3, dy j (K j) z := by
    intro z
    simp only [hdK, nuLapT, lapT, Pi.smul_apply, ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.smul_apply, map_sum, ContinuousLinearMap.sum_apply, Complex.real_smul,
      Finset.mul_sum, ← mul_sub, ← Finset.sum_sub_distrib]
  obtain ⟨R₁, hR₁⟩ := (isPhaseTest_dotL hhΨ hΦ).bounded_support
  obtain ⟨R₂, hR₂⟩ := (isPhaseTest_dotL hΨ hhΦ).bounded_support
  have i1 := integrable_slab (𝒯 := 𝒯) (isPhaseTest_dotL hhΨ hΦ).continuous hR₁
  have i2 := integrable_slab (𝒯 := 𝒯) (isPhaseTest_dotL hΨ hhΦ).continuous hR₂
  have iK : ∀ j, Integrable (dy j (K j)) μ := fun j => by
    obtain ⟨R, hR⟩ := ((hK j).dy j).bounded_support
    exact integrable_slab ((hK j).dy j).continuous hR
  rw [← integral_sub i1 i2]
  simp only [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun j _ => iK j,
    Finset.sum_eq_zero fun j _ => integral_slab_dy (hK j) j, mul_zero]

end Main

end UnforcedLeray.B0005
