import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Units.B0005.Consistency
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# Part II-a, `PartII-a:F14/1/1/org`: Schwartz-type functions lie in the maximal graph

Source of record: `the November 2 reference manuscript`, lines 1456-1467 (the
smooth periodic Schwartz class, whose classical drift and diffusion are its graph operators) and
lines 1344-1352 (the maximal distributional graph `D_r`).

`SchwartzGraphIBP`: for a smooth `P`-periodic `Ψ` whose slices and those of its operators lie in
`L^q`, the classical `𝒯₀Ψ = ∂_τΨ - ½ y·∇Ψ` and `νΔΨ` are the distributional `𝒯₀` and `νΔ` of the
test element. This is `B0005.hasT0_testElem` / `B0005.hasHLap_testElem` with the same proofs: only
the *test* needs bounded support (the product `Φ · Ψ` of a phase test `Φ` with a smooth periodic `Ψ`
is a phase test, `isPhaseTest_dotL_left`), and the a.e. identification of the test element with
its slices only needs slice continuity (`testElem_ae_slice`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

section IBP

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- `B0005.testElem_ae` for slice tests. -/
theorem testElem_ae_slice {Φ : ℝ × Space → CVec3} (hs : IsSliceTest 𝒯 q Φ) :
    ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioc (0 : ℝ) 𝒯)),
      ((testElem 𝒯 q Φ (t : AddCircle 𝒯)) : Space → CVec3) =ᵐ[volume] fun y => Φ (t, y) := by
  have h1 : (testElem 𝒯 q Φ : AddCircle 𝒯 → Lp CVec3 q (volume : Measure Space))
      =ᵐ[AddCircle.haarAddCircle] circleSlice hs := by
    rw [testElem_of hs]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 q (volume : Measure Space)) (p := q) (𝕜 := ℂ)
      AddCircle.haarAddCircle (circleSlice hs)
  have h2 := (B0005.measurePreserving_phase 𝒯).quasiMeasurePreserving.ae_eq_comp h1
  have hne : (ENNReal.ofReal 𝒯)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have h3 := (Measure.ae_ennreal_smul_measure_iff hne).mp h2
  filter_upwards [h3] with t ht
  have ht' : testElem 𝒯 q Φ (t : AddCircle 𝒯) = sliceMap hs.2 t :=
    ht.trans (circleSlice_coe hs t)
  rw [ht']
  exact MemLp.coeFn_toLp _

/-- `B0005.phasePair_testElem` for a slice test on the right. -/
theorem phasePair_testElem_slice {Ψ Φ : ℝ × Space → CVec3} (hΨ : IsPhaseTest 𝒯 Ψ)
    (hΦ : IsSliceTest 𝒯 q Φ) :
    phasePair 𝒯 q Ψ (testElem 𝒯 q Φ) =
      (𝒯⁻¹ : ℝ) • ∫ t in Ioc (0 : ℝ) 𝒯, ∫ y, dotL (Ψ (t, y)) (Φ (t, y)) := by
  rw [phasePair_eq_periodIntegral hΨ, zero_add]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [testElem_ae_slice hΦ] with t ht
  exact integral_congr_ae (by filter_upwards [ht] with y hy; rw [hy])

omit hT in
/-- The dot product of a phase test with a smooth periodic field is a phase test. -/
theorem isPhaseTest_dotL_left {Ψ Φ : ℝ × Space → CVec3} (hΨ : IsPhaseTest 𝒯 Ψ)
    (hΦs : ContDiff ℝ ∞ Φ) (hΦp : ∀ τ y, Φ (τ + 𝒯, y) = Φ (τ, y)) :
    IsPhaseTest 𝒯 (fun z => dotL (Ψ z) (Φ z)) where
  smooth := by
    have := B0005.dotR.isBoundedBilinearMap.contDiff.comp (hΨ.smooth.prodMk hΦs)
    exact this
  periodic := fun τ y => by simp only [hΨ.periodic τ y, hΦp τ y]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΨ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

omit hT in
theorem contDiff_T0op {Φ : ℝ × Space → CVec3} (hΦs : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (B0005.T0op Φ) := by
  show ContDiff ℝ ∞ (fun p : ℝ × Space => dτ Φ p - (1 / 2 : ℝ) • radialT Φ p)
  exact (PhaseSpace.contDiff_dτ hΦs).sub ((PhaseSpace.contDiff_radialT hΦs).const_smul _)

omit hT in
theorem periodic_T0op {Φ : ℝ × Space → CVec3} (hΦp : ∀ τ y, Φ (τ + 𝒯, y) = Φ (τ, y)) :
    ∀ τ y, B0005.T0op Φ (τ + 𝒯, y) = B0005.T0op Φ (τ, y) := by
  intro τ y
  simp only [B0005.T0op, radialT, periodic_dτ hΦp τ y, periodic_dy hΦp _ τ y]

/-- **Consistency of `𝒯₀` for smooth periodic fields with `L^q` slices** (copy of
`B0005.hasT0_testElem`). -/
theorem hasT0_testElem_smooth {Φ : ℝ × Space → CVec3} (hΦs : ContDiff ℝ ∞ Φ)
    (hΦp : ∀ τ y, Φ (τ + 𝒯, y) = Φ (τ, y)) (h1 : IsSliceTest 𝒯 q Φ)
    (h2 : IsSliceTest 𝒯 q (B0005.T0op Φ)) :
    HasPhaseOp driftT (testElem 𝒯 q Φ) (testElem 𝒯 q (B0005.T0op Φ)) := by
  intro Ψ hΨ
  rw [phasePair_testElem_slice hΨ.driftT h1, phasePair_testElem_slice hΨ h2]
  congr 1
  set μ := (volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space) with hμ
  set H : ℝ × Space → ℂ := fun z => dotL (Ψ z) (Φ z) with hHdef
  have hH : IsPhaseTest 𝒯 H := isPhaseTest_dotL_left hΨ hΦs hΦp
  have hΨd : Differentiable ℝ Ψ := hΨ.smooth.differentiable (by simp)
  have hΦd : Differentiable ℝ Φ := hΦs.differentiable (by simp)
  have hTs := contDiff_T0op hΦs
  have hTp := periodic_T0op hΦp
  have hconv : ∀ {A B : ℝ × Space → CVec3}, IsPhaseTest 𝒯 A → ContDiff ℝ ∞ B →
      (∀ τ y, B (τ + 𝒯, y) = B (τ, y)) →
      ∫ t in Ioc (0 : ℝ) 𝒯, ∫ y, dotL (A (t, y)) (B (t, y)) = ∫ z, dotL (A z) (B z) ∂μ := by
    intro A B hA hBs hBp
    obtain ⟨R, hR⟩ := (isPhaseTest_dotL_left hA hBs hBp).bounded_support
    exact (integral_prod _
      (B0005.integrable_slab (isPhaseTest_dotL_left hA hBs hBp).continuous hR)).symm
  rw [hconv hΨ.driftT hΦs hΦp, hconv hΨ hTs hTp, ← sub_eq_zero]
  have hdτ : ∀ z, dτ H z = dotL (dτ Ψ z) (Φ z) + dotL (Ψ z) (dτ Φ z) :=
    fun z => B0005.fderiv_dotL hΨd hΦd z _
  have hrad : ∀ z, radialT H z = dotL (radialT Ψ z) (Φ z) + dotL (Ψ z) (radialT Φ z) := by
    intro z
    have hd' : ∀ v, fderiv ℝ H z v = dotL (fderiv ℝ Ψ z v) (Φ z) + dotL (Ψ z) (fderiv ℝ Φ z v) :=
      fun v => B0005.fderiv_dotL hΨd hΦd z v
    simp only [radialT, dy, hd', map_sum, ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_add,
      Finset.sum_add_distrib]
  have hpt : ∀ z, dotL (driftT Ψ z) (Φ z) - dotL (Ψ z) (B0005.T0op Φ z) =
      -dτ H z + (1 / 2 : ℂ) * (radialT H z + (3 : ℂ) * H z) := by
    intro z
    rw [hdτ, hrad]
    simp only [driftT, B0005.T0op, map_add, map_neg, map_sub,
      ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, Complex.real_smul, hHdef]
    push_cast
    ring
  obtain ⟨R₁, hR₁⟩ := (isPhaseTest_dotL_left hΨ.driftT hΦs hΦp).bounded_support
  obtain ⟨R₂, hR₂⟩ := (isPhaseTest_dotL_left hΨ hTs hTp).bounded_support
  obtain ⟨R₃, hR₃⟩ := hH.dτ.bounded_support
  obtain ⟨R₄, hR₄⟩ := hH.radialT.bounded_support
  obtain ⟨R₅, hR₅⟩ := hH.bounded_support
  have i1 := B0005.integrable_slab (𝒯 := 𝒯)
    (isPhaseTest_dotL_left hΨ.driftT hΦs hΦp).continuous hR₁
  have i2 := B0005.integrable_slab (𝒯 := 𝒯) (isPhaseTest_dotL_left hΨ hTs hTp).continuous hR₂
  have i3 := B0005.integrable_slab (𝒯 := 𝒯) hH.dτ.continuous hR₃
  have i4 : Integrable (fun z => radialT H z + (3 : ℂ) * H z) μ :=
    (B0005.integrable_slab hH.radialT.continuous hR₄).add
      ((B0005.integrable_slab hH.continuous hR₅).const_mul _)
  rw [← integral_sub i1 i2]
  simp only [hpt]
  have i3' : Integrable (fun z => -dτ H z) μ := i3.neg
  have i4' : Integrable (fun z => (1 / 2 : ℂ) * (radialT H z + (3 : ℂ) * H z)) μ :=
    i4.const_mul _
  rw [integral_add i3' i4', integral_neg, integral_const_mul, B0005.integral_slab_dτ hH,
    B0005.integral_slab_radial hH]
  simp

/-- **Consistency of `νΔ` for smooth periodic fields with `L^q` slices** (copy of
`B0005.hasHLap_testElem`). -/
theorem hasHLap_testElem_smooth {Φ : ℝ × Space → CVec3} (hΦs : ContDiff ℝ ∞ Φ)
    (hΦp : ∀ τ y, Φ (τ + 𝒯, y) = Φ (τ, y)) (h : ℝ) (h1 : IsSliceTest 𝒯 q Φ)
    (h2 : IsSliceTest 𝒯 q (nuLapT h Φ)) :
    HasPhaseOp (nuLapT h) (testElem 𝒯 q Φ) (testElem 𝒯 q (nuLapT h Φ)) := by
  intro Ψ hΨ
  have hhΦs : ContDiff ℝ ∞ (nuLapT h Φ) := (PhaseSpace.contDiff_lapT hΦs).const_smul h
  have hhΦp : ∀ τ y, nuLapT h Φ (τ + 𝒯, y) = nuLapT h Φ (τ, y) := fun τ y => by
    simp only [nuLapT, Pi.smul_apply, periodic_lapT hΦp τ y]
  have hhΨ : IsPhaseTest 𝒯 (nuLapT h Ψ) := hΨ.lapT.const_smul h
  rw [phasePair_testElem_slice hhΨ h1, phasePair_testElem_slice hΨ h2]
  congr 1
  set μ := (volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space) with hμ
  have hconv : ∀ {A B : ℝ × Space → CVec3}, IsPhaseTest 𝒯 A → ContDiff ℝ ∞ B →
      (∀ τ y, B (τ + 𝒯, y) = B (τ, y)) →
      ∫ t in Ioc (0 : ℝ) 𝒯, ∫ y, dotL (A (t, y)) (B (t, y)) = ∫ z, dotL (A z) (B z) ∂μ := by
    intro A B hA hBs hBp
    obtain ⟨R, hR⟩ := (isPhaseTest_dotL_left hA hBs hBp).bounded_support
    exact (integral_prod _
      (B0005.integrable_slab (isPhaseTest_dotL_left hA hBs hBp).continuous hR)).symm
  rw [hconv hhΨ hΦs hΦp, hconv hΨ hhΦs hhΦp, ← sub_eq_zero]
  have hΨd : Differentiable ℝ Ψ := hΨ.smooth.differentiable (by simp)
  have hΦd : Differentiable ℝ Φ := hΦs.differentiable (by simp)
  set K : Fin 3 → ℝ × Space → ℂ := fun j z => dotL (dy j Ψ z) (Φ z) - dotL (Ψ z) (dy j Φ z)
    with hKdef
  have hK : ∀ j, IsPhaseTest 𝒯 (K j) := fun j =>
    (isPhaseTest_dotL_left (hΨ.dy j) hΦs hΦp).sub
      (isPhaseTest_dotL_left hΨ (PhaseSpace.contDiff_dy hΦs j) (periodic_dy hΦp j))
  have hdK : ∀ j z, dy j (K j) z = dotL (dy j (dy j Ψ) z) (Φ z) - dotL (Ψ z) (dy j (dy j Φ) z) := by
    intro j z
    have hdΨ : Differentiable ℝ (dy j Ψ) := (hΨ.dy j).smooth.differentiable (by simp)
    have hdΦ : Differentiable ℝ (dy j Φ) := (PhaseSpace.contDiff_dy hΦs j).differentiable (by simp)
    have h1' : DifferentiableAt ℝ (fun z => dotL (dy j Ψ z) (Φ z)) z :=
      ((isPhaseTest_dotL_left (hΨ.dy j) hΦs hΦp).smooth.differentiable (by simp)) z
    have h2' : DifferentiableAt ℝ (fun z => dotL (Ψ z) (dy j Φ z)) z :=
      ((isPhaseTest_dotL_left hΨ (PhaseSpace.contDiff_dy hΦs j) (periodic_dy hΦp j)).smooth.differentiable
        (by simp)) z
    have e1 := B0005.fderiv_dotL hdΨ hΦd z (0, coordinateVector j)
    have e2 := B0005.fderiv_dotL hΨd hdΦ z (0, coordinateVector j)
    show fderiv ℝ (fun z => dotL (dy j Ψ z) (Φ z) - dotL (Ψ z) (dy j Φ z)) z
      (0, coordinateVector j) = _
    rw [fderiv_fun_sub h1' h2', ContinuousLinearMap.sub_apply, e1, e2]
    simp only [dy]
    ring
  have hpt : ∀ z, dotL (nuLapT h Ψ z) (Φ z) - dotL (Ψ z) (nuLapT h Φ z) =
      (h : ℂ) * ∑ j : Fin 3, dy j (K j) z := by
    intro z
    simp only [hdK, nuLapT, lapT, Pi.smul_apply, ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.smul_apply, map_sum, ContinuousLinearMap.sum_apply, Complex.real_smul,
      Finset.mul_sum, ← mul_sub, ← Finset.sum_sub_distrib]
  obtain ⟨R₁, hR₁⟩ := (isPhaseTest_dotL_left hhΨ hΦs hΦp).bounded_support
  obtain ⟨R₂, hR₂⟩ := (isPhaseTest_dotL_left hΨ hhΦs hhΦp).bounded_support
  have i1 := B0005.integrable_slab (𝒯 := 𝒯) (isPhaseTest_dotL_left hhΨ hΦs hΦp).continuous hR₁
  have i2 := B0005.integrable_slab (𝒯 := 𝒯) (isPhaseTest_dotL_left hΨ hhΦs hhΦp).continuous hR₂
  have iK : ∀ j, Integrable (dy j (K j)) μ := fun j => by
    obtain ⟨R, hR⟩ := ((hK j).dy j).bounded_support
    exact B0005.integrable_slab ((hK j).dy j).continuous hR
  rw [← integral_sub i1 i2]
  simp only [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun j _ => iK j,
    Finset.sum_eq_zero fun j _ => B0005.integral_slab_dy (hK j) j, mul_zero]

end IBP

/-- **Schwartz-type functions lie in the maximal graph with their classical operators.** -/
theorem schwartzGraphIBP : SchwartzGraphIBP := by
  intro P _ q _ ν Ψ hΨ
  have hT : IsSliceTest P q (B0005.T0op Ψ) := by
    have e : B0005.T0op Ψ = -driftT Ψ + (3 / 2 : ℂ) • Ψ := by
      funext p
      have h32 : (3 / 2 : ℂ) • Ψ p = (3 / 2 : ℝ) • Ψ p := by
        rw [← Complex.coe_smul]
        norm_num
      simp only [B0005.T0op, driftT, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, h32]
      abel
    rw [e]
    exact hΨ.sliceTest_driftT.neg.add (hΨ.sliceTest.const_smul _)
  have hL : IsSliceTest P q (nuLapT ν Ψ) := by
    have e : nuLapT ν Ψ = (ν : ℂ) • lapT Ψ := by
      funext p
      simp [nuLapT, Complex.coe_smul]
    rw [e]
    exact hΨ.sliceTest_lapT.const_smul _
  exact ⟨hasHLap_testElem_smooth hΨ.smooth hΨ.periodic ν hΨ.sliceTest hL,
    hasT0_testElem_smooth hΨ.smooth hΨ.periodic hΨ.sliceTest hT⟩

end UnforcedLeray.Short.PartIIa
