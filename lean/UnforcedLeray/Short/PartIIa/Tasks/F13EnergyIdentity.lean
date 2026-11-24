import UnforcedLeray.Short.PartIIa.Sub.F13

/-!
# Part II-a, task `PartII-a:F13`: the Hilbert energy identity on the smooth core

Source of record: `the November 2 reference manuscript`, lines 1491-1496.

The assembly `freeEnergyIdentity_of` and the bridge `inner_testElem_two` are in
`Short/PartII-a/Sub/F13.lean`; this file proves the two slab identities `PhaseTestLap` and
`PhaseTestSkew` (direct integration by parts) and the unconditional theorem.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace

/-- The Hermitian pairing of two phase tests is a complex-valued phase test. -/
theorem isPhaseTest_inner {P : ℝ} {A B : ℝ × Space → CVec3} (hA : IsPhaseTest P A)
    (hB : IsPhaseTest P B) : IsPhaseTest P (fun z => inner ℂ (A z) (B z)) where
  smooth := hA.smooth.inner ℂ hB.smooth
  periodic := fun τ y => by simp only [hA.periodic τ y, hB.periodic τ y]
  bounded_support := by
    obtain ⟨R, hR⟩ := hA.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

/-- Product rule for the Hermitian pairing along a spatial direction. -/
theorem dy_inner {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (j : Fin 3) (p : ℝ × Space) :
    dy j (fun z => inner ℂ (A z) (B z)) p =
      inner ℂ (A p) (dy j B p) + inner ℂ (dy j A p) (B p) := by
  unfold dy
  have h := HasFDerivAt.inner ℂ (hA p).hasFDerivAt (hB p).hasFDerivAt
  rw [h.fderiv]
  simp [fderivInnerCLM_apply]

/-- Product rule for the Hermitian pairing along the phase. -/
theorem dτ_inner {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (p : ℝ × Space) :
    dτ (fun z => inner ℂ (A z) (B z)) p =
      inner ℂ (A p) (dτ B p) + inner ℂ (dτ A p) (B p) := by
  unfold dτ
  have h := HasFDerivAt.inner ℂ (hA p).hasFDerivAt (hB p).hasFDerivAt
  rw [h.fderiv]
  simp [fderivInnerCLM_apply]

/-- The iterated period integral is the integral over the period slab `(0, P] × ℝ³`. -/
theorem slabInner_eq {P : ℝ} [Fact (0 < P)] {A B : ℝ × Space → CVec3} (hA : IsPhaseTest P A)
    (hB : IsPhaseTest P B) :
    slabInner P A B = ∫ z, inner ℂ (A z) (B z)
      ∂((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := by
  obtain ⟨R, hR⟩ := (isPhaseTest_inner hA hB).bounded_support
  unfold slabInner
  rw [zero_add]
  exact (integral_prod _ (B0005.integrable_slab (isPhaseTest_inner hA hB).continuous hR)).symm

/-- A complex-valued phase test is integrable on the period slab. -/
theorem integrable_slab_of_test {P : ℝ} {H : ℝ × Space → ℂ} (hH : IsPhaseTest P H) :
    Integrable H ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := by
  obtain ⟨R, hR⟩ := hH.bounded_support
  exact B0005.integrable_slab hH.continuous hR

/-- **Diffusion part of the energy identity** (`PhaseTestLap`). -/
theorem phaseTestLap : PhaseTestLap := by
  intro P _ ν G hG
  let μ : Measure (ℝ × Space) := (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)
  have hGd : Differentiable ℝ G := hG.smooth.differentiable (by simp)
  have hdj : ∀ j : Fin 3, Differentiable ℝ (dy j G) :=
    fun j => (hG.dy j).smooth.differentiable (by simp)
  have hK : ∀ j : Fin 3, IsPhaseTest P (fun z => inner ℂ (G z) (dy j G z)) :=
    fun j => isPhaseTest_inner hG (hG.dy j)
  have hKint : ∀ j : Fin 3,
      ∫ z, dy j (fun z => inner ℂ (G z) (dy j G z)) z ∂μ = 0 :=
    fun j => B0005.integral_slab_dy (hK j) j
  have hdyK : ∀ j : Fin 3, Integrable (fun z => dy j (fun z => inner ℂ (G z) (dy j G z)) z) μ :=
    fun j => integrable_slab_of_test ((hK j).dy j)
  have hI1 : ∀ j : Fin 3, Integrable (fun z => inner ℂ (dy j G z) (dy j G z)) μ :=
    fun j => integrable_slab_of_test (isPhaseTest_inner (hG.dy j) (hG.dy j))
  have hpt : ∀ z, inner ℂ (G z) (nuLapT ν G z) = (ν : ℂ) * ∑ j : Fin 3,
      (dy j (fun z => inner ℂ (G z) (dy j G z)) z - inner ℂ (dy j G z) (dy j G z)) := by
    intro z
    have h1 : nuLapT ν G z = ν • ∑ j : Fin 3, dy j (dy j G) z := by
      simp [nuLapT, lapT]
    rw [h1, ← Complex.coe_smul, inner_smul_right, inner_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dy_inner hGd (hdj j) j z]
    ring
  rw [slabInner_eq hG (B0411.isPhaseTest_nuLapT hG ν)]
  simp_rw [hpt]
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun z =>
      dy j (fun z => inner ℂ (G z) (dy j G z)) z - inner ℂ (dy j G z) (dy j G z)) μ :=
    fun j _ => (hdyK j).sub (hI1 j)
  rw [integral_const_mul, integral_finsetSum _ hint]
  have hsum : ∀ j : Fin 3, ∫ z, (dy j (fun z => inner ℂ (G z) (dy j G z)) z -
      inner ℂ (dy j G z) (dy j G z)) ∂μ = -slabInner P (dy j G) (dy j G) := by
    intro j
    rw [integral_sub (hdyK j) (hI1 j), hKint j, slabInner_eq (hG.dy j) (hG.dy j), zero_sub]
  simp_rw [hsum]
  rw [Finset.sum_neg_distrib]
  ring

/-- Real scalars pull out of the second slot of the Hermitian pairing. -/
theorem inner_real_smul_right' (x y : CVec3) (r : ℝ) :
    inner ℂ x (r • y) = (r : ℂ) * inner ℂ x y := by
  rw [← Complex.coe_smul, inner_smul_right]

/-- **Skew part of the energy identity** (`PhaseTestSkew`). -/
theorem phaseTestSkew : PhaseTestSkew := by
  intro P _ G hG
  let μ : Measure (ℝ × Space) := (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)
  have hGd : Differentiable ℝ G := hG.smooth.differentiable (by simp)
  have hh : IsPhaseTest P (fun z => inner ℂ (G z) (G z)) := isPhaseTest_inner hG hG
  set h : ℝ × Space → ℂ := fun z => inner ℂ (G z) (G z) with hhdef
  have hT : IsPhaseTest P (B0005.T0op G) := B0005.IsPhaseTest.T0op hG
  have hsym : ∀ z (x : CVec3), (inner ℂ x (G z)).re = (inner ℂ (G z) x).re := by
    intro z x
    rw [← inner_conj_symm (G z) x, Complex.conj_re]
  have hpt : ∀ z, (inner ℂ (G z) (B0005.T0op G z)).re =
      1 / 2 * (dτ h z).re - 1 / 4 * (radialT h z).re := by
    intro z
    have e1 : dτ h z = inner ℂ (G z) (dτ G z) + inner ℂ (dτ G z) (G z) := dτ_inner hGd hGd z
    have e2 : ∀ j : Fin 3, dy j h z =
        inner ℂ (G z) (dy j G z) + inner ℂ (dy j G z) (G z) := fun j => dy_inner hGd hGd j z
    have a1 : (dτ h z).re = 2 * (inner ℂ (G z) (dτ G z)).re := by
      rw [e1, Complex.add_re, hsym]; ring
    have a2 : (radialT h z).re = ∑ j : Fin 3, z.2 j * (2 * (inner ℂ (G z) (dy j G z)).re) := by
      simp only [radialT, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.smul_re, e2 j, Complex.add_re, hsym, smul_eq_mul]
      ring
    have a3 : (inner ℂ (G z) (B0005.T0op G z)).re =
        (inner ℂ (G z) (dτ G z)).re -
          1 / 2 * ∑ j : Fin 3, z.2 j * (inner ℂ (G z) (dy j G z)).re := by
      have : inner ℂ (G z) (B0005.T0op G z) = inner ℂ (G z) (dτ G z) -
          ((1 / 2 : ℝ) : ℂ) * ∑ j : Fin 3, ((z.2 j : ℝ) : ℂ) * inner ℂ (G z) (dy j G z) := by
        simp only [B0005.T0op, radialT, inner_sub_right, inner_real_smul_right', inner_sum]
      rw [this, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_sum]
      simp only [Complex.re_ofReal_mul]
    rw [a3, a1, a2, Finset.mul_sum]
    simp only [Finset.mul_sum]
    have : ∑ j : Fin 3, 1 / 4 * (z.2 j * (2 * (inner ℂ (G z) (dy j G z)).re)) =
        ∑ j : Fin 3, 1 / 2 * (z.2 j * (inner ℂ (G z) (dy j G z)).re) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    ring
  have hIh : Integrable h μ := integrable_slab_of_test hh
  have hIdτ : Integrable (dτ h) μ := integrable_slab_of_test hh.dτ
  have hIrad : Integrable (radialT h) μ := integrable_slab_of_test hh.radialT
  have h0 : ∫ z, dτ h z ∂μ = 0 := B0005.integral_slab_dτ hh
  have hrad : ∫ z, radialT h z ∂μ = -3 * ∫ z, h z ∂μ := by
    have h3 := B0005.integral_slab_radial hh
    rw [integral_add hIrad (hIh.const_mul 3), integral_const_mul] at h3
    linear_combination h3
  have hint_re : ∀ {f : ℝ × Space → ℂ}, Integrable f μ →
      (∫ z, f z ∂μ).re = ∫ z, (f z).re ∂μ := fun hf => by
    simpa using (Complex.reCLM.integral_comp_comm hf).symm
  have hIre : Integrable (fun z => inner ℂ (G z) (B0005.T0op G z)) μ :=
    integrable_slab_of_test (isPhaseTest_inner hG hT)
  rw [slabInner_eq hG hT, slabInner_eq hG hG, hint_re hIre]
  simp_rw [hpt]
  have hr1 : Integrable (fun z => (dτ h z).re) μ := Complex.reCLM.integrable_comp hIdτ
  have hr2 : Integrable (fun z => (radialT h z).re) μ := Complex.reCLM.integrable_comp hIrad
  rw [integral_sub (hr1.const_mul _) (hr2.const_mul _), integral_const_mul, integral_const_mul,
    ← hint_re hIdτ, ← hint_re hIrad, h0, hrad]
  simp only [Complex.zero_re]
  have : (-3 * ∫ z, h z ∂μ).re = -3 * (∫ z, h z ∂μ).re := by
    simp [Complex.mul_re]
  rw [this]
  ring

/-- **Hilbert energy identity on the smooth core** (source lines 1491-1496,
"`Re ⟨(μ+L)w, w⟩ = (Re μ + 1/4)‖w‖² + ν‖∇w‖²`"). For a phase test `G`, `w = testElem G ∈ Y_2` and
`g = L₀ w` in distributions (`HasPhaseOp (L0T ν) w g`, with `L₀ = 𝒯₀ - νΔ - 1/2`,
`𝒯₀ = ∂_τ - ½ y·∇`),
`Re ⟨w, μ w + g⟩ = (Re μ + 1/4) ‖w‖² + ν ∑ⱼ ‖∂ⱼ w‖²`, where `∂ⱼ w = testElem (∂ⱼ G)`. -/
theorem freeEnergyIdentity {P ν : ℝ} [Fact (0 < P)] {G : ℝ × Space → CVec3}
    (hG : IsPhaseTest P G) (g : Yq P 2)
    (hg : HasPhaseOp (B0411.L0T ν) (testElem P 2 G) g) (μ : ℂ) :
    (inner ℂ (testElem P 2 G) (μ • testElem P 2 G + g)).re =
      (μ.re + 1 / 4) * ‖testElem P 2 G‖ ^ 2 +
        ν * ∑ j : Fin 3, ‖testElem P 2 (dy j G)‖ ^ 2 :=
  freeEnergyIdentity_of phaseTestSkew phaseTestLap hG g hg μ

end UnforcedLeray.Short.PartIIa
