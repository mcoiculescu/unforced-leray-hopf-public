import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Units.B0005.Consistency
import UnforcedLeray.Units.B0411

/-!
# Part II-a, task `PartII-a:F13`: the Hilbert energy identity on the smooth core
(assembly, conditional on two period-slab integral identities; both are proved in
`Short/PartII-a/Tasks/F13EnergyIdentity.lean`, which also states the unconditional theorem)

Source of record: `the November 2 reference manuscript`, lines 1491-1496
("On the Hilbert core, direct integration by parts gives
`Re ⟨(μ+L)w, w⟩ = (Re μ + 1/4)‖w‖² + ν‖∇w‖²`").


(`L₀ w = g` is expressed by `HasPhaseOp (L0T ν) w g`, which determines `g` by
`hasPhaseOp_unique`; the gradient term is the sum of squared `Y_2` norms of the three partial
derivatives of the smooth core element).

Library facts used (Units/B0005/Consistency.lean, Units/B0411.lean):
`hasT0_testElem`, `hasHLap_testElem` (the smooth core element is in the graph with `𝒯₀w`,
`νΔw` the test elements of the classical `T0op G`, `nuLapT ν G`), `hasPhaseOp_L0T`,
`hasPhaseOp_unique`.

New here:
* `inner_testElem_two` (PROVED): the Hilbert inner product of two test elements of `Y_2` is
  `P⁻¹ ∫₀ᴾ∫ ⟪G, H⟫ dy dt` (`L2.inner_def` on both layers, as in `phasePair_eq_periodIntegral`).
* `PhaseTestSkew` and `PhaseTestLap`: the two integral identities of the direct integration by
  parts (proved in `Tasks/F13EnergyIdentity.lean` as `phaseTestSkew`, `phaseTestLap`).
* `freeEnergyIdentity_of` (PROVED from the two): the assembly.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace

/-- The period-slab integral `∫₀ᴾ ∫_{ℝ³} ⟪A(t,y), B(t,y)⟫ dy dt` of the Hermitian pairing
(conjugate-linear in `A`). -/
def slabInner (P : ℝ) (A B : ℝ × Space → CVec3) : ℂ :=
  ∫ t in Ioc (0 : ℝ) (0 + P), ∫ y, inner ℂ (A (t, y)) (B (t, y))

/-- **Skew part of the energy identity** (source lines 1491-1496):
for a phase test `G`, `Re ∫₀ᴾ∫ ⟪G, 𝒯₀G⟫ = (3/4) ∫₀ᴾ∫ |G|²`, with `𝒯₀ = ∂_τ - ½ y·∇`
(`B0005.T0op`). Proof idea: with `h = ⟪G, G⟫` one has `2 Re ⟪G, ∂_τ G⟫ = ∂_τ h` and
`2 Re ⟪G, ∂ⱼ G⟫ = ∂ⱼ h`, and the slab integrals `∫ ∂_τ h = 0` and `∫ (y·∇h + 3h) = 0`
(`B0005.integral_slab_dτ`, `B0005.integral_slab_radial`). -/
def PhaseTestSkew : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (G : ℝ × Space → CVec3), IsPhaseTest P G →
    (slabInner P G (B0005.T0op G)).re = 3 / 4 * (slabInner P G G).re

/-- **Diffusion part of the energy identity** (source lines 1491-1496):
for a phase test `G`, `∫₀ᴾ∫ ⟪G, νΔG⟫ = -ν ∑ⱼ ∫₀ᴾ∫ |∂ⱼG|²`. Proof idea: with
`Kⱼ = ⟪G, ∂ⱼ G⟫` one has `∂ⱼ Kⱼ = ⟪∂ⱼG, ∂ⱼG⟫ + ⟪G, ∂ⱼ∂ⱼ G⟫` and `∫ ∂ⱼ Kⱼ = 0`
(`B0005.integral_slab_dy`). -/
def PhaseTestLap : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (G : ℝ × Space → CVec3), IsPhaseTest P G →
    slabInner P G (nuLapT ν G) = -(ν : ℂ) * ∑ j : Fin 3, slabInner P (dy j G) (dy j G)

/-! ### The Hilbert inner product of two test elements -/

/-- **Bridge**: the Hilbert inner product on `Y_2` of two test elements is the normalised
period-slab integral of the pointwise Hermitian pairing. -/
theorem inner_testElem_two {P : ℝ} [Fact (0 < P)] {G H : ℝ × Space → CVec3}
    (hG : IsPhaseTest P G) (hH : IsPhaseTest P H) :
    inner ℂ (testElem P 2 G) (testElem P 2 H) = ((P⁻¹ : ℝ) : ℂ) * slabInner P G H := by
  have hsG := hG.isSliceTest 2
  have hsH := hH.isSliceTest 2
  rw [MeasureTheory.L2.inner_def, testElem_of hsG, testElem_of hsH]
  have h1 : (fun τ : AddCircle P => inner ℂ
      ((ContinuousMap.toLp (E := Lp CVec3 2 (volume : Measure Space)) 2
        AddCircle.haarAddCircle ℂ (circleSlice hsG)) τ)
      ((ContinuousMap.toLp (E := Lp CVec3 2 (volume : Measure Space)) 2
        AddCircle.haarAddCircle ℂ (circleSlice hsH)) τ)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => inner ℂ (circleSlice hsG τ) (circleSlice hsH τ) := by
    filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space))
      (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hsG),
      ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space))
      (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hsH)] with τ h1 h2
    simp only [h1, h2]
  rw [integral_congr_ae h1, AddCircle.integral_haarAddCircle,
    ← AddCircle.integral_preimage (T := P) (0 : ℝ)]
  rw [Complex.real_smul]
  congr 1
  unfold slabInner
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [circleSlice_coe, circleSlice_coe, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hsG.2.memLp t), MemLp.coeFn_toLp (hsH.2.memLp t)] with y h1 h2
  simp only [sliceMap]
  rw [h1, h2]

/-! ### Assembly -/

/-- The squared `Y_2` norm of a test element is the normalised slab integral of `|G|²`. -/
theorem normSq_testElem {P : ℝ} [Fact (0 < P)] {G : ℝ × Space → CVec3} (hG : IsPhaseTest P G) :
    ‖testElem P 2 G‖ ^ 2 = P⁻¹ * (slabInner P G G).re := by
  have h := inner_testElem_two hG hG
  have h1 : (inner ℂ (testElem P 2 G) (testElem P 2 G)).re = ‖testElem P 2 G‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [← h1, h, Complex.re_ofReal_mul]

/-- **`PartII-a:F13`, conditional on the two slab identities.** For a phase test `G` and
`g = L₀ (testElem G)` in distributions (`HasPhaseOp (L0T ν) (testElem G) g`),
`Re ⟨w, μ w + g⟩ = (Re μ + 1/4) ‖w‖² + ν ∑ⱼ ‖∂ⱼ w‖²` for `w = testElem G` (source lines 1491-1496). -/
theorem freeEnergyIdentity_of (hS : PhaseTestSkew) (hL : PhaseTestLap)
    {P ν : ℝ} [Fact (0 < P)] {G : ℝ × Space → CVec3} (hG : IsPhaseTest P G) (g : Yq P 2)
    (hg : HasPhaseOp (B0411.L0T ν) (testElem P 2 G) g) (μ : ℂ) :
    (inner ℂ (testElem P 2 G) (μ • testElem P 2 G + g)).re =
      (μ.re + 1 / 4) * ‖testElem P 2 G‖ ^ 2 +
        ν * ∑ j : Fin 3, ‖testElem P 2 (dy j G)‖ ^ 2 := by
  have hT := B0005.hasT0_testElem (q := 2) hG
  have hLap := B0005.hasHLap_testElem (q := 2) hG ν
  have hL0 := B0411.hasPhaseOp_L0T hLap hT
  have hgeq : g = testElem P 2 (B0005.T0op G) - testElem P 2 (nuLapT ν G) -
      (1 / 2 : ℂ) • testElem P 2 G := B0411.hasPhaseOp_unique hg hL0
  have hG1 : IsPhaseTest P (B0005.T0op G) := B0005.IsPhaseTest.T0op hG
  have hG2 : IsPhaseTest P (nuLapT ν G) := hG.lapT.const_smul ν
  have hGj : ∀ j : Fin 3, IsPhaseTest P (dy j G) := fun j => hG.dy j
  set w := testElem P 2 G with hw
  set b := testElem P 2 (B0005.T0op G) with hb
  set a := testElem P 2 (nuLapT ν G) with ha
  have e1 : inner ℂ w (μ • w + g) =
      μ * inner ℂ w w + inner ℂ w b - inner ℂ w a - (1 / 2 : ℂ) * inner ℂ w w := by
    rw [hgeq, inner_add_right, inner_sub_right, inner_sub_right, inner_smul_right,
      inner_smul_right]
    ring
  have i0 : inner ℂ w w = ((P⁻¹ : ℝ) : ℂ) * slabInner P G G := inner_testElem_two hG hG
  have i1 : inner ℂ w b = ((P⁻¹ : ℝ) : ℂ) * slabInner P G (B0005.T0op G) :=
    inner_testElem_two hG hG1
  have i2 : inner ℂ w a = ((P⁻¹ : ℝ) : ℂ) * slabInner P G (nuLapT ν G) :=
    inner_testElem_two hG hG2
  have hlap := hL P ν G hG
  have hsk := hS P G hG
  have hnj : ∀ j : Fin 3, ‖testElem P 2 (dy j G)‖ ^ 2 = P⁻¹ * (slabInner P (dy j G) (dy j G)).re :=
    fun j => normSq_testElem (hGj j)
  have hn0 : ‖w‖ ^ 2 = P⁻¹ * (slabInner P G G).re := normSq_testElem hG
  have himw : (slabInner P G G).im = 0 := by
    have h := i0
    have h2 : (inner ℂ w w).im = 0 := by simpa using (inner_self_im (𝕜 := ℂ) w)
    rw [h] at h2
    have hP : (P⁻¹ : ℝ) ≠ 0 := inv_ne_zero (Fact.out : 0 < P).ne'
    simpa [Complex.mul_im, hP] using h2
  have hPc : ((P⁻¹ : ℝ) : ℂ) = (P⁻¹ : ℝ) := rfl
  set c : ℝ := P⁻¹ with hc
  set A : ℂ := slabInner P G G with hA
  set S : ℝ := ∑ j : Fin 3, (slabInner P (dy j G) (dy j G)).re with hSdef
  rw [e1, i0, i1, i2, hlap, hn0]
  have r1 : (μ * ((c : ℂ) * A)).re = μ.re * (c * A.re) := by
    simp [Complex.mul_re, himw]
  have r2 : ((c : ℂ) * slabInner P G (B0005.T0op G)).re = c * (3 / 4 * A.re) := by
    rw [Complex.re_ofReal_mul, hsk]
  have r3 : ((c : ℂ) * (-(ν : ℂ) * ∑ j : Fin 3, slabInner P (dy j G) (dy j G))).re =
      c * (-ν * S) := by
    rw [Complex.re_ofReal_mul]
    simp [Complex.mul_re, Complex.re_sum, Complex.im_sum, hSdef]
  have r4 : ((1 / 2 : ℂ) * ((c : ℂ) * A)).re = 1 / 2 * (c * A.re) := by
    simp [Complex.mul_re, himw]
  rw [Complex.sub_re, Complex.sub_re, Complex.add_re, r1, r2, r3, r4]
  have hS1 : ∑ j : Fin 3, ‖testElem P 2 (dy j G)‖ ^ 2 = c * S := by
    simp only [hnj]
    rw [hSdef, Finset.mul_sum]
  rw [hS1]
  ring

end UnforcedLeray.Short.PartIIa
