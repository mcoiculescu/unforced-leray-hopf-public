import UnforcedLeray.Cons.C09PressureProjection.Density

/-!
# C9 helper: the pressure Poisson relation at almost every phase

Step C9 (`PressureProjectionStep`, `Blueprint/Construction/Steps.lean`, blueprint unit B0708,
`paper/main.tex` lines 107–110, 164–167 and 13719–13733). Testing the unprojected equation
(2.5) (`SolvesSimilarityNSWithPressure`) on `Ψ_η(τ, y) = η(τ)∇Φ(y)` kills every linear term,
because `U(τ)` is solenoidal at every phase and each linear term pairs `U(τ)` with the
gradient of a test (`Φ`, `∂_k∂_kΦ` and `Θ = DΦ(y)y`). What is left is
`∫ η(τ) Σ_j ⟨(U⊗U + pI)_{·j}, ∇∂_jΦ⟩ dy dτ = 0` for all `η`, so the Hessian relation
`Σ_j ⟨G_j(τ), ∇∂_jΦ⟩ = 0` (that is `-Δp = ∂_i∂_j(U_iU_j)` tested on `Φ`) holds at almost
every phase (`ae_colPairing_stress_hess`); by `Density.lean` one null set serves all tests
(`ae_forall_colPairing_stress_hess`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.Cons.C09

open UnforcedLeray.Blueprint UnforcedLeray.RieszLp

/-! ## `L²` pairings as integrals -/

theorem inner_toL2_toL2 {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (toL2 f) (toL2 g) = ∫ y, inner ℝ (f y) (g y) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_toL2 hf, coeFn_toL2 hg] with y h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {f g : SpatialField} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : Integrable (fun y => inner ℝ (f y) (g y)) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (toL2 f) (toL2 g)).congr ?_
  filter_upwards [coeFn_toL2 hf, coeFn_toL2 hg] with y h1 h2
  rw [h1, h2]

/-- `p e_j ∈ L²` for `p ∈ L²`. -/
theorem memLp_smul_coordinateVector {q : Space → ℝ} (hq : MemLp q 2 volume) (j : Fin 3) :
    MemLp (fun y => q y • coordinateVector j) 2 volume := by
  refine hq.of_le (hq.aestronglyMeasurable.smul_const _) (Eventually.of_forall fun y => ?_)
  rw [norm_smul, norm_coordinateVector, mul_one]

theorem memLp_gradField_test {h : Space → ℝ} (hh : IsSpatialTest h) :
    MemLp (gradField h) 2 volume :=
  (continuous_gradField hh.smooth).memLp_of_hasCompactSupport (hasCompactSupport_gradField hh)

/-! ## The stress columns and the Hessian integrand -/

/-- The columns of `U(τ)⊗U(τ) + p(τ)I` as `L²` classes: `G_j = [U_jU] + [p e_j]`. -/
def stressL2 (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (τ : ℝ) : Fin 3 → L2Space :=
  fun j => toL2 (tensorColumns (U τ) (U τ) j) + toL2 (fun y => p τ y • coordinateVector j)

/-- The pointwise integrand `Σ_j ⟨U_jU + p e_j, ∇∂_jΦ⟩ = Σ_{ij} U_iU_j∂_i∂_jΦ + pΔΦ`. -/
def hessIntegrand (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (Φ : Space → ℝ)
    (z : SpaceTime) : ℝ :=
  ∑ j : Fin 3, (inner ℝ (tensorColumns (U z.1) (U z.1) j z.2)
      (gradField (spatialTestDerivative j Φ) z.2) +
    inner ℝ (p z.1 z.2 • coordinateVector j) (gradField (spatialTestDerivative j Φ) z.2))

theorem integrable_hessIntegrand_slice {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} {τ : ℝ}
    (hT : ColumnsL2 (tensorColumns (U τ) (U τ))) (hp : MemLp (p τ) 2 volume)
    {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) :
    Integrable (fun y => hessIntegrand U p Φ (τ, y)) volume := by
  unfold hessIntegrand
  refine integrable_finset_sum _ fun j _ => ?_
  exact (integrable_inner_of_memLp (hT j) (memLp_gradField_test (hΦ.derivative j))).add
    (integrable_inner_of_memLp (memLp_smul_coordinateVector hp j)
      (memLp_gradField_test (hΦ.derivative j)))

/-- At a phase with `L²` products and pressure, the Hessian relation is the integral of
`hessIntegrand`. -/
theorem colPairing_stressL2_hessL2 {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} {τ : ℝ}
    (hT : ColumnsL2 (tensorColumns (U τ) (U τ))) (hp : MemLp (p τ) 2 volume)
    {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) :
    colPairing (stressL2 U p τ) (hessL2 Φ) = ∫ y, hessIntegrand U p Φ (τ, y) := by
  unfold hessIntegrand colPairing stressL2 hessL2
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hg := memLp_gradField_test (hΦ.derivative j)
    rw [inner_add_left, inner_toL2_toL2 (hT j) hg,
      inner_toL2_toL2 (memLp_smul_coordinateVector hp j) hg,
      integral_add (integrable_inner_of_memLp (hT j) hg)
        (integrable_inner_of_memLp (memLp_smul_coordinateVector hp j) hg)]
  · intro j _
    have hg := memLp_gradField_test (hΦ.derivative j)
    exact (integrable_inner_of_memLp (hT j) hg).add
      (integrable_inner_of_memLp (memLp_smul_coordinateVector hp j) hg)

/-! ## Integrable functions with zero integral -/

/-- An integrable function on `ℝ³` with zero integral. -/
structure IntZero (f : Space → ℝ) : Prop where
  int : Integrable f volume
  zero : ∫ y, f y = 0

theorem IntZero.add {f g : Space → ℝ} (hf : IntZero f) (hg : IntZero g) :
    IntZero (fun y => f y + g y) :=
  ⟨hf.int.add hg.int, by rw [integral_add hf.int hg.int, hf.zero, hg.zero, add_zero]⟩

theorem IntZero.sub {f g : Space → ℝ} (hf : IntZero f) (hg : IntZero g) :
    IntZero (fun y => f y - g y) :=
  ⟨hf.int.sub hg.int, by rw [integral_sub hf.int hg.int, hf.zero, hg.zero, sub_zero]⟩

theorem IntZero.const_mul {f : Space → ℝ} (hf : IntZero f) (c : ℝ) :
    IntZero (fun y => c * f y) :=
  ⟨hf.int.const_mul c, by rw [integral_const_mul, hf.zero, mul_zero]⟩

theorem IntZero.sum {ι : Type*} (s : Finset ι) {f : ι → Space → ℝ}
    (h : ∀ i ∈ s, IntZero (f i)) : IntZero (fun y => ∑ i ∈ s, f i y) :=
  ⟨integrable_finset_sum s fun i hi => (h i hi).int, by
    rw [integral_finset_sum s fun i hi => (h i hi).int]
    exact Finset.sum_eq_zero fun i hi => (h i hi).zero⟩

theorem intZero_solTerm {u : SpatialField} (hu : IsSolenoidal u) {h : Space → ℝ}
    (hh : IsSpatialTest h) : IntZero (solTerm u h) :=
  ⟨hu.integrable h hh, hu.identity h hh⟩

/-- The linear part of (2.5) on `Ψ_η` integrates to zero over `ℝ³` at every phase. -/
theorem intZero_linear_gradTest {η : ℝ → ℝ} (hη : Differentiable ℝ η) {Φ : Space → ℝ}
    (hΦ : IsSpatialTest Φ) (ν : ℝ) {U : ℝ → SpatialField} (τ : ℝ) (hU : IsSolenoidal (U τ)) :
    IntZero (fun y => linearBackgroundIntegrand ν U (gradTest η Φ) (τ, y)) := by
  have hA := intZero_solTerm hU hΦ
  have hB : ∀ k ∈ (Finset.univ : Finset (Fin 3)), IntZero
      (solTerm (U τ) (spatialTestDerivative k (spatialTestDerivative k Φ))) :=
    fun k _ => intZero_solTerm hU ((hΦ.derivative k).derivative k)
  have hC := intZero_solTerm hU (isSpatialTest_radialTest hΦ)
  have hcomb := ((((hA.const_mul (deriv η τ)).add
      (((IntZero.sum _ hB).const_mul (η τ)).const_mul ν)).sub (hA.const_mul (η τ))).sub
      (((hC.sub hA).const_mul (η τ)).const_mul (1 / 2 : ℝ)))
  have hfun : (fun y => linearBackgroundIntegrand ν U (gradTest η Φ) (τ, y)) =
      fun y => deriv η τ * solTerm (U τ) Φ y +
        ν * (η τ * ∑ k : Fin 3,
          solTerm (U τ) (spatialTestDerivative k (spatialTestDerivative k Φ)) y) -
        η τ * solTerm (U τ) Φ y -
        (1 / 2 : ℝ) * (η τ * (solTerm (U τ) (radialTest Φ) y - solTerm (U τ) Φ y)) :=
    funext fun y => linearBackgroundIntegrand_gradTest hη hΦ ν U τ y
  rw [hfun]
  exact hcomb

/-! ## The Poisson relation at almost every phase -/

/-- For each phase test `η`, the Hessian integrand weighted by `η(τ)` is integrable on
spacetime with zero integral: this is (2.5) tested on `η(τ)∇Φ(y)`. -/
theorem weighted_hessIntegrand {ν : ℝ} {U : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    (hsol : ∀ τ, IsSolenoidal (U τ)) (heq : SolvesSimilarityNSWithPressure ν U p)
    {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) :
    Integrable (fun z : SpaceTime => η z.1 * hessIntegrand U p Φ z) volume ∧
      ∫ z : SpaceTime, η z.1 * hessIntegrand U p Φ z = 0 := by
  have hΨ := isSimilarityTest_gradTest hη hηc hΦ
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  have hpt : ∀ z : SpaceTime, convectionTerm U (gradTest η Φ) z +
      pressureSimilarityTerm p (gradTest η Φ) z = η z.1 * hessIntegrand U p Φ z := by
    rintro ⟨τ, y⟩
    rw [convectionTerm_gradTest hΦ, pressureSimilarityTerm_gradTest hΦ, hessIntegrand,
      ← mul_add, ← Finset.sum_add_distrib]
  have hcp : Integrable (fun z => convectionTerm U (gradTest η Φ) z +
      pressureSimilarityTerm p (gradTest η Φ) z) volume :=
    (heq.convection_integrable _ hΨ).add (heq.pressure_integrable _ hΨ)
  have hlin_int : Integrable (linearBackgroundIntegrand ν U (gradTest η Φ)) volume := by
    have h := (((heq.temporal_integrable _ hΨ).add
      ((heq.diffusion_integrable _ hΨ).const_mul ν)).sub (heq.pair_integrable _ hΨ)).sub
      ((heq.dilation_integrable _ hΨ).const_mul (1 / 2 : ℝ))
    exact h
  have hlin : ∫ z, linearBackgroundIntegrand ν U (gradTest η Φ) z = 0 := by
    rw [Measure.volume_eq_prod, integral_prod _ hlin_int]
    have h0 : ∀ τ, ∫ y, linearBackgroundIntegrand ν U (gradTest η Φ) (τ, y) = 0 :=
      fun τ => (intZero_linear_gradTest hηd hΦ ν τ (hsol τ)).zero
    simp only [h0, integral_zero]
  have hid := heq.identity _ hΨ
  have hsplit : ∫ z, (linearBackgroundIntegrand ν U (gradTest η Φ) z +
      convectionTerm U (gradTest η Φ) z + pressureSimilarityTerm p (gradTest η Φ) z) =
      (∫ z, linearBackgroundIntegrand ν U (gradTest η Φ) z) +
        ∫ z, (convectionTerm U (gradTest η Φ) z + pressureSimilarityTerm p (gradTest η Φ) z) := by
    rw [← integral_add hlin_int hcp]
    congr 1
    funext z
    ring
  have hcp0 : ∫ z, (convectionTerm U (gradTest η Φ) z +
      pressureSimilarityTerm p (gradTest η Φ) z) = 0 := by
    linarith
  have hfun : (fun z : SpaceTime => η z.1 * hessIntegrand U p Φ z) =
      fun z => convectionTerm U (gradTest η Φ) z + pressureSimilarityTerm p (gradTest η Φ) z :=
    funext fun z => (hpt z).symm
  rw [hfun]
  exact ⟨hcp, hcp0⟩

/-- **The Poisson relation for one test.** For each compact smooth scalar test `Φ`,
`Σ_j ⟨G_j(τ), ∇∂_jΦ⟩ = 0` at almost every phase `τ`. -/
theorem ae_colPairing_stress_hess {ν : ℝ} {U : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    (hsol : ∀ τ, IsSolenoidal (U τ)) (hT : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)))
    (hp : ∀ τ, MemLp (p τ) 2 volume) (heq : SolvesSimilarityNSWithPressure ν U p)
    {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) :
    ∀ᵐ τ, colPairing (stressL2 U p τ) (hessL2 Φ) = 0 := by
  set r : ℝ → ℝ := fun τ => ∫ y, hessIntegrand U p Φ (τ, y) with hr
  have hslice : ∀ (η : ℝ → ℝ) (τ : ℝ),
      ∫ y, (fun z : SpaceTime => η z.1 * hessIntegrand U p Φ z) (τ, y) = η τ * r τ :=
    fun η τ => by
      show ∫ y, η τ * hessIntegrand U p Φ (τ, y) = η τ * r τ
      exact integral_const_mul _ _
  -- local integrability of `r`
  have hloc : LocallyIntegrable r volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
    let b : ContDiffBump (0 : ℝ) :=
      ⟨max ρ 1, max ρ 1 + 1, by positivity, by linarith⟩
    have hb1 : ∀ τ ∈ K, b τ = 1 := fun τ hτ =>
      b.one_of_mem_closedBall (closedBall_subset_closedBall (le_max_left _ _) (hρ hτ))
    have hw := (weighted_hessIntegrand hsol heq hΦ (b.contDiff (n := (⊤ : ℕ∞)))
      b.hasCompactSupport).1
    have hint := hw.integral_prod_left
    simp only [hslice] at hint
    refine (hint.integrableOn (s := K)).congr_fun ?_ hK.measurableSet
    intro τ hτ
    simp only [hb1 τ hτ, one_mul]
  have hae : ∀ᵐ τ, r τ = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    intro g hg hgc
    have hw := weighted_hessIntegrand hsol heq hΦ hg hgc
    have h2 := hw.2
    rw [Measure.volume_eq_prod, integral_prod _ hw.1] at h2
    simp only [hslice] at h2
    simpa only [smul_eq_mul] using h2
  filter_upwards [hae] with τ hτ
  rw [colPairing_stressL2_hessL2 (hT τ) (hp τ) hΦ]
  exact hτ

/-- **One null set for all tests.** At almost every phase, `Σ_j ⟨G_j(τ), ∇∂_jΦ⟩ = 0` for
every compact smooth scalar test `Φ`. -/
theorem ae_forall_colPairing_stress_hess {ν : ℝ} {U : ℝ → SpatialField}
    {p : ℝ → Space → ℝ} (hsol : ∀ τ, IsSolenoidal (U τ))
    (hT : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ))) (hp : ∀ τ, MemLp (p τ) 2 volume)
    (heq : SolvesSimilarityNSWithPressure ν U p) :
    ∀ᵐ τ, ∀ Φ, IsSpatialTest Φ → colPairing (stressL2 U p τ) (hessL2 Φ) = 0 :=
  ae_forall_colPairing_hessL2 (stressL2 U p) fun _ hΦ =>
    ae_colPairing_stress_hess hsol hT hp heq hΦ

end UnforcedLeray.Cons.C09
