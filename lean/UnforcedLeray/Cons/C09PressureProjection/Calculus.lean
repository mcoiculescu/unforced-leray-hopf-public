import UnforcedLeray.Blueprint.Construction.Steps
import UnforcedLeray.Lib.CZL2.TestProjection
import UnforcedLeray.Analysis.SobolevGraph.MixedPartials

/-!
# C9 helper: the calculus of the gradient tests `η(τ)∇Φ(y)`

Step C9 (`PressureProjectionStep`, `Blueprint/Construction/Steps.lean`, blueprint unit B0708,
`paper/main.tex` lines 107–110 and 164–167) tests the unprojected equation (2.5) on the
similarity tests `Ψ(τ, y) = η(τ) ∇Φ(y)`. This file computes every derivative of `Ψ` that
the weak form uses, and the pointwise pairings, in terms of the scalar test `Φ`:

* `∂_τΨ = η'∇Φ`, `DΨ = η D∇Φ`, `ΔΨ = η Σ_k ∇(∂_k∂_kΦ)`, `div Ψ = η Σ_k ∂_k∂_kΦ`;
* `(D∇Φ(y) y)_i = ∂_iΘ(y) - ∂_iΦ(y)` with the test `Θ(y) = DΦ(y) y`;
* `∂_j∇Φ = ∇∂_jΦ` (symmetry of the Hessian of a smooth function).

The lemma `fderiv_apply_coord` is copied from

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.Cons.C09

open UnforcedLeray.Blueprint UnforcedLeray.RieszLp

/-- Components of the derivative of a vector field: `(DF(x) v)_i = D(F_i)(x) v`
(copied from `Units/B0628.lean`, `fderiv_apply_coord`). -/
theorem fderiv_apply_coord {F : Space → Space} {x : Space} (hF : DifferentiableAt ℝ F x)
    (v : Space) (i : Fin 3) : fderiv ℝ F x v i = fderiv ℝ (fun y => F y i) x v := by
  have h : HasFDerivAt (fun y => F y i)
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ F x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).hasFDerivAt.comp x hF.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The Euclidean inner product in coordinates. -/
theorem inner_eq_sum (v w : Space) : inner ℝ v w = ∑ i : Fin 3, v i * w i := by
  simp [PiLp.inner_apply, mul_comm]

/-- `⟨v, ∇h(y)⟩ = Σ_i v_i ∂_i h(y)`. -/
theorem inner_gradField (v : Space) (h : Space → ℝ) (y : Space) :
    inner ℝ v (gradField h y) = ∑ i : Fin 3, v i * spatialTestDerivative i h y := by
  rw [real_inner_comm]
  exact Leray.gradient_inner h y v

/-- `⟨c e_j, w⟩ = c w_j`. -/
theorem inner_smul_coordinateVector (c : ℝ) (j : Fin 3) (w : Space) :
    inner ℝ (c • coordinateVector j) w = c * w j := by
  rw [real_inner_smul_left, coordinateVector, EuclideanSpace.inner_single_left]
  simp

theorem contDiff_gradField {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (gradField Φ) := by
  unfold gradField
  exact ContDiff.sum fun i _ =>
    (PressureAnalysis.contDiff_spatialTestDerivative hΦ i).smul contDiff_const

theorem differentiable_gradField {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Differentiable ℝ (gradField Φ) :=
  (contDiff_gradField hΦ).differentiable (by simp)

theorem hasCompactSupport_gradField {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) :
    HasCompactSupport (gradField Φ) := by
  refine (hΦ.compact.fderiv ℝ).mono ?_
  intro y hy h
  apply hy
  simp [gradField, spatialTestDerivative, h]

/-- The derivative of a coordinate partial: `D(∂_jΦ)(x) = (D²Φ(x))(·)(e_j)`. -/
theorem hasFDerivAt_partial {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3) (x : Space) :
    HasFDerivAt (fun y => fderiv ℝ Φ y (coordinateVector j))
      ((fderiv ℝ (fderiv ℝ Φ) x).flip (coordinateVector j)) x := by
  have hd : Differentiable ℝ (fderiv ℝ Φ) :=
    (ContDiff.fderiv_right (m := ∞) hΦ (by simp)).differentiable (by simp)
  simpa using (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector j) x)

/-- `∂_i∂_jΦ(x) = D²Φ(x) e_i e_j` for a smooth function. -/
theorem second_partial_eq {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i j : Fin 3) (x : Space) :
    spatialTestDerivative i (spatialTestDerivative j Φ) x =
      fderiv ℝ (fderiv ℝ Φ) x (coordinateVector i) (coordinateVector j) := by
  change fderiv ℝ (fun y => fderiv ℝ Φ y (coordinateVector j)) x (coordinateVector i) = _
  rw [(hasFDerivAt_partial hΦ j x).fderiv]
  rfl

/-- Coordinate partials of a smooth function commute. -/
theorem partial_comm {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i j : Fin 3) :
    spatialTestDerivative i (spatialTestDerivative j Φ) =
      spatialTestDerivative j (spatialTestDerivative i Φ) := by
  funext x
  rw [second_partial_eq hΦ i j x, second_partial_eq hΦ j i x]
  exact (hΦ.contDiffAt.isSymmSndFDerivAt (by simp)).eq
    (coordinateVector i) (coordinateVector j)

/-- `(D∇Φ(y) v)_i = D²Φ(y) v e_i`. -/
theorem fderiv_gradField_apply_coord {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (y v : Space)
    (i : Fin 3) :
    fderiv ℝ (gradField Φ) y v i = fderiv ℝ (fderiv ℝ Φ) y v (coordinateVector i) := by
  rw [fderiv_apply_coord ((differentiable_gradField hΦ) y)]
  have : (fun y => gradField Φ y i) = fun y => fderiv ℝ Φ y (coordinateVector i) :=
    funext fun y => gradField_apply Φ y i
  rw [this, (hasFDerivAt_partial hΦ i y).fderiv]
  rfl

/-- `∂_j ∇Φ = ∇ ∂_jΦ` for a smooth function. -/
theorem fderiv_gradField_coord {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (y : Space) (j : Fin 3) :
    fderiv ℝ (gradField Φ) y (coordinateVector j) = gradField (spatialTestDerivative j Φ) y := by
  refine PiLp.ext fun i => ?_
  rw [fderiv_gradField_apply_coord hΦ, gradField_apply, second_partial_eq hΦ i j y]
  exact (hΦ.contDiffAt.isSymmSndFDerivAt (by simp)).eq
    (coordinateVector j) (coordinateVector i)

/-! ## The radial test `Θ(y) = DΦ(y) y` -/

/-- `Θ(y) = DΦ(y) y = Σ_k y_k ∂_kΦ(y)`. -/
def radialTest (Φ : Space → ℝ) : Space → ℝ := fun y => fderiv ℝ Φ y y

theorem isSpatialTest_radialTest {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) :
    IsSpatialTest (radialTest Φ) where
  smooth := (ContDiff.fderiv_right (m := ∞) hΦ.smooth (by simp)).clm_apply contDiff_id
  compact := by
    refine (hΦ.compact.fderiv ℝ).mono ?_
    intro y hy h
    apply hy
    simp [radialTest, h]

/-- `∂_iΘ(y) = D²Φ(y) e_i y + ∂_iΦ(y)`. -/
theorem spatialTestDerivative_radialTest {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin 3)
    (y : Space) :
    spatialTestDerivative i (radialTest Φ) y =
      fderiv ℝ (fderiv ℝ Φ) y (coordinateVector i) y + spatialTestDerivative i Φ y := by
  have hd : DifferentiableAt ℝ (fderiv ℝ Φ) y :=
    ((ContDiff.fderiv_right (m := ∞) hΦ (by simp)).differentiable (by simp)) y
  change fderiv ℝ (fun y => (fderiv ℝ Φ y) (id y)) y (coordinateVector i) = _
  rw [fderiv_clm_apply hd differentiableAt_id, fderiv_id]
  simp [spatialTestDerivative, add_comm]

/-- `(D∇Φ(y) y)_i = ∂_iΘ(y) - ∂_iΦ(y)`. -/
theorem fderiv_gradField_radial {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (y : Space)
    (i : Fin 3) :
    fderiv ℝ (gradField Φ) y y i =
      spatialTestDerivative i (radialTest Φ) y - spatialTestDerivative i Φ y := by
  rw [fderiv_gradField_apply_coord hΦ, spatialTestDerivative_radialTest hΦ, add_sub_cancel_right]
  exact (hΦ.contDiffAt.isSymmSndFDerivAt (by simp)).eq y (coordinateVector i)

/-! ## The similarity test `Ψ_η(τ, y) = η(τ) ∇Φ(y)` -/

/-- `Ψ_η(τ, y) = η(τ) ∇Φ(y)`. -/
def gradTest (η : ℝ → ℝ) (Φ : Space → ℝ) : SpaceTime → Space :=
  fun z => η z.1 • gradField Φ z.2

theorem isSimilarityTest_gradTest {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) :
    IsSimilarityTest (gradTest η Φ) where
  smooth := (hη.comp contDiff_fst).smul ((contDiff_gradField hΦ.smooth).comp contDiff_snd)
  compact := by
    have hg := hasCompactSupport_gradField hΦ
    refine IsCompact.of_isClosed_subset (hηc.isCompact.prod hg.isCompact)
      (isClosed_tsupport _) ?_
    refine closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    intro z hz
    refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
    · intro h
      apply hz
      simp [gradTest, h]
    · intro h
      apply hz
      simp [gradTest, h]

theorem timeDerivative_gradTest {η : ℝ → ℝ} (hη : Differentiable ℝ η) (Φ : Space → ℝ)
    (τ : ℝ) (y : Space) :
    timeDerivative (gradTest η Φ) τ y = deriv η τ • gradField Φ y := by
  have h : HasDerivAt (fun s => η s • gradField Φ y) (deriv η τ • gradField Φ y) τ :=
    (hη τ).hasDerivAt.smul_const (gradField Φ y)
  change fderiv ℝ (fun s => η s • gradField Φ y) τ 1 = _
  rw [h.hasFDerivAt.fderiv]
  simp

theorem spatialDerivative_gradTest {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (η : ℝ → ℝ)
    (τ : ℝ) (y : Space) :
    spatialDerivative (gradTest η Φ) τ y = η τ • fderiv ℝ (gradField Φ) y := by
  change fderiv ℝ (fun y => η τ • gradField Φ y) y = _
  exact fderiv_fun_const_smul ((differentiable_gradField hΦ) y) (η τ)

theorem spatialLaplacian_gradTest {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) (η : ℝ → ℝ)
    (τ : ℝ) (y : Space) :
    spatialLaplacian (gradTest η Φ) τ y =
      η τ • ∑ k : Fin 3, gradField (spatialTestDerivative k (spatialTestDerivative k Φ)) y := by
  unfold spatialLaplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hf : (fun y => spatialDerivative (gradTest η Φ) τ y (coordinateVector k)) =
      fun y => η τ • gradField (spatialTestDerivative k Φ) y := by
    funext y
    rw [spatialDerivative_gradTest hΦ.smooth, ContinuousLinearMap.smul_apply,
      fderiv_gradField_coord hΦ.smooth]
  rw [hf, fderiv_fun_const_smul ((differentiable_gradField (hΦ.derivative k).smooth) y),
    ContinuousLinearMap.smul_apply, fderiv_gradField_coord (hΦ.derivative k).smooth]

theorem spatialDivergence_gradTest {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) (η : ℝ → ℝ)
    (τ : ℝ) (y : Space) :
    spatialDivergence (gradTest η Φ) τ y =
      η τ * ∑ k : Fin 3, spatialTestDerivative k (spatialTestDerivative k Φ) y := by
  unfold spatialDivergence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [spatialDerivative_gradTest hΦ.smooth, ContinuousLinearMap.smul_apply,
    fderiv_gradField_coord hΦ.smooth, PiLp.smul_apply, gradField_apply, smul_eq_mul]

/-! ## The pointwise integrands on `Ψ_η` -/

/-- The integrand `Σ_i u_i ∂_i h` of `IsSolenoidal`. -/
def solTerm (u : SpatialField) (h : Space → ℝ) (y : Space) : ℝ :=
  ∑ i : Fin 3, u y i * spatialTestDerivative i h y

theorem inner_gradField_eq_solTerm (u : SpatialField) (h : Space → ℝ) (y : Space) :
    inner ℝ (u y) (gradField h y) = solTerm u h y :=
  inner_gradField (u y) h y

/-- The linear part of (2.5) on `Ψ_η` is a combination of solenoidal pairings against the
gradients of the tests `Φ`, `∂_k∂_kΦ` and `Θ`. -/
theorem linearBackgroundIntegrand_gradTest {η : ℝ → ℝ} (hη : Differentiable ℝ η)
    {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) (ν : ℝ) (U : ℝ → SpatialField) (τ : ℝ)
    (y : Space) :
    linearBackgroundIntegrand ν U (gradTest η Φ) (τ, y) =
      deriv η τ * solTerm (U τ) Φ y +
        ν * (η τ * ∑ k : Fin 3,
          solTerm (U τ) (spatialTestDerivative k (spatialTestDerivative k Φ)) y) -
        η τ * solTerm (U τ) Φ y -
        (1 / 2 : ℝ) * (η τ * (solTerm (U τ) (radialTest Φ) y - solTerm (U τ) Φ y)) := by
  have hdil : inner ℝ (U τ y) (fderiv ℝ (gradField Φ) y y) =
      solTerm (U τ) (radialTest Φ) y - solTerm (U τ) Φ y := by
    rw [inner_eq_sum, solTerm, solTerm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_gradField_radial hΦ.smooth, mul_sub]
  simp only [linearBackgroundIntegrand, temporalTerm, diffusionTerm, pairTerm, dilationTerm]
  rw [timeDerivative_gradTest hη, spatialLaplacian_gradTest hΦ,
    spatialDerivative_gradTest hΦ.smooth, ContinuousLinearMap.smul_apply]
  simp only [gradTest, real_inner_smul_right, inner_sum, inner_gradField_eq_solTerm, hdil]

/-- `∇Φ`'s Hessian pairing with the columns of `U ⊗ U`: the convection term on `Ψ_η`. -/
theorem convectionTerm_gradTest {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) (η : ℝ → ℝ)
    (U : ℝ → SpatialField) (τ : ℝ) (y : Space) :
    convectionTerm U (gradTest η Φ) (τ, y) =
      η τ * ∑ j : Fin 3, inner ℝ (tensorColumns (U τ) (U τ) j y)
        (gradField (spatialTestDerivative j Φ) y) := by
  simp only [convectionTerm]
  rw [spatialDerivative_gradTest hΦ.smooth, ContinuousLinearMap.smul_apply,
    real_inner_smul_right]
  congr 1
  have hU : fderiv ℝ (gradField Φ) y (U τ y) =
      ∑ j : Fin 3, U τ y j • gradField (spatialTestDerivative j Φ) y := by
    conv_lhs => rw [eq_sum_coordinateVector (U τ y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, fderiv_gradField_coord hΦ.smooth]
  rw [hU, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_right, tensorColumns, real_inner_smul_left]

/-- The pressure term on `Ψ_η`. -/
theorem pressureSimilarityTerm_gradTest {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) (η : ℝ → ℝ)
    (p : ℝ → Space → ℝ) (τ : ℝ) (y : Space) :
    pressureSimilarityTerm p (gradTest η Φ) (τ, y) =
      η τ * ∑ j : Fin 3, inner ℝ (p τ y • coordinateVector j)
        (gradField (spatialTestDerivative j Φ) y) := by
  simp only [pressureSimilarityTerm]
  rw [spatialDivergence_gradTest hΦ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_coordinateVector, gradField_apply]
  ring

end UnforcedLeray.Cons.C09
