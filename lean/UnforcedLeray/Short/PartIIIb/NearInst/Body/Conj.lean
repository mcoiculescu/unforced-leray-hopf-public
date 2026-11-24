import UnforcedLeray.Short.PartIIIb.NearInst.Targets

/-!
# Complex conjugation and the real body inverses (source 1675-1677)

Source of record: `the November 2 reference manuscript`.  The body inverses
`T_ε = (μ - A_ε)^{-1}P_ε` and `T_0` of `near/free-comparison.tex` (1675-1677) are defined in
`PartII-a/StatementsNear.lean` on complex `L²` spaces (`PartIIa.Teps = B0223.RepsVec ∘ PepsC`,
`PartIIa.T0flat = B0225.R0 ∘ PepsC 0`), because `μ` is complex there.  For real `μ` they map real
fields to real fields: the Cartesian Leray projection, the meridional lift `J_ε`, the
Ornstein-Uhlenbeck heat semigroup and the flat cylinder heat semigroup all have real kernels, and
`e^{-μt}` is real.  This file gives the abstract mechanism.

* `conjV n` : componentwise conjugation of `ℂⁿ` (conjugate linear, isometric).
* `cjLp μ n` : the induced conjugation `f ↦ \bar f` of `L²(μ; ℂⁿ)` (`IsConj`: involutive,
  `⟪\bar f, \bar g⟫ = conj ⟪f, g⟫`).
* `conjComm_adjoint`, `conjComm_starProjection`, `conjComm_laplace`, `cj_setIntegral_exp_smul` :
  conjugation commutes with adjoints of commuting maps, with orthogonal projections onto
  conjugation-invariant subspaces and with the Laplace transform `∫_0^∞ e^{-μt} S(t) dt` at real
  `μ` of a commuting semigroup.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

/-! ## Componentwise conjugation of `ℂⁿ` -/

/-- Componentwise complex conjugation of `ℂⁿ`, conjugate linear. -/
def conjVLin (n : ℕ) : EuclideanSpace ℂ (Fin n) →ₗ⋆[ℂ] EuclideanSpace ℂ (Fin n) where
  toFun v := WithLp.toLp 2 fun i => conj (v i)
  map_add' v w := by
    ext i
    simp
  map_smul' a v := by
    ext i
    simp

theorem conjVLin_apply (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    conjVLin n v i = conj (v i) := rfl

theorem norm_conjVLin (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) : ‖conjVLin n v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjVLin_apply, RCLike.norm_conj]

/-- Componentwise conjugation as a continuous conjugate-linear map. -/
def conjV (n : ℕ) : EuclideanSpace ℂ (Fin n) →L⋆[ℂ] EuclideanSpace ℂ (Fin n) :=
  (conjVLin n).mkContinuous 1 fun v => by rw [norm_conjVLin, one_mul]

@[simp] theorem conjV_apply (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    conjV n v i = conj (v i) := rfl

theorem conjV_conjV (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) : conjV n (conjV n v) = v := by
  ext i
  simp

theorem inner_conjV (n : ℕ) (v w : EuclideanSpace ℂ (Fin n)) :
    ⟪conjV n v, conjV n w⟫_ℂ = conj ⟪v, w⟫_ℂ := by
  simp only [PiLp.inner_apply, conjV_apply, RCLike.inner_apply, map_sum, map_mul,
    RingHomCompTriple.comp_apply, RingHom.id_apply]

/-! ## Abstract conjugations -/

section Abstract

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- `cj` is a conjugation: an involutive conjugate-linear map with `⟪cj x, cj y⟫ = conj ⟪x, y⟫`. -/
def IsConj (cj : X →L⋆[ℂ] X) : Prop :=
  (∀ x, cj (cj x) = x) ∧ ∀ x y, ⟪cj x, cj y⟫_ℂ = conj ⟪x, y⟫_ℂ

theorem IsConj.inner_left {cj : X →L⋆[ℂ] X} (h : IsConj cj) (x y : X) :
    ⟪cj x, y⟫_ℂ = conj ⟪x, cj y⟫_ℂ := by
  conv_lhs => rw [← h.1 y]
  exact h.2 x (cj y)

end Abstract

section Adjoint

variable {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- If `J` commutes with conjugations, so does its adjoint. -/
theorem conjComm_adjoint {cjH : H →L⋆[ℂ] H} {cjY : Y →L⋆[ℂ] Y} (hH : IsConj cjH)
    (hY : IsConj cjY) (J : H →L[ℂ] Y) (hJ : ∀ x, J (cjH x) = cjY (J x)) (y : Y) :
    ContinuousLinearMap.adjoint J (cjY y) = cjH (ContinuousLinearMap.adjoint J y) := by
  refine ext_inner_right ℂ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, hH.inner_left,
    ContinuousLinearMap.adjoint_inner_left, hJ, hY.inner_left]

end Adjoint

section Projection

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The orthogonal projection onto a conjugation-invariant closed subspace commutes with the
conjugation. -/
theorem conjComm_starProjection {cj : X →L⋆[ℂ] X} (h : IsConj cj) (K : Submodule ℂ X)
    [K.HasOrthogonalProjection] (hK : ∀ x ∈ K, cj x ∈ K) (x : X) :
    K.starProjection (cj x) = cj (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hK _ (K.starProjection_apply_mem x))
    fun w hw => ?_
  rw [← map_sub, h.inner_left,
    Submodule.inner_left_of_mem_orthogonal (hK w hw) (K.sub_starProjection_mem_orthogonal x),
    map_zero]

end Projection

section Laplace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Conjugation commutes with `∫_0^∞ e^{-μt} φ(t) dt` for real `μ` and integrable integrand. -/
theorem cj_setIntegral_exp_smul (cj : X →L⋆[ℂ] X) (φ : ℝ → X) (μ : ℝ)
    (hφ : IntegrableOn (fun t : ℝ => Complex.exp (-((μ : ℂ) * t)) • φ t) (Ioi 0)) :
    cj (∫ t in Ioi (0 : ℝ), Complex.exp (-((μ : ℂ) * t)) • φ t) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-((μ : ℂ) * t)) • cj (φ t) := by
  rw [← ContinuousLinearMap.integral_comp_commSL (fun r x => by simp) cj hφ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.map_smulₛₗ]
  congr 1
  rw [← Complex.exp_conj]
  simp

/-- **The Laplace transform at real `μ` commutes with a conjugation commuting with the
semigroup.** -/
theorem conjComm_laplace (S : UnforcedLeray.Infra.ExpSemigroup X) (cj : X →L⋆[ℂ] X)
    (hS : ∀ t : ℝ, 0 < t → ∀ x, S.T t (cj x) = cj (S.T t x)) {μ : ℝ} (hμ : S.ω < μ) (x : X) :
    S.laplace (μ : ℂ) (cj x) = cj (S.laplace (μ : ℂ) x) := by
  have hμ' : S.ω < (μ : ℂ).re := by simpa using hμ
  rw [S.laplace_apply hμ', S.laplace_apply hμ',
    cj_setIntegral_exp_smul cj (fun t => S.T t x) μ (S.integrableOn_lapInt hμ' x)]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by
    simp only [hS t ht]

end Laplace

/-! ## Conjugation on `L²(μ; ℂⁿ)` -/

section Lp

variable {α : Type*} [MeasurableSpace α]

/-- The conjugation `f ↦ \bar f` of `L²(μ; ℂⁿ)`. -/
def cjLp (μ : Measure α) (n : ℕ) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 μ →L⋆[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 μ :=
  (conjV n).compLpL 2 μ

theorem coeFn_cjLp (μ : Measure α) (n : ℕ) (f : Lp (EuclideanSpace ℂ (Fin n)) 2 μ) :
    (cjLp μ n f : α → EuclideanSpace ℂ (Fin n)) =ᵐ[μ] fun a => conjV n (f a) :=
  (conjV n).coeFn_compLp' f

theorem cjLp_cjLp (μ : Measure α) (n : ℕ) (f : Lp (EuclideanSpace ℂ (Fin n)) 2 μ) :
    cjLp μ n (cjLp μ n f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_cjLp μ n (cjLp μ n f), coeFn_cjLp μ n f] with a h1 h2
  rw [h1, h2, conjV_conjV]

theorem inner_cjLp (μ : Measure α) (n : ℕ) (f g : Lp (EuclideanSpace ℂ (Fin n)) 2 μ) :
    ⟪cjLp μ n f, cjLp μ n g⟫_ℂ = conj ⟪f, g⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cjLp μ n f, coeFn_cjLp μ n g] with a h1 h2
  rw [h1, h2, inner_conjV]

theorem isConj_cjLp (μ : Measure α) (n : ℕ) : IsConj (cjLp μ n) :=
  ⟨cjLp_cjLp μ n, inner_cjLp μ n⟩

end Lp

end UnforcedLeray.Short.PartIIIb.NearInst.Body
