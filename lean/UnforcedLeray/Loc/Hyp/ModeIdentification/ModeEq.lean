import UnforcedLeray.Loc.Hyp.ModeIdentification.Slices

/-!
# H-ModeId helpers: the graph and the mode equation at almost every phase

Support for `Loc/Hyp/ModeIdentification.lean` (target `ModeIdentificationHyp`,
`paper/main.tex` lines 172–185, `loc:eq:graph` and `loc:eq:mode`; blueprint units B1007, B1009).

The package states `Δb_* = lapB` and the mode equation against spacetime tests only. Testing
with products `θ(τ)φ(y)` and Fubini gives, at almost every phase `τ` and for every vector test
`φ` (one null set for all tests, `ae_forall_tests`):

* `ae_laplacian`: `⟨b_*(τ), Δφ⟩ = ⟨lapB(τ), φ⟩`;
* `ae_mode`: `(σ - ½)⟨b_*(τ), φ⟩ + ⟨driftB(τ), φ⟩ - h⟨lapB(τ), φ⟩ + ⟨𝔓div(U_*⊗b_* + b_*⊗U_*), φ⟩ = 0`,
  with the literal Leray pairing.

The coupling term has no `L²` bound in the package; its local integrability in `τ` comes from
`coupling_integrable` with a product test whose time factor is `1` on the compact set.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.ModeId

open SobolevGraph

variable {D : BackgroundData}

/-- `∫ θ • g = 0` for `g` locally integrable on `ℝ` and every test `θ` gives `g = 0` a.e. -/
theorem integrable_test_mul {g : ℝ → ℝ} (hg : LocallyIntegrable g) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) : Integrable (fun τ => θ τ * g τ) :=
  hg.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc

theorem locallyIntegrable_const_mul {g : ℝ → ℝ} (hg : LocallyIntegrable g) (c : ℝ) :
    LocallyIntegrable (fun τ => c * g τ) :=
  hg.smul c

theorem integral_lin3 {α : Type*} [MeasurableSpace α] {μ : Measure α} {f₁ f₂ f₃ : α → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (a b : ℝ) :
    ∫ x, (a * f₁ x + f₂ x - b * f₃ x) ∂μ = a * ∫ x, f₁ x ∂μ + ∫ x, f₂ x ∂μ - b * ∫ x, f₃ x ∂μ := by
  have i1 : Integrable (fun x => a * f₁ x) μ := h₁.const_mul a
  have i12 : Integrable (fun x => a * f₁ x + f₂ x) μ := i1.add h₂
  have i3 : Integrable (fun x => b * f₃ x) μ := h₃.const_mul b
  rw [integral_sub i12 i3, integral_add i1 h₂, integral_const_mul, integral_const_mul]

theorem integral_lin4 {α : Type*} [MeasurableSpace α] {μ : Measure α} {f₁ f₂ f₃ f₄ : α → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ)
    (a b : ℝ) :
    ∫ x, (a * f₁ x + f₂ x - b * f₃ x + f₄ x) ∂μ =
      a * ∫ x, f₁ x ∂μ + ∫ x, f₂ x ∂μ - b * ∫ x, f₃ x ∂μ + ∫ x, f₄ x ∂μ := by
  have i : Integrable (fun x => a * f₁ x + f₂ x - b * f₃ x) μ :=
    ((h₁.const_mul a).add h₂).sub (h₃.const_mul b)
  rw [integral_add i h₄, integral_lin3 h₁ h₂ h₃]

/-- **`Δb_* = lapB` at a.e. phase** against every vector test. -/
theorem ae_laplacian (hD : IsUnstableBackground D) :
    ∀ᵐ τ, ∀ φ, IsVectorTest φ →
      inner ℝ (toL2 (D.bstar τ)) (toL2 (testLap φ)) = inner ℝ (toL2 (D.lapB τ)) (toL2 φ) := by
  have hT := hD.1.period_pos
  have hg := hD.2.graph
  have key := ae_forall_tests (Λ := fun τ v =>
      inner ℝ (toL2 (D.bstar τ)) v.2.1 - inner ℝ (toL2 (D.lapB τ)) v.1)
    (fun τ => (continuous_const.inner continuous_snd.fst).sub
      (continuous_const.inner continuous_fst)) (fun φ hφ => ?_)
  · filter_upwards [key] with τ hτ φ hφ
    exact sub_eq_zero.mp (hτ φ hφ)
  · dsimp only [testData]
    have hloc : LocallyIntegrable (fun τ => inner ℝ (toL2 (D.bstar τ)) (toL2 (testLap φ)) -
        inner ℝ (toL2 (D.lapB τ)) (toL2 φ)) :=
      (Y2.locallyIntegrable_inner hT hg.value _).sub (Y2.locallyIntegrable_inner hT hg.laplacian _)
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun θ hθ hθc => ?_)
    have hw := hg.laplacian_weak (prodTest θ φ) (isSimilarityTest_prodTest hθ hθc hφ)
    have e1 : diffusionTerm D.bstar (prodTest θ φ) =
        fun z => inner ℝ (D.bstar z.1 z.2) (θ z.1 • testLap φ z.2) := by
      funext z
      simp only [diffusionTerm, spatialLaplacian_prodTest hφ]
    have e2 : pairTerm D.lapB (prodTest θ φ) =
        fun z => inner ℝ (D.lapB z.1 z.2) (θ z.1 • φ z.2) := rfl
    have hi1 := hw.left_integrable
    have hi2 := hw.right_integrable
    rw [e1] at hi1
    rw [e2] at hi2
    have i1 := integral_pair_prod (θ := θ) (L13.isVectorTest_memLp (isVectorTest_testLap hφ))
      (Y2.ae_memLp hT hg.value) hi1
    have i2 := integral_pair_prod (θ := θ) (L13.isVectorTest_memLp hφ)
      (Y2.ae_memLp hT hg.laplacian) hi2
    have heq := hw.eq
    rw [e1, e2, i1, i2] at heq
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub (integrable_test_mul (Y2.locallyIntegrable_inner hT hg.value _) hθ hθc)
      (integrable_test_mul (Y2.locallyIntegrable_inner hT hg.laplacian _) hθ hθc), heq, sub_self]

theorem projectedCoupling_prodTest {θ : ℝ → ℝ} {φ : Space → Space} (hφ : IsVectorTest φ)
    (U b : ℝ → SpatialField) (τ : ℝ) :
    projectedCoupling U b (prodTest θ φ) τ =
      θ τ * lerayDivPairing (symTensorColumns (U τ) (b τ)) φ := by
  have e : slice (prodTest θ φ) τ = fun y => θ τ • φ y := rfl
  rw [projectedCoupling, e, lerayDivPairing_smul _ _ hφ]

/-- The coupling `τ ↦ ⟨𝔓div(U_*⊗b_* + b_*⊗U_*)(τ), φ⟩` (literal pairing) is locally
integrable. -/
theorem locallyIntegrable_coupling (hD : IsUnstableBackground D) {φ : Space → Space}
    (hφ : IsVectorTest φ) :
    LocallyIntegrable (fun τ => lerayDivPairing (symTensorColumns (D.Ustar τ) (D.bstar τ)) φ) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨θ, hθ, hθc, hθ1⟩ : ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      ∀ x ∈ Metric.closedBall (0 : ℝ) (max R 0 + 1), θ x = 1 := by
    let bump : ContDiffBump (0 : ℝ) := ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
    exact ⟨bump, bump.contDiff, bump.hasCompactSupport, fun x hx => bump.one_of_mem_closedBall hx⟩
  have hint := hD.2.mode_equation.coupling_integrable (prodTest θ φ)
    (isSimilarityTest_prodTest hθ hθc hφ)
  have e : ∀ τ, projectedCoupling D.Ustar D.bstar (prodTest θ φ) τ =
      θ τ * lerayDivPairing (symTensorColumns (D.Ustar τ) (D.bstar τ)) φ :=
    projectedCoupling_prodTest hφ _ _
  refine (hint.integrableOn (s := K)).congr_fun (fun τ hτ => ?_) hK.measurableSet
  have hb : θ τ = 1 := by
    apply hθ1
    have := hR hτ
    rw [Metric.mem_closedBall] at this ⊢
    linarith [le_max_left R 0]
  rw [e, hb, one_mul]

/-- **The mode equation at a.e. phase** against every vector test, with the literal Leray
pairing of the coupling. -/
theorem ae_mode (hD : IsUnstableBackground D) :
    ∀ᵐ τ, ∀ φ, IsVectorTest φ →
      (D.σ - 1 / 2) * inner ℝ (toL2 (D.bstar τ)) (toL2 φ) +
        inner ℝ (toL2 (D.driftB τ)) (toL2 φ) - D.h * inner ℝ (toL2 (D.lapB τ)) (toL2 φ) +
        lerayDivPairing (symTensorColumns (D.Ustar τ) (D.bstar τ)) φ = 0 := by
  have hT := hD.1.period_pos
  have hg := hD.2.graph
  have hme := hD.2.mode_equation
  have key := ae_forall_tests (Λ := fun τ v =>
      (D.σ - 1 / 2) * inner ℝ (toL2 (D.bstar τ)) v.1 + inner ℝ (toL2 (D.driftB τ)) v.1 -
        D.h * inner ℝ (toL2 (D.lapB τ)) v.1 +
        -∑ j : Fin 3, inner ℝ (toL2 (symTensorColumns (D.Ustar τ) (D.bstar τ) j))
          (Leray.projection (v.2.2 j)))
    (fun τ => by
      refine ((((continuous_const.mul (continuous_const.inner continuous_fst)).add
        (continuous_const.inner continuous_fst)).sub
        (continuous_const.mul (continuous_const.inner continuous_fst))).add ?_)
      refine Continuous.neg (continuous_finsetSum _ (fun j _ => ?_))
      exact continuous_const.inner (Leray.projection.continuous.comp
        ((continuous_apply j).comp continuous_snd.snd)))
    (fun φ hφ => ?_)
  · filter_upwards [key] with τ hτ φ hφ
    exact hτ φ hφ
  · have l1 := Y2.locallyIntegrable_inner hT hg.value (toL2 φ)
    have l2 := Y2.locallyIntegrable_inner hT hg.drift (toL2 φ)
    have l3 := Y2.locallyIntegrable_inner hT hg.laplacian (toL2 φ)
    have l4 := locallyIntegrable_coupling hD hφ
    have hloc : LocallyIntegrable (fun τ => (D.σ - 1 / 2) * inner ℝ (toL2 (D.bstar τ)) (toL2 φ) +
        inner ℝ (toL2 (D.driftB τ)) (toL2 φ) - D.h * inner ℝ (toL2 (D.lapB τ)) (toL2 φ) +
        lerayDivPairing (symTensorColumns (D.Ustar τ) (D.bstar τ)) φ) :=
      (((locallyIntegrable_const_mul l1 _).add l2).sub (locallyIntegrable_const_mul l3 _)).add l4
    show ∀ᵐ τ, (D.σ - 1 / 2) * inner ℝ (toL2 (D.bstar τ)) (toL2 φ) +
        inner ℝ (toL2 (D.driftB τ)) (toL2 φ) - D.h * inner ℝ (toL2 (D.lapB τ)) (toL2 φ) +
        lerayDivPairing (symTensorColumns (D.Ustar τ) (D.bstar τ)) φ = 0
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun θ hθ hθc => ?_)
    have hψt : IsSimilarityTest (prodTest θ φ) := isSimilarityTest_prodTest hθ hθc hφ
    have hid := hme.identity (prodTest θ φ) hψt
    have p1 := hme.value_integrable (prodTest θ φ) hψt
    have p2 := hme.drift_integrable (prodTest θ φ) hψt
    have p3 := hme.laplacian_integrable (prodTest θ φ) hψt
    have e1 : ∀ z, linearModeIntegrand D.h D.σ D.bstar D.lapB D.driftB (prodTest θ φ) z =
        (D.σ - 1 / 2) * pairTerm D.bstar (prodTest θ φ) z + pairTerm D.driftB (prodTest θ φ) z -
          D.h * pairTerm D.lapB (prodTest θ φ) z := fun z => by
      simp only [linearModeIntegrand]
      ring
    simp_rw [e1] at hid
    rw [integral_lin3 p1 p2 p3] at hid
    have q : ∀ f : ℝ → SpatialField, IsY2Div D.period f →
        Integrable (pairTerm f (prodTest θ φ)) → (∫ z, pairTerm f (prodTest θ φ) z) =
          ∫ τ, θ τ * inner ℝ (toL2 (f τ)) (toL2 φ) := fun f hf hi =>
      integral_pair_prod (θ := θ) (L13.isVectorTest_memLp hφ) (Y2.ae_memLp hT hf) hi
    have hc : ∀ τ, projectedCoupling D.Ustar D.bstar (prodTest θ φ) τ =
        θ τ * lerayDivPairing (symTensorColumns (D.Ustar τ) (D.bstar τ)) φ :=
      projectedCoupling_prodTest hφ _ _
    simp_rw [hc] at hid
    rw [q _ hg.value p1, q _ hg.drift p2, q _ hg.laplacian p3] at hid
    have j1 := integrable_test_mul l1 hθ hθc
    have j2 := integrable_test_mul l2 hθ hθc
    have j3 := integrable_test_mul l3 hθ hθc
    have j4 := integrable_test_mul l4 hθ hθc
    have e : ∀ τ, θ τ * ((D.σ - 1 / 2) * inner ℝ (toL2 (D.bstar τ)) (toL2 φ) +
        inner ℝ (toL2 (D.driftB τ)) (toL2 φ) - D.h * inner ℝ (toL2 (D.lapB τ)) (toL2 φ) +
        lerayDivPairing (symTensorColumns (D.Ustar τ) (D.bstar τ)) φ) =
        (D.σ - 1 / 2) * (θ τ * inner ℝ (toL2 (D.bstar τ)) (toL2 φ)) +
          θ τ * inner ℝ (toL2 (D.driftB τ)) (toL2 φ) -
          D.h * (θ τ * inner ℝ (toL2 (D.lapB τ)) (toL2 φ)) +
          θ τ * lerayDivPairing (symTensorColumns (D.Ustar τ) (D.bstar τ)) φ := fun τ => by
      ring
    simp only [smul_eq_mul, e]
    rw [integral_lin4 j1 j2 j3 j4]
    exact hid

end UnforcedLeray.Blueprint.ModeId
