import UnforcedLeray.Loc.Hyp.BackgroundStrongForm.Convection

/-!
# H-BgStrong, helpers: from the spacetime equation to the equation at every phase

Support for `Loc/Hyp/BackgroundStrongForm.lean` (target `BackgroundStrongForm`,
`paper/main.tex` lines 159–168; blueprint units B0707, B0708).

The package states `loc:eq:background` against spacetime tests only (`Ustar_equation`,
`SolvesSimilarityBackground`). Here it is tested with products `ψ(τ,y) = θ(τ)φ(y)`
(`prodTest`): by Fubini, the identity becomes `∫ θ'A + θ A_L dτ = -∫ θ⟨N, φ⟩ dτ` with
`A(τ) = ∫⟨U(τ), φ⟩` and `A_L(τ) = ∫⟨U(τ), hΔφ - φ - ½(y·∇)φ⟩`. With `U = H + r` and the
classical equation of the heat profile (`d/dτ ∫⟨H, φ⟩ = ∫⟨H, hΔφ - φ - ½(y·∇)φ⟩`), an
integration by parts in `τ` removes the `H` terms, and what is left is the weak time derivative
of `b(τ) = ⟨r(τ), φ⟩`. Both `b` and the right side are continuous (`r ∈ C(H²)`,
`N ∈ C(L²)`), so the du Bois-Reymond lemma (`BochnerTime.HasWeakDerivTime.hasDerivAt_rep`)
makes `b` differentiable at every phase (`hasDerivAt_of_weak_identity`). The result is
`isSimilarityWeakSolution_of_background`, which is package-free.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.HypBg

open SobolevGraph
open UnforcedLeray.Blueprint.L13 (radialDeriv isVectorTest_radialDeriv IsSimilarityWeakSolution)

/-! ## Vector tests -/

theorem isVectorTest_add {φ ψ : Space → Space} (hφ : IsVectorTest φ) (hψ : IsVectorTest ψ) :
    IsVectorTest (fun y => φ y + ψ y) :=
  ⟨hφ.smooth.add hψ.smooth, hφ.compact.add hψ.compact⟩

theorem isVectorTest_sub {φ ψ : Space → Space} (hφ : IsVectorTest φ) (hψ : IsVectorTest ψ) :
    IsVectorTest (fun y => φ y - ψ y) :=
  ⟨hφ.smooth.sub hψ.smooth, hφ.compact.sub hψ.compact⟩

theorem isVectorTest_smul (c : ℝ) {φ : Space → Space} (hφ : IsVectorTest φ) :
    IsVectorTest (fun y => c • φ y) :=
  ⟨hφ.smooth.const_smul c, (hφ.compact.smul_left (f := fun _ : Space => c))⟩

theorem isVectorTest_testLaplacian {φ : Space → Space} (hφ : IsVectorTest φ) :
    IsVectorTest (testLaplacian φ) := by
  have h : ∀ i, IsVectorTest (testPartial (testPartial φ i) i) := fun i =>
    L14.isVectorTest_testPartial (L14.isVectorTest_testPartial hφ i) i
  have e : testLaplacian φ = fun x => (testPartial (testPartial φ 0) 0 x +
      testPartial (testPartial φ 1) 1 x) + testPartial (testPartial φ 2) 2 x := by
    funext x
    simp [testLaplacian, Fin.sum_univ_three]
  rw [e]
  exact isVectorTest_add (isVectorTest_add (h 0) (h 1)) (h 2)

theorem isVectorTest_adjointTest (h : ℝ) {φ : Space → Space} (hφ : IsVectorTest φ) :
    IsVectorTest (adjointTest h φ) :=
  isVectorTest_sub (isVectorTest_sub (isVectorTest_smul h (isVectorTest_testLaplacian hφ)) hφ)
    (isVectorTest_smul (1 / 2) (isVectorTest_radialDeriv hφ))

/-! ## Pairings with `L²` fields and bounded fields -/

theorem toL2_sub' {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    toL2 (f - g) = toL2 f - toL2 g := by
  rw [toL2_of_memLp (hf.sub hg), toL2_of_memLp hf, toL2_of_memLp hg]
  exact hf.toLp_sub hg

theorem inner_toL2_eq_integral' (F : L2Space) {φ : Space → Space} (hφ : MemLp φ 2 volume) :
    inner ℝ F (toL2 φ) = ∫ x, inner ℝ ((F : SpatialField) x) (φ x) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 hφ] with x hx
  rw [hx]

theorem integrable_inner_L2 (F : L2Space) {φ : Space → Space} (hφ : MemLp φ 2 volume) :
    Integrable (fun x => inner ℝ ((F : SpatialField) x) (φ x)) := by
  refine (MeasureTheory.L2.integrable_inner F (toL2 φ)).congr ?_
  filter_upwards [coeFn_toL2 hφ] with x hx
  rw [hx]

theorem integrable_inner_C0 (V : ZeroAtInftyContinuousMap Space Space) {φ : Space → Space}
    (hφ : IsVectorTest φ) : Integrable (fun x => inner ℝ (V x) (φ x)) := by
  refine (V.continuous.inner hφ.smooth.continuous).integrable_of_hasCompactSupport ?_
  refine hφ.compact.mono' ?_
  intro x hx
  apply subset_tsupport
  intro h0
  apply hx
  simp [h0]

/-! ## Product tests `ψ(τ, y) = θ(τ) φ(y)` -/

/-- The product test `ψ(τ, y) = θ(τ) φ(y)`. -/
def prodTest (θ : ℝ → ℝ) (φ : Space → Space) : SpaceTime → Space := fun z => θ z.1 • φ z.2

variable {θ : ℝ → ℝ} {φ : Space → Space}

theorem isSimilarityTest_prodTest (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hφ : IsVectorTest φ) : IsSimilarityTest (prodTest θ φ) := by
  refine ⟨(hθ.comp contDiff_fst).smul (hφ.smooth.comp contDiff_snd), ?_⟩
  have hsub : tsupport (prodTest θ φ) ⊆ tsupport θ ×ˢ tsupport φ := by
    refine closure_minimal ?_ ((isClosed_tsupport θ).prod (isClosed_tsupport φ))
    intro z hz
    rw [Function.mem_support] at hz
    refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
    · intro h0
      apply hz
      simp [prodTest, h0]
    · intro h0
      apply hz
      simp [prodTest, h0]
  exact IsCompact.of_isClosed_subset (IsCompact.prod hθc hφ.compact) (isClosed_tsupport _) hsub

theorem timeDerivative_prodTest (hθ : ContDiff ℝ ∞ θ) (t : ℝ) (x : Space) :
    timeDerivative (prodTest θ φ) t x = deriv θ t • φ x := by
  have hd : HasDerivAt (fun s => θ s • φ x) (deriv θ t • φ x) t :=
    ((hθ.differentiable (by simp) t).hasDerivAt).smul_const (φ x)
  show deriv (fun s => θ s • φ x) t = _
  exact hd.deriv

theorem spatialDerivative_prodTest (hφ : IsVectorTest φ) (t : ℝ) (x : Space) :
    spatialDerivative (prodTest θ φ) t x = θ t • fderiv ℝ φ x := by
  unfold spatialDerivative prodTest
  exact fderiv_fun_const_smul (hφ.smooth.differentiable (by simp) x) (θ t)

theorem spatialLaplacian_prodTest (hφ : IsVectorTest φ) (t : ℝ) (x : Space) :
    spatialLaplacian (prodTest θ φ) t x = θ t • testLaplacian φ x := by
  unfold spatialLaplacian testLaplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (fun y => spatialDerivative (prodTest θ φ) t y (coordinateVector i)) =
      fun y => θ t • testPartial φ i y := by
    funext y
    rw [spatialDerivative_prodTest hφ]
    rfl
  rw [e, fderiv_fun_const_smul
    ((L14.isVectorTest_testPartial hφ i).smooth.differentiable (by simp) x) (θ t)]
  rfl

theorem linearBackgroundIntegrand_prodTest (hθ : ContDiff ℝ ∞ θ) (hφ : IsVectorTest φ)
    (h : ℝ) (U : ℝ → SpatialField) (z : SpaceTime) :
    linearBackgroundIntegrand h U (prodTest θ φ) z =
      deriv θ z.1 * inner ℝ (U z.1 z.2) (φ z.2) +
        θ z.1 * inner ℝ (U z.1 z.2) (adjointTest h φ z.2) := by
  simp only [linearBackgroundIntegrand, temporalTerm, diffusionTerm, pairTerm, dilationTerm,
    timeDerivative_prodTest hθ, spatialLaplacian_prodTest hφ, spatialDerivative_prodTest hφ,
    adjointTest, radialDeriv, ContinuousLinearMap.smul_apply, inner_smul_right, inner_sub_right]
  simp only [prodTest, inner_smul_right]
  ring

theorem testPartial_smul (c : ℝ) (hφ : IsVectorTest φ) (j : Fin 3) :
    testPartial (fun y => c • φ y) j = c • testPartial φ j := by
  funext y
  unfold testPartial
  rw [fderiv_fun_const_smul (hφ.smooth.differentiable (by simp) y) c]
  rfl

theorem lerayDivPairing_smul (col : Fin 3 → SpatialField) (c : ℝ) (hφ : IsVectorTest φ) :
    lerayDivPairing col (fun y => c • φ y) = c * lerayDivPairing col φ := by
  unfold lerayDivPairing
  have e : ∀ j, toL2 (testPartial (fun y => c • φ y) j) = c • toL2 (testPartial φ j) := by
    intro j
    rw [testPartial_smul c hφ j]
    exact L10.toL2_smul' c (L10.vectorTest_memLp (L14.isVectorTest_testPartial hφ j) 2)
  simp only [e, map_smul, inner_smul_right]
  rw [mul_neg, Finset.mul_sum]

theorem projectedConvection_prodTest (hφ : IsVectorTest φ) {U : ℝ → SpatialField}
    {N : ℝ → L2Space} (hNw : ∀ τ, IsMinusLerayDiv (tensorColumns (U τ) (U τ)) (N τ))
    (t : ℝ) :
    projectedConvection U (prodTest θ φ) t = θ t * -inner ℝ (N t) (toL2 φ) := by
  have e : slice (prodTest θ φ) t = fun y => θ t • φ y := rfl
  rw [projectedConvection, e, lerayDivPairing_smul _ _ hφ, (hNw t).2 φ hφ, neg_neg]

/-! ## Integrals in time against `θ` -/

theorem integrable_cs_mul {θ f : ℝ → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hf : Continuous f) : Integrable (fun t => θ t * f t) :=
  (hθ.mul hf).integrable_of_hasCompactSupport hθc.mul_right

/-- **du Bois-Reymond at every phase.** A continuous `b` whose distributional derivative is a
continuous `g` is differentiable with derivative `g` at every point. -/
theorem hasDerivAt_of_weak_identity {b g : ℝ → ℝ} (hb : Continuous b) (hg : Continuous g)
    (hK : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ∫ t, deriv θ t * b t = -∫ t, θ t * g t)
    (τ : ℝ) : HasDerivAt b (g τ) τ := by
  have hW : BochnerTime.HasWeakDerivTime (τ - 1) (τ + 1) b g := by
    refine ⟨(hb.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self,
      (hg.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self,
      fun θ hθ hθc _ => ?_⟩
    simp only [smul_eq_mul]
    exact hK θ hθ hθc
  have hτ : τ ∈ Ioo (τ - 1) (τ + 1) := ⟨by linarith, by linarith⟩
  have hd := hW.hasDerivAt_rep hg.continuousOn hτ
  have heq := hW.eqOn_rep (by linarith) hb.continuousOn (ae_eq_refl _)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with s hs
  exact heq (Ioo_subset_Icc_self hs)

/-! ## The weak equation of the remainder at every phase -/

/-- `a_ψ(σ) = ∫⟨H(σ), ψ⟩`. -/
def pairH (H : ℝ → SpatialField) (ψ : Space → Space) (σ : ℝ) : ℝ :=
  ∫ y, inner ℝ (H σ y) (ψ y)

/-- `b_ψ(σ) = ⟨r(σ), ψ⟩`. -/
def pairR (r : ℝ → H2) (ψ : Space → Space) (σ : ℝ) : ℝ := inner ℝ (r σ).value (toL2 ψ)

/-- The right side of `IsSimilarityWeakSolution` at the phase `σ`. -/
def rhsFun (h : ℝ) (r : ℝ → H2) (N : ℝ → L2Space) (φ : Space → Space) (σ : ℝ) : ℝ :=
  inner ℝ (h • H2.laplace (r σ) + N σ) (toL2 φ) - inner ℝ (r σ).value (toL2 φ) -
    (1 / 2 : ℝ) * inner ℝ (r σ).value (toL2 (radialDeriv φ))

theorem continuous_pairR {r : ℝ → H2} (hr : Continuous r) (ψ : Space → Space) :
    Continuous (pairR r ψ) :=
  (H2.valueCLM.continuous.comp hr).inner continuous_const

theorem continuous_rhsFun (h : ℝ) {r : ℝ → H2} {N : ℝ → L2Space} (hr : Continuous r)
    (hN : Continuous N) (φ : Space → Space) : Continuous (rhsFun h r N φ) := by
  have hl : Continuous fun σ => H2.laplace (r σ) := H2.laplaceCLM.continuous.comp hr
  have hv : Continuous fun σ => (r σ).value := H2.valueCLM.continuous.comp hr
  have hs : Continuous fun σ => h • H2.laplace (r σ) := hl.const_smul h
  have hsN : Continuous fun σ => h • H2.laplace (r σ) + N σ := hs.add hN
  have h1 : Continuous fun σ => inner ℝ (h • H2.laplace (r σ) + N σ) (toL2 φ) :=
    hsN.inner continuous_const
  have h2 : Continuous fun σ => inner ℝ (r σ).value (toL2 φ) := hv.inner continuous_const
  have h3 : Continuous fun σ => inner ℝ (r σ).value (toL2 (radialDeriv φ)) :=
    hv.inner continuous_const
  exact (h1.sub h2).sub (continuous_const.mul h3)

/-- `rhs = ⟨r, hΔφ - φ - ½(y·∇)φ⟩ + ⟨N, φ⟩`. -/
theorem rhsFun_eq (h : ℝ) (r : ℝ → H2) (N : ℝ → L2Space) {φ : Space → Space}
    (hφ : IsVectorTest φ) (σ : ℝ) :
    rhsFun h r N φ σ = pairR r (adjointTest h φ) σ + inner ℝ (N σ) (toL2 φ) := by
  have hL := L10.vectorTest_memLp (isVectorTest_testLaplacian hφ) 2
  have hR := L10.vectorTest_memLp (isVectorTest_radialDeriv hφ) 2
  have hφ2 := L10.vectorTest_memLp hφ 2
  have e1 : toL2 (adjointTest h φ) = h • toL2 (testLaplacian φ) - toL2 φ -
      (1 / 2 : ℝ) • toL2 (radialDeriv φ) := by
    rw [show adjointTest h φ = (h • testLaplacian φ - φ) - (1 / 2 : ℝ) • radialDeriv φ
      from rfl, toL2_sub' ((hL.const_smul h).sub hφ2) (hR.const_smul _),
      toL2_sub' (hL.const_smul h) hφ2, L10.toL2_smul' _ hL, L10.toL2_smul' _ hR]
  have hlap := L14.inner_laplace_toL2 (r σ) hφ
  have e2 : toL2 (fun x => ∑ i : Fin 3, testPartial (testPartial φ i) i x) =
      toL2 (testLaplacian φ) := rfl
  rw [e2] at hlap
  rw [rhsFun, pairR, e1, inner_add_left, real_inner_smul_left, hlap, inner_sub_right,
    inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  ring

section Split

variable {U H : ℝ → SpatialField} {r : ℝ → H2} {V : ℝ → ZeroAtInftyContinuousMap Space Space}

theorem integrable_pairH (hV : ∀ τ, (V τ : SpatialField) =ᵐ[volume] H τ) {ψ : Space → Space}
    (hψ : IsVectorTest ψ) (σ : ℝ) : Integrable (fun y => inner ℝ (H σ y) (ψ y)) := by
  refine (integrable_inner_C0 (V σ) hψ).congr ?_
  filter_upwards [hV σ] with y hy
  rw [hy]

theorem integrable_pairU (hdec : ∀ τ, U τ =ᵐ[volume] fun y => H τ y + ((r τ).value : SpatialField) y)
    (hV : ∀ τ, (V τ : SpatialField) =ᵐ[volume] H τ) {ψ : Space → Space}
    (hψ : IsVectorTest ψ) (σ : ℝ) : Integrable (fun y => inner ℝ (U σ y) (ψ y)) := by
  refine ((integrable_pairH hV hψ σ).add
    (integrable_inner_L2 (r σ).value (L10.vectorTest_memLp hψ 2))).congr ?_
  filter_upwards [hdec σ] with y hy
  rw [hy, inner_add_left]
  rfl

theorem integral_pairU (hdec : ∀ τ, U τ =ᵐ[volume] fun y => H τ y + ((r τ).value : SpatialField) y)
    (hV : ∀ τ, (V τ : SpatialField) =ᵐ[volume] H τ) {ψ : Space → Space}
    (hψ : IsVectorTest ψ) (σ : ℝ) :
    ∫ y, inner ℝ (U σ y) (ψ y) = pairH H ψ σ + pairR r ψ σ := by
  have hcongr : (fun y => inner ℝ (U σ y) (ψ y)) =ᵐ[volume]
      fun y => inner ℝ (H σ y) (ψ y) + inner ℝ (((r σ).value : SpatialField) y) (ψ y) := by
    filter_upwards [hdec σ] with y hy
    rw [hy, inner_add_left]
  rw [integral_congr_ae hcongr, integral_add (integrable_pairH hV hψ σ)
      (integrable_inner_L2 (r σ).value (L10.vectorTest_memLp hψ 2)), pairH, pairR,
    inner_toL2_eq_integral' _ (L10.vectorTest_memLp hψ 2)]

/-- The linear part of the background identity for a product test, by Fubini. -/
theorem integral_linear_prodTest {h : ℝ} (hU : SolvesSimilarityBackground h U)
    (hdec : ∀ τ, U τ =ᵐ[volume] fun y => H τ y + ((r τ).value : SpatialField) y)
    (hV : ∀ τ, (V τ : SpatialField) =ᵐ[volume] H τ) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) {φ : Space → Space} (hφ : IsVectorTest φ) :
    (∫ z, linearBackgroundIntegrand h U (prodTest θ φ) z) =
      ∫ t, (deriv θ t * (pairH H φ t + pairR r φ t) +
        θ t * (pairH H (adjointTest h φ) t + pairR r (adjointTest h φ) t)) := by
  have hψ := isSimilarityTest_prodTest hθ hθc hφ
  have hφL := isVectorTest_adjointTest h hφ
  have hLint : Integrable (linearBackgroundIntegrand h U (prodTest θ φ)) :=
    (((hU.temporal_integrable _ hψ).add ((hU.diffusion_integrable _ hψ).const_mul h)).sub
      (hU.pair_integrable _ hψ)).sub ((hU.dilation_integrable _ hψ).const_mul (1 / 2))
  rw [Measure.volume_eq_prod, integral_prod _ hLint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [linearBackgroundIntegrand_prodTest hθ hφ]
  rw [integral_add ((integrable_pairU hdec hV hφ t).const_mul _)
      ((integrable_pairU hdec hV hφL t).const_mul _), integral_const_mul,
    integral_const_mul, integral_pairU hdec hV hφ t, integral_pairU hdec hV hφL t]

end Split

/-- **The identity against `θ`.** -/
theorem weak_identity_of_background {h : ℝ} {U H : ℝ → SpatialField} {r : ℝ → H2}
    {N : ℝ → L2Space} {V : ℝ → ZeroAtInftyContinuousMap Space Space}
    (hU : SolvesSimilarityBackground h U)
    (hdec : ∀ τ, U τ =ᵐ[volume] fun y => H τ y + ((r τ).value : SpatialField) y)
    (hV : ∀ τ, (V τ : SpatialField) =ᵐ[volume] H τ)
    (hHeq : ∀ φ : Space → Space, IsVectorTest φ → ∀ τ : ℝ,
      HasDerivAt (pairH H φ) (pairH H (adjointTest h φ) τ) τ)
    (hr : Continuous r) (hN : Continuous N)
    (hNw : ∀ τ, IsMinusLerayDiv (tensorColumns (U τ) (U τ)) (N τ))
    {φ : Space → Space} (hφ : IsVectorTest φ) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) :
    ∫ t, deriv θ t * pairR r φ t = -∫ t, θ t * rhsFun h r N φ t := by
  have hφL := isVectorTest_adjointTest h hφ
  have hψ := isSimilarityTest_prodTest hθ hθc hφ
  have hθ' : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
  have hθ'c : HasCompactSupport (deriv θ) := hθc.deriv
  have hacont : ∀ ψ, IsVectorTest ψ → Continuous (pairH H ψ) := fun ψ hψ =>
    continuous_iff_continuousAt.mpr fun σ => (hHeq ψ hψ σ).continuousAt
  have hid := hU.identity _ hψ
  have hconv : (∫ t, projectedConvection U (prodTest θ φ) t) =
      ∫ t, θ t * -inner ℝ (N t) (toL2 φ) :=
    integral_congr_ae (Eventually.of_forall fun t => projectedConvection_prodTest hφ hNw t)
  rw [integral_linear_prodTest hU hdec hV hθ hθc hφ, hconv] at hid
  have hibp : ∫ t, θ t * pairH H (adjointTest h φ) t = -∫ t, deriv θ t * pairH H φ t :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun t _ => (hθ.differentiable (by simp) t).hasDerivAt)
      (fun t _ => hHeq φ hφ t)
      (integrable_cs_mul hθ.continuous hθc (hacont _ hφL))
      (integrable_cs_mul hθ' hθ'c (hacont φ hφ))
      (integrable_cs_mul hθ.continuous hθc (hacont φ hφ))
  have iA := integrable_cs_mul hθ' hθ'c (hacont φ hφ)
  have iB := integrable_cs_mul hθ' hθ'c (continuous_pairR hr φ)
  have iC := integrable_cs_mul hθ.continuous hθc (hacont _ hφL)
  have iD := integrable_cs_mul hθ.continuous hθc (continuous_pairR hr (adjointTest h φ))
  have iN := integrable_cs_mul hθ.continuous hθc
    ((hN.inner continuous_const : Continuous fun t => inner ℝ (N t) (toL2 φ)))
  have hsplit : ∫ t, (deriv θ t * (pairH H φ t + pairR r φ t) +
      θ t * (pairH H (adjointTest h φ) t + pairR r (adjointTest h φ) t)) =
      (∫ t, deriv θ t * pairH H φ t) + (∫ t, deriv θ t * pairR r φ t) +
        (∫ t, θ t * pairH H (adjointTest h φ) t) + ∫ t, θ t * pairR r (adjointTest h φ) t := by
    have e : (fun t => deriv θ t * (pairH H φ t + pairR r φ t) +
        θ t * (pairH H (adjointTest h φ) t + pairR r (adjointTest h φ) t)) =
        fun t => ((deriv θ t * pairH H φ t + deriv θ t * pairR r φ t) +
          θ t * pairH H (adjointTest h φ) t) + θ t * pairR r (adjointTest h φ) t := by
      funext t
      ring
    have iAB : Integrable (fun t => deriv θ t * pairH H φ t + deriv θ t * pairR r φ t) :=
      iA.add iB
    have iABC : Integrable (fun t => deriv θ t * pairH H φ t + deriv θ t * pairR r φ t +
        θ t * pairH H (adjointTest h φ) t) := iAB.add iC
    rw [e, integral_add iABC iD, integral_add iAB iC, integral_add iA iB]
  have hgint : ∫ t, θ t * rhsFun h r N φ t =
      (∫ t, θ t * pairR r (adjointTest h φ) t) + ∫ t, θ t * inner ℝ (N t) (toL2 φ) := by
    have e : (fun t => θ t * rhsFun h r N φ t) =
        fun t => θ t * pairR r (adjointTest h φ) t + θ t * inner ℝ (N t) (toL2 φ) := by
      funext t
      rw [rhsFun_eq h r N hφ t]
      ring
    rw [e, integral_add iD iN]
  have hNneg : ∫ t, θ t * -inner ℝ (N t) (toL2 φ) = -∫ t, θ t * inner ℝ (N t) (toL2 φ) := by
    rw [← integral_neg]
    congr 1
    funext t
    ring
  rw [hsplit, hibp, hNneg] at hid
  rw [hgint]
  linarith

/-- **The background equation at every phase** (lines 159–168). Let `U` solve
`loc:eq:background` in spacetime distributions with `-𝔓div(U ⊗ U) = N`, `N ∈ C(ℝ; L²)`,
and `U = H + r` with `r ∈ C(ℝ; H²)` and `H` a bounded (`C₀` representative `V`) solution of
`∂_τH = hΔH + ½y·∇H + ½H` weakly at every phase. Then `r` solves
`∂_τr = hΔr + ½r + ½y·∇r + N` weakly in space at every phase. -/
theorem isSimilarityWeakSolution_of_background {h : ℝ} {U H : ℝ → SpatialField} {r : ℝ → H2}
    {N : ℝ → L2Space} {V : ℝ → ZeroAtInftyContinuousMap Space Space}
    (hU : SolvesSimilarityBackground h U)
    (hdec : ∀ τ, U τ =ᵐ[volume] fun y => H τ y + ((r τ).value : SpatialField) y)
    (hV : ∀ τ, (V τ : SpatialField) =ᵐ[volume] H τ)
    (hHeq : ∀ φ : Space → Space, IsVectorTest φ → ∀ τ : ℝ,
      HasDerivAt (fun σ => ∫ y, inner ℝ (H σ y) (φ y))
        (∫ y, inner ℝ (H τ y) (adjointTest h φ y)) τ)
    (hr : Continuous r) (hN : Continuous N)
    (hNw : ∀ τ, IsMinusLerayDiv (tensorColumns (U τ) (U τ)) (N τ)) :
    IsSimilarityWeakSolution h univ r N := by
  intro φ hφ τ _
  exact hasDerivAt_of_weak_identity (continuous_pairR hr φ) (continuous_rhsFun h hr hN φ)
    (fun θ hθ hθc => weak_identity_of_background hU hdec hV hHeq hr hN hNw hφ hθ hθc) τ

end UnforcedLeray.Blueprint.HypBg
