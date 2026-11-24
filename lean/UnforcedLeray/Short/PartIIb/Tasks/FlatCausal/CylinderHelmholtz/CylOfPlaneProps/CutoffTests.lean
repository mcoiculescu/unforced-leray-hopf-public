import UnforcedLeray.Short.PartIIb.Sub.T12_1_5

/-!
# Part II-b, task `PartII-b:T12/1/5/4` (`CylCutoffTests`): planar tests from a cylinder test

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`) and
lines 1727-1731 (the zero-frequency remark). The statement is `CylCutoffTests` of
`Sub/T12_1_5.lean`: for `θ ∈ C_c^∞(ℝ)` and a cylinder test `φ`, the function `θ(q) φ` is a planar
test, and `(θ ∂_ηφ, -(θ' φ + θ ∂_qφ))` is a planar solenoidal test.

Proof. Every component is smooth by the product rule. Each component vanishes outside
`tsupport θ ×ˢ [-M, M]`, where `M` bounds the support of `φ`, `∂_qφ` and `∂_ηφ` in `η`. The
divergence vanishes by symmetry of second derivatives, as in `planarTest_div_free`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The partial derivative `y ↦ ∂_v φ(y)` of a smooth function has Fréchet derivative
`(D²φ(z)).flip v`. -/
theorem cct_hasFDerivAt_partial {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (v z : ℝ × ℝ) :
    HasFDerivAt (fun y => fderiv ℝ φ y v) ((fderiv ℝ (fderiv ℝ φ) z).flip v) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((ContDiff.fderiv_right (m := ∞) hφ (by simp)).differentiable (by simp)) z
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v z)
  simpa using h

/-- Product rule for `y ↦ ψ(y.1) * g y`, where `ψ` is differentiable at `z.1`. -/
theorem cct_hasFDerivAt_theta_mul {ψ : ℝ → ℝ} {g : ℝ × ℝ → ℝ} {g' : ℝ × ℝ →L[ℝ] ℝ}
    {z : ℝ × ℝ} (hψ : DifferentiableAt ℝ ψ z.1) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun y : ℝ × ℝ => ψ y.1 * g y)
      (ψ z.1 • g' + g z • (deriv ψ z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)) z := by
  have hfst : HasFDerivAt (fun y : ℝ × ℝ => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    hasFDerivAt_fst
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => ψ y.1)
      (deriv ψ z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    hψ.hasDerivAt.comp_hasFDerivAt z hfst
  exact h1.mul hg

/-- Directional derivative of `y ↦ ψ(y.1) * g y` in direction `v`. -/
theorem cct_fderiv_theta_mul {ψ : ℝ → ℝ} {g : ℝ × ℝ → ℝ} {g' : ℝ × ℝ →L[ℝ] ℝ} {z : ℝ × ℝ}
    (hψ : DifferentiableAt ℝ ψ z.1) (hg : HasFDerivAt g g' z) (v : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => ψ y.1 * g y) z v =
      ψ z.1 * g' v + g z * (deriv ψ z.1 * v.1) := by
  rw [(cct_hasFDerivAt_theta_mul hψ hg).fderiv]
  simp [ContinuousLinearMap.coe_fst']

/-- A derivative of a function that vanishes near a point outside `tsupport` is zero there. -/
theorem cct_deriv_eq_zero_of_notMem {θ : ℝ → ℝ} {t : ℝ} (ht : t ∉ tsupport θ) :
    deriv θ t = 0 := by
  by_contra h
  have hmem : t ∈ Function.support (deriv θ) := h
  exact ht (support_deriv_subset (f := θ) hmem)

/-- **Leaf `PartII-b:T12/1/5/4`** (SP 1670, 1727-1731): for `θ ∈ C_c^∞(ℝ)` and a cylinder test
`φ`, `θ(q) φ` is a planar test, and `(θ ∂_ηφ, -(θ' φ + θ ∂_qφ))` is a planar solenoidal test. -/
theorem cylCutoffTests : CylCutoffTests := by
  unfold CylCutoffTests
  intro c θ hθ hθc φ hφ
  have hφs : ContDiff ℝ ∞ φ := hφ.smooth
  -- one bound `M` beyond which `φ`, `∂_qφ` and `∂_ηφ` all vanish
  obtain ⟨M, hvan⟩ : ∃ M : ℝ, ∀ z : ℝ × ℝ, M < |z.2| →
      φ z = 0 ∧ fderiv ℝ φ z (1, 0) = 0 ∧ fderiv ℝ φ z (0, 1) = 0 := by
    obtain ⟨L, hL⟩ := hφ.bounded
    obtain ⟨L1, hL1⟩ := cylTest_fderiv_vanish hφ (1, 0)
    obtain ⟨L2, hL2⟩ := cylTest_fderiv_vanish hφ (0, 1)
    exact ⟨max L (max L1 L2), fun z hz =>
      ⟨hL z (lt_of_le_of_lt (le_max_left L (max L1 L2)) hz),
       hL1 z (lt_of_le_of_lt ((le_max_left L1 L2).trans (le_max_right L (max L1 L2))) hz),
       hL2 z (lt_of_le_of_lt ((le_max_right L1 L2).trans (le_max_right L (max L1 L2))) hz)⟩⟩
  have hK : IsCompact (tsupport θ ×ˢ Icc (-M) M) :=
    IsCompact.prod (show IsCompact (tsupport θ) from hθc) isCompact_Icc
  have hθdiff : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hθ' : ContDiff ℝ ∞ (deriv θ) := (contDiff_infty_iff_deriv.1 hθ).2
  have hθ'diff : Differentiable ℝ (deriv θ) := hθ'.differentiable (by simp)
  -- outside `tsupport θ ×ˢ [-M, M]` each product vanishes
  have hzero : ∀ x : ℝ × ℝ, x ∉ tsupport θ ×ˢ Icc (-M) M →
      (θ x.1 = 0 ∧ deriv θ x.1 = 0) ∨
        (φ x = 0 ∧ fderiv ℝ φ x (1, 0) = 0 ∧ fderiv ℝ φ x (0, 1) = 0) := by
    intro x hx
    by_cases h1 : x.1 ∈ tsupport θ
    · right
      have h2 : x.2 ∉ Icc (-M) M := fun h2 => hx (Set.mem_prod.2 ⟨h1, h2⟩)
      exact hvan x (not_le.1 (fun h => h2 (abs_le.1 h)))
    · left
      exact ⟨image_eq_zero_of_notMem_tsupport h1, cct_deriv_eq_zero_of_notMem h1⟩
  -- the planar test `θ φ`
  have hPT1 : PlaneTest (fun z : ℝ × ℝ => θ z.1 * φ z) := by
    refine ⟨(hθ.comp contDiff_fst).mul hφs, HasCompactSupport.intro hK (fun x hx => ?_)⟩
    rcases hzero x hx with ⟨h1, -⟩ | ⟨h1, -⟩
    · simp [h1]
    · simp [h1]
  -- the first component `θ ∂_ηφ` of the solenoidal field
  have hPT2 : PlaneTest (fun z : ℝ × ℝ => θ z.1 * fderiv ℝ φ z (0, 1)) := by
    refine ⟨(hθ.comp contDiff_fst).mul (cylTest_fderiv_contDiff hφ (0, 1)),
      HasCompactSupport.intro hK (fun x hx => ?_)⟩
    rcases hzero x hx with ⟨h1, -⟩ | ⟨-, -, h3⟩
    · simp [h1]
    · simp [h3]
  -- the second component `-(θ' φ + θ ∂_qφ)` of the solenoidal field
  have hPT3 : PlaneTest
      (fun z : ℝ × ℝ => -(deriv θ z.1 * φ z + θ z.1 * fderiv ℝ φ z (1, 0))) := by
    refine ⟨(((hθ'.comp contDiff_fst).mul hφs).add
        ((hθ.comp contDiff_fst).mul (cylTest_fderiv_contDiff hφ (1, 0)))).neg,
      HasCompactSupport.intro hK (fun x hx => ?_)⟩
    rcases hzero x hx with ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · simp [h1, h2]
    · simp [h1, h2]
  -- the derivatives of `θ φ`
  have h2 : ∀ z : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => θ y.1 * φ y) z (1, 0) =
      deriv θ z.1 * φ z + θ z.1 * fderiv ℝ φ z (1, 0) := by
    intro z
    rw [cct_fderiv_theta_mul (hθdiff z.1) (hφs.differentiable (by simp) z).hasFDerivAt]
    simp <;> ring
  have h3 : ∀ z : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => θ y.1 * φ y) z (0, 1) =
      θ z.1 * fderiv ℝ φ z (0, 1) := by
    intro z
    rw [cct_fderiv_theta_mul (hθdiff z.1) (hφs.differentiable (by simp) z).hasFDerivAt]
    simp
  -- the divergence of the solenoidal field vanishes by symmetry of second derivatives
  have hdiv : ∀ z : ℝ × ℝ,
      fderiv ℝ (fun y : ℝ × ℝ => θ y.1 * fderiv ℝ φ y (0, 1)) z (1, 0) +
        fderiv ℝ (fun y : ℝ × ℝ => -(deriv θ y.1 * φ y + θ y.1 * fderiv ℝ φ y (1, 0)))
          z (0, 1) = 0 := by
    intro z
    have hsymm : IsSymmSndFDerivAt ℝ φ z := hφs.contDiffAt.isSymmSndFDerivAt (by simp)
    have hF := cct_hasFDerivAt_partial hφs (0, 1) z
    have hG := cct_hasFDerivAt_partial hφs (1, 0) z
    have hP := cct_hasFDerivAt_theta_mul (ψ := deriv θ) (hθ'diff z.1)
      (hφs.differentiable (by simp) z).hasFDerivAt
    have hQ := cct_hasFDerivAt_theta_mul (ψ := θ) (hθdiff z.1) hG
    have hPQ : HasFDerivAt
        (fun y : ℝ × ℝ => -(deriv θ y.1 * φ y + θ y.1 * fderiv ℝ φ y (1, 0))) _ z :=
      (hP.add hQ).neg
    rw [cct_fderiv_theta_mul (hθdiff z.1) hF (1, 0), hPQ.fderiv]
    have hs := hsymm (0, 1) (1, 0)
    simp [ContinuousLinearMap.coe_fst', ContinuousLinearMap.flip_apply, hs] <;> ring
  refine ⟨hPT1, h2, h3, ⟨fun i => ?_, fun z => ?_⟩⟩
  · fin_cases i
    · exact hPT2
    · exact hPT3
  · exact hdiv z

end UnforcedLeray.Short.IIb
