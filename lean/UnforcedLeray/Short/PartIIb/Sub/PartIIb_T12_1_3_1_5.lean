import UnforcedLeray.Short.PartIIb.Sub.T12_1_3_1

/-!


Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
With `φ_ρ(u) = ∫ ρ(y) φ(u + y) dy` (`testMoll`), the identity
`∫_cell (ρ*D)·∇φ = ∫_cell D·∇φ_ρ` (Fubini + cell shift) and `φ_ρ ∈ CylTest` with
`∇φ_ρ = ρ * ∇φ` give `CylWeakDiv (ρ * D)` from `CylWeakDiv D`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The reflected mollification of a test: `φ_ρ(u) = ∫ ρ(y) φ(u + y) dy`. -/
def testMoll (ρ : ContDiffBump (0 : ℝ × ℝ)) (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun u => ∫ y, ρ.normed volume y * φ (u + y)

/-- **Leaf `T12/1/3/1/5/1`**: `φ_ρ` is again a `CylTest` (smooth by `contDiff_convolution`,
periodic by translation, `η`-support enlarged by `ρ.rOut`). -/
def TestMollIsTest : Prop :=
  ∀ (c : ℝ) (ρ : ContDiffBump (0 : ℝ × ℝ)) (φ : ℝ × ℝ → ℝ), CylTest c φ →
    CylTest c (testMoll ρ φ)

/-- **Leaf `T12/1/3/1/5/2`**: derivative under the integral,
`∂ φ_ρ (u) v = ∫ ρ(y) ∂φ(u + y) v dy` (`HasCompactSupport.hasFDerivAt_convolution_left`). -/
def TestMollDeriv : Prop :=
  ∀ (c : ℝ) (ρ : ContDiffBump (0 : ℝ × ℝ)) (φ : ℝ × ℝ → ℝ), CylTest c φ →
    ∀ (u v : ℝ × ℝ), fderiv ℝ (testMoll ρ φ) u v = ∫ y, ρ.normed volume y * fderiv ℝ φ (u + y) v

/-- **Leaf `T12/1/3/1/5/3`** (Fubini + cell shift, `integral_cell_comp_sub_left`, `cylLocInt`):
`∫_cell (ρ*D)·∇φ = ∫_cell D·(ρ * ∇φ)`. -/
def CylMollSwapDiv : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D →
    ∀ (ρ : ContDiffBump (0 : ℝ × ℝ)) (φ : ℝ × ℝ → ℝ), CylTest c φ →
      ∫ z, (cylMoll ρ D z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + cylMoll ρ D z 1 * (fderiv ℝ φ z (0, 1) : ℂ))
          ∂(UnforcedLeray.Cyl.avgμ c) =
        ∫ u, (D u 0 * ((∫ y, ρ.normed volume y * fderiv ℝ φ (u + y) (1, 0) : ℝ) : ℂ) +
            D u 1 * ((∫ y, ρ.normed volume y * fderiv ℝ φ (u + y) (0, 1) : ℝ) : ℂ))
          ∂(UnforcedLeray.Cyl.avgμ c)

theorem cylMollWeakDiv_of (h1 : TestMollIsTest) (h2 : TestMollDeriv) (h3 : CylMollSwapDiv) :
    CylMollWeakDiv := by
  intro c r hc hr D hD hdiv ρ φ hφ
  have := hdiv (testMoll ρ φ) (h1 c ρ φ hφ)
  rw [h3 c r hc hr D hD ρ φ hφ, ← this]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [h2 c ρ φ hφ u]

end UnforcedLeray.Short.IIb
