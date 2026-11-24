import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5

/-!
# Steps of `HardyApprox`: mollification, radial cutoff, diagonal choice

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480 (as cited
by the parent task; the Hardy inequality in `ℝ³` with `C_c^∞` density).  `HardyApprox` is
obtained in three steps:

* `MollifyApprox`: smooth `L⁶` fields `v n` with `L²` partial derivatives, `v n → u` in `L⁶`,
  `∂ⱼ v n → Dⱼ` in `L²` (convolution with an approximate identity; weak gradient commutes
  with convolution);
* `CutoffApprox`: a smooth `L⁶` field with `L²` gradient is the limit, in the same norms, of
  `C_c^∞` fields (radial cutoff `χ(y/n)`, the gradient error is `‖v ∇χₙ‖₂ ≤ C ‖v‖_{L⁶(n<|y|<2n)}`
  by Hölder on annuli);
* a diagonal choice with a.e. convergence from fast `L⁶` convergence (`AeOfFastLp`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Convolution `ρ ⋆ f` of a vector field with a real kernel. -/
def mollify (ρ : Space → ℝ) (f : Space → CVec3) (x : Space) : CVec3 :=
  ∫ z : Space, ρ z • f (x - z)

/-- Partial derivative `∂ⱼ v` of a field in the Cartesian direction `j`. -/
def pdir (j : Fin 3) (v : Space → CVec3) (y : Space) : CVec3 :=
  fderiv ℝ v y (EuclideanSpace.single j (1 : ℝ))

/-- Weak derivative relation `∂ⱼ u = D` against `C_c^∞` test functions. -/
def WeakDeriv (j : Fin 3) (u D : Space → CVec3) : Prop :=
  ∀ φ : Space → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ y : Space, (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) • u y
      = -∫ y : Space, φ y • D y

/-- A mollifier family: smooth, compactly supported, nonnegative, mass one, support in the ball of
radius `1/(n+1)`. -/
def IsMollifierFamily (ρ : ℕ → Space → ℝ) : Prop :=
  ∀ n, ContDiff ℝ ∞ (ρ n) ∧ HasCompactSupport (ρ n) ∧ (∀ z, 0 ≤ ρ n z) ∧
    ∫ z : Space, ρ n z = 1 ∧ ∀ z, ρ n z ≠ 0 → ‖z‖ ≤ 1 / ((n : ℝ) + 1)

/-- Mollifier families exist. -/
def MollifierFamilyExists : Prop := ∃ ρ : ℕ → Space → ℝ, IsMollifierFamily ρ

/-- Convolution of `u ∈ L⁶` with weak derivative `D` by a `C_c^∞` kernel is smooth and its
derivatives are the convolutions of `D` (weak gradient commutes with convolution). -/
def MollifySmooth : Prop :=
  ∀ (ρ : Space → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
    ∀ (u : Space → CVec3) (D : Fin 3 → Space → CVec3),
      MemLp u 6 volume → (∀ j, MemLp (D j) 2 volume) → (∀ j, WeakDeriv j u (D j)) →
      ContDiff ℝ ∞ (mollify ρ u) ∧ ∀ j, pdir j (mollify ρ u) = mollify ρ (D j)

/-- Convolution with a mollifier family keeps `L^p` and converges in `L^p`, `1 ≤ p < ∞`. -/
def MollifyLp : Prop :=
  ∀ (ρ : ℕ → Space → ℝ), IsMollifierFamily ρ → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
    ∀ f : Space → CVec3, MemLp f p volume →
      (∀ n, MemLp (mollify (ρ n) f) p volume) ∧
      Tendsto (fun n => eLpNorm (mollify (ρ n) f - f) p volume) atTop (𝓝 0)

/-- Mollification approximation (step 1). -/
def MollifyApprox : Prop :=
  ∀ (u : Space → CVec3) (D : Fin 3 → Space → CVec3),
    MemLp u 6 volume → (∀ j, MemLp (D j) 2 volume) → (∀ j, WeakDeriv j u (D j)) →
    ∃ v : ℕ → Space → CVec3, (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, MemLp (v n) 6 volume) ∧
      (∀ n j, MemLp (pdir j (v n)) 2 volume) ∧
      Tendsto (fun n => eLpNorm (v n - u) 6 volume) atTop (𝓝 0) ∧
      ∀ j, Tendsto (fun n => eLpNorm (pdir j (v n) - D j) 2 volume) atTop (𝓝 0)

/-- Cutoff family `χₙ(y) = χ(y/(n+1))`: smooth, equal to `1` on the ball of radius `n+1`,
supported in the ball of radius `2(n+1)`, with `|∇χₙ| ≤ C/(n+1)` (and `∇χₙ = 0` off the annulus). -/
def CutoffFamilyExists : Prop :=
  ∃ (C : ℝ) (χ : ℕ → Space → ℝ), ∀ n, ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n) ∧
    (∀ y, 0 ≤ χ n y ∧ χ n y ≤ 1) ∧ (∀ y, ‖y‖ ≤ (n : ℝ) + 1 → χ n y = 1) ∧
    (∀ y, ‖y‖ ≥ 2 * ((n : ℝ) + 1) → χ n y = 0) ∧
    ∀ y, ‖fderiv ℝ (χ n) y‖ ≤ C / ((n : ℝ) + 1)

/-- Hölder on annuli: for `v ∈ L⁶` the cutoff error `‖v ∇χₙ‖₂ ≤ C ‖v‖_{L⁶(|y|>n)} → 0`. -/
def CutoffHolder : Prop :=
  ∀ (C : ℝ) (χ : ℕ → Space → ℝ),
    (∀ n, ContDiff ℝ ∞ (χ n)) →
    (∀ (n : ℕ) (y : Space), ‖y‖ < (n : ℝ) + 1 → fderiv ℝ (χ n) y = 0) →
    (∀ (n : ℕ) (y : Space), ‖y‖ > 2 * ((n : ℝ) + 1) → fderiv ℝ (χ n) y = 0) →
    (∀ (n : ℕ) (y : Space), ‖fderiv ℝ (χ n) y‖ ≤ C / ((n : ℝ) + 1)) →
    ∀ v : Space → CVec3, MemLp v 6 volume → ∀ j : Fin 3,
      Tendsto (fun n => eLpNorm (fun y => (fderiv ℝ (χ n) y (EuclideanSpace.single j (1 : ℝ))) • v y)
        2 volume) atTop (𝓝 0)

/-- Radial cutoff approximation (step 2). -/
def CutoffApprox : Prop :=
  ∀ v : Space → CVec3, ContDiff ℝ ∞ v → MemLp v 6 volume → (∀ j, MemLp (pdir j v) 2 volume) →
    ∃ φ : ℕ → Space → CVec3, (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n)) ∧
      Tendsto (fun n => eLpNorm (φ n - v) 6 volume) atTop (𝓝 0) ∧
      ∀ j, Tendsto (fun n => eLpNorm (pdir j (φ n) - pdir j v) 2 volume) atTop (𝓝 0)

/-- Fast `L⁶` convergence gives a.e. convergence (Borel–Cantelli / `exists_seq_tendsto_ae`). -/
def AeOfFastLp : Prop :=
  ∀ (f : ℕ → Space → CVec3) (u : Space → CVec3), (∀ n, AEStronglyMeasurable (f n) volume) → AEStronglyMeasurable u volume →
    (∀ n, eLpNorm (f n - u) 6 volume ≤ (1 / 2 : ℝ≥0∞) ^ n) →
    ∀ᵐ y : Space, Tendsto (fun n => f n y) atTop (𝓝 (u y))

end UnforcedLeray.Short.PartIIIb.Concrete
