import UnforcedLeray.Short.PartIIb.Sub.T12_1_1

/-!
# The planar Riesz family: concrete definitions and the exact statements of its leaves

Design file for `PartII-b:T12/1/1/2` (`PlaneRieszFamilyExists`).  Source of record:
`the November 2 reference manuscript`, line 1670 (`P_0`, the ordinary planar
cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); Grafakos, *Classical
Fourier Analysis*, Cor. 5.2.8.

Everything is on the plane `Pl = Fin 2 → ℝ` (norm `‖x‖` = sup norm; the Euclidean quantity is
`x 0 ^ 2 + x 1 ^ 2`).  The planar Newton kernel is `N(x) = (2π)⁻¹ log |x| = (4π)⁻¹ log (x₀² + x₁²)`,
so `ΔN = δ`.  The test-level Riesz pair is `S_{ik} f = ∂_i ∂_k (N * f)` and the operator on
`PlaneL2` is its `L²`-extension (`ExtendsRieszTest`).

Every leaf of the family is stated below as a `Prop` definition, so that the statements are
type-checked once, here; the leaf files prove `theorem name : <Prop>`.  This file contains no
proofs and no `sorry`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The plane. -/
abbrev Pl : Type := Fin 2 → ℝ

/-- A test function: `C^∞` with compact support. -/
def IsTest (f : Pl → ℝ) : Prop := ContDiff ℝ ∞ f ∧ HasCompactSupport f

/-- The partial derivative `∂_k g`. -/
def pd (k : Fin 2) (g : Pl → ℝ) : Pl → ℝ := fun x => fderiv ℝ g x (Pi.single k 1)

/-- The divergence `Σ_i ∂_i F_i`. -/
def divTest (F : Fin 2 → Pl → ℝ) : Pl → ℝ := fun x => ∑ i, pd i (F i) x

/-- The planar Newton kernel `N(x) = (2π)⁻¹ log |x| = (4π)⁻¹ log (x₀² + x₁²)`. -/
def newtonKernel (x : Pl) : ℝ := (4 * Real.pi)⁻¹ * Real.log (x 0 ^ 2 + x 1 ^ 2)

/-- The gradient kernel `∂_k N(x) = (2π)⁻¹ x_k / |x|²` (value `0` at `0`). -/
def newtonGradKernel (k : Fin 2) (x : Pl) : ℝ := (2 * Real.pi)⁻¹ * x k / (x 0 ^ 2 + x 1 ^ 2)

/-- The Newton potential `(N * f)(x) = ∫ N(x - y) f(y) dy`. -/
def newtonConv (f : Pl → ℝ) (x : Pl) : ℝ := ∫ y, newtonKernel (x - y) * f y

/-- The test-level Riesz pair `S_{ik} f = ∂_i ∂_k (N * f)`. -/
def rieszTest (i k : Fin 2) (f : Pl → ℝ) : Pl → ℝ := pd i (pd k (newtonConv f))

/-- `T` is the `L²` extension of the test-level Riesz pair `S_{ik}`. -/
def ExtendsRieszTest (T : PlaneL2 →L[ℝ] PlaneL2) (i k : Fin 2) : Prop :=
  ∀ f : Pl → ℝ, IsTest f → ∀ (h1 : MemLp f 2 volume) (h2 : MemLp (rieszTest i k f) 2 volume),
    T (h1.toLp f) = h2.toLp _

/-! ## Group A: the planar Newton potential of a test (port of `Lib/CZL2/NewtonConv.lean`) -/

/-- `∂_k` of a test is a test. -/
def PdTest : Prop := ∀ (k : Fin 2) (f : Pl → ℝ), IsTest f → IsTest (pd k f)

/-- `log |x|` is locally integrable on the plane. -/
def NewtonKernelLocInt : Prop := LocallyIntegrable newtonKernel volume

/-- `x_k / |x|²` is locally integrable on the plane. -/
def NewtonGradKernelLocInt : Prop := ∀ k : Fin 2, LocallyIntegrable (newtonGradKernel k) volume

/-- Weak derivative of the Newton kernel: `∫ N ∂_kψ = -∫ ∂_kN ψ` for a test `ψ`. -/
def NewtonKernelWeakDeriv : Prop :=
  ∀ (k : Fin 2) (ψ : Pl → ℝ), IsTest ψ →
    ∫ y, newtonKernel y * pd k ψ y = -∫ y, newtonGradKernel k y * ψ y

/-- `∫ ∇N · ∇φ = -φ(0)` for a test `φ` (polar coordinates). -/
def NewtonGradKernelPolar : Prop :=
  ∀ φ : Pl → ℝ, IsTest φ →
    ∫ y, (newtonGradKernel 0 y * pd 0 φ y + newtonGradKernel 1 y * pd 1 φ y) = -φ 0

/-- Fundamental solution: `∫ N(y) Δφ(y) dy = φ(0)` for a test `φ`. -/
def NewtonKernelLaplace : Prop :=
  ∀ φ : Pl → ℝ, IsTest φ → ∫ y, newtonKernel y * (pd 0 (pd 0 φ) y + pd 1 (pd 1 φ) y) = φ 0

/-- `N * f` is `C^∞` for a test `f`. -/
def NewtonConvContDiff : Prop := ∀ f : Pl → ℝ, IsTest f → ContDiff ℝ ∞ (newtonConv f)

/-- `∂_k (N * f) = N * ∂_k f` for a test `f`. -/
def NewtonConvPd : Prop :=
  ∀ (k : Fin 2) (f : Pl → ℝ), IsTest f → pd k (newtonConv f) = newtonConv (pd k f)

/-- `Δ (N * f) = f` for a test `f`. -/
def NewtonConvLaplace : Prop :=
  ∀ f : Pl → ℝ, IsTest f → ∀ x, pd 0 (pd 0 (newtonConv f)) x + pd 1 (pd 1 (newtonConv f)) x = f x

/-- Linearity of `f ↦ N * f` on tests. -/
def NewtonConvLinear : Prop :=
  ∀ f g : Pl → ℝ, IsTest f → IsTest g → ∀ c : ℝ,
    newtonConv (f + g) = newtonConv f + newtonConv g ∧ newtonConv (c • f) = c • newtonConv f

/-- `∂_k (N * f)(x) = ∫ ∂_kN(x - y) f(y) dy` for a test `f`. -/
def NewtonConvGradKernel : Prop :=
  ∀ (k : Fin 2) (f : Pl → ℝ), IsTest f → ∀ x, pd k (newtonConv f) x = ∫ y, newtonGradKernel k (x - y) * f y

/-- `∇(N * f) = O(1/|x|)` at infinity. -/
def NewtonConvGradDecay : Prop :=
  ∀ (k : Fin 2) (f : Pl → ℝ), IsTest f → ∃ C R : ℝ, ∀ x : Pl, R ≤ ‖x‖ →
    |pd k (newtonConv f) x| ≤ C * ‖x‖⁻¹

/-! ## Group B: the Hessian and its kernel (port of `HessianKernel`, `TestOffSupport`) -/

/-- `S_{ik} f = ∂_i (N * ∂_k f)` for a test `f`. -/
def RieszTestEqConvPd : Prop :=
  ∀ (i k : Fin 2) (f : Pl → ℝ), IsTest f → rieszTest i k f = pd i (newtonConv (pd k f))

/-- `S_{ik} f = S_{ki} f` for a test `f`. -/
def RieszTestComm : Prop :=
  ∀ (i k : Fin 2) (f : Pl → ℝ), IsTest f → rieszTest i k f = rieszTest k i f

/-- `S_{ik} f` is `C^∞` for a test `f`. -/
def RieszTestContDiff : Prop :=
  ∀ (i k : Fin 2) (f : Pl → ℝ), IsTest f → ContDiff ℝ ∞ (rieszTest i k f)

/-- Linearity of `f ↦ S_{ik} f` on tests. -/
def RieszTestLinear : Prop :=
  ∀ (i k : Fin 2) (f g : Pl → ℝ), IsTest f → IsTest g → ∀ c : ℝ,
    rieszTest i k (f + g) = rieszTest i k f + rieszTest i k g ∧
      rieszTest i k (c • f) = c • rieszTest i k f

/-- `∂_i` of the gradient kernel is the Riesz kernel off the origin. -/
def PlaneRieszKernelEq : Prop :=
  ∀ (i k : Fin 2) (z : Pl), z ≠ 0 →
    fderiv ℝ (newtonGradKernel k) z (Pi.single i 1) = planeRieszKernel i k z

/-- Pointwise kernel bound away from the origin: `|K_{ik}(z)| ≤ δ⁻²` when `δ ≤ ‖z‖`. -/
def PlaneRieszKernelBound : Prop :=
  ∀ (i k : Fin 2) (δ : ℝ) (z : Pl), 0 < δ → δ ≤ ‖z‖ → |planeRieszKernel i k z| ≤ (δ ^ 2)⁻¹

/-- The kernel `K_{ik}` is measurable. -/
def PlaneRieszKernelMeasurable : Prop := ∀ i k : Fin 2, Measurable (planeRieszKernel i k)

/-- `x ↦ ∫ K_{ik}(x - y) φ(y) dy` is strongly measurable. -/
def KernelIntegralMeasurable : Prop :=
  ∀ (i k : Fin 2) (φ : Pl → ℝ), StronglyMeasurable φ →
    StronglyMeasurable (fun x => ∫ y, planeRieszKernel i k (x - y) * φ y)

/-- Bound for `∫ K_{ik}(x - y) φ(y) dy` when `φ` is supported at distance `≥ δ` from `x`. -/
def KernelIntegralBound : Prop :=
  ∀ (i k : Fin 2) (φ : Pl → ℝ) (δ : ℝ) (x : Pl), Integrable φ volume → 0 < δ →
    (∀ y, φ y ≠ 0 → δ ≤ ‖x - y‖) →
    ‖∫ y, planeRieszKernel i k (x - y) * φ y‖ ≤ (δ ^ 2)⁻¹ * ∫ y, |φ y|

/-- Kernel representation of `S_{ik} f` off the support of a test `f`. -/
def RieszTestOffSupport : Prop :=
  ∀ (i k : Fin 2) (f : Pl → ℝ), IsTest f → ∀ x : Pl, x ∉ tsupport f →
    rieszTest i k f x = ∫ y, planeRieszKernel i k (x - y) * f y

/-- `S_{ik} f = O(|x|⁻²)` at infinity. -/
def RieszTestDecay : Prop :=
  ∀ (i k : Fin 2) (f : Pl → ℝ), IsTest f → ∃ C R : ℝ, ∀ x : Pl, R ≤ ‖x‖ →
    |rieszTest i k f x| ≤ C * ‖x‖ ^ (-2 : ℝ)

/-- `S_{ik} f ∈ L²` for a test `f`. -/
def RieszTestMemLp : Prop :=
  ∀ (i k : Fin 2) (f : Pl → ℝ), IsTest f → MemLp (rieszTest i k f) 2 volume

/-! ## Group C: the integral identities on tests (port of `RieszL2`, `PressureIdentity`) -/

/-- A family of smooth cutoffs `χ_R`: `1` on `‖x‖ ≤ R`, `0` on `‖x‖ ≥ 2R`, `|∇χ_R| ≤ M / R`. -/
def IsCutoffFamily (χ : ℝ → Pl → ℝ) : Prop :=
  (∀ R, 1 ≤ R → ContDiff ℝ ∞ (χ R) ∧ HasCompactSupport (χ R)) ∧
    (∀ R x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧ (∀ R x, 1 ≤ R → ‖x‖ ≤ R → χ R x = 1) ∧
    (∀ R x, 1 ≤ R → 2 * R ≤ ‖x‖ → χ R x = 0) ∧
    ∃ M : ℝ, ∀ R x, 1 ≤ R → ‖fderiv ℝ (χ R) x‖ ≤ M / R

/-- Such cutoffs exist. -/
def PlaneCutoffExists : Prop := ∃ χ : ℝ → Pl → ℝ, IsCutoffFamily χ

/-- Integration by parts against a cutoff: for smooth `ψ` and a test `χ`,
`Σ_i ∫ χ (∂_iψ)² = -∫ χ ψ Δψ - Σ_i ∫ ψ ∂_iχ ∂_iψ`. -/
def CutoffIBP : Prop :=
  ∀ ψ χ : Pl → ℝ, ContDiff ℝ ∞ ψ → IsTest χ →
    ∑ i, ∫ x, χ x * (pd i ψ x) ^ 2 =
      -(∫ x, χ x * ψ x * (pd 0 (pd 0 ψ) x + pd 1 (pd 1 ψ) x)) -
        ∑ i, ∫ x, ψ x * pd i χ x * pd i ψ x

/-- The cutoff boundary term vanishes when `ψ = O(1/|x|)`, `∇ψ = O(|x|⁻²)`. -/
def BoundaryTermTendsto : Prop :=
  ∀ χ : ℝ → Pl → ℝ, IsCutoffFamily χ → ∀ ψ : Pl → ℝ, ContDiff ℝ ∞ ψ →
    (∃ C R0 : ℝ, ∀ x : Pl, R0 ≤ ‖x‖ →
      |ψ x| ≤ C * ‖x‖⁻¹ ∧ ∀ i, |pd i ψ x| ≤ C * ‖x‖ ^ (-2 : ℝ)) →
    ∀ i, Tendsto (fun R : ℝ => ∫ x, ψ x * pd i (χ R) x * pd i ψ x) atTop (𝓝 0)

/-- Dominated convergence for the cutoffs: `∫ χ_R g → ∫ g` for integrable `g`. -/
def DominatedCutoffLimit : Prop :=
  ∀ χ : ℝ → Pl → ℝ, IsCutoffFamily χ → ∀ g : Pl → ℝ, Integrable g volume →
    Tendsto (fun R : ℝ => ∫ x, χ R x * g x) atTop (𝓝 (∫ x, g x))

/-- The divergence of a test field is a test. -/
def DivTestIsTest : Prop :=
  ∀ F : Fin 2 → Pl → ℝ, (∀ k, IsTest (F k)) → IsTest (divTest F)

/-- `ψ = N * div F = O(1/|x|)` for a test field `F` (`∫ div F = 0`). -/
def PsiDecay : Prop :=
  ∀ F : Fin 2 → Pl → ℝ, (∀ k, IsTest (F k)) →
    ∃ C R : ℝ, ∀ x : Pl, R ≤ ‖x‖ → |newtonConv (divTest F) x| ≤ C * ‖x‖⁻¹

/-- `∂_i (N * div F) = Σ_k S_{ik} F_k`. -/
def PsiGrad : Prop :=
  ∀ F : Fin 2 → Pl → ℝ, (∀ k, IsTest (F k)) → ∀ i : Fin 2,
    pd i (newtonConv (divTest F)) = fun x => ∑ k, rieszTest i k (F k) x

/-- Self-adjointness of the Newton potential on tests: `∫ g (N * f) = ∫ (N * g) f`. -/
def NewtonConvSymm : Prop :=
  ∀ f g : Pl → ℝ, IsTest f → IsTest g → ∫ x, g x * newtonConv f x = ∫ x, newtonConv g x * f x

/-- Integration by parts of a test against a smooth function. -/
def PdIBP : Prop :=
  ∀ (k : Fin 2) (u f : Pl → ℝ), ContDiff ℝ ∞ u → IsTest f →
    ∫ x, pd k f x * u x = -∫ x, f x * pd k u x

/-- `Σ_k S_{kk} f = f` for a test `f`. -/
def RieszTestDiag : Prop :=
  ∀ f : Pl → ℝ, IsTest f → ∀ x, rieszTest 0 0 f x + rieszTest 1 1 f x = f x

/-- The pressure identity on tests: for tests `F_0, F_1`, with `ψ_i = Σ_k S_{ik} F_k`,
`Σ_i ∫ F_i ψ_i = Σ_i ∫ ψ_i²`. -/
def PressureIdentityTest : Prop :=
  ∀ F : Fin 2 → Pl → ℝ, (∀ k, IsTest (F k)) →
    ∑ i, ∫ x, F i x * (∑ k, rieszTest i k (F k) x) = ∑ i, ∫ x, (∑ k, rieszTest i k (F k) x) ^ 2

/-- `Σ_{i,k} ‖S_{ik} f‖₂² = ‖f‖₂²` for a test `f`. -/
def RieszTestSqSum : Prop :=
  ∀ f : Pl → ℝ, IsTest f → ∑ i, ∑ k, ∫ x, (rieszTest i k f x) ^ 2 = ∫ x, (f x) ^ 2

/-- Test-level symmetry `∫ S_{ik} f · g = ∫ f · S_{ik} g`. -/
def RieszTestSymm : Prop :=
  ∀ (i k : Fin 2) (f g : Pl → ℝ), IsTest f → IsTest g →
    ∫ x, rieszTest i k f x * g x = ∫ x, f x * rieszTest i k g x

/-- `Σ_i S_{ki}(∂_iφ) = ∂_kφ` for a test `φ`. -/
def RieszTestGrad : Prop :=
  ∀ (φ : Pl → ℝ), IsTest φ → ∀ (k : Fin 2) (x : Pl), ∑ i, rieszTest k i (pd i φ) x = pd k φ x

/-- `Σ_i S_{ki} Ψ_i = 0` for a solenoidal test field `Ψ`. -/
def RieszTestSol : Prop :=
  ∀ Ψ : Fin 2 → Pl → ℝ, (∀ i, IsTest (Ψ i)) → (∀ x, divTest Ψ x = 0) →
    ∀ (k : Fin 2) (x : Pl), ∑ i, rieszTest k i (Ψ i) x = 0

/-! ## Group D: the `L²` operators (extension by density, then the five properties) -/

/-- `f ↦ S_{ik} f` is `L²`-bounded by `1` on tests. -/
def RieszTestL2Bound : Prop :=
  ∀ (i k : Fin 2) (f : Pl → ℝ), IsTest f → ∀ (h1 : MemLp f 2 volume)
    (h2 : MemLp (rieszTest i k f) 2 volume), ‖h2.toLp _‖ ≤ ‖h1.toLp f‖

/-- Smooth compactly supported functions are dense in `PlaneL2` (abstract extension lemma input). -/
def PlaneTestDense : Prop :=
  ∀ g : PlaneL2, ∀ ε : ℝ, 0 < ε → ∃ f : Pl → ℝ, IsTest f ∧ ∃ h : MemLp f 2 volume, ‖g - h.toLp f‖ < ε

/-- A dense submodule of `PlaneL2` of (classes of) tests. -/
def PlaneTestSub : Prop :=
  ∃ M : Submodule ℝ PlaneL2,
    (∀ g ∈ M, ∃ f : Pl → ℝ, IsTest f ∧ ∃ h : MemLp f 2 volume, g = h.toLp f) ∧
      (∀ f : Pl → ℝ, IsTest f → ∀ h : MemLp f 2 volume, h.toLp f ∈ M) ∧ Dense (M : Set PlaneL2)

/-- Abstract extension: a norm-`≤ 1` linear map on a dense submodule extends to `PlaneL2`. -/
def ExtensionLemma : Prop :=
  ∀ (M : Submodule ℝ PlaneL2), Dense (M : Set PlaneL2) → ∀ L : M →ₗ[ℝ] PlaneL2,
    (∀ g : M, ‖L g‖ ≤ ‖(g : PlaneL2)‖) →
      ∃ T : PlaneL2 →L[ℝ] PlaneL2, ‖T‖ ≤ 1 ∧ ∀ g : M, T g = L g

/-- The pressure identity on `L²`: `Σ_i ⟨F_i, Σ_k S_{ik}F_k⟩ = Σ_i ‖Σ_k S_{ik}F_k‖²`. -/
def RieszL2Pressure : Prop :=
  ∀ (T : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)),
    (∀ i k, ExtendsRieszTest (T i k) i k) →
    ∀ F : Fin 2 → PlaneL2,
      ∑ i, inner ℝ (F i) (∑ k, T i k (F k)) = ∑ i, ‖∑ k, T i k (F k)‖ ^ 2

/-- Existence of the `L²` operators `S_{ik}`, norm `≤ 1`, extending the test-level pairs. -/
def RieszL2Exists : Prop :=
  ∀ i k : Fin 2, ∃ T : PlaneL2 →L[ℝ] PlaneL2, ‖T‖ ≤ 1 ∧ ExtendsRieszTest T i k

/-- Two `L²` extensions of the same test-level operator coincide. -/
def RieszL2Unique : Prop :=
  ∀ (T T' : PlaneL2 →L[ℝ] PlaneL2) (i k : Fin 2), ExtendsRieszTest T i k →
    ExtendsRieszTest T' i k → T = T'

/-- `S_{ik}ᵀ = S_{ki}` on `L²` (the form of `IsPlaneRieszFamily`). -/
def RieszL2Transpose : Prop :=
  ∀ (T : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)),
    (∀ i k, ExtendsRieszTest (T i k) i k) →
    ∀ (i k : Fin 2) (f g : PlaneL2), ∫ x, T i k f x * g x = ∫ x, f x * T k i g x

/-- The pair contraction `Σ_i ‖f_i - Σ_k S_{ik} f_k‖² ≤ Σ_i ‖f_i‖²` on `L²`. -/
def RieszL2Contraction : Prop :=
  ∀ (T : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)),
    (∀ i k, ExtendsRieszTest (T i k) i k) →
    ∀ f : Fin 2 → PlaneL2, ∑ i, ‖f i - ∑ k, T i k (f k)‖ ^ 2 ≤ ∑ i, ‖f i‖ ^ 2

/-- The gradient test identity on `L²` (fourth field of `IsPlaneRieszFamily`). -/
def RieszL2Grad : Prop :=
  ∀ (T : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)),
    (∀ i k, ExtendsRieszTest (T i k) i k) →
    ∀ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ (h : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ φ x (Pi.single i 1)) 2 volume) (k : Fin 2),
        ∑ i, T k i ((h i).toLp _) = (h k).toLp _

/-- The solenoidal test identity on `L²` (fifth field of `IsPlaneRieszFamily`). -/
def RieszL2Sol : Prop :=
  ∀ (T : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)),
    (∀ i k, ExtendsRieszTest (T i k) i k) →
    ∀ Ψ : Fin 2 → (Fin 2 → ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (Ψ i) ∧ HasCompactSupport (Ψ i)) →
      (∀ x, ∑ i, fderiv ℝ (Ψ i) x (Pi.single i 1) = 0) →
      ∀ (h : ∀ i : Fin 2, MemLp (Ψ i) 2 volume) (k : Fin 2),
        ∑ i, T k i ((h i).toLp _) = 0

/-- Off-support kernel representation on `L²` (the `offSupport` field of `IsCZConvolution`). -/
def RieszL2OffSupport : Prop :=
  ∀ (T : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)),
    (∀ i k, ExtendsRieszTest (T i k) i k) → ∀ (i k : Fin 2),
    ∀ f : PlaneL2, ∀ S : Set (Fin 2 → ℝ), IsCompact S → (∀ᵐ y, y ∉ S → f y = 0) →
      ∀ᵐ x, x ∉ S → T i k f x = ∫ y, planeRieszKernel i k (x - y) * f y

/-- `K_{ki}(-z) = K_{ik}(z)`: the kernel is even and symmetric in `(i, k)`. -/
def PlaneRieszKernelSymmNeg : Prop :=
  ∀ (i k : Fin 2) (z : Pl), planeRieszKernel k i (-z) = planeRieszKernel i k z

/-- Duality identity for the kernel representation: for `f ∈ L²` vanishing off a compact `S` and
a test `g` supported in `Sᶜ`, `∫ g · S_{ik} f = ∫ g(x) ∫ K_{ik}(x - y) f(y) dy dx`. -/
def KernelDuality : Prop :=
  ∀ (T : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)),
    (∀ a b, ExtendsRieszTest (T a b) a b) → ∀ (i k : Fin 2) (f : PlaneL2) (S : Set Pl),
    IsCompact S → (∀ᵐ y, y ∉ S → f y = 0) → ∀ g : Pl → ℝ, IsTest g → tsupport g ⊆ Sᶜ →
      Integrable (fun x => g x * ∫ y, planeRieszKernel i k (x - y) * f y) volume ∧
        ∫ x, g x * T i k f x = ∫ x, g x * ∫ y, planeRieszKernel i k (x - y) * f y

end UnforcedLeray.Short.IIb.PlaneRiesz
