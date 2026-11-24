import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Defs
import UnforcedLeray.Analysis.Pressure.NewtonIdentity

/-!
# Biot-Savart Fubini infrastructure: the lemma statements

Source `the November 2 reference manuscript` lines 1351-1362 (`curl ψ = Φ` for the
stream potential `ψ = bsPot Φ` of a weakly solenoidal `Φ ∈ Y_2`), 1334-1337 (`Y_r`).

Plan.  Slice level (pure `ℝ³`): for `f ∈ L²(ℝ³; ℂ³)` weakly solenoidal and `Θ` a smooth compactly
supported vector field, `∫ curl Θ · bsSlice f = ∫ Θ · f`.  Proof: Fubini
(`BSPairIntegrable`, `BSFubiniSwap`), the kernel identity
`∫ K(y-z) × curl Θ(y) dy = Θ(z) + ∫ div Θ(y) K(y-z) dy` (`BSKernelCurlId`, from the Newton
potential `1/(4π|x|)`), and the vanishing of `∫ f · G` for the gradient field
`G(z) = ∫ h(y) K(y-z) dy` (`BSGradField`).  Phase level: a.e. slice (`BSSliceL2`,
`BSSliceSol`) and integration over the period (`BSPhaseCurl_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ## Spatial (slice) operators -/

/-- Spatial gradient of a scalar function, as a `ℂ³`-vector. -/
def bsGradS (χ : Space → ℂ) (y : Space) : CVec3 :=
  WithLp.toLp 2 fun j => fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ))

/-- Spatial divergence of a vector field. -/
def bsDivS (Θ : Space → CVec3) (y : Space) : ℂ :=
  ∑ j : Fin 3, (fderiv ℝ Θ y (EuclideanSpace.single j (1 : ℝ))) j

/-- Spatial curl `∑ⱼ eⱼ × ∂ⱼ Θ` of a vector field. -/
def bsCurlS (Θ : Space → CVec3) (y : Space) : CVec3 :=
  ∑ j : Fin 3, crossC (EuclideanSpace.single j (1 : ℂ)) (fderiv ℝ Θ y (EuclideanSpace.single j (1 : ℝ)))

/-- Spatial Laplacian of a scalar function. -/
def bsLapS (φ : Space → ℂ) (y : Space) : ℂ :=
  ∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))) y
    (EuclideanSpace.single j (1 : ℝ))

/-- The Biot-Savart potential of a single slice `f : ℝ³ → ℂ³`. -/
def bsSlice (f : Space → CVec3) (y : Space) : CVec3 :=
  ∫ z : Space, crossC (f z) (bsKernel (y - z))

/-- A slice is weakly solenoidal: `∫ ∇χ · f = 0` for every smooth compactly supported `χ`. -/
def BSSliceSolenoidal (f : Space → CVec3) : Prop :=
  ∀ χ : Space → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ → ∫ y : Space, dotL (bsGradS χ y) (f y) = 0

/-! ## Kernel facts -/

/-- `‖K(w)‖ = 1/(4π‖w‖²)`. -/
def BSKernelNorm : Prop :=
  ∀ w : Space, ‖bsKernel w‖ = (4 * Real.pi)⁻¹ * (‖w‖ ^ 2)⁻¹

/-- `K = -(newtonGradientKernel)` componentwise (audited kernel of the pressure analysis). -/
def BSKernelNewton : Prop :=
  ∀ (w : Space) (i : Fin 3),
    bsKernel w i = ((-(UnforcedLeray.PressureAnalysis.newtonGradientKernel i w) : ℝ) : ℂ)

/-- `K` is locally integrable. -/
def BSKernelLocInt : Prop := LocallyIntegrable bsKernel volume

/-- Convolution of `|K|` with a compactly supported continuous function decays like `(1+|z|²)⁻¹`. -/
def BSTestConvBound : Prop :=
  ∀ φ : Space → ℂ, Continuous φ → HasCompactSupport φ → ∃ C : ℝ, ∀ z : Space,
    Integrable (fun y : Space => ‖φ y‖ * ‖bsKernel (y - z)‖) volume ∧
      ∫ y : Space, ‖φ y‖ * ‖bsKernel (y - z)‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹

/-- `(1+|z|²)⁻¹ ∈ L²(ℝ³)`. -/
def BSDecayL2 : Prop := MemLp (fun z : Space => (1 + ‖z‖ ^ 2)⁻¹) 2 volume

/-- Integrability of `(y,z) ↦ A(y) · (f(z) × K(y-z))` on `ℝ³ × ℝ³` for `f ∈ L²`. -/
def BSPairIntegrable : Prop :=
  ∀ (A : Space → CVec3), Continuous A → HasCompactSupport A →
    ∀ f : Space → CVec3, MemLp f 2 volume →
      Integrable (fun p : Space × Space => dotL (A p.1) (crossC (f p.2) (bsKernel (p.1 - p.2))))
        ((volume : Measure Space).prod volume)

/-- Fubini swap: `∫ A · bsSlice f = ∫ f · (∫ K(y-z) × A(y) dy)`. -/
def BSFubiniSwap : Prop :=
  ∀ (A : Space → CVec3), Continuous A → HasCompactSupport A →
    ∀ f : Space → CVec3, MemLp f 2 volume →
      ∫ y : Space, dotL (A y) (bsSlice f y) =
        ∫ z : Space, dotL (f z) (∫ y : Space, crossC (bsKernel (y - z)) (A y))

/-! ## The kernel identity -/

/-- Newton identity: `∫ P(y-z) Δφ(y) dy = -φ(z)`, `P = 1/(4π|x|)`, for complex `C_c^∞` `φ`. -/
def BSNewtonLaplace : Prop :=
  ∀ (φ : Space → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → ∀ z : Space,
    ∫ y : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) * bsLapS φ y
      = -φ z

/-- Weak derivative of `P`: `∫ P(y-z) ∂ⱼh(y) dy = ∫ K_j(y-z) h(y) dy`. -/
def BSKernelWeakDeriv : Prop :=
  ∀ (h : Space → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h → HasCompactSupport h → ∀ (z : Space) (j : Fin 3),
    ∫ y : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) *
        fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ))
      = ∫ y : Space, bsKernel (y - z) j * h y

/-- `∫ K(y-z) × curl Θ(y) dy = Θ(z) + ∫ div Θ(y) K(y-z) dy`. -/
def BSKernelCurlId : Prop :=
  ∀ (Θ : Space → CVec3), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ → HasCompactSupport Θ → ∀ z : Space,
    ∫ y : Space, crossC (bsKernel (y - z)) (bsCurlS Θ y) =
      Θ z + ∫ y : Space, bsDivS Θ y • bsKernel (y - z)

/-! ## The gradient field `G(z) = ∫ h(y) K(y-z) dy` -/

/-- With `g(z) = ∫ P(y-z) h(y) dy`: `g` is smooth with `∇g = G`. -/
def BSGradFieldSmooth : Prop :=
  ∀ (h : Space → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h → HasCompactSupport h →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Space =>
        ∫ y : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) * h y) ∧
    ∀ z : Space, bsGradS (fun z : Space =>
        ∫ y : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) * h y) z =
      ∫ y : Space, h y • bsKernel (y - z)

/-- Decay: `|g(z)| ≤ C/(1+|z|)`, `|G(z)| ≤ C/(1+|z|²)`. -/
def BSGradFieldDecay : Prop :=
  ∀ (h : Space → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h → HasCompactSupport h → ∃ C : ℝ, ∀ z : Space,
    ‖∫ y : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) * h y‖
        ≤ C * (1 + ‖z‖)⁻¹ ∧
      ‖∫ y : Space, h y • bsKernel (y - z)‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹

/-- Cutoff argument: a solenoidal `f ∈ L²` is orthogonal to `∇g` for smooth `g` with
`|g| ≤ C/(1+|z|)` and `|∇g| ≤ C/(1+|z|²)`. -/
def BSCutoff : Prop :=
  ∀ f : Space → CVec3, MemLp f 2 volume → BSSliceSolenoidal f →
    ∀ (g : Space → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → ∀ C : ℝ,
      (∀ z, ‖g z‖ ≤ C * (1 + ‖z‖)⁻¹) → (∀ z, ‖bsGradS g z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) →
        ∫ z : Space, dotL (f z) (bsGradS g z) = 0

/-- `∫ f · G = 0` for the gradient field `G(z) = ∫ h(y) K(y-z) dy`. -/
def BSGradField : Prop :=
  ∀ f : Space → CVec3, MemLp f 2 volume → BSSliceSolenoidal f →
    ∀ (h : Space → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h → HasCompactSupport h →
      ∫ z : Space, dotL (f z) (∫ y : Space, h y • bsKernel (y - z)) = 0

/-- **Slice curl identity**: `∫ curl Θ · bsSlice f = ∫ Θ · f`. -/
def BSSliceCurl : Prop :=
  ∀ f : Space → CVec3, MemLp f 2 volume → BSSliceSolenoidal f →
    ∀ (Θ : Space → CVec3), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ → HasCompactSupport Θ →
      ∫ y : Space, dotL (bsCurlS Θ y) (bsSlice f y) = ∫ z : Space, dotL (Θ z) (f z)

/-! ## Phase level -/

/-- Slices of `Φ ∈ Y_2` are in `L²(ℝ³)` for a.e. phase. -/
def BSSliceL2 : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
    ∀ᵐ t : ℝ, MemLp (fun y : Space => Φ (t, y)) 2 volume

/-- Fixed spatial test: a weakly solenoidal `Φ ∈ Y_2` has a.e. slice orthogonal to `∇χ`. -/
def BSSliceSolFixed : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
    IsWeakSolenoidal P Φ → ∀ χ : Space → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
      ∀ᵐ t : ℝ, ∫ y : Space, dotL (bsGradS χ y) (Φ (t, y)) = 0

/-- A countable family of tests dense (in `C¹` with common compact support) in all tests. -/
def BSTestDense : Prop :=
  ∃ D : Set (Space → ℂ), D.Countable ∧ (∀ χ ∈ D, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ) ∧
    ∀ χ : Space → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ → ∀ ε : ℝ, 0 < ε →
      ∃ χ' ∈ D, (∀ y, ‖χ y - χ' y‖ ≤ ε) ∧ (∀ y, ‖bsGradS χ y - bsGradS χ' y‖ ≤ ε) ∧
        ∃ R : ℝ, ∀ y, R < ‖y‖ → χ' y = 0

/-- A.e. slice solenoidality (all tests at once). -/
def BSSliceSol : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
    IsWeakSolenoidal P Φ → ∀ᵐ t : ℝ, BSSliceSolenoidal (fun y : Space => Φ (t, y))

/-- The phase curl of a phase test is the slice curl of its slices. -/
def BSCurlSlice : Prop :=
  ∀ (P : ℝ) (Θ : ℝ × Space → CVec3), IsPhaseTest P Θ → ∀ (t : ℝ) (y : Space),
    curlT Θ (t, y) = bsCurlS (fun y' : Space => Θ (t, y')) y

/-- A phase test has smooth compactly supported slices. -/
def BSPhaseSliceTest : Prop :=
  ∀ (P : ℝ) (Θ : ℝ × Space → CVec3), IsPhaseTest P Θ → ∀ t : ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Space => Θ (t, y)) ∧ HasCompactSupport (fun y : Space => Θ (t, y))

end UnforcedLeray.Short.PartIIIb.Concrete
