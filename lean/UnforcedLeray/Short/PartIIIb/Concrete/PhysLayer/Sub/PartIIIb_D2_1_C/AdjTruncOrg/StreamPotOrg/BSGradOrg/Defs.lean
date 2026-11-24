import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Defs
import UnforcedLeray.Lib.CZL2.RieszL2

/-!
# `BSGrad`: the slice gradient operator of the Biot-Savart potential and its ingredients

Source `the November 2 reference manuscript` lines 1334-1337 (`Y_r` is the plain
`L^r((ℝ/Pℤ) × ℝ³)`), 1351-1362 (adjoint at `r = 2`; the stream potential `ψ = bsPot Φ` of the
solenoidal cutoff, `∇ψ ∈ Y_2`), 1470-1480 (radial cutoffs).

Mathematics.  On one slice, `f ∈ L²(ℝ³; ℂ³)` and `ψ = f ×∗ K`, `K = -∇N`, `N = 1/(4π|x|)`, so
`ψ = curl (N ∗ f) = ∑_c e_c × ∂_c(N ∗ f)` and `∂ⱼψ = ∑_c e_c × R_{jc} f`, `R_{jc} = ∂ⱼ∂_c(-Δ)⁻¹`.
The bounded operator `R_{jc}` on `L²(ℝ³)` is the audited-library operator `rieszPairL2 j c`
(`Lib/CZL2/RieszL2.lean`, norm `≤ 1`, equal to `∂ⱼ∂_c(N ∗ ·)` on tests).  So the slice gradient is
the concrete bounded operator
`bsGradL2 j f = ∑_{c,b} R_{jc}(f_b) (e_c × e_b)` on `L²(ℝ³; ℂ³)`
(`R_{jc}` applied to real and imaginary parts).  The phase-level gradient `Dψ j` is the jointly
measurable `Y_2` representative of `τ ↦ bsGradL2 j (Φ(τ))` (`Yq` dictionary of Part II-b), so the
`L²` bound, measurability and periodicity are automatic; what remains is the slice weak identity
`∫ (-∂ⱼθ) · ψ = ∫ θ · bsGradL2 j f` (`BSGSliceId`), proved from
* the Fubini swap `∫ A · ψ = ∫ f · (∫ K(y-z) × A(y) dy)` (`BSFubiniSwap`, `Fubini/Defs.lean`),
* the kernel identity `∫ K(y-z) × ∂ⱼθ(y) dy = bsgW j θ z` (`BSGKernelVec`, from
  `∫ K_c(y-z) ∂ⱼw(y) dy = ∂_c∂ⱼ(N ∗ w)(z)`, i.e. `newtonConv_partial`),
* the `L²` duality `∫ f · bsgW j θ = -∫ θ · bsGradL2 j f` (`BSGDualVec`, from the self-adjointness
  `inner_rieszPairL2` and `rieszPairL2_toLp`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-! ## Slice operators on `L²(ℝ³)` -/

/-- Complex scalar `L²(ℝ³)`. -/
abbrev BsgCL2 : Type := Lp ℂ 2 (volume : Measure Space)

/-- Complex vector `L²(ℝ³; ℂ³)`, the space of slices of `Y_2`. -/
abbrev BsgVL2 : Type := Lp CVec3 2 (volume : Measure Space)

/-- The unit vector `e_b` of `ℂ³`. -/
abbrev bsgE (b : Fin 3) : CVec3 := EuclideanSpace.single b (1 : ℂ)

/-- Real part, `L²(ℝ³; ℂ) → L²(ℝ³; ℝ)`. -/
def bsgReL2 : BsgCL2 →L[ℝ] ScalarL2 := Complex.reCLM.compLpL 2 volume

/-- Imaginary part, `L²(ℝ³; ℂ) → L²(ℝ³; ℝ)`. -/
def bsgImL2 : BsgCL2 →L[ℝ] ScalarL2 := Complex.imCLM.compLpL 2 volume

/-- `g ↦ g + 0 i`, `L²(ℝ³; ℝ) → L²(ℝ³; ℂ)`. -/
def bsgOfRealL2 : ScalarL2 →L[ℝ] BsgCL2 := Complex.ofRealCLM.compLpL 2 volume

/-- `g ↦ i g`, `L²(ℝ³; ℝ) → L²(ℝ³; ℂ)`. -/
def bsgIOfRealL2 : ScalarL2 →L[ℝ] BsgCL2 :=
  (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) Complex.I).compLpL 2 volume

/-- Complexification of a real scalar operator: `R(u + i v) = R u + i R v`. -/
def bsgCplxOp (R : ScalarL2 →L[ℝ] ScalarL2) : BsgCL2 →L[ℝ] BsgCL2 :=
  bsgOfRealL2.comp (R.comp bsgReL2) + bsgIOfRealL2.comp (R.comp bsgImL2)

/-- The `b`-th component, `L²(ℝ³; ℂ³) → L²(ℝ³; ℂ)`. -/
def bsgCoord (b : Fin 3) : BsgVL2 →L[ℝ] BsgCL2 :=
  ((EuclideanSpace.proj b : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).compLpL 2 volume

/-- `g ↦ g v`, `L²(ℝ³; ℂ) → L²(ℝ³; ℂ³)`. -/
def bsgEmb (v : CVec3) : BsgCL2 →L[ℝ] BsgVL2 :=
  ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v).restrictScalars ℝ).compLpL 2 volume

/-- **The slice gradient of the Biot-Savart potential** (source 1351-1362):
`bsGradL2 j f = ∂ⱼ(f ×∗ K) = ∑_c e_c × R_{jc} f = ∑_{c,b} R_{jc}(f_b) (e_c × e_b)`, with
`R_{jc} = rieszPairL2 j c = ∂ⱼ∂_c(-Δ)⁻¹` (bounded on `L²`, `Lib/CZL2/RieszL2.lean`). -/
def bsGradL2 (j : Fin 3) : BsgVL2 →L[ℝ] BsgVL2 :=
  ∑ c : Fin 3, ∑ b : Fin 3,
    (bsgEmb (crossC (bsgE c) (bsgE b))).comp ((bsgCplxOp (rieszPairL2 j c)).comp (bsgCoord b))

/-! ## Test-level objects -/

/-- The Newton Hessian `T_{cj} = ∂_c∂ⱼ(N ∗ ·)` on complex scalar functions:
`T_{cj}(u + i v) = T_{cj} u + i T_{cj} v` (`rieszPairTest`). -/
def bsgHess (c j : Fin 3) (θ : Space → ℂ) (z : Space) : ℂ :=
  (rieszPairTest c j (fun y => (θ y).re) z : ℂ) +
    Complex.I * (rieszPairTest c j (fun y => (θ y).im) z : ℂ)

/-- The scalar coefficient `θ · (e_c × e_b)` of a vector field (bilinear dot product). -/
def bsgCoef (c b : Fin 3) (θ : Space → CVec3) (y : Space) : ℂ :=
  dotL (θ y) (crossC (bsgE c) (bsgE b))

/-- `W_j θ(z) = -∑_{c,b} T_{cj}(θ · (e_c × e_b))(z) e_b`; for a test `θ` this is
`∫ K(y - z) × ∂ⱼθ(y) dy` (`BSGKernelVec`). -/
def bsgW (j : Fin 3) (θ : Space → CVec3) (z : Space) : CVec3 :=
  -∑ c : Fin 3, ∑ b : Fin 3, bsgHess c j (bsgCoef c b θ) z • bsgE b

/-! ## The ingredients -/

/-- **Real kernel identity** (source 1351-1362; `K_c(x) = x_c/(4π|x|³) = -∂_cN(x)`): for a real
compact smooth test `w`, `∫ K_c(y - z) ∂ⱼw(y) dy = ∂_c∂ⱼ(N ∗ w)(z)`. -/
def BSGKernelReal : Prop :=
  ∀ w : Space → ℝ, IsSpatialTest w → ∀ (c j : Fin 3) (z : Space),
    ∫ y : Space, (4 * Real.pi)⁻¹ * (‖y - z‖ ^ 3)⁻¹ * (y - z) c * spatialTestDerivative j w y =
      rieszPairTest c j w z

/-- **Complex kernel identity** (source 1351-1362): for a complex compact smooth `θ`,
`∫ K_c(y - z) ∂ⱼθ(y) dy = T_{cj} θ(z)`. -/
def BSGKernelCplx : Prop :=
  ∀ θ : Space → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → ∀ (c j : Fin 3) (z : Space),
    ∫ y : Space, bsKernel (y - z) c * fderiv ℝ θ y (EuclideanSpace.single j 1) = bsgHess c j θ z

/-- **Vector kernel identity** (source 1351-1362): for a compact smooth vector field `θ`,
`∫ K(y - z) × ∂ⱼθ(y) dy = W_j θ(z)`. -/
def BSGKernelVec : Prop :=
  ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ → ∀ (j : Fin 3) (z : Space),
    ∫ y : Space, crossC (bsKernel (y - z)) (fderiv ℝ θ y (EuclideanSpace.single j 1)) =
      bsgW j θ z

/-- **Real duality** (source 1351-1362; `R_{jc}` is the `L²` adjoint of `T_{cj}`): for a real test
`u` and `g ∈ L²(ℝ³)`, `∫ u R_{jc} g = ∫ T_{cj} u g`. -/
def BSGDualReal : Prop :=
  ∀ u : Space → ℝ, IsSpatialTest u → ∀ (g : ScalarL2) (c j : Fin 3),
    ∫ y : Space, u y * rieszPairL2 j c g y = ∫ y : Space, rieszPairTest c j u y * g y

/-- `T_{cj}` maps complex compact smooth functions into `L²(ℝ³)`. -/
def BSGHessMemLp : Prop :=
  ∀ θ : Space → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → ∀ c j : Fin 3,
    MemLp (bsgHess c j θ) 2 volume

/-- Almost-everywhere formulas for the slice operators. -/
def BSGCoeFn : Prop :=
  (∀ g : BsgCL2, (bsgReL2 g : Space → ℝ) =ᵐ[volume] fun y => (g y).re) ∧
  (∀ g : BsgCL2, (bsgImL2 g : Space → ℝ) =ᵐ[volume] fun y => (g y).im) ∧
  (∀ (R : ScalarL2 →L[ℝ] ScalarL2) (g : BsgCL2), (bsgCplxOp R g : Space → ℂ) =ᵐ[volume]
      fun y => ((R (bsgReL2 g) y : ℝ) : ℂ) + Complex.I * ((R (bsgImL2 g) y : ℝ) : ℂ)) ∧
  (∀ (b : Fin 3) (F : BsgVL2), (bsgCoord b F : Space → ℂ) =ᵐ[volume] fun y => F y b) ∧
  (∀ (j : Fin 3) (F : BsgVL2), (bsGradL2 j F : Space → CVec3) =ᵐ[volume] fun y =>
      ∑ c : Fin 3, ∑ b : Fin 3, bsgCplxOp (rieszPairL2 j c) (bsgCoord b F) y •
        crossC (bsgE c) (bsgE b))

/-- **Complex duality** (source 1351-1362): for a complex compact smooth `θ` and `g ∈ L²(ℝ³; ℂ)`,
`∫ θ R_{jc} g = ∫ T_{cj} θ g` (bilinear, `R_{jc}` complexified). -/
def BSGDualCplx : Prop :=
  ∀ θ : Space → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → ∀ (g : BsgCL2) (c j : Fin 3),
    ∫ y : Space, θ y * bsgCplxOp (rieszPairL2 j c) g y = ∫ y : Space, bsgHess c j θ y * g y

/-- **Vector duality** (source 1351-1362): for a compact smooth `θ` and `f ∈ L²(ℝ³; ℂ³)`,
`∫ f · W_j θ = -∫ θ · bsGradL2 j f`. -/
def BSGDualVec : Prop :=
  ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
    ∀ (f : Space → CVec3) (hf : MemLp f 2 volume) (j : Fin 3),
      ∫ z : Space, dotL (f z) (bsgW j θ z) =
        -∫ y : Space, dotL (θ y) (bsGradL2 j (hf.toLp f) y)

/-- **Slice weak gradient** (source 1351-1362): for a compact smooth `θ` and `f ∈ L²(ℝ³; ℂ³)`,
`∫ (-∂ⱼθ) · (f ×∗ K) = ∫ θ · bsGradL2 j f`, i.e. `bsGradL2 j f` is the weak `∂ⱼ` of the slice
Biot-Savart potential. -/
def BSGSliceId : Prop :=
  ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
    ∀ (f : Space → CVec3) (hf : MemLp f 2 volume) (j : Fin 3),
      ∫ y : Space, dotL (-fderiv ℝ θ y (EuclideanSpace.single j 1))
          (∫ z : Space, crossC (f z) (bsKernel (y - z))) =
        ∫ y : Space, dotL (θ y) (bsGradL2 j (hf.toLp f) y)

end UnforcedLeray.Short.PartIIIb.Concrete
