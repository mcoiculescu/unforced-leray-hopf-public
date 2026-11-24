import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4

/-!
# `adjDomGradSlice`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Three steps: (1) phase-test Laplacian identity descends to a.e. phase slice (countable dense family
of tests); (2) on one slice, `f, h ∈ L²(ℝ³; ℂ³)` with `∫ f·Δθ = ∫ h·θ` has `f ∈ H¹` with
`∑ⱼ ‖∂ⱼ f‖² ≤ ‖f‖ ‖h‖` (Fourier, or `Cons.L2.FreeLapReg.ae_h1_slices_of_periodicLaplacian` /
`ModeId.laplacianH1Regularity` after splitting into real and imaginary parts); (3) jointly
measurable periodic selection of the slice derivatives in `Y_2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The spatial Laplacian of a vector test `θ : ℝ³ → ℂ³`: `∑ⱼ ∂ⱼ∂ⱼ θ`. -/
def lapS (θ : Space → CVec3) (y : Space) : CVec3 :=
  ∑ j : Fin 3, fderiv ℝ (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y
    (EuclideanSpace.single j (1 : ℝ))

/-- (1) Slice Laplacian (source 1351-1362): if `Φ, a ∈ Y_2` and `νΔΦ = a` against phase tests
(`HasPtwOp P (nuLapT ν) Φ a`), then for a.e. phase `τ` and every smooth compactly supported
`θ`, `ν ∫ Φ(τ,y)·Δθ(y) dy = ∫ a(τ,y)·θ(y) dy`.  Proof: test with `φ(τ)θ(y)` over a countable
family of `θ` dense in `C_c^∞` in `C²`-norm on balls (cf. `Cons.L2.FreeLapReg.ae_laplacian_of_globalPairing`),
then `ae_eq_zero_of_integral_contDiff_smul_eq_zero` in `τ`. -/
def AdjSliceLap : Prop :=
  ∀ (P ν : ℝ), 0 < P → ∀ Φ a : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 a →
    UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) Φ a →
      ∀ᵐ τ : ℝ, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        ν * (∫ y : Space, ∑ i : Fin 3, Φ (τ, y) i * lapS θ y i)
          = ∫ y : Space, ∑ i : Fin 3, a (τ, y) i * θ y i

/-- (2) One-slice `H¹` regularity (source 1351-1362, Fourier: `|ξ|² |f̂|² ≤ |f̂| |ĥ|`): if
`f, h ∈ L²(ℝ³; ℂ³)` satisfy `∫ f·Δθ = ∫ h·θ` for all smooth compactly supported `θ`, there are
`gⱼ ∈ L²` with `-∫ f·∂ⱼθ = ∫ gⱼ·θ` and `∑ⱼ ‖gⱼ‖₂² ≤ ‖f‖₂ ‖h‖₂`. -/
def SliceH1 : Prop :=
  ∀ f h : Space → CVec3, MemLp f 2 volume → MemLp h 2 volume →
    (∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ y : Space, ∑ i : Fin 3, f y i * lapS θ y i) = ∫ y : Space, ∑ i : Fin 3, h y i * θ y i) →
    ∃ g : Fin 3 → Space → CVec3, (∀ j, MemLp (g j) 2 volume) ∧
      (∀ (j : Fin 3) (θ : Space → CVec3), ContDiff ℝ ∞ θ → HasCompactSupport θ →
        -(∫ y : Space, ∑ i : Fin 3,
            f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
          = ∫ y : Space, ∑ i : Fin 3, g j y i * θ y i) ∧
      ∑ j : Fin 3, (∫ y : Space, ‖g j y‖ ^ 2)
        ≤ (∫ y : Space, ‖f y‖ ^ 2) ^ (1 / 2 : ℝ) * (∫ y : Space, ‖h y‖ ^ 2) ^ (1 / 2 : ℝ)

/-- (3) Measurable periodic selection in `Y_2` (source 1351-1362, 1470-1480): `Φ, a ∈ Y_2`
satisfying the slice Laplacian identity a.e. have jointly measurable periodic `DΦ j ∈ Y_2`
whose slices are the weak derivatives.  Sketch: `Φ_n = η_{1/n} *_y Φ` is jointly measurable with
`∂ⱼΦ_n` Cauchy in `Y_2` by `SliceH1` applied to `Φ_n - Φ_m` (whose Laplacian is
`ν⁻¹(η_{1/n} * a - η_{1/m} * a)`); the `Y_2` limit has a jointly measurable representative and a
subsequence converges for a.e. `τ` in `L²(ℝ³)`, identifying the slice weak derivative by `SliceH1`
uniqueness. -/
def SliceSelect : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ Φ a : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 a →
    (∀ᵐ τ : ℝ, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        ν * (∫ y : Space, ∑ i : Fin 3, Φ (τ, y) i * lapS θ y i)
          = ∫ y : Space, ∑ i : Fin 3, a (τ, y) i * θ y i) →
      ∃ DΦ : Fin 3 → ℝ × Space → CVec3, ∀ j : Fin 3,
        UnforcedLeray.Short.IIb.IsInYr P 2 (DΦ j) ∧
          ∀ᵐ τ : ℝ, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
            -(∫ y : Space, ∑ i : Fin 3,
                Φ (τ, y) i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
              = ∫ y : Space, ∑ i : Fin 3, DΦ j (τ, y) i * θ y i

theorem adjDomGradSlice_of (h1 : AdjSliceLap) (h2 : SliceSelect) : AdjDomGradSlice := by
  intro P ν μ hP hP1 hν hμ Φ g hdom
  obtain ⟨a, ha, hpa⟩ := hdom.lapl
  exact h2 P ν hP hν Φ a hdom.mem ha (h1 P ν hP Φ a hdom.mem ha hpa)

end UnforcedLeray.Short.PartIIIb.Concrete
