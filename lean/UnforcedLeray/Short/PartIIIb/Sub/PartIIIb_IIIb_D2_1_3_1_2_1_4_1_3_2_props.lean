import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1

/-!
# `selCauchy`: slice-level and `τ`-level facts (statements only; no `_1_2`/`_1_3` import)

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
These Props are stated in unfolded form so that their proofs may import `Slice/H1.lean`
(which declares its own `SliceLapId`) without clashing with `PartIII-b_IIIb-D2_1_3_1_2_1_4_1_3`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- (C1) One-slice energy bound (source 1351-1362): `f, h, gⱼ ∈ L²(ℝ³)`, `ν ∫ f·Δθ = ∫ h·θ` for all
smooth compactly supported `θ`, and `gⱼ` the weak `∂ⱼ`-derivative of `f`.  Then
`∑ⱼ ‖gⱼ‖² ≤ ν⁻¹ ‖f‖ ‖h‖`.  Proof: apply `sliceH1` (`Slice/H1.lean`) to `f` and `ν⁻¹ h`, identify
the resulting `L²` derivatives with `gⱼ` by a.e. uniqueness of weak derivatives
(`ae_eq_zero_of_integral_contDiff_smul_eq_zero`), convert `∫` of `‖·‖²` to `∫⁻ ‖·‖ₑ ^ 2`. -/
def CSliceEnergy : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (f h : Space → CVec3) (g : Fin 3 → Space → CVec3),
    MemLp f 2 volume → MemLp h 2 volume → (∀ j, MemLp (g j) 2 volume) →
    (∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ν * (∫ y : Space, ∑ i : Fin 3, f y i * lapS θ y i)
        = ∫ y : Space, ∑ i : Fin 3, h y i * θ y i) →
    (∀ (j : Fin 3) (θ : Space → CVec3), ContDiff ℝ ∞ θ → HasCompactSupport θ →
      -(∫ y : Space, ∑ i : Fin 3,
          f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        = ∫ y : Space, ∑ i : Fin 3, g j y i * θ y i) →
      ∑ j : Fin 3, ∫⁻ y : Space, ‖g j y‖ₑ ^ (2 : ℝ)
        ≤ ENNReal.ofReal ν⁻¹ * (∫⁻ y : Space, ‖f y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫⁻ y : Space, ‖h y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- (C2) Slices of a `Y_2` field are `L²` for a.e. `τ ∈ ℝ` (source 1334-1337): finite norm over
`(0,P]` gives a.e. `τ ∈ (0,P]`; a.e. periodicity transports it to all `τ`; joint
`AEStronglyMeasurable` gives measurable slices a.e. -/
def CSliceAe : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ f : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 f →
    ∀ᵐ τ : ℝ, MemLp (fun y : Space => f (τ, y)) 2 volume

/-- (C3a) Linearity of the slice Laplacian identity (source 1351-1362): if `(f₁,h₁)`, `(f₂,h₂)`
satisfy it with all four in `L²`, so does `(f₁-f₂, h₁-h₂)` (integrability of `f·Δθ`, `h·θ`:
`L²` times compactly supported continuous). -/
def CLapDiff : Prop :=
  ∀ (ν : ℝ) (f₁ f₂ h₁ h₂ : Space → CVec3),
    MemLp f₁ 2 volume → MemLp f₂ 2 volume → MemLp h₁ 2 volume → MemLp h₂ 2 volume →
    (∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ν * (∫ y : Space, ∑ i : Fin 3, f₁ y i * lapS θ y i)
        = ∫ y : Space, ∑ i : Fin 3, h₁ y i * θ y i) →
    (∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ν * (∫ y : Space, ∑ i : Fin 3, f₂ y i * lapS θ y i)
        = ∫ y : Space, ∑ i : Fin 3, h₂ y i * θ y i) →
      ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        ν * (∫ y : Space, ∑ i : Fin 3, (f₁ - f₂) y i * lapS θ y i)
          = ∫ y : Space, ∑ i : Fin 3, (h₁ - h₂) y i * θ y i

/-- (C3b) Linearity of the weak-derivative identity (source 1351-1362): if `g₁, g₂` are weak
`∂ⱼ`-derivatives of `f₁, f₂ ∈ L²` (and `gₖ ∈ L²`), then `g₁ - g₂` is one of `f₁ - f₂`. -/
def CWeakDiff : Prop :=
  ∀ (j : Fin 3) (f₁ f₂ g₁ g₂ : Space → CVec3),
    MemLp f₁ 2 volume → MemLp f₂ 2 volume → MemLp g₁ 2 volume → MemLp g₂ 2 volume →
    (∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      -(∫ y : Space, ∑ i : Fin 3,
          f₁ y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        = ∫ y : Space, ∑ i : Fin 3, g₁ y i * θ y i) →
    (∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      -(∫ y : Space, ∑ i : Fin 3,
          f₂ y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        = ∫ y : Space, ∑ i : Fin 3, g₂ y i * θ y i) →
      ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        -(∫ y : Space, ∑ i : Fin 3,
            (f₁ - f₂) y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
          = ∫ y : Space, ∑ i : Fin 3, (g₁ - g₂) y i * θ y i

/-- (C4) Cauchy–Schwarz in `τ` (source 1351-1362, 1470-1480): `f, h, gⱼ ∈ Y_2`, and for a.e. `τ`
the slice bound `∑ⱼ ∫⁻ ‖gⱼ(τ)‖² ≤ ν⁻¹ (∫⁻ ‖f(τ)‖²)^{1/2} (∫⁻ ‖h(τ)‖²)^{1/2}`.  Then
`∑ⱼ ‖gⱼ‖_{Y_2}² ≤ ν⁻¹ ‖f‖_{Y_2} ‖h‖_{Y_2}` (Hölder for the pair `(2,2)` in `τ ∈ (0,P]`,
`ENNReal.lintegral_mul_le_Lp_mul_Lq`, with the `P⁻¹` normalisation). -/
def CYEnergy : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (f h : ℝ × Space → CVec3) (g : Fin 3 → ℝ × Space → CVec3),
    UnforcedLeray.Short.IIb.IsInYr P 2 f → UnforcedLeray.Short.IIb.IsInYr P 2 h →
    (∀ j, UnforcedLeray.Short.IIb.IsInYr P 2 (g j)) →
    (∀ᵐ τ : ℝ, ∑ j : Fin 3, ∫⁻ y : Space, ‖g j (τ, y)‖ₑ ^ (2 : ℝ)
        ≤ ENNReal.ofReal ν⁻¹ * (∫⁻ y : Space, ‖f (τ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫⁻ y : Space, ‖h (τ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) →
      ∑ j : Fin 3, UnforcedLeray.Short.IIb.phaseLpNorm P 2 (g j) ^ (2 : ℝ)
        ≤ ENNReal.ofReal ν⁻¹ * UnforcedLeray.Short.IIb.phaseLpNorm P 2 f
          * UnforcedLeray.Short.IIb.phaseLpNorm P 2 h

/-- (C5) Pure `ℝ≥0∞` Cauchy bookkeeping: if `x, y` are Cauchy-small, `c ≠ ⊤` and
`z n m ^ 2 ≤ c * x n m * y n m`, then `z` is Cauchy-small. -/
def CEnnrealCauchy : Prop :=
  ∀ (x y z : ℕ → ℕ → ENNReal) (c : ENNReal), c ≠ ⊤ →
    (∀ ε : ENNReal, 0 < ε → ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m → x n m < ε) →
    (∀ ε : ENNReal, 0 < ε → ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m → y n m < ε) →
    (∀ n m, z n m ^ (2 : ℝ) ≤ c * x n m * y n m) →
      ∀ ε : ENNReal, 0 < ε → ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m → z n m < ε

end UnforcedLeray.Short.PartIIIb.Concrete
