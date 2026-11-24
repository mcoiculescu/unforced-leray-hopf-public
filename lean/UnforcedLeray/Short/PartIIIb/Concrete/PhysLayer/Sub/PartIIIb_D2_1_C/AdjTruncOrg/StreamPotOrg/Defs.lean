import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `StreamPotExists`: the canonical Biot-Savart formula and its ingredients

Source `the November 2 reference manuscript` lines 1334-1337 (`Y_r`), 1351-1362
(adjoint at `r = 2`, stream potential of the solenoidal cutoff), 1470-1480 (radial cutoffs).

The stream potential is given by the canonical, jointly measurable linear formula
`ψ = bsPot Φ = curl (Newton * Φ)`, i.e. `ψ(τ, x) = ∫ Φ(τ, z) × K(x - z) dz`,
`K(w) = w / (4π |w|³)`.  For `Φ` weakly solenoidal, `curl ψ = Φ`, `div ψ = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The Biot-Savart kernel `K(w) = w / (4π |w|³)` (gradient of minus the Newton kernel),
complexified. -/
def bsKernel (w : Space) : CVec3 :=
  WithLp.toLp 2 fun i => (((4 * Real.pi)⁻¹ * (‖w‖ ^ 3)⁻¹ * w i : ℝ) : ℂ)

/-- The Biot-Savart potential of a phase field, slice by slice:
`ψ(τ, x) = ∫ Φ(τ, z) × K(x - z) dz`. -/
def bsPot (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => ∫ z : Space, crossC (Φ (x.1, z)) (bsKernel (x.2 - z))

/-- **BSDefined** (source 1351-1362): for `Φ ∈ Y_2` the integral defining `bsPot Φ` converges a.e.
(`L² * |w|⁻² → L⁶` slice-wise, Hardy-Littlewood-Sobolev), and `bsPot Φ` is a.e. strongly
measurable on `ℝ × ℝ³` and `P`-periodic in the phase. -/
def BSDefined : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → IsWeakSolenoidal P Φ →
      AEStronglyMeasurable (bsPot Φ) volume ∧
        ∀ᵐ x : ℝ × Space, bsPot Φ (x.1 + P, x.2) = bsPot Φ x

/-- **BSGrad** (source 1351-1362): `bsPot Φ` has a weak `y`-gradient in `Y_2`
(`∂ⱼψ` is a Calderon-Zygmund transform of `Φ`, `L²` bounded). -/
def BSGrad : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → IsWeakSolenoidal P Φ →
      ∃ Dψ : Fin 3 → ℝ × Space → CVec3, ∀ j : Fin 3,
        UnforcedLeray.Short.IIb.IsInYr P 2 (Dψ j) ∧
          UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy j Θ) (bsPot Φ) (Dψ j)

/-- **BSCurl** (source 1351-1362): `curl (bsPot Φ) = Φ` weakly for weakly solenoidal `Φ ∈ Y_2`. -/
def BSCurl : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → IsWeakSolenoidal P Φ →
      UnforcedLeray.Short.IIb.HasPtwOp P curlT (bsPot Φ) Φ

/-- **BSSol** (source 1351-1362): `div (bsPot Φ) = 0` weakly (Coulomb gauge). -/
def BSSol : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → IsWeakSolenoidal P Φ →
      IsWeakSolenoidal P (bsPot Φ)

/-- **BSSlice** (source 1351-1362): for any weak `y`-gradient `Dψ ∈ Y_2` of `bsPot Φ`, a.e. phase
slice of `bsPot Φ` lies in `L⁶(ℝ³)` (Sobolev/HLS) and has slice weak gradient `Dψ j (τ, ·)`
(tested against `C_c^∞` scalar functions of `y`). -/
def BSSlice : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → IsWeakSolenoidal P Φ →
    ∀ Dψ : Fin 3 → ℝ × Space → CVec3,
      (∀ j : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (Dψ j) ∧
        UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy j Θ) (bsPot Φ) (Dψ j)) →
      ∀ᵐ τ : ℝ, MemLp (fun y : Space => bsPot Φ (τ, y)) 6 volume ∧
        ∀ j : Fin 3, MemLp (fun y : Space => Dψ j (τ, y)) 2 volume ∧
          ∀ φ : Space → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
            ∫ y : Space, (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) • bsPot Φ (τ, y)
              = -∫ y : Space, φ y • Dψ j (τ, y)

/-- **HardyR3** (source 1351-1362, Hardy inequality in `ℝ³`): if `u ∈ L⁶(ℝ³; ℂ³)` has weak
gradient `D ∈ L²`, then `∫ |u|²/|y|² ≤ 4 ∑ⱼ ∫ |Dⱼ|²`
(`C_c^∞` density and radial integration by parts). -/
def HardyR3 : Prop :=
  ∀ (u : Space → CVec3) (D : Fin 3 → Space → CVec3),
    MemLp u 6 volume → (∀ j, MemLp (D j) 2 volume) →
    (∀ (j : Fin 3) (φ : Space → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ y : Space, (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) • u y
        = -∫ y : Space, φ y • D j y) →
    ∫⁻ y : Space, ‖u y‖ₑ ^ 2 / ‖y‖ₑ ^ 2 ≤ 4 * ∑ j : Fin 3, ∫⁻ y : Space, ‖D j y‖ₑ ^ 2

/-- **BSHardyY2** (source 1351-1362): from the slice Hardy inequality, `ψ/|y| ∈ Y_2` for
`ψ = bsPot Φ` (integrate `HardyR3` over the period; measurability of `ψ/|y|`, periodicity from
`BSDefined`-type facts, finite norm from `∑ⱼ ‖Dψ j‖_{Y_2} < ∞`). -/
def BSHardyY2 : Prop :=
  HardyR3 → ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → IsWeakSolenoidal P Φ →
    AEStronglyMeasurable (bsPot Φ) volume →
    (∀ᵐ x : ℝ × Space, bsPot Φ (x.1 + P, x.2) = bsPot Φ x) →
    ∀ Dψ : Fin 3 → ℝ × Space → CVec3,
      (∀ j : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (Dψ j) ∧
        UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy j Θ) (bsPot Φ) (Dψ j)) →
      (∀ᵐ τ : ℝ, MemLp (fun y : Space => bsPot Φ (τ, y)) 6 volume ∧
        ∀ j : Fin 3, MemLp (fun y : Space => Dψ j (τ, y)) 2 volume ∧
          ∀ φ : Space → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
            ∫ y : Space, (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) • bsPot Φ (τ, y)
              = -∫ y : Space, φ y • Dψ j (τ, y)) →
      UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • bsPot Φ x)

end UnforcedLeray.Short.PartIIIb.Concrete
