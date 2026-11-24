import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1

/-!
# `adjSliceLap`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Per-test step (product test `φ(t)θ(y)`, Fubini, periodic zero lemma) followed by the countable
dense family of tests in the `L²` data `(θ, Δθ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The slice defect `F_θ(t) = ν ∫ Φ(t,y)·Δθ - ∫ a(t,y)·θ`. -/
def sliceDefect (ν : ℝ) (Φ a : ℝ × Space → CVec3) (θ : Space → CVec3) (t : ℝ) : ℂ :=
  (ν : ℂ) * (∫ y : Space, ∑ i : Fin 3, Φ (t, y) i * lapS θ y i)
    - ∫ y : Space, ∑ i : Fin 3, a (t, y) i * θ y i

/-- (L1) Source 1351-1362: testing `HasPtwOp P (nuLapT ν) Φ a` with `φ(t)θ(y)` (smooth periodic `φ`,
smooth compactly supported `θ`; then `lapT (φθ) = φ lapS θ`) and Fubini gives
`∫_{(0,P]} φ F_θ = 0`. -/
def SliceProdPairing : Prop :=
  ∀ (P ν : ℝ), 0 < P → ∀ Φ a : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 a →
    UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) Φ a →
      ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → (∀ t, φ (t + P) = φ t) →
          ∫ t in Ioc (0 : ℝ) P, φ t * sliceDefect ν Φ a θ t = 0

/-- (L2) `F_θ` is locally integrable and a.e. `P`-periodic (Fubini with `locInt_of_isInYr` and
the a.e. periodicity of `Φ, a`). -/
def SliceDefectLocPer : Prop :=
  ∀ (P ν : ℝ), 0 < P → ∀ Φ a : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 a →
      ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        LocallyIntegrable (sliceDefect ν Φ a θ) volume ∧
          ∀ᵐ t : ℝ, sliceDefect ν Φ a θ (t + P) = sliceDefect ν Φ a θ t

/-- (L3) Periodic zero lemma (periodize compactly supported smooth tests;
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
def PeriodicZero : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ F : ℝ → ℂ, LocallyIntegrable F volume → (∀ᵐ t : ℝ, F (t + P) = F t) →
    (∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → (∀ t, φ (t + P) = φ t) →
      ∫ t in Ioc (0 : ℝ) P, φ t * F t = 0) → F =ᵐ[volume] 0

/-- (L4) From each test to all tests at a.e. phase (source 1351-1362): `Λ_τ(θ) = sliceDefect`
is continuous in the `L²` data `(θ, Δθ)` when `Φ(τ), a(τ) ∈ L²` (a.e. `τ` by `IsInYr P 2`);
take a countable dense family of the data (separable `L²×L²`), as in
`Blueprint.ModeId.ae_forall_tests` (Loc/Hyp/ModeIdentification/Slices.lean:173). -/
def SliceCountableTests : Prop :=
  ∀ (P ν : ℝ), 0 < P → ∀ Φ a : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 a →
    (∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ∀ᵐ τ : ℝ, sliceDefect ν Φ a θ τ = 0) →
      ∀ᵐ τ : ℝ, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        sliceDefect ν Φ a θ τ = 0

theorem adjSliceLap_of (h1 : SliceProdPairing) (h2 : SliceDefectLocPer) (h3 : PeriodicZero)
    (h4 : SliceCountableTests) : AdjSliceLap := by
  intro P ν hP Φ a hΦ ha hop
  have hall := h4 P ν hP Φ a hΦ ha (fun θ hθ hc => by
    obtain ⟨hl, hper⟩ := h2 P ν hP Φ a hΦ ha θ hθ hc
    exact h3 P hP _ hl hper (fun φ hφ hpφ => h1 P ν hP Φ a hΦ ha hop θ hθ hc φ hφ hpφ))
  filter_upwards [hall] with τ hτ θ hθ hc
  have := hτ θ hθ hc
  unfold sliceDefect at this
  have h := sub_eq_zero.mp this
  exact_mod_cast h

end UnforcedLeray.Short.PartIIIb.Concrete
