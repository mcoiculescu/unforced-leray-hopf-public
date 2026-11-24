import UnforcedLeray.Short.PartIIb.Bridge.FieldModel
import UnforcedLeray.Units.B0414.Orthogonal

/-!
# `PartII-b:T10/org/2` (`SolSeparation`): decomposition

Source `the November 2 reference manuscript` 1409-1412, 1498-1500: a solenoidal
`s ∈ Y_q` (`1 < q < ∞`) orthogonal to all solenoidal phase tests has, for a.e. phase, a spatial slice
that is a solenoidal `L^q` field orthogonal to all smooth compactly supported solenoidal fields, hence
zero (Leray projection + density of compactly supported solenoidal fields in `L^{q'}_σ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0414

/-- A smooth compactly supported spatially solenoidal complex test field `Ψ : ℝ³ → ℂ³`. -/
def SpatialSolTest (Ψ : Space → CVec3) : Prop :=
  ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧
    ∀ y : Space, ∑ j : Fin 3, fderiv ℝ Ψ y (EuclideanSpace.single j (1 : ℝ)) j = 0

/-- **Slices of a phase-solenoidal field are solenoidal** (a.e. phase).  Test `⟪∇(χ ⊗ φ), s⟫ = 0` with
`χ` ranging over a countable Fourier family of the phase circle and `φ` over a countable dense family of
scalar spatial tests; fundamental lemma on `AddCircle P` (cf. `B0411.eq_zero_of_forall_phasePair`
proof, `ae_eq_zero_of_fourier`). -/
def SolSepSliceSol : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (P : ℝ) [Fact (0 < P)] (s : Yq P q), IsPhaseSolenoidal s →
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), IsSolenoidalC (s τ : Space → CVec3)

/-- **Slices are orthogonal to the compactly supported solenoidal fields** (a.e. phase): from
`⟪χ ⊗ Ψ, s⟫ = 0` for `χ` in a countable Fourier family and `Ψ` in a countable `C¹`-dense family of
`SpatialSolTest`s (separability of `C_c^∞` solenoidal fields in the `C^1_c` topology), plus continuity of
`Ψ ↦ ∫ Ψ·s(τ)` in `L^{q'}`-norm to pass from the countable family to all `Ψ`. -/
def SolSepSliceOrth : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (P : ℝ) [Fact (0 < P)] (s : Yq P q),
    (∀ Φ : ℝ × Space → CVec3, Cons.C03.Concrete.IsSolTest P Φ → phasePair P q Φ s = 0) →
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      ∀ Ψ : Space → CVec3, SpatialSolTest Ψ → ∫ y, dotL (Ψ y) ((s τ : Space → CVec3) y) = 0

/-- **Spatial nondegeneracy** (`1 < q < ∞`): a solenoidal `w ∈ L^q(ℝ³;ℂ³)` orthogonal to all smooth
compactly supported solenoidal fields vanishes (`w = 𝐏w`, symmetry of `𝐏`, density of `SpatialSolTest`
in `L^{q'}_σ`, SP 1409-1412). -/
def SolSepSpatial : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ w : Lp CVec3 q (volume : Measure Space),
    IsSolenoidalC (w : Space → CVec3) →
    (∀ Ψ : Space → CVec3, SpatialSolTest Ψ → ∫ y, dotL (Ψ y) (w y) = 0) → w = 0

theorem solSeparation_of (h1 : SolSepSliceSol) (h2 : SolSepSliceOrth) (h3 : SolSepSpatial) :
    UnforcedLeray.Short.IIb.SolSeparation := by
  intro q _ hq1 hq P _ s hsol horth
  have a1 := h1 q P s hsol
  have a2 := h2 q P s horth
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [a1, a2] with τ b1 b2
  rw [Pi.zero_apply]
  exact h3 q hq1 hq (s τ) b1 b2

end UnforcedLeray.Short.IIb
