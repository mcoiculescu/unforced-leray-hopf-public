import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3

/-!
# Lemma statements for `PhaseSliceWeakGrad`

Source `the November 2 reference manuscript` lines 1351-1362 and 1334-1337.
Each `Prop` is a step of the Fubini / fundamental-lemma / density argument described in
`Sub/PartIII-b_IIIb-D2_1_3_1_2_1_2_6_3.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt)
open UnforcedLeray.Short.IIb (IsInYr HasPtwOp)

/-- `bsPot Φ` is a.e. strongly measurable and a.e. `P`-periodic (the content of `BSDefined`, which
does not use solenoidality). -/
def PotMeasPeriodic : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3, IsInYr P 2 Φ →
    AEStronglyMeasurable (bsPot Φ) volume ∧
      ∀ᵐ x : ℝ × Space, bsPot Φ (x.1 + P, x.2) = bsPot Φ x

/-- `bsPot Φ` is integrable on `[0,P] × B_R` (kernel bound `|K(w)| = 1/(4π|w|²)`, Hölder against
`(1+|z|²)⁻¹ ∈ L²`). -/
def PotLocIntCell : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3, IsInYr P 2 Φ → ∀ R : ℝ,
    IntegrableOn (bsPot Φ) (Ioc 0 P ×ˢ closedBall (0 : Space) R) volume

/-- A phase `L²` field is integrable on `[0,P] × B_R`. -/
def YrLocIntCell : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Ψ : ℝ × Space → CVec3, IsInYr P 2 Ψ → ∀ R : ℝ,
    IntegrableOn Ψ (Ioc 0 P ×ˢ closedBall (0 : Space) R) volume

/-- A smooth function supported in `(0,P)` extends to a smooth `P`-periodic function. -/
def PeriodicBump : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ s0 : ℝ → ℂ, ContDiff ℝ ∞ s0 → HasCompactSupport s0 →
    tsupport s0 ⊆ Ioo 0 P →
    ∃ s : ℝ → ℂ, ContDiff ℝ ∞ s ∧ (∀ t, s (t + P) = s t) ∧ ∀ t ∈ Ioc 0 P, s t = s0 t

/-- A property true a.e. on one period and a.e. invariant under the shift `t ↦ t + P` holds a.e. on
the line. -/
def AePeriodicExtend : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Q : ℝ → Prop,
    (∀ᵐ t ∂(volume.restrict (Ioc 0 P)), Q t) → (∀ᵐ t : ℝ, Q (t + P) ↔ Q t) → ∀ᵐ t : ℝ, Q t

/-- The product test `s(t) g(y) eᵢ` is a phase test for smooth periodic `s`, `g ∈ C_c^∞`. -/
def ProdTestPhase : Prop :=
  ∀ (P : ℝ) (s : ℝ → ℂ) (g : Space → ℂ) (i : Fin 3), ContDiff ℝ ∞ s → (∀ t, s (t + P) = s t) →
    SmoothCS g → UnforcedLeray.PhaseSpace.IsPhaseTest P (prodTest s g i)

/-- Pairings of the product test with a field `f`, written as iterated integrals. -/
def PairFProd : Prop :=
  ∀ (P : ℝ) (s : ℝ → ℂ) (g : Space → ℂ) (j i : Fin 3), ContDiff ℝ ∞ s → SmoothCS g →
    ∀ f : ℝ × Space → CVec3,
      pairF P (-dy j (prodTest s g i)) f =
        -(P⁻¹ • ∫ t in Ioc 0 P, s t *
          ∫ y : Space, fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) * f (t, y) i) ∧
      pairF P (prodTest s g i) f = P⁻¹ • ∫ t in Ioc 0 P, s t * ∫ y : Space, g y * f (t, y) i

/-- Fubini: `∫ h(y) f(t,y) dy` is integrable in `t` for `f` integrable on `[0,P] × B_R` and
continuous `h` vanishing outside `B_R`. -/
def CellIntegrable : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (f : ℝ × Space → ℂ) (R : ℝ),
    IntegrableOn f (Ioc 0 P ×ˢ closedBall (0 : Space) R) volume →
    ∀ h : Space → ℂ, Continuous h → (∀ y : Space, R < ‖y‖ → h y = 0) →
      IntegrableOn (fun t : ℝ => ∫ y : Space, h y * f (t, y)) (Ioc 0 P) volume

end UnforcedLeray.Short.PartIIIb.Concrete
