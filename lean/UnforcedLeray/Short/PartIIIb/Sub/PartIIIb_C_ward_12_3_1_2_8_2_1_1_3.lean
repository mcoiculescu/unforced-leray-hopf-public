import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.ProjCommuteProps

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/3`: `SigmaDecay`

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  `σ = L0Tscal ν π` with `π = projPot Φ` (Newton potential of `-div Φ`,
`Φ` a phase test, compact in `y`).  Decomposition: (i) Newton decay of `π` and its spatial
derivatives up to order three (`PiDecay`, applied to `Φ` and to `∂_τΦ`); (ii) `∂_τ π = projPot ∂_τΦ`
(`ProjPotDtau`); (iii) periodicity of `π` (`ProjPotPeriodic`); (iv) the purely algebraic passage
from `π` to `σ` (`L0TscalSmooth`, `L0TscalPeriodic`, `L0TscalBound`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- `ψ = O((1+|y|)^a)` uniformly in the phase. -/
def Dec (a : ℝ) (ψ : ℝ × UnforcedLeray.Space → ℂ) : Prop :=
  ∃ C : ℝ, ∀ τ y, ‖ψ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ a

/-- Decay of a potential and its spatial derivatives: `ψ = O(|y|^{-2})`, `∂ψ = O(|y|^{-3})`,
`∂²ψ = O(|y|^{-4})`, `∂³ψ = O(|y|^{-5})`. -/
def PotDecay0 (ψ : ℝ × UnforcedLeray.Space → ℂ) : Prop :=
  Dec (-2) ψ ∧ (∀ j, Dec (-3) (dy j ψ)) ∧ (∀ j k, Dec (-4) (dy j (dy k ψ))) ∧
    ∀ i j k, Dec (-5) (dy i (dy j (dy k ψ)))

/-- `PotDecay0` plus the decay of the time derivative: `∂_τψ = O(|y|^{-2})`,
`∇∂_τψ = O(|y|^{-3})`. -/
def PotDecay (ψ : ℝ × UnforcedLeray.Space → ℂ) : Prop :=
  PotDecay0 ψ ∧ Dec (-2) (dτ ψ) ∧ ∀ j, Dec (-3) (dy j (dτ ψ))

/-- **(i) Newton decay.**  For a phase test `Ψ` (smooth, `P`-periodic, `y`-compact), the Newton
potential `π = projPot Ψ` of `-div Ψ` (zero mean, since `Ψ` has compact support) satisfies
`π = O(|y|^{-2})` and each spatial derivative gains a power, uniformly in `τ` (periodicity and
compactness in `τ ∈ [0,P]`; for `|y|` beyond the support, `∂^α π = ∫ ∂^α∇N(y-x)·Ψ(τ,x)dx`, expand
the kernel to first order using `∫ Ψ`-moment structure of `div`).  Library:
`exists_uniform_projectedPotentialReCutoffShell_powWeight_bound` and
`exists_uniform_projectedNewtonCorrectionCutoffShell_powWeight_bound` (Cons/L2/BackgroundConcrete). -/
def PiDecay : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Ψ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest P Ψ →
    PotDecay0 (projPot Ψ)

/-- **(ii)** `∂_τ` commutes with the Newton convolution: `∂_τ (projPot Φ) = projPot (∂_τ Φ)`
(differentiation under the integral sign, `Φ` smooth with compact `y`-support). -/
def ProjPotDtau : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest P Φ →
    dτ (projPot Φ) = projPot (dτ Φ)

/-- **(iii)** `projPot Φ (τ+P, y) = projPot Φ (τ, y)` for a `P`-periodic phase test
(`projectedPotentialRePath_periodic_joint` and the `Im` analogue,
`Cons/L2/BackgroundConcrete/SelectedProjectedPotentialPathSmooth`). -/
def ProjPotPeriodic : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest P Φ →
    ∀ τ y, projPot Φ (τ + P, y) = projPot Φ (τ, y)

/-- **(iv-a)** `L0Tscal ν ψ` is smooth for smooth `ψ`. -/
def L0TscalSmooth : Prop :=
  ∀ (ν : ℝ) (ψ : ℝ × UnforcedLeray.Space → ℂ), ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ (L0Tscal ν ψ)

/-- **(iv-b)** `L0Tscal ν ψ` is `P`-periodic if the smooth `ψ` is
(`dτ`, `radialT`, `lapT` preserve `P`-periodicity in `τ`). -/
def L0TscalPeriodic : Prop :=
  ∀ (P : ℝ) (ν : ℝ) (ψ : ℝ × UnforcedLeray.Space → ℂ), ContDiff ℝ ∞ ψ →
    (∀ τ y, ψ (τ + P, y) = ψ (τ, y)) → ∀ τ y, L0Tscal ν ψ (τ + P, y) = L0Tscal ν ψ (τ, y)

/-- **(iv-c)** The algebra `σ = -∂_τψ + ½ y·∇ψ + ½ψ - νΔψ`: from `PotDecay ψ`,
`|σ| ≤ |∂_τψ| + ½|y||∇ψ| + ½|ψ| + ν|Δψ| ≲ (1+|y|)^{-2}` and
`∇σ = -∇∂_τψ + ∇ψ + ½ y·∇²ψ - ν∇Δψ`-type terms `≲ (1+|y|)^{-3}`
(`∂ₖ(y·∇ψ) = ∂ₖψ + y·∇∂ₖψ`, `|y| ≤ 1+|y|`; `∂ₖ` commutes with `Δ`, `∂_τ`). -/
def L0TscalBound : Prop :=
  ∀ (ν : ℝ) (ψ : ℝ × UnforcedLeray.Space → ℂ), ContDiff ℝ ∞ ψ → PotDecay ψ →
    ∃ C : ℝ, ∀ τ y, ‖L0Tscal ν ψ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) ∧
      ‖gradT (L0Tscal ν ψ) (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-3 : ℝ)

theorem sigmaDecay_of (h1 : PiDecay) (h2 : ProjPotDtau) (h3 : ProjPotPeriodic)
    (h4 : L0TscalSmooth) (h5 : L0TscalPeriodic) (h6 : L0TscalBound) : SigmaDecay := by
  intro P _ ν Φ hΦ
  have hsm := contDiff_projPot hΦ
  have hdt : PotDecay (projPot Φ) := by
    refine ⟨h1 P Φ hΦ, ?_, ?_⟩
    · rw [h2 P Φ hΦ]; exact (h1 P _ hΦ.dτ).1
    · intro j; rw [h2 P Φ hΦ]; exact (h1 P _ hΦ.dτ).2.1 j
  exact ⟨h4 ν _ hsm, h5 P ν _ hsm (h3 P Φ hΦ), h6 ν _ hsm hdt⟩

end UnforcedLeray.Short.PartIIIb.Concrete
