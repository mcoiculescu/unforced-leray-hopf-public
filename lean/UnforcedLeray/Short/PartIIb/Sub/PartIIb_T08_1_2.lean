import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1

/-!
# Part II-b, task `PartII-b:T08/1/2`: `DriftSmoothPt` from three physical-space leaves

Source of record: `the November 2 reference manuscript`, lines 1912-1915
(`𝒯(√s b) = √s (S + 1/2) b`, `𝒯 = ∂_τ - y·∇/2`).

For a nice profile `b` (smooth, `c`-periodic in `q`, supported in `s₀ ≤ s ≤ s₁`, `|η| ≤ L`),
the ring lift `u = N_v b` is a smooth, `P`-periodic field with bounded `y`-support, away from the
axis.  The drift identity then splits as a pointwise transport identity
(`NvCDriftPtw`, a chain-rule computation) and a phase-space integration by parts
(`DriftIBP`, valid for every such `u`).

Proved here: `driftSmoothPt_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- **Leaf `T08/1/2/1`**: for nice `b`, `u = N_v b` is a phase test (smooth, `2εc`-periodic in `τ`,
bounded `y`-support).  Proof: `NiceProf` forces `s ∈ [s₀, s₁]`, `|η| ≤ L` on the support, i.e.
`y` stays in a compact set off the axis, where `age`, `phase`, `trans`, `frameL` are smooth
(`Lib/Axisymmetric/RingChart.lean`, `Lib/AxisymmetricB/Lift.lean`); periodicity in `τ` is
`phase R (τ + 2c/R) y = phase R τ y + c` together with `b ∘ qShift c = b`. -/
def NvCNicePhaseTest : Prop :=
  ∀ (c ε : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b →
    IsPhaseTest (2 * ε * c) (NvC ε⁻¹ b)

/-- **Leaf `T08/1/2/2`** (SP 1912-1915): pointwise drift identity
`(∂_τ - ½ y·∇) N_v b = N_v (s ∂_s b + b/2)` for nice `b` (chain rule in the chart
`(τ,y) ↦ (s,q,η)` of `Axi.chart`; the `1/2` comes from `√s`; off the axis, and both sides vanish
near the axis). -/
def NvCDriftPtw : Prop :=
  ∀ (c ε : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b → ∀ p : ℝ × Space,
    dτ (NvC ε⁻¹ b) p - (1 / 2 : ℝ) • radialT (NvC ε⁻¹ b) p =
      NvC ε⁻¹ (fun x => x.1 • fderiv ℝ b x (cdir 0) + (1 / 2 : ℂ) • b x) p

/-- **Leaf `T08/1/2/3`**: integration by parts for the drift transpose against a phase test:
`⟪𝒯ᵗΦ, u⟫ = ⟪Φ, ∂_τ u - ½ y·∇u⟫` (periodicity in `τ`, `div y = 3`, compact `y`-support). -/
def DriftIBP : Prop :=
  ∀ (P : ℝ) (Φ u : ℝ × Space → CVec3), 0 < P → IsPhaseTest P Φ → IsPhaseTest P u →
    pairF P (driftT Φ) u = pairF P Φ (fun p => dτ u p - (1 / 2 : ℝ) • radialT u p)

theorem driftSmoothPt_of (h1 : NvCNicePhaseTest) (h2 : NvCDriftPtw) (h3 : DriftIBP) :
    DriftSmoothPt := by
  intro c ε b Φ hc hε hb hΦ
  have hP : 0 < 2 * ε * c := by positivity
  rw [h3 _ Φ _ hP hΦ (h1 c ε b hc hε hb)]
  congr 1
  funext p
  exact h2 c ε b hc hε hb p

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.driftSmoothPt_of
