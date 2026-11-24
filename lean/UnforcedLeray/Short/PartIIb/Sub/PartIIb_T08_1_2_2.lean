import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2

/-!
# Part II-b, task `PartII-b:T08/1/2/2`: `NvCDriftPtw` split into off-axis chain rule and on-axis vanishing

Source `the November 2 reference manuscript`, lines 1912-1915.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- **Leaf `T08/1/2/2/1`** (SP 1912-1915): the chain-rule identity off the axis,
`(∂_τ - ½ y·∇) N_v b = N_v (s ∂_s b + b/2)` at `(τ,y)` with `y ∉ axis`, in the chart
`(τ,y) ↦ (age, phase, trans)` (`∂_τ phase = R/2`, `y·∇ age = -2 age`, `y·∇ phase = -R`,
`trans` of degree 0, `frameL` dilation invariant, `√age` supplies the `1/2`). -/
def NvCDriftOffAxis : Prop :=
  ∀ (c ε : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b → ∀ p : ℝ × Space,
    p.2 ∉ Axi.axis →
    dτ (NvC ε⁻¹ b) p - (1 / 2 : ℝ) • radialT (NvC ε⁻¹ b) p =
      NvC ε⁻¹ (fun x => x.1 • fderiv ℝ b x (cdir 0) + (1 / 2 : ℂ) • b x) p

/-- **Leaf `T08/1/2/2/2`**: on the axis (a closed set) both sides vanish near the axis since
`NiceProf` forces `s ∈ [s₀, s₁]` (so `N_v b` and `N_v (s ∂_s b + b/2)` vanish on a neighbourhood of
the axis), hence also all derivatives of `N_v b` there. -/
def NvCDriftOnAxis : Prop :=
  ∀ (c ε : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b → ∀ p : ℝ × Space,
    p.2 ∈ Axi.axis →
    dτ (NvC ε⁻¹ b) p - (1 / 2 : ℝ) • radialT (NvC ε⁻¹ b) p =
      NvC ε⁻¹ (fun x => x.1 • fderiv ℝ b x (cdir 0) + (1 / 2 : ℂ) • b x) p

theorem nvCDriftPtw_of (h1 : NvCDriftOffAxis) (h2 : NvCDriftOnAxis) : NvCDriftPtw := by
  intro c ε b hc hε hb p
  by_cases hp : p.2 ∈ Axi.axis
  · exact h2 c ε b hc hε hb p hp
  · exact h1 c ε b hc hε hb p hp

end UnforcedLeray.Short.IIb
