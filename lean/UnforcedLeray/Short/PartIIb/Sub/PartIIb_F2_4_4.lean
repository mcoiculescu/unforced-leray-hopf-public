import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2

/-!
# `PartII-b:F2/4/4` (`Sub/PartII-b_F2_4_4.lean`): joint strong continuity of the frozen radial
transport

Source of record: `the November 2 reference manuscript` (SP), lines 841-852
("The free transport is `T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)`"), 931-953 (the frozen scalings
`a = 1 + σ`, `Ω_a`), 2104-2115 ("The frozen radial transport is unitary in this radial weighted
space"), 2141-2150 (the compact-Duhamel comparison on blocks of length `L` at the slow age
`σ = νt`).

The compact-Duhamel comparison of the blocks (`PartII-b:F2/4/3`, through
`UnforcedLeray.Short.IIb.RCDuhamel.real_compact_duhamel_window` in
`Short/PartII-b/Org/RealCompactDuhamel.lean`) compares the lifted cylinder evolution with the
frozen planar evolution at a limiting slow age `σ*`, and the collective compactness of the frozen
Duhamel terms (`PartII-b:F2/4/2`) takes images of compact sets under `T_pl σ τ` for all
`σ ∈ [0, Sig]`. Both use that the frozen radial transport depends continuously on the slow age, the
time and the datum together. This is not a field of `IsFrozenRadialTransport`; it follows from the
`flow` field (`T_pl σ τ f = f ∘ frozenRadialFlow σ τ` a.e.), the continuity of `frozenOmega` in
`(σ, x)` for `σ ≥ 0`, the invariance of `|x|` under the flow, and the `isometry` field.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

/-- **Joint strong continuity of the frozen radial transport** (SP 841-852, 931-953, 2104-2115,
2141-2150): for `m > 8`, `Sig > 0` and the frozen planar radial transport group `T_pl` at the slow
ages `σ ∈ [0, Sig]` (`IsFrozenRadialTransport m Sig T_pl`), the map
`(σ, τ, f) ↦ T_pl σ τ f` is continuous on `[0, Sig] × ℝ × X_m`.

Proof route: for `g` continuous with compact support in a ball `B_R`, `T_pl σ τ g = g ∘ Φ_{σ,τ}`
a.e. with `Φ_{σ,τ} = frozenRadialFlow σ τ` a rotation of each circle `|x| = r` by the angle
`-τ Ω_{1+σ}(x)`, so `g ∘ Φ_{σ,τ}` is supported in `B_R` and depends continuously on `(σ, τ)`
uniformly on `B_R`; dominated convergence (bound `sup|g| · 1_{B_R}`, `planeMeasure m` finite on
balls) gives continuity in `X_m`. Continuous compactly supported functions are dense in
`X_m = L²(planeMeasure m)`, and `‖T_pl σ τ h‖ = ‖h‖` makes the family equicontinuous in the
datum, which gives joint continuity in `(σ, τ, f)`. -/
def FrozenTransportJointCont : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sig : ℝ, 0 < Sig →
  ∀ T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m), IsFrozenRadialTransport m Sig T_pl →
    ContinuousOn (fun q : ℝ × ℝ × Xm m => T_pl q.1 q.2.1 q.2.2) (Icc 0 Sig ×ˢ univ)

end UnforcedLeray.Short.IIb
