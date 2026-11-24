import UnforcedLeray.Short.PartIIb.StatementsNonlinear

/-!
# The exact background of a level is the contraction-ball solution (source 2505-2524, 2664-2713)

Source of record: `the November 2 reference manuscript` (73 pages).

Part of `ORG:return-concrete/instance-3/background-facts`.

The exact background of the return (source 2664-2672: `U = V + r_b`, `V = U_raw + E_ε α_bg`,
`r_b` the energy repair) is *the* background constructed in `short-bg:result` (2505-2524): the
state `z = (w, A)` is the fixed point of the contraction on the ball of radius
`2Mδ = 𝒫_ν e^{m/ν} ε^{3/11}` (2507-2512), so
`‖w‖_{X_p} + R^{8/11}|α| = ‖z‖_Z ≤ 𝒫_ν e^{m/ν} ε^{3/11}` (2516-2520), and `ρ_b` is "a fixed upper
bound from the exact-background construction" (2706-2711).  `IsBallSplit p ρ V r_b` records this:
the split is `V = U_raw + Σᵢ αᵢ E_i`, `r_b = w` for a solution `z` of the projected equation
(`IIb.ProjectedEquation`, 2519-2524) with `‖z‖_Z ≤ ρ`.

`IIb.ExactSplitII` (`Short/PartII-b/ExactSplit.lean:39`) records the same split with the bounds
`|αᵢ| ≤ ρ_b` and `sup_τ(‖r_b‖_{11/4} + ‖r_b‖_∞) ≤ ρ_b`, but not `‖z‖_Z ≤ ρ_b`; without it the
regularity of `short-bg:strong` (2525-2562, `IIb.StrongRegularity`, stated for the solutions in
the contraction ball) does not apply, so the symmetry of `U` and the `W^{1,∞}` bound of
`U - U_raw` used in the return (2031, 2522-2523, 4144-4145, 5007-5008, 5094) need this datum.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **The split `(V, r_b)` is the contraction-ball background** (source 2505-2524, 2664-2672,
2706-2711): there is a state `z = (w, A)` solving the projected equation
`𝔓F_R + 𝓛z + 𝒬(z, z) = 0` (`IIb.ProjectedEquation`, 2519-2524) with
`V = U_raw + Σᵢ αᵢ E_i` (`α = coord z`), `r_b = w` (`corr z`) and `‖z‖_Z ≤ ρ`
(`short-bg:result`, 2516-2520). -/
def IsBallSplit (p : Params) (ρ : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField) : Prop :=
  ∃ z : p.Z, UnforcedLeray.Short.IIb.ProjectedEquation p z ∧
    (∀ τ y, V τ y = p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y) ∧
    rb = p.corr z ∧ ‖z‖ ≤ ρ

/-- On a ball split, `V + r_b` is the background field `U_raw + E_εα + w` of the state
(`IIb.bgField`, source 2519-2524). -/
theorem isBallSplit_bgField {p : Params} {V rb : ℝ → UnforcedLeray.SpatialField} {z : p.Z}
    (hV : ∀ τ y, V τ y = p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y)
    (hrb : rb = p.corr z) (τ : ℝ) :
    (fun y => V τ y + rb τ y) = UnforcedLeray.Short.IIb.bgField p z τ := by
  funext y
  rw [hV, hrb]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
