import UnforcedLeray.Short.PartIIa.Sub.N02_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.
Target: `PartialDerivSlice` (`Sub/N02_2.lean`): for a `C^∞` profile `F : Profile → ℂ`, the profile
partial derivatives `pdS`, `pdQ`, `pdEta` (`fderiv ℝ F p (1,0,0)` and so on, `StatementsNear.lean`)
equal the ordinary derivatives of the coordinate slices `t ↦ F(t,q,η)`, `t ↦ F(s,t,η)`,
`t ↦ F(s,q,t)`.

Helpers (prefix `pds`): the chain rule along a line `γ` with `HasDerivAt γ v x`, and the three
coordinate lines with their derivative vectors `(1,0,0)`, `(0,1,0)`, `(0,0,1)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Chain rule along a line: if `F` is differentiable and `γ` has derivative `v` at `x`, then
`t ↦ F (γ t)` has derivative `fderiv ℝ F (γ x) v` at `x`. -/
theorem pdsSlice_hasDerivAt {F : Profile → ℂ} (hF : Differentiable ℝ F) {γ : ℝ → Profile}
    {v : Profile} {x : ℝ} (hγ : HasDerivAt γ v x) :
    HasDerivAt (fun t => F (γ t)) (fderiv ℝ F (γ x) v) x :=
  (hF (γ x)).hasFDerivAt.comp_hasDerivAt x hγ

/-- The `s`-line `t ↦ (t, q, η)` has derivative `(1, 0, 0)`. -/
theorem pdsLineS (q η s : ℝ) :
    HasDerivAt (fun t : ℝ => ((t, q, η) : Profile)) ((1, 0, 0) : Profile) s :=
  (hasDerivAt_id' s).prodMk ((hasDerivAt_const s q).prodMk (hasDerivAt_const s η))

/-- The `q`-line `t ↦ (s, t, η)` has derivative `(0, 1, 0)`. -/
theorem pdsLineQ (s η q : ℝ) :
    HasDerivAt (fun t : ℝ => ((s, t, η) : Profile)) ((0, 1, 0) : Profile) q :=
  (hasDerivAt_const q s).prodMk ((hasDerivAt_id' q).prodMk (hasDerivAt_const q η))

/-- The `η`-line `t ↦ (s, q, t)` has derivative `(0, 0, 1)`. -/
theorem pdsLineEta (s q η : ℝ) :
    HasDerivAt (fun t : ℝ => ((s, q, t) : Profile)) ((0, 0, 1) : Profile) η :=
  (hasDerivAt_const η s).prodMk ((hasDerivAt_const η q).prodMk (hasDerivAt_id' η))

/-- **Target `PartII-a:N02/2/9`**: `PartialDerivSlice`, the profile partial derivatives of a `C^∞`
profile are the derivatives of its coordinate slices. -/
theorem partialDerivSlice : UnforcedLeray.Short.PartIIa.PartialDerivSlice := by
  intro F hF s q η
  have hd : Differentiable ℝ F := hF.differentiable (by simp)
  refine ⟨?_, ?_, ?_⟩
  · exact (pdsSlice_hasDerivAt hd (pdsLineS q η s)).deriv.symm
  · exact (pdsSlice_hasDerivAt hd (pdsLineQ s η q)).deriv.symm
  · exact (pdsSlice_hasDerivAt hd (pdsLineEta s q η)).deriv.symm

end UnforcedLeray.Short.PartIIa
