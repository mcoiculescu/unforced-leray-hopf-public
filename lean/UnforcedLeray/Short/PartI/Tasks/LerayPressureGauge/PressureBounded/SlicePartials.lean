import UnforcedLeray.Short.PartI.Sub.T02_2_3

/-!
# Part I, task `PartI:T02/2/3`, leaf `pbSlicePartials`: slice partials of a jointly smooth family

Source of record: `the November 2 reference manuscript`, line 447 (the decaying
pressure gauge is used here).  Target `pbSlicePartials : PbSlicePartials` (definition in
`Sub/T02_2_3.lean`): if `(σ, z) ↦ F σ z` is `C^∞` on `[0,T] × ℝ²`, then so are
`(σ, z) ↦ ∂_q (F σ) z` and `(σ, z) ↦ ∂_η (F σ) z`.

Proof.  Let `S = [0,T] × ℝ²` and `H (σ, z) = F σ z`.  `S` is `UniqueDiffOn` (`UniqueDiffOn.prod`).
For `(σ, z) ∈ S` the slice partial `∂_q (F σ) z` is the within-`S` derivative of `H` in the direction
`(0,(1,0))`, because the path `q ↦ (σ, (q, z₂))` stays in `S` (`pbSP_within_pQ`, as in
`within_pQ` of `Tasks/LerayPressureGauge/PressurePoisson.lean`); likewise `∂_η` with `(0,(0,1))`.
By `contDiffOn_infty_iff_fderivWithin` the map `x ↦ fderivWithin H S x` is `C^∞` on `S`; composing
with a constant vector (`ContDiffOn.clm_apply`) and using `ContDiffOn.congr` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- The product `[0,T] × ℝ²` is a set of unique differentiability for `0 < T`. -/
theorem pbSP_uniq {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

/-- The `q`-partial of a slice is the within-`[0,T] × ℝ²` derivative in direction `(0,(1,0))`. -/
theorem pbSP_within_pQ {K : ℝ × Plane → ℝ} {T : ℝ}
    (hK : ContDiffOn ℝ ∞ K (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    {t : ℝ} {z : Plane} (hx : (t, z) ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :
    Cyl.partialQ (fun w => K (t, w)) z =
      fderivWithin ℝ K (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) (t, z)
        ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
  have hxt : t ∈ Icc (0 : ℝ) T := (Set.mem_prod.mp hx).1
  have hd : DifferentiableWithinAt ℝ K (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) (t, z) :=
    (hK.differentiableOn (by simp)) _ hx
  have hF := hd.hasFDerivWithinAt
  have hpath : HasDerivAt (fun q : ℝ => ((t, (q, z.2)) : ℝ × Plane))
      ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) z.1 :=
    (hasDerivAt_const z.1 t).prodMk ((hasDerivAt_id' z.1).prodMk (hasDerivAt_const z.1 z.2))
  have hmaps : MapsTo (fun q : ℝ => ((t, (q, z.2)) : ℝ × Plane)) univ
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    fun q _ => ⟨hxt, mem_univ _⟩
  have hc := hF.comp_hasDerivWithinAt z.1 hpath.hasDerivWithinAt hmaps
  exact (hasDerivWithinAt_univ.mp hc).deriv

/-- The `η`-partial of a slice is the within-`[0,T] × ℝ²` derivative in direction `(0,(0,1))`. -/
theorem pbSP_within_pE {K : ℝ × Plane → ℝ} {T : ℝ}
    (hK : ContDiffOn ℝ ∞ K (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    {t : ℝ} {z : Plane} (hx : (t, z) ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :
    Cyl.partialEta (fun w => K (t, w)) z =
      fderivWithin ℝ K (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) (t, z)
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
  have hxt : t ∈ Icc (0 : ℝ) T := (Set.mem_prod.mp hx).1
  have hd : DifferentiableWithinAt ℝ K (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) (t, z) :=
    (hK.differentiableOn (by simp)) _ hx
  have hF := hd.hasFDerivWithinAt
  have hpath : HasDerivAt (fun q : ℝ => ((t, (z.1, q)) : ℝ × Plane))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) z.2 :=
    (hasDerivAt_const z.2 t).prodMk ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id' z.2))
  have hmaps : MapsTo (fun q : ℝ => ((t, (z.1, q)) : ℝ × Plane)) univ
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    fun q _ => ⟨hxt, mem_univ _⟩
  have hc := hF.comp_hasDerivWithinAt z.2 hpath.hasDerivWithinAt hmaps
  exact (hasDerivWithinAt_univ.mp hc).deriv

/-- **Slice partials** (leaf of `PbTimeAvgSmooth` and `PbMomentumIntegrated`, source line 447):
if `(σ, z) ↦ F σ z` is `C^∞` on `[0,T] × ℝ²`, then so are `(σ, z) ↦ ∂_q (F σ) z` and
`(σ, z) ↦ ∂_η (F σ) z`.  Proof: `x ↦ fderivWithin H S x` is `C^∞` on `S = [0,T] × ℝ²`
(`contDiffOn_infty_iff_fderivWithin`), its values on the constant vectors `(0,(1,0))`, `(0,(0,1))`
are `C^∞` (`ContDiffOn.clm_apply`), and they agree with the slice partials on `S`
(`pbSP_within_pQ`, `pbSP_within_pE`, via `ContDiffOn.congr`). -/
theorem pbSlicePartials : PbSlicePartials := by
  intro T F hT hF
  have hD := ((contDiffOn_infty_iff_fderivWithin (pbSP_uniq hT)).1 hF).2
  constructor
  · refine (hD.clm_apply (contDiffOn_const (c := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))))).congr ?_
    rintro ⟨σ, z⟩ hx
    exact pbSP_within_pQ hF hx
  · refine (hD.clm_apply (contDiffOn_const (c := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))).congr ?_
    rintro ⟨σ, z⟩ hx
    exact pbSP_within_pE hF hx

end UnforcedLeray.Short.PartI
