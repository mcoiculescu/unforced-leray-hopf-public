import UnforcedLeray.Short.PartIIIa.Sub.T15

/-!
# Part III-a, task `PartIII-a:T15/9`: second partials are local

Proves `part2Congr : Part2Congr` (`Sub/T15.lean`): if `f = g` near `x`, then
`part2 f i k = part2 g i k` near `x`. No smoothness is needed.

Proof. Let `y` be a point with `f = g` near `y`.
1. `fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ g` (`Filter.EventuallyEq.fderiv`).
2. Hence `(fun z => fderiv ℝ f z e_k) =ᶠ[𝓝 y] (fun z => fderiv ℝ g z e_k)`.
3. Hence the derivatives of these two functions agree at `y` (`Filter.EventuallyEq.fderiv_eq`),
   which is `part2 f i k y = part2 g i k y`.
The set of such `y` is a neighbourhood of `x` (`Filter.EventuallyEq.eventuallyEq_nhds`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Pointwise locality: if `f = g` near `y`, then `part2 f i k` and `part2 g i k` agree at `y`. -/
theorem part2_eq_at_of_eventuallyEq_nhds {f g : Space → ℝ} {y : Space} (h : f =ᶠ[𝓝 y] g)
    (i k : Fin 3) : part2 f i k y = part2 g i k y := by
  have h1 : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ g := h.fderiv
  have h2 : (fun z => fderiv ℝ f z (coordinateVector k)) =ᶠ[𝓝 y]
      (fun z => fderiv ℝ g z (coordinateVector k)) := by
    filter_upwards [h1] with z hz
    simp only [hz]
  unfold part2
  rw [h2.fderiv_eq]

/-- **Second partials are local** (`PartIII-a:T15/9`; `Part2Congr`, `Sub/T15.lean`): if `f = g`
near `x`, then `part2 f i k = part2 g i k` near `x`. -/
theorem part2Congr : UnforcedLeray.Short.IIIa.Part2Congr := by
  unfold UnforcedLeray.Short.IIIa.Part2Congr
  intro f g x hfg i k
  filter_upwards [hfg.eventuallyEq_nhds] with y hy
  exact part2_eq_at_of_eventuallyEq_nhds hy i k

end UnforcedLeray.Short.IIIa
