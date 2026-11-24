import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.DualSplit
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.DuhamelSplit

/-!
# Part III-a, `PartIII-a:T21/3/2/2/org`: the concrete smoothed tests `P_θ ψ`

Source of record: `the November 2 reference manuscript`, lines 2819-2836 (the
weighted heat semigroup `S₀` and its divergence response `S` on the cylinder; the response is
tested against a cylinder test through the dual heat flow).

The family `P` left abstract in `Sub/PartIIIa_T21_3_2_2.lean` (`UnitHeatDual P`,
`UnitHeatDuhamel P`, `unitHeatResponseWeak_of P`) is instantiated by `cylHeatSmooth`
(defined in `PartIIIa_T21_3_2_2_Smooth/Basic.lean`):
`cylHeatSmooth c θ ψ x = ∫_{ℝ²} G_θ(w) ψ(x - w) dw` for `θ > 0`, with `G_θ = B0284.heatKernel2 θ`
the planar Gaussian of the response `S(θ) = -e^{θΔ} div` (`B0296.heatDiv`), and `= ψ x` for
`θ ≤ 0`. Since a cylinder test is represented by its `c`-periodic lift, this is the cylinder heat
flow `e^{θΔ} ψ`.

Regularity. Gaussian convolution does NOT preserve `B0579.IsCylTest`: the bounded `η`-support is
lost (for `ψ ≥ 0`, `ψ ≢ 0`, `P_θ ψ > 0` everywhere when `θ > 0`). The smoothed test lies in the
weaker class `IsCylSmoothBdd c` (smooth, `c`-periodic, every partial-derivative word globally
bounded). This is all `UnitHeatDual` / `UnitHeatDuhamel` need: they apply `IsCylTest` only to `ψ`
and `Δψ`, and use `P_θ ψ` only through `∂_i P_θ ψ` in `fluxPair`, which is bounded uniformly in
`θ` (`exists_bound_pdWord_cylHeatSmooth`) and jointly continuous in `(θ, x)`
(`continuous_pd_cylHeatSmooth_joint`). `unitHeatResponseWeak_of` takes `P` arbitrary, so no
statement in `Sub/PartIIIa_T21_3_2_2.lean` changes.

Main results (for `c > 0` and a cylinder test `ψ`):
* `cylHeatSmooth_zero`: `P_0 ψ = ψ`;
* `isCylSmoothBdd_cylHeatSmooth`: `IsCylSmoothBdd c (P_θ ψ)` for every `θ`;
* `pd_cylHeatSmooth`, `cylHeatSmooth_lapP`: `∂_j P_θ = P_θ ∂_j`, `P_θ Δ = Δ P_θ`;
* `hasDerivAt_cylHeatSmooth_age`: `∂_θ P_θ ψ(x) = Δ P_θ ψ(x)` for `θ > 0`;
* `continuous_pd_cylHeatSmooth_joint`: `(θ, x) ↦ ∂_i P_θ ψ(x)` is continuous on `ℝ × ℝ²`;
* `cylHeatSmooth_duhamel`, `pd_cylHeatSmooth_duhamel`: `P_θ φ = φ + ∫_0^θ P_η Δφ dη` and its
  first-derivative form (`θ ≥ 0`), the pointwise input of `UnitHeatDuhamel` (N3);
* `pd_lapP`: `∂_i Δφ = Δ∂_i φ` for a cylinder test.

`PartIIIa_T21_3_2_2_Smooth/DualSplit.lean` splits `UnitHeatDual cylHeatSmooth` into
`UnitHeatDualUnfold`, `HeatDivFluxDual`, `FluxPairPeriodicRep` (`unitHeatDual_of`);
`PartIIIa_T21_3_2_2_Smooth/DuhamelSplit.lean` states the inputs `FluxPairHeatDuhamel`,
`FluxPairHeatContinuous` of `UnitHeatDuhamel cylHeatSmooth`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa

/-- The properties of the concrete smoothing `P_θ ψ` on the age window `[0, 1]`
(source lines 2819-2836): `P_0 = id`, the regularity class `IsCylSmoothBdd`, commutation with
`Δ`, the heat equation in the age, and joint continuity of the first derivatives. -/
theorem cylHeatSmooth_spec {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    cylHeatSmooth c 0 ψ = ψ ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, IsCylSmoothBdd c (cylHeatSmooth c θ ψ)) ∧
      (∀ θ : ℝ, cylHeatSmooth c θ (lapP ψ) = lapP (cylHeatSmooth c θ ψ)) ∧
      (∀ θ ∈ Ioo (0 : ℝ) 1, ∀ x : ℝ × ℝ,
        HasDerivAt (fun s : ℝ => cylHeatSmooth c s ψ x) (lapP (cylHeatSmooth c θ ψ) x) θ) ∧
      (∀ i : Fin 2, ContinuousOn
        (fun p : ℝ × (ℝ × ℝ) => B0579.pd i (cylHeatSmooth c p.1 ψ) p.2)
        (Icc (0 : ℝ) 1 ×ˢ univ)) :=
  ⟨cylHeatSmooth_zero c ψ,
    fun _ _ => isCylSmoothBdd_cylHeatSmooth hc hψ,
    fun _ => cylHeatSmooth_lapP hc hψ,
    fun _ hθ x => hasDerivAt_cylHeatSmooth_age hc hψ hθ.1 x,
    fun i => (continuous_pd_cylHeatSmooth_joint hc hψ i).continuousOn⟩

/-- The follow-up targets are well-typed for the concrete family. -/
example : Prop := UnitHeatDual cylHeatSmooth

example : Prop := UnitHeatDuhamel cylHeatSmooth

end UnforcedLeray.Short.IIIa.Exist

#print axioms UnforcedLeray.Short.IIIa.Exist.cylHeatSmooth_spec
#print axioms UnforcedLeray.Short.IIIa.Exist.pd_cylHeatSmooth_duhamel
#print axioms UnforcedLeray.Short.IIIa.Exist.exists_bound_pdWord_cylHeatSmooth
