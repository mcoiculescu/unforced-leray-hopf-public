import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Sub.T12

/-!
# Part II-b, task `PartII-b:T12`: existence and `H_r` bound of the flat response (conditional)

Source of record: `the November 2 reference manuscript`, lines 1920-1930:
"The causal formula `T_0F(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} P_0 F(t) dt/t` and weighted dilation give
`‖T_0‖_{H_r → H_r} ≤ C_r/a_r`", `a_r = Re μ + (3/r - 1)/2` (the shift gap `γ_r` of
`ProfileGraphFlat`, SP 1927).

## Target of the task (statement-first)

`FlatCausalExists`: for `1 < r < 3` there is `C = C_r` such that for every `μ` with `a_r > 0`, every
`ν, c > 0` and every `F ∈ H_r` there is a flat response `b ∈ H_r` (`IsFlatResponse ν μ F b`) with
`‖b‖_{H_r} ≤ (C/a_r) ‖F‖_{H_r}`. This is the "existence + `H_r` bound" input of `PartII-b:T14`
(`ProfileGraphFlat`); the graph bounds are `T13`, uniqueness is `T11`.

## Why a density extension is not needed


Duhamel operator to be linear on a dense class and `IsFlatResponse` to be closed under `H_r`-limits.
Both are avoided by working directly in `H_r`: split `T_0 = D ∘ P_0` where

* `P_0` is the planar Leray (Helmholtz) projection acting in `(q, η)` at each age, bounded on `H_r`
  with a constant `C_r` depending only on `r` (it is a Calderón-Zygmund operator; this is the
  repository's INF01 / Grafakos Cor. 5.2.8 input, here for `ℂ²`-valued fields on the cylinder);
* `D G(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} G(t) dt/t` (`flatDuhamel`) is the causal heat Duhamel operator
  on weakly solenoidal `G ∈ H_r`: heat contraction in `L^r(dq/c dη)`, Minkowski, and the dilation
  identity `‖φ(u ·)‖_{L^r(s^{r/2-5/2}ds)} = u^{γ_r}‖φ‖` give `‖D G‖_{H_r} ≤ (1/a_r)‖G‖_{H_r}`.

## Proved here

`flatCausalExists_of` : the conditional assembly `FlatCausalExists` from the seven leaves

* `CylinderHelmholtzLr` (`PartII-b:T12/1`): the cylinder Helmholtz decomposition in `L^r`;
* `FlatLerayLiftOfSlice` (`PartII-b:T12/2`): lift from slices to `H_r` (`FlatLerayHr`);
* `DuhamelMeasurable` (`PartII-b:T12/3`), `DuhamelBound` (`PartII-b:T12/4`),
  `DuhamelPeriodic` (`PartII-b:T12/5`), `DuhamelSolenoidal` (`PartII-b:T12/6`),
  `dfe_DuhamelEquation` (`PartII-b:T12/7`): properties of `flatDuhamel`.

The helper leaf `FlatHeatContraction` (`PartII-b:T12/8`) feeds `T12/4`.

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## The causal Duhamel operator -/

/-- **Leaf `PartII-b:T12/7`** (SP 1924): the Duhamel integral solves `(μ + S - νsΔ_{q,η}) b = G`
weakly: for every planar solenoidal test `Ψ` the pairings converge and
`∫ b·((μ-1)Ψ - SΨ - νsΔΨ) = ∫ G·Ψ` (`flatTranspose`; `S^T = -1 - s∂_s`). -/
def dfe_DuhamelEquation : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → InHr c r (flatDuhamel ν μ G) → ∀ Ψ, IsPlanarTestDfe Ψ →
      Integrable (fun x => ∑ i : Fin 2, flatDuhamel ν μ G x i * flatTranspose ν μ Ψ x i) ∧
        Integrable (cdot G Ψ) ∧
        ∫ x, ∑ i : Fin 2, flatDuhamel ν μ G x i * flatTranspose ν μ Ψ x i = ∫ x, cdot G Ψ x

/-! ## Conditional assembly -/

end UnforcedLeray.Short.IIb
