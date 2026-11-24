import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_Org
import UnforcedLeray.Lib.PhaseSpace.Ops

/-!
# `MeridCoreResolventDense` (task `PartII-a:N04/3/3/2`): reduction to two leaves

Source of record: `the November 2 reference manuscript`,
lines 1456–1480 (the smooth periodic tests with radial cutoffs form a core of the generator) and
1838–1845, 3340–3363 (the outer semigroup `S_ε` and the meridional generator `A_ε^vec`).

The density of `(μ - A_ε^vec)(IsMeridCoreTest ε c)` in `H` is reduced to

* `OuterPhaseTestCoreDense` (the physical core statement, source 1456–1480): smooth phase tests
  `ψ` (`IsPhaseTest`: smooth, `P`-periodic, bounded `x`-support) are a core of the generator of the
  outer semigroup on `X = L²(ℝ³ × ℝ/Pℤ; ℂ³)`, where that generator acts on them as
  `νε²Δ + x·∇/2 + 1/2 - ∂_τ`; equivalently `(μ - G)(tests)` has trivial orthogonal complement;
* `MeridProjOfPhaseTest` (meridional projection): the adjoint `J*` of the meridional lift
  `B0223.liftVec` (the `O(2)`-average onto no-swirl axisymmetric fields read in the chart) maps the
  pair `(ψ, Gψ)` of a phase test to the pair `(u, A_ε^vec u)` of a core test `u`
  (`G` commutes with rotations and reflections fixing the axis, source 1477–1478).

Given both, `⟪(μ - G)ψ, J W⟫ = ⟪J*(μ - G)ψ, W⟫ = ⟪(μ - A_ε^vec)u, W⟫ = 0`, hence `J W = 0`,
hence `W = 0` (`J` is an isometry).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0221 UnforcedLeray.B0222
open UnforcedLeray.B0223
open UnforcedLeray.PhaseSpace

/-- The outer operator `νε²Δ + x·∇/2 + 1/2 - ∂_τ` on phase functions `ψ(τ, x)`
(source 3346–3352). -/
def phaseGen (ν ε : ℝ) (ψ : ℝ × Space → CVec3) : ℝ × Space → CVec3 := fun q =>
  (ν * ε ^ 2) • lapT ψ q + (1 / 2 : ℝ) • radialT ψ q + (1 / 2 : ℝ) • ψ q - dτ ψ q

/-- **Leaf (physical core, source 1456–1480).** Smooth phase tests are a core for the generator
of the outer semigroup `B0223.outerS` on `X`: for `μ` in the half-plane `Re μ > -1/4`, a vector
`Z ∈ X` orthogonal to every `μΨ - Ψ'`, with `Ψ`, `Ψ'` the classes of a phase test `ψ` and of
`phaseGen ν ε ψ`, vanishes. -/
def OuterPhaseTestCoreDense : Prop :=
  ∀ (ν ε : ℝ), 0 < ν → 0 < ε → ∀ (P : ℝ) [Fact (0 < P)] (μ : ℂ), 0 < μ.re + 1 / 4 →
    ∀ Z : X SpaceC P,
      (∀ (ψ : ℝ × Space → CVec3), IsPhaseTest P ψ → ∀ Ψ Ψ' : X SpaceC P,
        (Ψ : PSpace P → SpaceC) =ᵐ[volume] (fun z => ψ ((toCell P z).2, (toCell P z).1)) →
        (Ψ' : PSpace P → SpaceC) =ᵐ[volume]
          (fun z => phaseGen ν ε ψ ((toCell P z).2, (toCell P z).1)) →
        inner ℂ (μ • Ψ - Ψ') Z = 0) →
      Z = 0

/-- **Leaf (meridional projection of phase tests).** The adjoint of the meridional lift maps the
classes of a phase test `ψ` and of `phaseGen ν ε ψ` to the classes of a core test `u` and of
`A_ε^vec u` (the `O(2)`-average of a smooth field is smooth across the axis and has no swirl;
`phaseGen` commutes with that average and is `A_ε^vec` in the chart, source 1477–1478,
3327–3352). -/
def MeridProjOfPhaseTest : Prop :=
  ∀ (ν c ε : ℝ), 0 < ν → ∀ (hc : 0 < c) (hε : 0 < ε) (P : ℝ) [Fact (0 < P)]
    (hP : P = 2 * ε * c) (ψ : ℝ × Space → CVec3), IsPhaseTest P ψ →
    ∀ Ψ Ψ' : X SpaceC P,
      (Ψ : PSpace P → SpaceC) =ᵐ[volume] (fun z => ψ ((toCell P z).2, (toCell P z).1)) →
      (Ψ' : PSpace P → SpaceC) =ᵐ[volume]
        (fun z => phaseGen ν ε ψ ((toCell P z).2, (toCell P z).1)) →
      ∃ (u : Profile → MeridC) (U AU : HSpace c MeridC), IsMeridCoreTest ε c u ∧
        (U : Profile → MeridC) =ᵐ[measureH c] u ∧
        (AU : Profile → MeridC) =ᵐ[measureH c] AepsVecC ν ε u ∧
        ContinuousLinearMap.adjoint (liftVec hε hc hP).toContinuousLinearMap Ψ = U ∧
        ContinuousLinearMap.adjoint (liftVec hε hc hP).toContinuousLinearMap Ψ' = AU

/-- **Conditional assembly** of `MeridCoreResolventDense` from the physical core leaf and the
meridional projection leaf. -/
theorem meridCoreResolventDense_of (h1 : OuterPhaseTestCoreDense)
    (h2 : MeridProjOfPhaseTest) : MeridCoreResolventDense := by
  intro ν c ε hν hc hε _hε1 P _ hP _hP1 μ hγ W hW
  have hZ : liftVec hε hc hP W = 0 := by
    refine h1 ν ε hν hε P μ hγ (liftVec hε hc hP W) ?_
    intro ψ hψ Ψ Ψ' hΨ hΨ'
    obtain ⟨u, U, AU, hu, hU, hAU, hLU, hLAU⟩ := h2 ν c ε hν hc hε P hP ψ hψ Ψ Ψ' hΨ hΨ'
    have hadj : ContinuousLinearMap.adjoint (liftVec hε hc hP).toContinuousLinearMap
        (μ • Ψ - Ψ') = μ • U - AU := by
      rw [map_sub, map_smul, hLU, hLAU]
    have hae : ((μ • U - AU : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c]
        (fun p => μ • u p - AepsVecC ν ε u p) := by
      filter_upwards [Lp.coeFn_sub (μ • U) AU, Lp.coeFn_smul μ U, hU, hAU] with
        p h1p h2p h3p h4p
      rw [h1p, Pi.sub_apply, h2p, Pi.smul_apply, h3p, h4p]
    have hinner : inner ℂ (μ • Ψ - Ψ') (liftVec hε hc hP W) =
        inner ℂ (ContinuousLinearMap.adjoint (liftVec hε hc hP).toContinuousLinearMap
          (μ • Ψ - Ψ')) W := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl
    rw [hinner, hadj]
    exact hW u (μ • U - AU) hu hae
  have hn : ‖W‖ = 0 := by
    rw [← (liftVec hε hc hP).norm_map W, hZ, norm_zero]
  exact norm_eq_zero.1 hn

end UnforcedLeray.Short.PartIIa
