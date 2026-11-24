import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Age

/-!
# Part III-a, `PartIII-a:T21/3/2/2/2`: splitting the dual heat pairing `UnitHeatDual`

Source of record: `the November 2 reference manuscript`, lines 2819-2836.

`UnitHeatDual cylHeatSmooth` (`⟨S(θ)F, ψ⟩ = ⟨F, ∇P_θψ⟩`, `0 < θ ≤ 1`) splits into
* `UnitHeatDualUnfold`: the response `S(θ)F` is, a.e. on the cell, the first row of
  `-e^{θΔ} div T_F` (`negativeHeatDiv`, `actualWeightedHeatResponse_value`), with `T_F` the
  periodic column tensor of `F` (`xFluxPeriodicTensor`);
* `HeatDivFluxDual`: Fubini on `cell × ℝ²`, periodic translation of the cell, and one Gaussian
  integration by parts (`integral_kernel_fderiv_mul_comp_sub`, `pd_gaussConv`) give
  `-∫_cell (e^{θΔ} div T_F)_1 ψ = ∫_cell (F̃₀ ∂_q P_θψ + F̃₁ ∂_η P_θψ)` with `F̃ᵢ` the periodic
  representatives `xColumnPeriodicRep`;
* `FluxPairPeriodicRep`: `F̃ᵢ = Fᵢ` a.e. on the cell, so the right side is `fluxPair`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- (N2a) The tested response is the tested first row of `-e^{θΔ} div T_F` on the cell
(source lines 2819-2836; `actualWeightedHeatResponse_value`). -/
def UnitHeatDualUnfold : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m),
    haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
    ∀ (F : ActualFlux (c := c) (m := m)) (ψ : ℝ × ℝ → ℝ), UnforcedLeray.B0579.IsCylTest c ψ →
      ∀ θ ∈ Ioc (0 : ℝ) 1,
        ∫ x in UnforcedLeray.B0579.cell c,
            vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S θ F) x
              * ψ x =
          ∫ x in UnforcedLeray.B0579.cell c,
            (negativeHeatDiv θ (xFluxPeriodicTensor (Fact.out : 0 < c) F) x).1 * ψ x

/-- (N2b) Duality of the Gaussian heat-divergence of the periodic flux tensor with the smoothed
test: `-∫_cell (e^{θΔ} div T_F)_1 ψ = ∫_cell (F̃₀ ∂_q P_θψ + F̃₁ ∂_η P_θψ)` for `θ > 0`
(source lines 2819-2836). -/
def HeatDivFluxDual : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (F : ActualFlux (c := c) (m := m))
    (ψ : ℝ × ℝ → ℝ), UnforcedLeray.B0579.IsCylTest c ψ →
      ∀ θ ∈ Ioc (0 : ℝ) 1,
        ∫ x in UnforcedLeray.B0579.cell c,
            (negativeHeatDiv θ (xFluxPeriodicTensor (Fact.out : 0 < c) F) x).1 * ψ x =
          ∫ x in UnforcedLeray.B0579.cell c,
            (xColumnPeriodicRep (Fact.out : 0 < c) (F 0) x *
                UnforcedLeray.B0579.pd 0 (cylHeatSmooth c θ ψ) x +
              xColumnPeriodicRep (Fact.out : 0 < c) (F 1) x *
                UnforcedLeray.B0579.pd 1 (cylHeatSmooth c θ ψ) x)

/-- (N2c) The flux pairing is unchanged by passing to the periodic column representatives. -/
def FluxPairPeriodicRep : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (F : ActualFlux (c := c) (m := m))
    (φ : ℝ × ℝ → ℝ),
      fluxPair hm F φ =
        ∫ x in UnforcedLeray.B0579.cell c,
          (xColumnPeriodicRep (Fact.out : 0 < c) (F 0) x * UnforcedLeray.B0579.pd 0 φ x +
            xColumnPeriodicRep (Fact.out : 0 < c) (F 1) x * UnforcedLeray.B0579.pd 1 φ x)

/-- `UnitHeatDual` for the concrete smoothing from (N2a), (N2b), (N2c). -/
theorem unitHeatDual_of (h1 : UnitHeatDualUnfold) (h2 : HeatDivFluxDual)
    (h3 : FluxPairPeriodicRep) : UnitHeatDual cylHeatSmooth := by
  intro c m _ hc1 hm
  haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
  intro F ψ hψ θ hθ
  rw [h1 c m hc1 hm F ψ hψ θ hθ, h2 c m hm F ψ hψ θ hθ, h3 c m hm F (cylHeatSmooth c θ ψ)]

end UnforcedLeray.Short.IIIa.Exist
