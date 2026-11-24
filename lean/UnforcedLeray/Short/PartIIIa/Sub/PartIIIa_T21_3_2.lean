import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip

/-!
# Part III-a, `PartIII-a:T21/3/2`: the unit-diffusivity heat family is weak

Source of record: `the November 2 reference manuscript`, lines 2819-2836 (the free
part of the Volterra iteration is the weighted heat semigroup and its divergence response).

`UnitHeatWeakActual` is the conjunction of the two conjuncts of `ScaledHeatWeak hm 1` for the
constructed supplier `actualPhysicalWeightedHeatStripSupplier`.  They are separated here:
* `UnitHeatS0Weak`: weak heat equation for the free family `S₀` (differentiate
  `∫ (G_θ * w) φ`; heat kernel normalisation `∂_θ G = ΔG`; Gaussian Fubini against the cylinder
  test; `Lib/HeatCylinder/HeatKernelAgeLaplacian.lean`; continuity at `0` from
  `tendsto_actualWeightedHeatS0_apply_zero`);
* `UnitHeatResponseWeak`: weak Duhamel identity for the heat-divergence response (dual pairing
  `⟨S(θ)F, φ⟩ = ⟨F, ∇P_θ φ⟩` with `P_θ` the cylinder heat smoothing, then Fubini on `[a,t]`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Conjunct (a) of `ScaledHeatWeak hm 1` for the physical supplier. -/
def UnitHeatS0Weak : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m),
    haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
    ∀ (w : ActualVorticity (c := c) (m := m) hm) (φ : ℝ × ℝ → ℝ),
      UnforcedLeray.B0579.IsCylTest c φ →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ∫ x in UnforcedLeray.B0579.cell c,
            vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S₀ t w) x
              * φ x =
          (∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * φ x) +
            (1 : ℝ) * ∫ r in (0 : ℝ)..t, ∫ x in UnforcedLeray.B0579.cell c,
              vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S₀ r w) x
                * lapP φ x

/-- Conjunct (b) of `ScaledHeatWeak hm 1` for the physical supplier. -/
def UnitHeatResponseWeak : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m),
    haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
    ∀ (F : ℝ → ActualFlux (c := c) (m := m)) (a b : ℝ), a ≤ b → b ≤ a + 1 →
      ContinuousOn F (Icc a b) → ∀ φ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c φ →
        ∀ t ∈ Icc a b,
          ∫ x in UnforcedLeray.B0579.cell c,
              vortFn hm (∫ r in a..t,
                (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S (t - r)
                  (F r)) x * φ x =
            ((1 : ℝ) * ∫ r in a..t, ∫ x in UnforcedLeray.B0579.cell c,
                vortFn hm (∫ s in a..r,
                  (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S (r - s)
                    (F s)) x * lapP φ x) +
              ∫ r in a..t, ∫ x in UnforcedLeray.B0579.cell c,
                (fluxFn (F r) 0 x * UnforcedLeray.B0579.pd 0 φ x +
                  fluxFn (F r) 1 x * UnforcedLeray.B0579.pd 1 φ x)

theorem unitHeatWeakActual_of (h1 : UnitHeatS0Weak) (h2 : UnitHeatResponseWeak) :
    UnitHeatWeakActual :=
  fun c m _ hc1 hm => ⟨h1 c m hc1 hm, h2 c m hc1 hm⟩

end UnforcedLeray.Short.IIIa.Exist
