import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Age

/-!
# Part III-a, `PartIII-a:T21/3/2/2/3`: splitting the Duhamel identity `UnitHeatDuhamel`

Source of record: `the November 2 reference manuscript`, lines 2819-2836.

`UnitHeatDuhamel cylHeatSmooth` follows from
* `FluxPairHeatDuhamel`: for one flux `F` and `0 ≤ θ ≤ 1`,
  `⟨F, ∇P_θφ⟩ = ⟨F, ∇φ⟩ + ∫_0^θ ⟨F, ∇P_η Δφ⟩ dη` (Fubini on `cell × [0, θ]` applied to
  `pd_cylHeatSmooth_duhamel`, with the uniform bound `exists_bound_pdWord_cylHeatSmooth`);
* `FluxPairHeatContinuous`: `(r, θ) ↦ ⟨F(r), ∇P_θ g⟩` is continuous on `[a, b] × [-1, 1]` for a
  flux path continuous on `[a, b]` (dominated convergence with `continuous_pd_cylHeatSmooth_joint`;
  `P_θ = id` for `θ ≤ 0`);
then `η = u - r` and the triangle swap `∫_a^t dr ∫_r^t du = ∫_a^t du ∫_a^u dr`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- (N3a) The Duhamel identity of the smoothed tests, paired with one weighted flux
(source lines 2819-2836). -/
def FluxPairHeatDuhamel : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (F : ActualFlux (c := c) (m := m))
    (φ : ℝ × ℝ → ℝ), UnforcedLeray.B0579.IsCylTest c φ → ∀ θ ∈ Icc (0 : ℝ) 1,
      fluxPair hm F (cylHeatSmooth c θ φ) =
        fluxPair hm F φ + ∫ η in (0 : ℝ)..θ, fluxPair hm F (cylHeatSmooth c η (lapP φ))

/-- (N3b) Joint continuity of the smoothed flux pairing along a continuous flux path. -/
def FluxPairHeatContinuous : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (F : ℝ → ActualFlux (c := c) (m := m)) (a b : ℝ),
    ContinuousOn F (Icc a b) → ∀ g : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c g →
      ContinuousOn (fun p : ℝ × ℝ => fluxPair hm (F p.1) (cylHeatSmooth c p.2 g))
        (Icc a b ×ˢ Icc (-1 : ℝ) 1)

/-- The follow-up assembly statement is well-typed. -/
example : Prop := FluxPairHeatDuhamel → FluxPairHeatContinuous → UnitHeatDuhamel cylHeatSmooth

end UnforcedLeray.Short.IIIa.Exist
