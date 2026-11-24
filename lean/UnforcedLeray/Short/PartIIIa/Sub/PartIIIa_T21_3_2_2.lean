import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2

/-!
# Part III-a, `PartIII-a:T21/3/2/2`: `UnitHeatResponseWeak` from the dual heat pairing

Source of record: `the November 2 reference manuscript`, lines 2819-2836 (the
heat-divergence response of the weighted heat semigroup solves the weak Duhamel equation).

`P c θ ψ` is an abstract family standing for the cylinder-periodised Gaussian smoothing `P_θ ψ` of
a cylinder test `ψ` (to be defined concretely by the organize follow-up).  Ingredients:
* `UnitHeatLinComm` (N4): the cell pairing with a cylinder test commutes with the Bochner integral
  `∫_a^t S(t-r) F(r) dr` in `ActualVorticity`;
* `UnitHeatDual P` (N2): `⟨S(θ) F, ψ⟩ = ⟨F, ∇ P_θ ψ⟩` for `0 < θ ≤ 1`;
* `UnitHeatDuhamel P` (N3 + `∂_θ P_θ = Δ P_θ`): the Duhamel identity of the smoothed tests after
  Fubini in `(r, u)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem cylTest_add' {c : ℝ} {f g : ℝ × ℝ → ℝ} (hf : UnforcedLeray.B0579.IsCylTest c f)
    (hg : UnforcedLeray.B0579.IsCylTest c g) :
    UnforcedLeray.B0579.IsCylTest c (fun x => f x + g x) where
  smooth := hf.smooth.add hg.smooth
  periodic x := by simp only [hf.periodic x, hg.periodic x]
  band := by
    obtain ⟨R1, h1⟩ := hf.band
    obtain ⟨R2, h2⟩ := hg.band
    refine ⟨max R1 R2, fun x hx => ?_⟩
    simp [h1 x (lt_of_le_of_lt (le_max_left _ _) hx), h2 x (lt_of_le_of_lt (le_max_right _ _) hx)]

/-- The flux pairing `∫_cell (F₀ ∂₀ψ + F₁ ∂₁ψ)`. -/
def fluxPair {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) (F : ActualFlux (c := c) (m := m))
    (ψ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in UnforcedLeray.B0579.cell c,
    (fluxFn F 0 x * UnforcedLeray.B0579.pd 0 ψ x + fluxFn F 1 x * UnforcedLeray.B0579.pd 1 ψ x)

/-- (N4) The cell pairing with a cylinder test commutes with the Duhamel Bochner integral. -/
def UnitHeatLinComm : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m),
    haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
    ∀ (F : ℝ → ActualFlux (c := c) (m := m)) (a b : ℝ), a ≤ b → b ≤ a + 1 →
      ContinuousOn F (Icc a b) → ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ →
        ∀ t ∈ Icc a b,
          ∫ x in UnforcedLeray.B0579.cell c,
              vortFn hm (∫ r in a..t,
                (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S (t - r)
                  (F r)) x * ψ x =
            ∫ r in a..t, ∫ x in UnforcedLeray.B0579.cell c,
              vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S
                (t - r) (F r)) x * ψ x

/-- (N2) Dual heat pairing for the response, with `P` the cylinder-periodised Gaussian smoothing:
`⟨S(θ)F, ψ⟩ = ⟨F, ∇P_θψ⟩` for `0 < θ ≤ 1`. -/
def UnitHeatDual (P : ℝ → ℝ → (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ)) : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m),
    haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
    ∀ (F : ActualFlux (c := c) (m := m)) (ψ : ℝ × ℝ → ℝ), UnforcedLeray.B0579.IsCylTest c ψ →
      ∀ θ ∈ Ioc (0 : ℝ) 1,
        ∫ x in UnforcedLeray.B0579.cell c,
            vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S θ F) x
              * ψ x = fluxPair hm F (P c θ ψ)

/-- (N3) Duhamel identity for the smoothed tests: from `P_θ φ = φ + ∫_0^θ P_η Δφ dη` and Fubini. -/
def UnitHeatDuhamel (P : ℝ → ℝ → (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ)) : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m)
    (F : ℝ → ActualFlux (c := c) (m := m)) (a b : ℝ), a ≤ b → b ≤ a + 1 →
      ContinuousOn F (Icc a b) → ∀ φ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c φ →
        ∀ t ∈ Icc a b,
          ∫ r in a..t, fluxPair hm (F r) (P c (t - r) φ) =
            (∫ r in a..t, fluxPair hm (F r) φ) +
              ∫ u in a..t, ∫ r in a..u, fluxPair hm (F r) (P c (u - r) (lapP φ))

theorem unitHeatResponseWeak_of (P : ℝ → ℝ → (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ))
    (h1 : UnitHeatLinComm) (h2 : UnitHeatDual P) (h3 : UnitHeatDuhamel P) :
    UnitHeatResponseWeak := by
  intro c m _ hc1 hm
  haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
  intro F a b hab hb hF φ hφ t ht
  -- pairing with a cylinder test equals the smoothed flux pairing
  have key : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ → ∀ u ∈ Icc a b,
      ∫ x in UnforcedLeray.B0579.cell c,
          vortFn hm (∫ r in a..u,
            (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S (u - r)
              (F r)) x * ψ x =
        ∫ r in a..u, fluxPair hm (F r) (P c (u - r) ψ) := by
    intro ψ hψ u hu
    rw [h1 c m hc1 hm F a b hab hb hF ψ hψ u hu]
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ ({u} : Set ℝ) :=
      (Set.countable_singleton u).ae_notMem _
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with r hr hrI
    rw [Set.uIoc_of_le hu.1] at hrI
    have hru : r ≠ u := by simpa using hr
    have hlt : r < u := lt_of_le_of_ne hrI.2 hru
    exact h2 c m hc1 hm (F r) ψ hψ (u - r) ⟨by linarith, by linarith [hu.2, hrI.1]⟩
  rw [one_mul, key φ hφ t ht, h3 c m hm F a b hab hb hF φ hφ t ht]
  refine (add_comm _ _).trans ?_
  congr 1
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le ht.1] at hu
    have hlap : UnforcedLeray.B0579.IsCylTest c (lapP φ) := by
      exact cylTest_add' ((hφ.pd 0).pd 0) ((hφ.pd 1).pd 1)
    exact (key (lapP φ) hlap u ⟨hu.1, hu.2.trans ht.2⟩).symm

end UnforcedLeray.Short.IIIa.Exist
