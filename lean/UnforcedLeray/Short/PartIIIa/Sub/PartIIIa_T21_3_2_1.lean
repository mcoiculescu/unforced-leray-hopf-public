import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2

/-!
# Part III-a, `PartIII-a:T21/3/2/1`: `UnitHeatS0Weak` from three lemmas

Source of record: `the November 2 reference manuscript`, lines 2819-2836 (the free
part of the Volterra iteration is the weighted heat semigroup).

The weak heat equation for the free family `S₀` is the fundamental theorem of calculus applied to
`g(θ) = ∫_cell vortFn(S₀ θ w) ψ`.  The ingredients, each a true source fact:
* `UnitHeatCellPairing` (L1): for `0 < θ ≤ 1` the cell pairing of `S₀ θ w` against a cylinder
  test is the pairing of the first component of the Gaussian heat flow `B0284.heat θ` of the
  periodic lift of `w` (from `coeFn_xColumnHeatS0Positive`, `actualWeightedHeatS0_apply_of_pos`);
* `UnitHeatKernelDeriv` (L2): `∂_θ ∫_cell (heat θ f)₁ φ = ∫_cell (heat θ f)₁ Δφ` (heat kernel
  normalisation `∂_θ G = ΔG`, `heatKernel2AgeDerivative_eq_spatialLaplacian`; differentiation under
  the integral; integration by parts against the `q`-periodic test);
* `UnitHeatPairingCont` (L3): continuity of `θ ↦ ∫_cell vortFn(S₀ θ w) ψ` on `[0,1]`
  (`continuous_actualWeightedHeatS0_apply`, continuity of the pairing with a cylinder test).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- L1: pairing reduction for `0 < θ ≤ 1`. -/
def UnitHeatCellPairing : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m),
    haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
    ∀ (w : ActualVorticity (c := c) (m := m) hm) (ψ : ℝ × ℝ → ℝ),
      UnforcedLeray.B0579.IsCylTest c ψ →
      ∀ θ ∈ Ioc (0 : ℝ) 1,
        ∫ x in UnforcedLeray.B0579.cell c,
            vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S₀ θ w) x
              * ψ x =
          ∫ z in UnforcedLeray.B0579.cell c,
            (UnforcedLeray.B0284.heat θ
              (xColumnHeatLift (Fact.out : 0 < c) w.1) z).1 * ψ z

/-- L2: age derivative of the cell pairing of the Gaussian heat flow. -/
def UnitHeatKernelDeriv : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m),
    haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
    ∀ (w : ActualVorticity (c := c) (m := m) hm) (φ : ℝ × ℝ → ℝ),
      UnforcedLeray.B0579.IsCylTest c φ →
      ∀ θ ∈ Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun τ : ℝ => ∫ z in UnforcedLeray.B0579.cell c,
            (UnforcedLeray.B0284.heat τ (xColumnHeatLift (Fact.out : 0 < c) w.1) z).1 * φ z)
          (∫ z in UnforcedLeray.B0579.cell c,
            (UnforcedLeray.B0284.heat θ (xColumnHeatLift (Fact.out : 0 < c) w.1) z).1 * lapP φ z)
          θ

/-- L3: continuity of the tested orbit of `S₀` on `[0,1]`. -/
def UnitHeatPairingCont : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m),
    haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
    ∀ (w : ActualVorticity (c := c) (m := m) hm) (ψ : ℝ × ℝ → ℝ),
      UnforcedLeray.B0579.IsCylTest c ψ →
      ContinuousOn (fun θ : ℝ => ∫ x in UnforcedLeray.B0579.cell c,
        vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S₀ θ w) x
          * ψ x) (Icc (0 : ℝ) 1)

theorem unitHeatS0Weak_of (h1 : UnitHeatCellPairing) (h2 : UnitHeatKernelDeriv)
    (h3 : UnitHeatPairingCont) : UnitHeatS0Weak := by
  intro c m _ hc1 hm
  haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
  intro w φ hφ t ht
  set H := actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm with hH
  let G : ℝ → ℝ := fun θ => ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (H.S₀ θ w) x * φ x
  let G' : ℝ → ℝ := fun θ => ∫ x in UnforcedLeray.B0579.cell c,
    vortFn hm (H.S₀ θ w) x * lapP φ x
  have hlap : UnforcedLeray.B0579.IsCylTest c (lapP φ) := by
    unfold lapP
    have h1 := (hφ.pd 0).pd 0
    have h2 := (hφ.pd 1).pd 1
    refine ⟨h1.smooth.add h2.smooth, fun x => ?_, ?_⟩
    · simp only [h1.periodic x, h2.periodic x]
    · obtain ⟨R, hR⟩ := h1.band
      obtain ⟨R', hR'⟩ := h2.band
      refine ⟨max R R', fun x hx => ?_⟩
      have := hR x (lt_of_le_of_lt (le_max_left _ _) hx)
      have := hR' x (lt_of_le_of_lt (le_max_right _ _) hx)
      simp [*]
  have hGc : ContinuousOn G (Icc 0 1) := h3 c m hc1 hm w φ hφ
  have hG'c : ContinuousOn G' (Icc 0 1) := h3 c m hc1 hm w (lapP φ) hlap
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) 1, HasDerivAt G (G' θ) θ := by
    intro θ hθ
    have hd := h2 c m hm w φ hφ θ hθ
    have hev : (fun τ : ℝ => ∫ z in UnforcedLeray.B0579.cell c,
        (UnforcedLeray.B0284.heat τ (xColumnHeatLift (Fact.out : 0 < c) w.1) z).1 * φ z)
        =ᶠ[𝓝 θ] G := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with τ hτ
      exact (h1 c m hc1 hm w φ hφ τ ⟨hτ.1, hτ.2.le⟩).symm
    have hval : (∫ z in UnforcedLeray.B0579.cell c,
        (UnforcedLeray.B0284.heat θ (xColumnHeatLift (Fact.out : 0 < c) w.1) z).1 * lapP φ z)
        = G' θ :=
      (h1 c m hc1 hm w (lapP φ) hlap θ ⟨hθ.1, hθ.2.le⟩).symm
    rw [hval] at hd
    exact hd.congr_of_eventuallyEq hev.symm
  have h0 : G 0 = ∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * φ x := by
    simp only [G, H.S₀_zero]
    rfl
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h
    simp [← h0, G]
  · have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hGc.mono hsub)
      (fun θ hθ => hderiv θ ⟨hθ.1, lt_of_lt_of_le hθ.2 ht.2⟩)
      ((hG'c.mono hsub).intervalIntegrable_of_Icc ht.1)
    change G t = _ + 1 * ∫ r in (0 : ℝ)..t, G' r
    rw [one_mul, hFTC, ← h0]
    ring

end UnforcedLeray.Short.IIIa.Exist
