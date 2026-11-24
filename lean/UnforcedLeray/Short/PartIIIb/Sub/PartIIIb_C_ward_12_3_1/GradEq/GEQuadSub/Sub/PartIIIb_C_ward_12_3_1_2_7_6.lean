import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# `GEQYq` from the cell facts of the quadratic field (decomposition)

Source `the November 2 reference manuscript`
lines 2562-2564 (Hölder: one factor in `L^∞`, the other in `Y_p`), 1478-1480 (periodic field
in `L^{q₀}` represents an element of `Y_{q₀}`).

`GEQFieldCell` is the content of the Hölder step on the whole cell `(0,P] × ℝ³`:
`GEQuadField` is strongly measurable, `P`-periodic in `τ`, with finite `L^{q₀}` period
integral.  It needs (i) global (not only local) integrability of the inlet jet
`∂e ∈ L^{2q₀}`, `∂²e ∈ L^{q₀}` and boundedness of `e` (`GEQInletGlobal`), and (ii) the a.e.
bound on `w` (`geSupBound`, already proved), plus `Dw ∈ L^{2q₀}` (`GEQHyp`) and the
`L^{q₀}` Hessian (`h j k : Yq`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF rep phaseInt)
open scoped ENNReal

/-- **Global integrability of the inlet jet** (source 2385-2387, 2562-2564): on the whole
cell `(0,P] × ℝ³`, `∂_j e ∈ L^{2q₀}`, `∂_j∂_k e ∈ L^{q₀}`, and `e` is bounded, for the affine
inlet `e = p.eFun (p.coord z)`. -/
def GEQInletGlobal : Prop := GERegime fun p z _ => ∀ j k : Fin 3,
  MemLp (fun x : ℝ × UnforcedLeray.Space => dy j (p.eFun (p.coord z)) x)
    (2 * UnforcedLeray.B0412.q0E)
    ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) ∧
  MemLp (fun x : ℝ × UnforcedLeray.Space => dy j (dy k (p.eFun (p.coord z))) x)
    UnforcedLeray.B0412.q0E
    ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) ∧
  ∃ C : ℝ, ∀ x, ‖p.eFun (p.coord z) x‖ ≤ C

/-- **Cell facts for the quadratic field** (source 2562-2564): `GEQuadField` is strongly
measurable, a.e. `P`-periodic in `τ`, and has finite `L^{q₀}` period integral. -/
def GEQFieldCell : Prop := GERegime fun p z g => ∀ h, GEQHyp p z g h → ∀ j : Fin 3,
  StronglyMeasurable (GEQuadField p z g h j) ∧
  (∀ᵐ τ : ℝ, (fun y => GEQuadField p z g h j (τ + p.period, y)) =ᵐ[volume]
    fun y => GEQuadField p z g h j (τ, y)) ∧
  ∫⁻ τ in Ioc (0 : ℝ) p.period, ∫⁻ y, ‖GEQuadField p z g h j (τ, y)‖ₑ ^
    UnforcedLeray.B0412.q0E.toReal < ⊤

/-- The lemma `GEQFieldCell` from the global inlet integrability (Hölder; uses `geSupBound`
for `w ∈ L^∞`, `GEQHyp` for `Dw ∈ L^{2q₀}`, the `Yq` Hessian, `stronglyMeasurable_rep`,
`rep_add_period`). -/
def GEQFieldCellOfInlet : Prop := GEQInletGlobal → GEQFieldCell

theorem gEQYq_of (h1 : GEQFieldCell) : GEQYq := by
  intro lam q hq dm dp hdm
  obtain ⟨n, hn, H⟩ := h1 lam q hq dm dp hdm
  refine ⟨n, hn, ?_⟩
  intro p d hreg hν hmode z g hd h hh j
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  obtain ⟨hm, hper, hfin⟩ := H p d hreg hν hmode z g hd h hh j
  obtain ⟨F, hF⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof
    UnforcedLeray.B0412.q0E (by simp [UnforcedLeray.B0412.q0E]) p.period _ hm hper hfin
  refine ⟨F, fun Φ hΦ => ?_⟩
  rw [UnforcedLeray.Cons.C03.Concrete.phasePair_eq_pairF_rep hΦ F]
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  have h2 : ∀ᵐ τ : ℝ, (fun y => rep F τ y) =ᵐ[volume] (fun y => GEQuadField p z g h j (τ, y)) := by
    filter_upwards [hF.slice] with τ hτ
    exact (UnforcedLeray.Cons.C03.Concrete.rep_slice F τ).trans hτ.symm
  filter_upwards [h2] with τ hτ
  exact integral_congr_ae (by filter_upwards [hτ] with y hy; simp only [hy])

end UnforcedLeray.Short.PartIIIb.Concrete
