import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellGradUT
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

/-- Integrating the actual spatial product rule against the canonical graph representative gives
the exact transpose-gradient/advection cancellation. Integrability of the advective term is
derived from the pointwise identity and the two genuine Hölder bounds. -/
theorem pairF_gradUT_advT_rep_sum_eq_zero {P : ℝ} [Fact (0 < P)]
    {w : Yq P q0E} (hw : IsPhaseSolenoidal w)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {V : ℝ → SpatialField} (hV : IsBoundedBackground V)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [ENNReal.HolderTriple p q0E 1] :
    pairF P (gradUT V Φ) (fun z => rep w z.1 z.2) +
      pairF P (advT (fun z => rep w z.1 z.2) Φ) (fun z => realC (V z.1 z.2)) = 0 := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let G : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  let S : SpaceTime → ℂ := fun z =>
    dotL (scalarSliceGrad (scalarTestBackground Φ V) z) (G z)
  let A : SpaceTime → ℂ := fun z => dotL (gradUT V Φ z) (G z)
  let B : SpaceTime → ℂ := fun z => dotL (advT G Φ z) (realC (V z.1 z.2))
  have hG : MemLp G q0E μ := by
    simpa [G, μ, phaseCell] using memLp_rep_periodCell q0E_ne_top w
  have hF : MemLp (scalarSliceGrad (scalarTestBackground Φ V)) p μ :=
    memLp_scalarSliceGrad_cell hΦ hV hp
  have hGrad : MemLp (gradUT V Φ) p μ := memLp_gradUT_cell hΦ hV hp
  have hS : Integrable S μ := by
    exact integrable_dotL_of_memLp_holder hF hG
  have hA : Integrable A μ := by
    exact integrable_dotL_of_memLp_holder hGrad hG
  have hpoint (z : SpaceTime) : S z = A z + B z := by
    exact scalarSliceGrad_dotL_productRule hΦ hV G z
  have hBAE : B =ᵐ[μ] (fun z => S z - A z) := by
    filter_upwards with z
    rw [hpoint z]
    ring
  have hB : Integrable B μ := by
    exact Integrable.congr (hS.sub hA) hBAE.symm
  have hSzero : ∫ z, S z ∂μ = 0 := by
    simpa [S, μ, G] using integral_scalarSliceGrad_pair_rep_zero hw hΦ hV hp
  have hsum : (∫ z, A z ∂μ) + (∫ z, B z ∂μ) = ∫ z, S z ∂μ := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    exact ae_of_all _ fun z => (hpoint z).symm
  have hsumzero : (∫ z, A z ∂μ) + (∫ z, B z ∂μ) = 0 := by
    rw [hsum, hSzero]
  rw [pairF_eq_restrictedProductIntegral hA,
      pairF_eq_restrictedProductIntegral hB]
  rw [← smul_add, hsumzero]
  simp

#print axioms pairF_gradUT_advT_rep_sum_eq_zero

end UnforcedLeray.Cons.C03.Concrete
