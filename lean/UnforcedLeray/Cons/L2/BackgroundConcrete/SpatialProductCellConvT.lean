import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellAdvT

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

/-- The actual compact-test convection identity for a bounded background and the selected
solenoidal graph correction. All three phase-cell pairings are integrable from proved Lp bounds;
the cancellation is obtained from the actual product rule and graph solenoidality. -/
theorem pairF_convT_convection_identity {P : ℝ} [Fact (0 < P)]
    {w : Yq P q0E} (hw : IsPhaseSolenoidal w)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {V : ℝ → SpatialField} (hV : IsBoundedBackground V)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [ENNReal.HolderTriple p q0E 1] :
    pairF P (convT V Φ) (fun z => rep w z.1 z.2) +
      pairF P (advT (fun z => rep w z.1 z.2) Φ)
        (fun z => realC (V z.1 z.2)) +
      pairF P (advT (fun z => realC (V z.1 z.2)) Φ)
        (fun z => rep w z.1 z.2) = 0 := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let G : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  let Vc : SpaceTime → CVec3 := fun z => realC (V z.1 z.2)
  let S : SpaceTime → ℂ := fun z =>
    dotL (scalarSliceGrad (scalarTestBackground Φ V) z) (G z)
  let A : SpaceTime → ℂ := fun z => dotL (gradUT V Φ z) (G z)
  let B : SpaceTime → ℂ := fun z => dotL (advT G Φ z) (Vc z)
  let T : SpaceTime → CVec3 := fun z => advT Vc Φ z
  let C : SpaceTime → ℂ := fun z => dotL (T z) (G z)
  have hG : MemLp G q0E μ := by
    simpa [G, μ, phaseCell] using memLp_rep_periodCell q0E_ne_top w
  have hF : MemLp (scalarSliceGrad (scalarTestBackground Φ V)) p μ :=
    memLp_scalarSliceGrad_cell hΦ hV hp
  have hGrad : MemLp (gradUT V Φ) p μ := memLp_gradUT_cell hΦ hV hp
  have hT : MemLp T p μ := by
    exact memLp_advT_background_cell hΦ hV hp
  have hConv : MemLp (convT V Φ) p μ := by
    change MemLp (fun z => gradUT V Φ z - T z) p μ
    exact hGrad.sub hT
  have hS : Integrable S μ := integrable_dotL_of_memLp_holder hF hG
  have hA : Integrable A μ := integrable_dotL_of_memLp_holder hGrad hG
  have hC : Integrable C μ := integrable_dotL_of_memLp_holder hT hG
  have hpoint (z : SpaceTime) : S z = A z + B z :=
    scalarSliceGrad_dotL_productRule hΦ hV G z
  have hBAE : B =ᵐ[μ] (fun z => S z - A z) := by
    filter_upwards with z
    rw [hpoint z]
    ring
  have hB : Integrable B μ := Integrable.congr (hS.sub hA) hBAE.symm
  have hSzero : ∫ z, S z ∂μ = 0 := by
    simpa [S, μ, G] using integral_scalarSliceGrad_pair_rep_zero hw hΦ hV hp
  have hsum : (∫ z, A z ∂μ) + (∫ z, B z ∂μ) = ∫ z, S z ∂μ := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    exact ae_of_all _ fun z => (hpoint z).symm
  have hsumzero : (∫ z, A z ∂μ) + (∫ z, B z ∂μ) = 0 := by
    rw [hsum, hSzero]
  have hpointConv (z : SpaceTime) :
      dotL (convT V Φ z) (G z) = A z - C z := by
    simp [convT, A, C, T, Vc, dotL_apply]
  have hconvIntegral : (∫ z, dotL (convT V Φ z) (G z) ∂μ) =
      (∫ z, A z ∂μ) - (∫ z, C z ∂μ) := by
    calc
      (∫ z, dotL (convT V Φ z) (G z) ∂μ) =
          ∫ z, (A z - C z) ∂μ := integral_congr_ae (ae_of_all _ hpointConv)
      _ = (∫ z, A z ∂μ) - (∫ z, C z ∂μ) := integral_sub hA hC
  have hfinalIntegral :
      (∫ z, dotL (convT V Φ z) (G z) ∂μ) +
        (∫ z, B z ∂μ) + (∫ z, C z ∂μ) = 0 := by
    rw [hconvIntegral]
    calc
      (∫ z, A z ∂μ) - (∫ z, C z ∂μ) +
          (∫ z, B z ∂μ) + (∫ z, C z ∂μ) =
          ((∫ z, A z ∂μ) + (∫ z, B z ∂μ)) := by ring
      _ = 0 := hsumzero
  have hConvInt : Integrable (fun z => dotL (convT V Φ z) (G z)) μ :=
    integrable_dotL_of_memLp_holder hConv hG
  rw [pairF_eq_restrictedProductIntegral hConvInt,
      pairF_eq_restrictedProductIntegral hB,
      pairF_eq_restrictedProductIntegral hC]
  rw [← smul_add, ← smul_add, hfinalIntegral]
  simp

#print axioms pairF_convT_convection_identity

end UnforcedLeray.Cons.C03.Concrete
