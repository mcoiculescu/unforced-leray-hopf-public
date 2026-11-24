import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellInletPhasePair
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellOuterPairing
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF
import UnforcedLeray.Cons.L2.BackgroundConcrete.PeriodizedCellPair

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.PhaseTrace
open UnforcedLeray.B0412

private theorem realC_eq_cplxV_inletProduct : realC = UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

private theorem norm_realC_inletProduct (x : Space) : ‖realC x‖ = ‖x‖ := by
  rw [realC_eq_cplxV_inletProduct, UnforcedLeray.Axi.norm_cplxV]

/-- At a fixed admissible phase cutoff, the actual scalar product gradient is annihilated by a
bounded pointwise-solenoidal field. Smooth nested mollifications are killed phasewise; the
actual gradient is reached in cell `L¹`, paired against the bounded field in `L∞`. -/
theorem integral_cutoffSquared_scalarSliceGrad_pair_boundedSolenoidal_zero
    {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U V : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (hV : IsBoundedBackground V) (hsol : ∀ τ, IsSolenoidal (V τ))
    (n : ℕ) (hn : 2 / ((n : ℝ) + 1) ≤ P) :
    ∫ z : SpaceTime, dotL
      ((phaseInteriorCutoff P n z.1) ^ 2 • scalarSliceGrad (scalarTestBackground Φ U) z)
      (realC (V z.1 z.2)) ∂(volume.restrict (phaseCell P)) = 0 := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let G : SpaceTime → CVec3 := fun z => realC (V z.1 z.2)
  let F : SpaceTime → CVec3 := fun z =>
    (phaseInteriorCutoff P n z.1) ^ 2 • scalarSliceGrad (scalarTestBackground Φ U) z
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have hGmeas : AEStronglyMeasurable G μ := by
    have h : AEStronglyMeasurable
        (fun z : SpaceTime => realC (V z.1 z.2)) volume := by
      have hc := UnforcedLeray.Axi.cplxV.continuous.comp_aestronglyMeasurable hV.measurable
      exact hc.congr (ae_of_all _ fun z => by rw [realC_eq_cplxV_inletProduct])
    exact h.mono_measure Measure.restrict_le_self
  obtain ⟨CV, hCV⟩ := hV.bounded
  have hGbound : ∀ᵐ z ∂μ, ‖G z‖ ≤ CV := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    change ‖realC (V z.1 z.2)‖ ≤ CV
    rw [norm_realC_inletProduct]
    exact (hCV z.1 z.2).1
  have hG : MemLp G ⊤ μ := memLp_top_of_bound hGmeas CV hGbound
  have hF : MemLp (scalarSliceGrad (scalarTestBackground Φ U)) 1 μ :=
    memLp_scalarSliceGrad_cell hΦ hU (by simp)
  have hFcut : MemLp F 1 μ :=
    memLp_cutoffSquared_scalarSliceGrad_cell hΦ hU (by simp) n
  have hseq (k : ℕ) : MemLp
      (fun z : SpaceTime => PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z)
      1 μ := memLp_nestedCutoff_gradT_cell hΦ hU (by simp) n k hn
  have hconv0 : Tendsto (fun k : ℕ => eLpNorm
      (fun z : SpaceTime => PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z - F z)
      1 μ) atTop (𝓝 0) := by
    simpa [μ, F] using tendsto_nestedCutoff_gradT_cellLp hΦ hU (by simp) n hn
  have hIntSeq (k : ℕ) : Integrable (fun z : SpaceTime => dotL
      (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) (G z)) μ :=
    integrable_dotL_of_memLp_holder (hseq k) hG
  have hτ : ∀ᵐ τ : ℝ ∂(volume : Measure ℝ), τ ≠ P := by
    simpa [ae_iff, measure_singleton]
  have hτz : ∀ᵐ z : SpaceTime ∂(volume : Measure SpaceTime), z.1 ≠ P := by
    have h : ∀ᵐ z : ℝ × Space ∂((volume : Measure ℝ).prod (volume : Measure Space)),
        z.1 ≠ P := Measure.quasiMeasurePreserving_fst.ae hτ
    simpa [Measure.volume_eq_prod] using h
  have hcell : MeasurableSet (phaseCell P) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hgradEqAE (k : ℕ) : (fun z : SpaceTime =>
      PhaseSpace.gradT (perT P (nestedCutoffMollification P n k Φ U)) z) =ᵐ[μ]
      (fun z : SpaceTime => PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) := by
    obtain ⟨_, _, htime, _⟩ :=
      nestedCutoffMollification_isCompactInteriorTest
        (P := P) (n := n) (k := k) hΦ hU hn
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    have hB : P - δ < P := by dsimp [δ]; linarith
    filter_upwards [ae_restrict_mem hcell, ae_restrict_of_ae hτz] with z hz hτP
    have hτlt : z.1 < P := lt_of_le_of_ne hz.1.2 hτP
    exact gradT_perT_eq_self_on_Ioo (P := P) Fact.out hδ hB htime
      hz.1.1 hτlt z.2
  have hzeroSeq (k : ℕ) : ∫ z : SpaceTime,
      dotL (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) (G z) ∂μ = 0 := by
    obtain ⟨_, _, htime, hG0⟩ :=
      nestedCutoffMollification_isCompactInteriorTest
        (P := P) (n := n) (k := k) hΦ hU hn
    have hperiod : IsPhaseTest P (perT P (nestedCutoffMollification P n k Φ U)) :=
      isPhaseTest_perT Fact.out htime hG0
    have hzero := integral_phaseTest_gradient_pair_boundedSolenoidal_zero
      hperiod hV hsol
    calc
      ∫ z : SpaceTime, dotL
          (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) (G z) ∂μ =
          ∫ z : SpaceTime, dotL
            (PhaseSpace.gradT (perT P (nestedCutoffMollification P n k Φ U)) z) (G z) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hgradEqAE k] with z hz
        rw [hz]
      _ = 0 := hzero
  have hconv : Tendsto (fun k : ℕ => eLpNorm
      ((fun z : SpaceTime => PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) - F)
      1 μ) atTop (𝓝 0) := hconv0
  have hlimit := tendsto_integral_dotL_of_eLpNorm hFcut hG hseq hconv
  have hconst : Tendsto (fun k : ℕ => ∫ z : SpaceTime,
      dotL (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) (G z) ∂μ)
      atTop (𝓝 0) := tendsto_const_nhds.congr' (Eventually.of_forall fun k => (hzeroSeq k).symm)
  have huniq := tendsto_nhds_unique hconst hlimit
  simpa [F, G, μ] using huniq.symm

#print axioms integral_cutoffSquared_scalarSliceGrad_pair_boundedSolenoidal_zero

end UnforcedLeray.Cons.C03.Concrete
