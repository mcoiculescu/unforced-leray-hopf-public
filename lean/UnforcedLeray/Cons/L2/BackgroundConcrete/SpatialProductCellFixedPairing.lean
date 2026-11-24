import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellVectorLimit
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellLpBridge
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellVectorLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairingLimit
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellTest
import UnforcedLeray.Cons.L2.BackgroundConcrete.PeriodizedCellPair

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412
open UnforcedLeray.PhaseTrace

/-- At a fixed phase cutoff, actual phase solenoidality annihilates the rough spatial-slice
gradient obtained as the limit of the periodized smooth cutoff-mollification gradients. -/
theorem integral_cutoffSquared_scalarSliceGrad_pair_rep_zero {P : ℝ} [Fact (0 < P)]
    {w : Yq P q0E} (hw : IsPhaseSolenoidal w)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [ENNReal.HolderTriple p q0E 1]
    (n : ℕ) (hn : 2 / ((n : ℝ) + 1) ≤ P) :
    ∫ z : SpaceTime, dotL
      ((phaseInteriorCutoff P n z.1) ^ 2 • scalarSliceGrad (scalarTestBackground Φ U) z)
      (rep w z.1 z.2) ∂(volume.restrict (phaseCell P)) = 0 := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let G : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  let F : SpaceTime → CVec3 := fun z =>
    (phaseInteriorCutoff P n z.1) ^ 2 • scalarSliceGrad (scalarTestBackground Φ U) z
  have hG : MemLp G q0E μ := by
    simpa [G, μ, phaseCell] using memLp_rep_periodCell q0E_ne_top w
  have hF : MemLp F p μ := by
    exact memLp_cutoffSquared_scalarSliceGrad_cell hΦ hU hp n
  have hseq : ∀ k : ℕ, MemLp
      (fun z : SpaceTime => PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z)
      p μ := by
    intro k
    exact memLp_nestedCutoff_gradT_cell hΦ hU hp n k hn
  have hconv0 : Tendsto (fun k : ℕ => eLpNorm
      (fun z : SpaceTime => PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z -
        (phaseInteriorCutoff P n z.1) ^ 2 • scalarSliceGrad (scalarTestBackground Φ U) z)
        p μ) atTop (𝓝 0) := by
    simpa [μ] using tendsto_nestedCutoff_gradT_cellLp hΦ hU hp n hn
  have hseqEq (k : ℕ) : eLpNorm
      (fun z : SpaceTime => PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z -
        (phaseInteriorCutoff P n z.1) ^ 2 • scalarSliceGrad (scalarTestBackground Φ U) z)
      p μ = eLpNorm
      ((fun z : SpaceTime => PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) - F)
      p μ := by
    congr 1
  have hconv : Tendsto (fun k : ℕ => eLpNorm
      ((fun z : SpaceTime => PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) - F)
        p μ) atTop (𝓝 0) :=
    hconv0.congr' (Eventually.of_forall hseqEq)
  have hIntSeq (k : ℕ) : Integrable (fun z : SpaceTime => dotL
      (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) (G z)) μ :=
    integrable_dotL_of_memLp_holder (hseq k) hG
  have hIntF : Integrable (fun z : SpaceTime => dotL (F z) (G z)) μ :=
    integrable_dotL_of_memLp_holder hF hG
  have hτ : ∀ᵐ τ : ℝ ∂(volume : Measure ℝ), τ ≠ P := by
    simpa [ae_iff, measure_singleton]
  have hτz : ∀ᵐ z : SpaceTime ∂(volume : Measure SpaceTime), z.1 ≠ P := by
    have h : ∀ᵐ z : ℝ × Space ∂((volume : Measure ℝ).prod (volume : Measure Space)),
        z.1 ≠ P := Measure.quasiMeasurePreserving_fst.ae hτ
    simpa [Measure.volume_eq_prod] using h
  have hcell : MeasurableSet (phaseCell P) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hpairEq (k : ℕ) :
      pairF P (fun z : SpaceTime => PhaseSpace.gradT
        (nestedCutoffMollification P n k Φ U) z) G =
      pairF P (PhaseSpace.gradT (perT P (nestedCutoffMollification P n k Φ U))) G := by
    obtain ⟨_, _, htime, _⟩ :=
      nestedCutoffMollification_isCompactInteriorTest
        (P := P) (n := n) (k := k) hΦ hU hn
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    have hB : P - δ < P := by dsimp [δ]; linarith
    have hAE : (fun z : SpaceTime => dotL
        (PhaseSpace.gradT (perT P (nestedCutoffMollification P n k Φ U)) z) (G z)) =ᵐ[μ]
        (fun z : SpaceTime => dotL
          (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) (G z)) := by
      filter_upwards [ae_restrict_mem hcell, ae_restrict_of_ae hτz] with z hz hτP
      have hτlt : z.1 < P := lt_of_le_of_ne hz.1.2 hτP
      have hgrad := gradT_perT_eq_self_on_Ioo (P := P) Fact.out hδ hB htime
        hz.1.1 hτlt z.2
      rw [hgrad]
    have hIntPer : Integrable (fun z : SpaceTime => dotL
        (PhaseSpace.gradT (perT P (nestedCutoffMollification P n k Φ U)) z) (G z)) μ :=
      (hIntSeq k).congr hAE.symm
    rw [pairF_eq_restrictedProductIntegral (P := P) (hIntSeq k),
      pairF_eq_restrictedProductIntegral (P := P) hIntPer]
    congr 1
    exact integral_congr_ae hAE.symm
  have hzero (k : ℕ) : pairF P
      (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U)) G = 0 := by
    rw [hpairEq k]
    exact phaseSolenoidal_pairF_nestedCutoffMollification_zero hw hΦ hU hn
  have hlim := tendsto_integral_dotL_of_eLpNorm hF hG hseq hconv
  have hIntZero (k : ℕ) : ∫ z : SpaceTime,
      dotL (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) (G z) ∂μ = 0 := by
    have hpEq := hzero k
    rw [pairF_eq_restrictedProductIntegral (P := P) (hIntSeq k)] at hpEq
    have hPne : P ≠ 0 := ne_of_gt (Fact.out : 0 < P)
    have hcinv : (P⁻¹ : ℝ) ≠ 0 := inv_ne_zero hPne
    exact (smul_eq_zero.mp hpEq).resolve_left hcinv
  have hconst : Tendsto (fun k : ℕ => ∫ z : SpaceTime,
      dotL (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z) (G z) ∂μ)
      atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun k => (hIntZero k).symm)
  have huniq := tendsto_nhds_unique hconst hlim
  simpa [F, G, μ] using huniq.symm

#print axioms integral_cutoffSquared_scalarSliceGrad_pair_rep_zero

end UnforcedLeray.Cons.C03.Concrete
