import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellLp

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.Sob

/-- The actual compact-test/background product converges to its cell representative after
removing the two phase seams in any finite `L^p` norm. -/
theorem tendsto_scalarTestBackground_phaseCutoff_cell {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Tendsto (fun n : ℕ => eLpNorm
      ((fun z : SpaceTime => phaseInteriorCutoff P n z.1 • scalarTestBackground Φ U z) -
        (phaseCell P).indicator (fun z => scalarTestBackground Φ U z)) p volume)
      atTop (𝓝 0) := by
  apply tendsto_phaseInteriorCutoff_on_cell Fact.out hp
  exact scalarTestBackground_memLp_cell hΦ hU hp

/-- Each spatial derivative of the actual compact-test/background product converges on the
reference cell after removal of the phase seams. -/
theorem tendsto_scalarTestBackground_spatialDerivative_phaseCutoff_cell
    {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (j : Fin 3) :
    Tendsto (fun n : ℕ => eLpNorm
      ((fun z : SpaceTime => phaseInteriorCutoff P n z.1 •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))) -
        (phaseCell P).indicator (fun z : SpaceTime =>
          fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
            (EuclideanSpace.single j (1 : ℝ)))) p volume)
      atTop (𝓝 0) := by
  apply tendsto_phaseInteriorCutoff_on_cell Fact.out hp
  exact scalarTestBackground_spatialDerivative_memLp_cell hΦ hU hp j

/-- A cutoff version of the actual product has global finite `L^p` integrability, so its genuine
spacetime mollifications converge to it in `L^p`. -/
theorem tendsto_spacetimeMollification_cutoff_scalarTestBackground
    {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (n : ℕ) :
    Tendsto (fun k : ℕ => eLpNorm
      (moll (spacetimeShrinkBump k) volume
        ((fun z : SpaceTime => phaseCutoffSpaceTime (phaseInteriorCutoff P n) z •
          scalarTestBackground Φ U z) ∘ spacetimeHilbertEquiv.symm) -
        ((fun z : SpaceTime => phaseCutoffSpaceTime (phaseInteriorCutoff P n) z •
          scalarTestBackground Φ U z) ∘ spacetimeHilbertEquiv.symm)) p volume)
      atTop (𝓝 0) := by
  have hcell := scalarTestBackground_memLp_cell hΦ hU hp
  have hcut : MemLp (fun z : SpaceTime => phaseCutoffSpaceTime
      (phaseInteriorCutoff P n) z • scalarTestBackground Φ U z) p volume := by
    simpa [phaseCutoffSpaceTime] using
      (memLp_phaseInteriorCutoff_of_cell_memLp (P := P) hcell n)
  exact tendsto_spacetimeMollification hp (memLp_spacetimeHilbertPullback hcut)

/-- The mollified cutoff product has the exact mollified spatial derivative supplied by its
actual weak derivative. -/
theorem iterDD_mollification_cutoff_scalarTestBackground
    {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (n : ℕ) (j : Fin 3) :
    iterDD [spacetimeHilbertEquiv (scalarTestSpaceTimeDir j)]
      (moll (spacetimeShrinkBump n) volume
        ((fun z : SpaceTime => phaseCutoffSpaceTime (phaseInteriorCutoff P n) z •
          scalarTestBackground Φ U z) ∘ spacetimeHilbertEquiv.symm)) =
    moll (spacetimeShrinkBump n) volume
      ((fun z : SpaceTime => phaseCutoffSpaceTime (phaseInteriorCutoff P n) z •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))) ∘ spacetimeHilbertEquiv.symm) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hcell := scalarTestBackground_memLp_cell (p := 2) hΦ hU (by norm_num)
  have hcut : MemLp (fun z : SpaceTime => phaseCutoffSpaceTime
      (phaseInteriorCutoff P n) z • scalarTestBackground Φ U z) 2 volume := by
    simpa [phaseCutoffSpaceTime] using
      (memLp_phaseInteriorCutoff_of_cell_memLp (P := P) hcell n)
  exact iterDD_cutoff_scalarTestBackground_mollification_of_cellLp
    (P := P) (hΦ := hΦ) (hU := hU) (hχ := contDiff_phaseInteriorCutoff P n)
    (p := 2) (j := j) (n := n) hcut

#print axioms tendsto_scalarTestBackground_phaseCutoff_cell
#print axioms tendsto_scalarTestBackground_spatialDerivative_phaseCutoff_cell
#print axioms tendsto_spacetimeMollification_cutoff_scalarTestBackground
#print axioms iterDD_mollification_cutoff_scalarTestBackground

end UnforcedLeray.Cons.C03.Concrete
