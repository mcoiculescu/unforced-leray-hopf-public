import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellVectorLimit
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellApprox

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace

/-- A smooth compact-interior scalar test has an actual Lp spatial gradient on the phase cell. -/
theorem memLp_nestedCutoff_gradT_cell {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (n k : ℕ) (hn : 2 / ((n : ℝ) + 1) ≤ P) :
    MemLp (PhaseSpace.gradT (nestedCutoffMollification P n k Φ U)) p
      (volume.restrict (phaseCell P)) := by
  obtain ⟨hcd, hcompact, _, _⟩ :=
    nestedCutoffMollification_isCompactInteriorTest
      (P := P) (n := n) (k := k) hΦ hU hn
  have hterm (j : Fin 3) :
      MemLp (fun z : SpaceTime =>
        PhaseSpace.dy j (nestedCutoffMollification P n k Φ U) z •
          EuclideanSpace.single j (1 : ℂ)) p volume := by
    have hc : HasCompactSupport
        (PhaseSpace.dy j (nestedCutoffMollification P n k Φ U)) := by
      change HasCompactSupport
        (fun z : SpaceTime => fderiv ℝ (nestedCutoffMollification P n k Φ U)
          z (0, coordinateVector j))
      exact hcompact.fderiv_apply ℝ (0, coordinateVector j)
    have hcont : Continuous
        (PhaseSpace.dy j (nestedCutoffMollification P n k Φ U)) := by
      exact (hcd.continuous_fderiv (by simp)).clm_apply continuous_const
    have htermc : Continuous (fun z : SpaceTime =>
        PhaseSpace.dy j (nestedCutoffMollification P n k Φ U) z •
          EuclideanSpace.single j (1 : ℂ)) :=
      hcont.smul continuous_const
    exact htermc.memLp_of_hasCompactSupport hc.smul_right
  have hsum := memLp_finsetSum (s := Finset.univ) (fun j _ => hterm j)
  change MemLp (fun z : SpaceTime =>
    ∑ j : Fin 3, PhaseSpace.dy j (nestedCutoffMollification P n k Φ U) z •
      EuclideanSpace.single j (1 : ℂ)) p (volume.restrict (phaseCell P))
  exact hsum.mono_measure Measure.restrict_le_self

/-- The actual phase-cutoff square times a spatial derivative of `Φ·U` has finite Lp on the
phase cell; apply the proved cutoff lifting twice, without a regularity premise on phase time. -/
theorem memLp_cutoffSquared_scalarTestBackground_spatialDerivative_cell
    {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (n : ℕ) (j : Fin 3) :
    MemLp (fun z : SpaceTime =>
      (phaseInteriorCutoff P n z.1) ^ 2 •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))) p
      (volume.restrict (phaseCell P)) := by
  let g : SpaceTime → ℂ := fun z =>
    fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
      (EuclideanSpace.single j (1 : ℝ))
  let χ : SpaceTime → ℂ := fun z => Complex.ofReal (phaseInteriorCutoff P n z.1)
  have hbase : MemLp g p (volume.restrict (phaseCell P)) := by
    exact scalarTestBackground_spatialDerivative_memLp_cell hΦ hU hp j
  have hfirst : MemLp (fun z : SpaceTime => χ z • g z) p volume := by
    simpa [χ, g] using memLp_phaseInteriorCutoff_of_cell_memLp
      (P := P) hbase n
  have hfirstCell : MemLp (fun z : SpaceTime => χ z • g z) p
      (volume.restrict (phaseCell P)) :=
    hfirst.mono_measure Measure.restrict_le_self
  have hsecond : MemLp (fun z : SpaceTime => χ z • (χ z • g z)) p volume := by
    exact memLp_phaseInteriorCutoff_of_cell_memLp (P := P) hfirstCell n
  have heq : (fun z : SpaceTime => χ z • (χ z • g z)) =
      (fun z => (phaseInteriorCutoff P n z.1) ^ 2 • g z) := by
    funext z
    rw [smul_smul]
    simp [χ, pow_two, Complex.ofReal_mul]
  rw [heq] at hsecond
  exact hsecond.mono_measure Measure.restrict_le_self

#print axioms memLp_nestedCutoff_gradT_cell
#print axioms memLp_cutoffSquared_scalarTestBackground_spatialDerivative_cell

end UnforcedLeray.Cons.C03.Concrete
