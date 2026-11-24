import UnforcedLeray.Lib.TrainB.InitialDatumDerivativeSolenoidal
import UnforcedLeray.Lib.TrainB.InitialDatumH3Class
import UnforcedLeray.Lib.TrainB.P0H3FixOfComponents
import UnforcedLeray.Lib.TrainB.ProjectedInitialDatum

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.TrainB

open UnforcedLeray.Cyl (Vec2)

private theorem datumH3_measure_eq_cell (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW c (0 : ℝ), Cyl.wμ]
  simp [Cyl.ρw]

private theorem datumH3Field_memLp_cell {c : ℝ} (hc : 0 < c) (α : Sob.Idx 2 3) :
    MemLp (datumH3Field (c := c) α) 2 (Cyl.cellμ c) :=
  (congrArg (fun μ : Measure Cyl.Plane => MemLp (datumH3Field (c := c) α) 2 μ)
    (datumH3_measure_eq_cell c)).mp (datumH3Field_memLp hc α)

private theorem periodic_fderiv_datum {c : ℝ} {u : Cyl.Plane → Vec2}
    (hper : Cyl.IsPeriodic c u) (v : Cyl.Plane) :
    Cyl.IsPeriodic c (fun z => fderiv ℝ u z v) := by
  intro z
  change fderiv ℝ u (z.1 + c, z.2) v = fderiv ℝ u z v
  have e : (fun y : Cyl.Plane => u (y + (c, 0))) = u := by
    funext y
    have hy : y + (c, 0) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hper y
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := z) ((c, 0) : Cyl.Plane)
  rw [e] at hd
  have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
  rw [← hz, ← hd]

private theorem iterD_periodic_datum {c : ℝ} {u : Cyl.Plane → Vec2}
    (hper : Cyl.IsPeriodic c u) : ∀ vs : List Cyl.Plane, Cyl.IsPeriodic c (Sob.iterD vs u)
  | [] => by simpa using hper
  | v :: vs => by
      simpa only [Sob.iterD_cons] using periodic_fderiv_datum (iterD_periodic_datum hper vs) v

/-- The actual centered-cell component of the Gaussian datum H³ class is the L² class of its
literal ordered classical derivative. -/
theorem datumVecH3_component_eq {c : ℝ} (hc : 0 < c) (α : Sob.Idx 2 3) :
    vecH3CellDerivCLM α (datumVecH3 hc) =
      (datumH3Field_memLp_cell hc α).toLp (datumH3Field α) := by
  change weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
        ℝ Vec2 3 2 α (datumVecH3 hc)) = _
  unfold datumVecH3
  rw [Sob.W.deriv_ofFields]
  let hmW := datumH3Field_memLp hc α
  let hmCell := datumH3Field_memLp_cell hc α
  apply Lp.ext
  let hMP : MeasurePreserving id (Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← datumH3_measure_eq_cell c]
    exact MeasurePreserving.id _
  change (Lp.compMeasurePreserving id hMP
      (hmW.toLp (Sob.iterD ((Sob.cylinder c).word α) (Train.datum c))) :
        Cyl.Plane → Vec2) =ᵐ[Cyl.cellμ c]
      (hmCell.toLp (Sob.iterD ((Sob.cylinder c).word α) (Train.datum c)) :
        Cyl.Plane → Vec2)
  have hmap := Lp.coeFn_compMeasurePreserving
    (hmW.toLp
      (Sob.iterD ((Sob.cylinder c).word α) (Train.datum c))) hMP
  have hcoeW := hMP.quasiMeasurePreserving.ae hmW.coeFn_toLp
  have hcoeCell := hmCell.coeFn_toLp
  filter_upwards [hmap, hcoeW, hcoeCell] with z hzMap hzW hzCell
  calc
    ((Lp.compMeasurePreserving id hMP (hmW.toLp
      (Sob.iterD ((Sob.cylinder c).word α) (Train.datum c))) : Cyl.L2v c) : Cyl.Plane → Vec2) z =
        (hmW.toLp (Sob.iterD ((Sob.cylinder c).word α) (Train.datum c)) :
          Lp Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) z := by
            simpa [Function.comp_id] using hzMap
    _ = Sob.iterD ((Sob.cylinder c).word α) (Train.datum c) z := hzW
    _ = hmCell.toLp (Sob.iterD ((Sob.cylinder c).word α) (Train.datum c)) z := hzCell.symm

/-- Every ordered derivative component of the actual Gaussian datum is weakly solenoidal on the
centered cylinder. The pointwise divergence identity is the all-word commutation theorem, and
membership is the actual periodic-cell integration-by-parts result. -/
theorem datumVecH3_components_divFree {c : ℝ} (hc : 0 < c) :
    ∀ α : Sob.Idx 2 3, vecH3CellDerivCLM α (datumVecH3 hc) ∈ Cyl.divFree c := by
  intro α
  rw [datumVecH3_component_eq hc α]
  have hsmooth : ContDiff ℝ ∞ (datumH3Field (c := c) α) := by
    exact Sob.contDiff_iterD (Train.datum_contDiff hc.ne') ((Sob.cylinder c).word α)
  have hperiodic : Cyl.IsPeriodic c (datumH3Field (c := c) α) := by
    exact iterD_periodic_datum (Train.datum_periodic c) ((Sob.cylinder c).word α)
  have hdiv : ∀ z, Cyl.divergence (datumH3Field (c := c) α) z = 0 := by
    exact datum_iterD_divergence_zero hc.ne' ((Sob.cylinder c).word α)
  exact mem_divFree_of_smooth_divergence_zero hc hsmooth hperiodic hdiv
    (datumH3Field_memLp_cell hc α)

/-- The actual cylinder Leray projector fixes the complete H³ Gaussian datum, because its value
and every ordered spatial derivative are genuinely divergence-free. -/
theorem P0H3CLM_datumVecH3_eq {c : ℝ} (hc : 0 < c) :
    P0H3CLM hc (datumVecH3 hc) = datumVecH3 hc :=
  P0H3CLM_eq_self_of_components_divFree hc (datumVecH3 hc)
    (datumVecH3_components_divFree hc)

/-- The named projected initial state is, as an entire H³ class, the original Gaussian datum. -/
theorem projectedInitialDatumH3_eq_datumVecH3 {c : ℝ} (hc : 0 < c) :
    projectedInitialDatumH3 hc = datumVecH3 hc := by
  exact P0H3CLM_datumVecH3_eq hc

#print axioms UnforcedLeray.TrainB.datumVecH3_component_eq
#print axioms UnforcedLeray.TrainB.datumVecH3_components_divFree
#print axioms UnforcedLeray.TrainB.P0H3CLM_datumVecH3_eq
#print axioms UnforcedLeray.TrainB.projectedInitialDatumH3_eq_datumVecH3

end UnforcedLeray.TrainB
