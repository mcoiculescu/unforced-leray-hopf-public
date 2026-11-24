import UnforcedLeray.Lib.TrainB.DatumHeatH3
import UnforcedLeray.Lib.TrainB.P0H3FixOfComponents
import UnforcedLeray.Lib.TrainB.WeakDivFreeC1
import UnforcedLeray.Lib.HeatCylinder.HeatVecConvolution
import UnforcedLeray.Lib.TrainB.DatumHeatSolenoidal

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem datumHeatH3_measure_eq_cell (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW c (0 : ℝ), Cyl.wμ]
  simp [Cyl.ρw]

private theorem datumHeat_fderiv_iterD {c θ : ℝ} (hc : 2 ≤ c) (hθ : 0 < θ)
    (vs : List Plane) (e z : Plane) :
    fderiv ℝ (Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c))) z e =
      HeatCylinder.heatVecConvolution θ (Sob.iterD (e :: vs) (Train.datum c)) z := by
  rw [datum_iterD_heatVecConvolution_commute hc hθ vs]
  rw [HeatCylinder.fderiv_heatVecConvolution_apply_of_bounds hθ
    ((Sob.contDiff_iterD (Train.datum_contDiff (by linarith)) vs).of_le (by norm_num))
    (datum_iterD_global_bound hc vs).choose_spec
    (datum_fderiv_iterD_global_bound hc vs).choose_spec z e]
  rfl

private theorem datumHeat_iterD_differentiable {c θ : ℝ} (hc : 2 ≤ c)
    (hθ : 0 < θ) (vs : List Plane) :
    Differentiable ℝ (Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c))) := by
  rw [datum_iterD_heatVecConvolution_commute hc hθ vs]
  obtain ⟨M₀, hM₀⟩ := datum_iterD_global_bound hc vs
  obtain ⟨M₁, hM₁⟩ := datum_fderiv_iterD_global_bound hc vs
  intro z
  exact (HeatCylinder.hasFDerivAt_heatVecConvolution hθ
    ((Sob.contDiff_iterD (Train.datum_contDiff (by linarith)) vs).of_le (by norm_num))
    hM₀ hM₁ z).differentiableAt

private theorem datumHeat_iterD_fderiv_continuous {c θ : ℝ} (hc : 2 ≤ c)
    (hθ : 0 < θ) (vs : List Plane) (e : Plane) :
    Continuous (fun z => fderiv ℝ (Sob.iterD vs
      (HeatCylinder.heatVecConvolution θ (Train.datum c))) z e) := by
  have hEq : (fun z => fderiv ℝ (Sob.iterD vs
      (HeatCylinder.heatVecConvolution θ (Train.datum c))) z e) =
      HeatCylinder.heatVecConvolution θ (Sob.iterD (e :: vs) (Train.datum c)) := by
    funext z
    exact datumHeat_fderiv_iterD hc hθ vs e z
  rw [hEq]
  simpa only [datum_iterD_heatVecConvolution_commute hc hθ (e :: vs)] using
    (datumHeat_iterD_differentiable hc hθ (e :: vs)).continuous

private theorem datumHeat_iterD_contDiff_one {c θ : ℝ} (hc : 2 ≤ c)
    (hθ : 0 < θ) (vs : List Plane) :
    ContDiff ℝ 1 (Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c))) := by
  rw [contDiff_one_iff_fderiv]
  constructor
  · exact datumHeat_iterD_differentiable hc hθ vs
  · rw [continuous_clm_apply]
    intro e
    exact datumHeat_iterD_fderiv_continuous hc hθ vs e

private theorem periodic_fderiv_datumHeatP0 {c : ℝ} {u : Plane → Vec}
    (hper : Cyl.IsPeriodic c u) (v : Plane) :
    Cyl.IsPeriodic c (fun z => fderiv ℝ u z v) := by
  intro z
  change fderiv ℝ u (z.1 + c, z.2) v = fderiv ℝ u z v
  have e : (fun y : Plane => u (y + (c, 0))) = u := by
    funext y
    have hy : y + (c, 0) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hper y
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := z) ((c, 0) : Plane)
  rw [e] at hd
  have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
  rw [← hz, ← hd]

private theorem iterD_periodic_datumHeatP0 {c : ℝ} {u : Plane → Vec}
    (hper : Cyl.IsPeriodic c u) : ∀ vs : List Plane, Cyl.IsPeriodic c (Sob.iterD vs u)
  | [] => by simpa using hper
  | v :: vs => by
      simpa only [Sob.iterD_cons] using
        periodic_fderiv_datumHeatP0 (iterD_periodic_datumHeatP0 hper vs) v

private theorem datumHeatField_memLp_cell {c θ : ℝ} (hc : 2 ≤ c) (hθ : 0 < θ)
    (α : Sob.Idx 2 3) :
    MemLp (Sob.iterD ((Sob.cylinder c).word α)
      (HeatCylinder.heatVecConvolution θ (Train.datum c))) 2 (Cyl.cellμ c) := by
  let vs := (Sob.cylinder c).word α
  have hEq : Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c)) =
      HeatCylinder.heatVecConvolution θ (Sob.iterD vs (Train.datum c)) :=
    datum_iterD_heatVecConvolution_commute hc hθ vs
  have hmeasIn : Measurable (Sob.iterD vs (Train.datum c)) :=
    (Sob.contDiff_iterD (Train.datum_contDiff (by linarith)) vs).continuous.measurable
  have hperIn : B0284.IsQPeriodic c (Sob.iterD vs (Train.datum c)) := by
    intro z
    have hp := iterD_periodic_datumHeatP0 (Train.datum_periodic c) vs z
    simpa [Cyl.IsPeriodic, B0284.IsQPeriodic] using hp
  have hcpos : 0 < c := by linarith
  have hcenter : MemLp (Sob.iterD vs (Train.datum c)) 2 (Cyl.cellμ c) := by
    have h := datumH3Field_memLp hcpos α
    have hm := congrArg (fun μ : Measure Plane =>
      MemLp (datumH3Field (c := c) α) 2 μ) (datumHeatH3_measure_eq_cell c)
    have ht : datumH3Field (c := c) α = Sob.iterD vs (Train.datum c) := rfl
    rw [← ht]
    exact hm.mp h
  have hnormalized := HeatCylinder.memLp_cellMeasure_of_memLp_cyl hcpos
    hmeasIn hperIn hcenter
  have hInAesm : AEStronglyMeasurable (Sob.iterD vs (Train.datum c)) volume :=
    hmeasIn.aestronglyMeasurable
  have hcontract := HeatCylinder.eLpNorm_heatVecConvolution_le hcpos hθ hperIn
    hInAesm (by norm_num) ENNReal.ofNat_ne_top
  have htop : eLpNorm (HeatCylinder.heatVecConvolution θ
      (Sob.iterD vs (Train.datum c))) 2 (B0284.cellMeasure c) < ⊤ :=
    lt_of_le_of_lt hcontract hnormalized.eLpNorm_ne_top.lt_top
  have hout : MemLp (HeatCylinder.heatVecConvolution θ
      (Sob.iterD vs (Train.datum c))) 2 (B0284.cellMeasure c) := by
    have hdiff : Differentiable ℝ (HeatCylinder.heatVecConvolution θ
        (Sob.iterD vs (Train.datum c))) := by
      simpa only [datum_iterD_heatVecConvolution_commute hc hθ vs] using
        datumHeat_iterD_differentiable hc hθ vs
    refine ⟨hdiff.continuous.measurable.aestronglyMeasurable, htop⟩
  have hperOut := TrainB.heatVecConvolution_periodic_of_periodic
    (c := c) (θ := θ) (T := Sob.iterD vs (Train.datum c))
    (iterD_periodic_datumHeatP0 (Train.datum_periodic c) vs)
  have hdiffOut : Differentiable ℝ (HeatCylinder.heatVecConvolution θ
      (Sob.iterD vs (Train.datum c))) := by
    simpa only [datum_iterD_heatVecConvolution_commute hc hθ vs] using
      datumHeat_iterD_differentiable hc hθ vs
  have hmeasOut : Measurable (HeatCylinder.heatVecConvolution θ
      (Sob.iterD vs (Train.datum c))) := hdiffOut.continuous.measurable
  have houtCell := HeatCylinder.memLp_cyl_of_memLp_cellMeasure hcpos
    hmeasOut (by simpa [B0284.IsQPeriodic, Cyl.IsPeriodic] using hperOut) hout
  rw [hEq]
  exact houtCell

/-- The centered H³ derivative component of the actual datum heat is the L² class of its literal
ordered derivative field. -/
theorem datumHeatVecH3_component_eq {c θ : ℝ} (hc : 2 ≤ c) (hθ : 0 < θ)
    (α : Sob.Idx 2 3) :
    vecH3CellDerivCLM α (datumHeatVecH3 hc hθ) =
      (datumHeatField_memLp_cell hc hθ α).toLp
        (Sob.iterD ((Sob.cylinder c).word α)
          (HeatCylinder.heatVecConvolution θ (Train.datum c))) := by
  let f : Plane → Vec := Sob.iterD ((Sob.cylinder c).word α)
    (HeatCylinder.heatVecConvolution θ (Train.datum c))
  change weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
        ℝ Vec 3 2 α (datumHeatVecH3 hc hθ)) =
      (datumHeatField_memLp_cell hc hθ α).toLp f
  unfold datumHeatVecH3
  rw [Sob.W.deriv_ofFields]
  let hmW : MemLp f 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    have hh := datumHeatField_memLp_cell hc hθ α
    exact (congrArg (fun μ : Measure Plane => MemLp f 2 μ)
      (datumHeatH3_measure_eq_cell c)).mpr hh
  let hmCell := datumHeatField_memLp_cell hc hθ α
  apply Lp.ext
  let hMP : MeasurePreserving id (Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← datumHeatH3_measure_eq_cell c]
    exact MeasurePreserving.id _
  change (Lp.compMeasurePreserving id hMP (hmW.toLp f) : Cyl.L2v c) =ᵐ[Cyl.cellμ c]
    (hmCell.toLp f : Plane → Vec)
  have hmap := Lp.coeFn_compMeasurePreserving (hmW.toLp f) hMP
  have hcoeW := hMP.quasiMeasurePreserving.ae hmW.coeFn_toLp
  have hcoeCell := hmCell.coeFn_toLp
  filter_upwards [hmap, hcoeW, hcoeCell] with z hzMap hzW hzCell
  calc
    ((Lp.compMeasurePreserving id hMP (hmW.toLp f) : Cyl.L2v c) : Plane → Vec) z =
        (hmW.toLp f : Lp Vec 2
          (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) z := by
            simpa [Function.comp_id] using hzMap
    _ = f z := hzW
    _ = hmCell.toLp f z := hzCell.symm

/-- Every ordered derivative component of the actual positive-age heat of the Train datum is
weakly solenoidal. This is a datum-specific statement, obtained from the literal heat divergence
identity and the actual centered-cell Gaussian-tail integrability. -/
theorem datumHeatVecH3_components_divFree {c θ : ℝ} (hc : 2 ≤ c) (hθ : 0 < θ) :
    ∀ α : Sob.Idx 2 3, vecH3CellDerivCLM α (datumHeatVecH3 hc hθ) ∈ Cyl.divFree c := by
  intro α
  rw [datumHeatVecH3_component_eq hc hθ α]
  let vs := (Sob.cylinder c).word α
  have hperIn : B0284.IsQPeriodic c (Sob.iterD vs (Train.datum c)) := by
    intro z
    have hp := iterD_periodic_datumHeatP0 (Train.datum_periodic c) vs z
    simpa [Cyl.IsPeriodic, B0284.IsQPeriodic] using hp
  have hperOut := TrainB.heatVecConvolution_periodic_of_periodic
    (c := c) (θ := θ) (T := Sob.iterD vs (Train.datum c)) hperIn
  have hdivConv : ∀ z, Cyl.divergence
      (HeatCylinder.heatVecConvolution θ (Sob.iterD vs (Train.datum c))) z = 0 :=
    datum_iterD_heatVecConvolution_divergence_zero hc hθ vs
  have hdiv : ∀ z, Cyl.divergence
      (Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c))) z = 0 := by
    intro z
    simpa only [datum_iterD_heatVecConvolution_commute hc hθ vs] using hdivConv z
  have hper : Cyl.IsPeriodic c
      (Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c))) := by
    rw [datum_iterD_heatVecConvolution_commute hc hθ vs]
    simpa [Cyl.IsPeriodic, B0284.IsQPeriodic] using hperOut
  exact mem_divFree_of_C1_divergence_zero (by linarith : 0 < c)
    (datumHeat_iterD_contDiff_one hc hθ vs) hper hdiv (datumHeatField_memLp_cell hc hθ α)

/-- The componentwise H³ Leray projection fixes the complete actual Gaussian heat of the Train
datum at every positive age. -/
theorem P0H3CLM_datumHeatVecH3_eq {c θ : ℝ} (hc : 2 ≤ c) (hθ : 0 < θ) :
    P0H3CLM (by linarith : 0 < c) (datumHeatVecH3 hc hθ) = datumHeatVecH3 hc hθ :=
  P0H3CLM_eq_self_of_components_divFree (by linarith : 0 < c) (datumHeatVecH3 hc hθ)
    (datumHeatVecH3_components_divFree hc hθ)

#print axioms UnforcedLeray.TrainB.datumHeatVecH3_component_eq
#print axioms UnforcedLeray.TrainB.datumHeatVecH3_components_divFree
#print axioms UnforcedLeray.TrainB.P0H3CLM_datumHeatVecH3_eq

end UnforcedLeray.TrainB
