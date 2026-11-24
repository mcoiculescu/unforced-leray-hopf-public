import UnforcedLeray.Lib.TrainB.InitialDatumP0H3Fixed
import UnforcedLeray.Lib.TrainB.DatumHeatCommutation
import UnforcedLeray.Lib.HeatCylinder.HeatVecGeneralDerivative
import UnforcedLeray.Lib.HeatCylinder.HeatVecConvolution
import UnforcedLeray.Lib.HeatCylinder.HeatVecDerivative
import UnforcedLeray.Lib.HeatCylinder.WeakOutput
import UnforcedLeray.Lib.HeatCylinder.CellBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem datumHeat_measure_eq_cell (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW c (0 : ℝ), Cyl.wμ]
  simp [Cyl.ρw]

private theorem periodic_fderiv_datumHeat {c : ℝ} {u : Plane → Vec}
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

private theorem iterD_periodic_datumHeat {c : ℝ} {u : Plane → Vec}
    (hper : Cyl.IsPeriodic c u) : ∀ vs : List Plane, Cyl.IsPeriodic c (Sob.iterD vs u)
  | [] => by simpa using hper
  | v :: vs => by
      simpa only [Sob.iterD_cons] using periodic_fderiv_datumHeat
        (iterD_periodic_datumHeat hper vs) v

/-- Gaussian convolution preserves exact period-c pointwise periodicity. This uses only equality
of the actual integrands under the horizontal period shift. -/
theorem heatVecConvolution_periodic_of_periodic {c θ : ℝ} {T : Plane → Vec}
    (hT : Cyl.IsPeriodic c T) :
    Cyl.IsPeriodic c (HeatCylinder.heatVecConvolution θ T) := by
  intro z
  unfold HeatCylinder.heatVecConvolution
  apply integral_congr_ae
  filter_upwards [] with w
  have harg : ((z.1 + c, z.2) - w) = ((z - w).1 + c, (z - w).2) := by
    ext <;> simp <;> ring
  rw [harg]
  have hper' := hT (z - w)
  simpa only [hper']

private theorem heatDatum_iterD_differentiable {c θ : ℝ} (hc : 2 ≤ c)
    (hθ : 0 < θ) (vs : List Plane) :
    Differentiable ℝ (HeatCylinder.heatVecConvolution θ
      (Sob.iterD vs (Train.datum c))) := by
  obtain ⟨M₀, hM₀⟩ := datum_iterD_global_bound hc vs
  obtain ⟨M₁, hM₁⟩ := datum_fderiv_iterD_global_bound hc vs
  intro z
  exact (HeatCylinder.hasFDerivAt_heatVecConvolution hθ
    ((Sob.contDiff_iterD (Train.datum_contDiff (by linarith)) vs).of_le (by norm_num))
    hM₀ hM₁ z).differentiableAt

private theorem heatDatum_iterD_output_differentiable {c θ : ℝ} (hc : 2 ≤ c)
    (hθ : 0 < θ) (vs : List Plane) :
    Differentiable ℝ (Sob.iterD vs
      (HeatCylinder.heatVecConvolution θ (Train.datum c))) := by
  rw [datum_iterD_heatVecConvolution_commute hc hθ vs]
  exact heatDatum_iterD_differentiable hc hθ vs

private theorem heatDatum_fderiv_eq_next {c θ : ℝ} (hc : 2 ≤ c)
    (hθ : 0 < θ) (vs : List Plane) (e : Plane) (z : Plane) :
    fderiv ℝ (Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c))) z e =
      HeatCylinder.heatVecConvolution θ
        (Sob.iterD (e :: vs) (Train.datum c)) z := by
  rw [datum_iterD_heatVecConvolution_commute hc hθ vs]
  rw [HeatCylinder.fderiv_heatVecConvolution_apply_of_bounds hθ
    ((Sob.contDiff_iterD (Train.datum_contDiff (by linarith)) vs).of_le (by norm_num))
    (datum_iterD_global_bound hc vs).choose_spec
    (datum_fderiv_iterD_global_bound hc vs).choose_spec z e]
  rfl

private theorem heatDatum_iterD_fderiv_continuous {c θ : ℝ} (hc : 2 ≤ c)
    (hθ : 0 < θ) (vs : List Plane) (e : Plane) :
    Continuous (fun z => fderiv ℝ (Sob.iterD vs
      (HeatCylinder.heatVecConvolution θ (Train.datum c))) z e) := by
  have hEq : (fun z => fderiv ℝ (Sob.iterD vs
      (HeatCylinder.heatVecConvolution θ (Train.datum c))) z e) =
      HeatCylinder.heatVecConvolution θ (Sob.iterD (e :: vs) (Train.datum c)) :=
    funext (heatDatum_fderiv_eq_next hc hθ vs e)
  rw [hEq]
  exact (heatDatum_iterD_differentiable hc hθ (e :: vs)).continuous

private theorem datumHeatField_memLp {c θ : ℝ} (hc : 2 ≤ c) (hθ : 0 < θ)
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
    have hp := iterD_periodic_datumHeat (Train.datum_periodic c) vs z
    simpa [Cyl.IsPeriodic, B0284.IsQPeriodic] using hp
  have hcpos : 0 < c := by linarith
  have hcenter : MemLp (Sob.iterD vs (Train.datum c)) 2 (Cyl.cellμ c) := by
    have h := datumH3Field_memLp hcpos α
    have hm := congrArg (fun μ : Measure Plane =>
      MemLp (datumH3Field (c := c) α) 2 μ) (datumHeat_measure_eq_cell c)
    have ht : datumH3Field (c := c) α = Sob.iterD vs (Train.datum c) := by
      rfl
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
    refine ⟨(heatDatum_iterD_differentiable hc hθ vs).continuous.measurable.aestronglyMeasurable,
      htop⟩
  have hperOut := heatVecConvolution_periodic_of_periodic
    (c := c) (θ := θ) (T := Sob.iterD vs (Train.datum c))
    (iterD_periodic_datumHeat (Train.datum_periodic c) vs)
  have hmeasOut : Measurable (HeatCylinder.heatVecConvolution θ
      (Sob.iterD vs (Train.datum c))) :=
    (heatDatum_iterD_differentiable hc hθ vs).continuous.measurable
  have houtCell := HeatCylinder.memLp_cyl_of_memLp_cellMeasure hcpos
    hmeasOut (by simpa [B0284.IsQPeriodic, Cyl.IsPeriodic] using hperOut) hout
  rw [hEq]
  exact houtCell

private theorem integrableOn_test_smul_continuous {c : ℝ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ)
    {u : Plane → F} (hu : Continuous u) :
    Integrable (fun z => φ z • u z) (volume.restrict (Cyl.cell c)) := by
  obtain ⟨R, hR⟩ := hφ.bounded
  have h := Sob.integrableOn_cylCell (c := c)
    (hφ.smooth.continuous.smul hu) (R := R) (fun z hz => by
      change φ z • u z = 0
      rw [hR z hz, zero_smul])
  change Integrable (fun z => φ z • u z) (volume.restrict (Cyl.cell c))
  rw [Sob.cyl_cell_eq]
  exact h

private theorem hasWeakDeriv_heatDatum_iterD {c θ : ℝ} (hc : 2 ≤ c)
    (hθ : 0 < θ) : ∀ vs : List Plane,
    Sob.HasWeakDeriv (Sob.cylinder c) vs
      (HeatCylinder.heatVecConvolution θ (Train.datum c))
      (Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c))) := by
  intro vs
  induction vs with
  | nil =>
      refine Sob.HasWeakDeriv.nil fun φ hφ => ?_
      have hφ' : Sob.IsCylTest c φ := hφ
      have hu := heatDatum_iterD_differentiable hc hθ []
      have huc := hu.continuous
      have hInt := integrableOn_test_smul_continuous hφ' huc
      simpa [Sob.cylinder_μ, Sob.cyl_cell_eq] using hInt
  | cons e vs ih =>
      have hu := heatDatum_iterD_output_differentiable hc hθ vs
      have huc := hu.continuous
      have hper : Cyl.IsPeriodic c
          (Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c))) := by
        rw [datum_iterD_heatVecConvolution_commute hc hθ vs]
        exact heatVecConvolution_periodic_of_periodic
          (iterD_periodic_datumHeat (Train.datum_periodic c) vs)
      have hweak := HeatCylinder.hasWeakDeriv_cylinder_dir_of_continuous_fderiv
        (by linarith : 0 < c) hu huc hper
        (heatDatum_iterD_fderiv_continuous hc hθ vs) e
      have htarget : (fun z => fderiv ℝ
          (Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c))) z e) =
          Sob.iterD (e :: vs) (HeatCylinder.heatVecConvolution θ (Train.datum c)) := by
        funext z
        simpa only [Sob.iterD_cons] using heatDatum_fderiv_eq_next hc hθ vs e z
      have hweak' := hweak.congr_ae (Filter.Eventually.of_forall fun _ => rfl)
        (Filter.Eventually.of_forall fun z => congrFun htarget z)
      exact ih.cons hweak'

/-- The actual positive-age Gaussian heat of the noncompact periodized Train datum is a genuine
centered-cell H³ class. The graph fields are the classical ordered derivatives of the literal
Gaussian convolution. -/
noncomputable def datumHeatVecH3 {c θ : ℝ} (hc : 2 ≤ c) (hθ : 0 < θ) : VecH3 c := by
  let g : Sob.Idx 2 3 → Plane → Vec := fun α =>
    Sob.iterD ((Sob.cylinder c).word α)
      (HeatCylinder.heatVecConvolution θ (Train.datum c))
  have hmem : ∀ α, MemLp (g α) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    intro α
    rw [datumHeat_measure_eq_cell]
    exact datumHeatField_memLp hc hθ α
  have hweak : ∀ α : Sob.Idx 2 3,
      Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α)
        (g Sob.Idx.zero) (g α) := by
    intro α
    have h := hasWeakDeriv_heatDatum_iterD hc hθ ((Sob.cylinder c).word α)
    simpa [g, Sob.TestDomain.word_zero, Sob.iterD_nil] using h
  exact Sob.W.ofFields (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec) (k := 3) (p := 2) g hmem hweak

/-- The actual order-zero value of the datum heat H³ class is the literal Gaussian convolution. -/
theorem datumHeatVecH3_value_ae {c θ : ℝ} (hc : 2 ≤ c) (hθ : 0 < θ) :
    (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
      (datumHeatVecH3 hc hθ) : Plane → Vec) =ᵐ[Cyl.cellμ c]
      HeatCylinder.heatVecConvolution θ (Train.datum c) := by
  rw [datumHeatVecH3, Sob.W.value_ofFields]
  rw [← datumHeat_measure_eq_cell c]
  have hmem := datumHeatField_memLp hc hθ Sob.Idx.zero
  have hmemW : MemLp (Sob.iterD ((Sob.cylinder c).word Sob.Idx.zero)
      (HeatCylinder.heatVecConvolution θ (Train.datum c))) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
    (congrArg (fun μ : Measure Plane => MemLp
      (Sob.iterD ((Sob.cylinder c).word Sob.Idx.zero)
        (HeatCylinder.heatVecConvolution θ (Train.datum c))) 2 μ)
      (datumHeat_measure_eq_cell c).symm).mp hmem
  filter_upwards [hmemW.coeFn_toLp] with z hz
  simpa [Cyl.word_zero, Sob.iterD_nil] using hz

#print axioms UnforcedLeray.TrainB.heatVecConvolution_periodic_of_periodic
#print axioms UnforcedLeray.TrainB.datumHeatVecH3
#print axioms UnforcedLeray.TrainB.datumHeatVecH3_value_ae

end UnforcedLeray.TrainB
