import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeComponents
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator

/-!
# Smooth H³ component representatives for ordinary heat

The heat and input derivative classes are compared through their actual centered-cell fields;
this keeps the centered and normalized L² quotients distinct.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem heatVecH3_measure_eq_cell_local'' (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

/-- The smooth input derivative has its literal classical representative on the centered cell.
-/
theorem deriv_ofCylSmooth_ae_cell {c : ℝ} (hc : 0 < c) {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (α : UnforcedLeray.Sob.Idx 2 3) :
    (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
      (UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc T hT) : Plane → Vec) =ᵐ[
          UnforcedLeray.Cyl.cellμ c]
      UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T := by
  have hderiv := UnforcedLeray.Sob.W.deriv_ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Vec) (k := 3) (p := 2) hc T hT α
  simpa only [heatVecH3_measure_eq_cell_local'' c] using hderiv

/-- Every centered weak derivative component of the actual smooth Gaussian heat output agrees
almost everywhere with its actual heat-kernel derivative field. -/
theorem deriv_heatVecH3_ae_cell {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
      (heatVecH3 hc hθ hT) : Plane → Vec) =ᵐ[
          UnforcedLeray.Cyl.cellμ c]
      heatVecH3Field (c := c) (θ := θ) T α := by
  let g : UnforcedLeray.Sob.Idx 2 3 → Plane → Vec :=
    heatVecH3Field (c := c) (θ := θ) T
  have hmem : ∀ β, MemLp (g β) 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    intro β
    exact memLp_heatVecH3Field hc hθ hT β
  have hweak : ∀ β : UnforcedLeray.Sob.Idx 2 3,
      UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c)
        ((UnforcedLeray.Sob.cylinder c).word β)
        (g UnforcedLeray.Sob.Idx.zero) (g β) := by
    intro β
    have h := hasWeakDeriv_iterD_heatVecConvolution hc hθ hT
      ((UnforcedLeray.Sob.cylinder c).word β)
    exact h.congr_ae (Filter.Eventually.of_forall fun _ => rfl)
      (Filter.Eventually.of_forall fun z =>
        congrFun (iterD_heatVecConvolution_commute hc hθ hT
          ((UnforcedLeray.Sob.cylinder c).word β)) z)
  have hclass := UnforcedLeray.Sob.W.deriv_ofFields
    (D := UnforcedLeray.Sob.cylinder c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec)
    (k := 3) (p := 2) g hmem hweak α
  have hcoe :
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
        (heatVecH3 hc hθ hT) : Plane → Vec) =ᵐ[
          UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
        heatVecH3Field (c := c) (θ := θ) T α := by
    rw [heatVecH3]
    have hfunEq :
        (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
          (UnforcedLeray.Sob.W.ofFields
            (D := UnforcedLeray.Sob.cylinder c)
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
            (F := Vec) (k := 3) (p := 2) g hmem hweak) : Plane → Vec) =
          ((hmem α).toLp (g α) : Plane → Vec) :=
      congrArg (fun y : Lp Vec 2
        (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => (y : Plane → Vec)) hclass
    filter_upwards [(hmem α).coeFn_toLp] with z hz
    calc
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
        (UnforcedLeray.Sob.W.ofFields
          (D := UnforcedLeray.Sob.cylinder c)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
          (F := Vec) (k := 3) (p := 2) g hmem hweak) : Plane → Vec) z =
          ((hmem α).toLp (g α) : Plane → Vec) z := congrFun hfunEq z
      _ = g α z := hz
  simpa only [heatVecH3_measure_eq_cell_local'' c] using hcoe

/-- The ordinary centered H³ heat CLM agrees with the literal smooth Gaussian output on smooth
compact-axial data. -/
theorem actualHeatVecH3CLM_apply_ofCylSmooth {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    actualHeatVecH3CLM hc hθ
      (UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc T hT) = heatVecH3 hc hθ hT := by
  rw [actualHeatVecH3CLM_apply]
  apply vectorH3NormalizedValue_injective hc
  rw [vectorH3NormalizedValue_actualHeatVecH3 hc hθ,
    vectorH3NormalizedValue_heatVecH3 hc hθ hT,
    vectorH3NormalizedValue_ofCylSmoothVec hc hT]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.deriv_ofCylSmooth_ae_cell
#print axioms UnforcedLeray.HeatCylinder.deriv_heatVecH3_ae_cell
#print axioms UnforcedLeray.HeatCylinder.actualHeatVecH3CLM_apply_ofCylSmooth
