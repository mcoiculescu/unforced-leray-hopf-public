import UnforcedLeray.Lib.TrainB.P0W1
import UnforcedLeray.Units.B0141.Datum

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

private theorem isCylSmooth_smul_test_periodic {c : ℝ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : Plane → F} {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) (hu : ContDiff ℝ ∞ u) (hper : IsPeriodic c u) :
    Sob.IsCylSmooth c (fun z => φ z • u z) := by
  refine ⟨hφ.smooth.smul hu, fun z => ?_, ?_⟩
  · rw [hφ.periodic]
    have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
    rw [hz, hper]
  · obtain ⟨R, hR⟩ := hφ.bounded
    exact ⟨R, fun z hz => by rw [hR z hz, zero_smul]⟩

private theorem periodic_fderiv {c : ℝ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u : Plane → F} (hper : IsPeriodic c u) (v : Plane) :
    IsPeriodic c (fun z => fderiv ℝ u z v) := by
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

/-- A smooth periodic field is weakly differentiable on the cylinder even when it has Gaussian
axial tails and therefore is not a compact-axial `IsCylSmooth` field. The compact support needed
for integration by parts comes from the test function. -/
theorem hasWeakDeriv_cylinder_dir_of_smooth_periodic {c : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : ContDiff ℝ ∞ u) (hper : IsPeriodic c u) (v : Plane) :
    Sob.HasWeakDeriv (Sob.cylinder c) [v] u (fun z => fderiv ℝ u z v) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have hφ' : Sob.IsCylTest c φ := hφ
    have hDφ : Sob.IsCylTest c (fun z => fderiv ℝ φ z v) :=
      (Sob.cylinder c).deriv_mem hφ' v
    change IntegrableOn (fun z => fderiv ℝ φ z v • u z) (Sob.cylCell c) volume
    exact (isCylSmooth_smul_test_periodic hDφ hu hper).integrableOn
  · change IntegrableOn (fun z => φ z • fderiv ℝ u z v) (Sob.cylCell c) volume
    exact (isCylSmooth_smul_test_periodic hφ
      ((ContDiff.fderiv_right (m := ∞) hu (by simp)).clm_apply contDiff_const)
      (periodic_fderiv hper v)).integrableOn
  · have hφ' : Sob.IsCylTest c φ := hφ
    have hDφ : Sob.IsCylTest c (fun z => fderiv ℝ φ z v) :=
      (Sob.cylinder c).deriv_mem hφ' v
    have huD : ContDiff ℝ ∞ (fun z => fderiv ℝ u z v) :=
      (ContDiff.fderiv_right (m := ∞) hu (by simp)).clm_apply contDiff_const
    have hprod := isCylSmooth_smul_test_periodic hφ' hu hper
    have hd : ∀ z, fderiv ℝ (fun y => φ y • u y) z v =
        fderiv ℝ φ z v • u z + φ z • fderiv ℝ u z v := by
      intro z
      have h1 : DifferentiableAt ℝ φ z := hφ'.smooth.differentiable (by simp) z
      have h2 : DifferentiableAt ℝ u z := hu.differentiable (by simp) z
      show fderiv ℝ (φ • u) z v = _
      rw [fderiv_smul h1 h2]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [add_comm]
    have h0 := Sob.integral_cylCell_fderiv_eq_zero hc hprod v
    simp_rw [hd] at h0
    have i1 : IntegrableOn (fun z => fderiv ℝ φ z v • u z) (Sob.cylCell c) :=
      (isCylSmooth_smul_test_periodic hDφ hu hper).integrableOn
    have i2 : IntegrableOn (fun z => φ z • fderiv ℝ u z v) (Sob.cylCell c) :=
      (isCylSmooth_smul_test_periodic hφ' huD (periodic_fderiv hper v)).integrableOn
    rw [integral_add i1 i2, add_eq_zero_iff_eq_neg] at h0
    simp only [Sob.cylinder_μ, List.length_singleton, pow_one, neg_smul, one_smul]
    exact h0

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.hasWeakDeriv_cylinder_dir_of_smooth_periodic
