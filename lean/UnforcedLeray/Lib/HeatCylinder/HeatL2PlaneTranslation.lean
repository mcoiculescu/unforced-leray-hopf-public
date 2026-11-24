import UnforcedLeray.Lib.HeatCylinder.HeatL2TranslationContinuity

/-!
# Strong continuity of all cylinder translations on centered vector `L²`

The two coordinate translation groups combine to the translation of the actual planar Gaussian
kernel. This is the translation orbit needed in the heat approximate-identity estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- The actual centered-cell translation by `-w` on vector `L²`. -/
noncomputable def planeShiftL2 {c : ℝ} (hc : 0 < c) (w : Plane)
    (x : UnforcedLeray.Cyl.L2v c) : UnforcedLeray.Cyl.L2v c :=
  UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
    (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)

theorem norm_planeShiftL2_sub_le {c : ℝ} (hc : 0 < c) (w : Plane)
    (x : UnforcedLeray.Cyl.L2v c) :
    ‖planeShiftL2 hc w x - x‖ ≤
      ‖UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x - x‖ +
        ‖UnforcedLeray.TrainB.qShiftL2 hc (-w.1) x - x‖ := by
  let S := UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)
  let R := UnforcedLeray.TrainB.etaShiftL2 c (-w.2)
  have hmap : S (R x) - S x = S (R x - x) := (S.map_sub _ _).symm
  have hnorm : ‖S (R x - x)‖ = ‖R x - x‖ := S.norm_map _
  change ‖S (R x) - x‖ ≤ ‖R x - x‖ + ‖S x - x‖
  calc
    ‖S (R x) - x‖ = ‖(S (R x) - S x) + (S x - x)‖ := by congr 1 <;> abel
    _ ≤ ‖S (R x) - S x‖ + ‖S x - x‖ := norm_add_le _ _
    _ = ‖R x - x‖ + ‖S x - x‖ := by rw [hmap, hnorm]

/-- Translations of the centered cylinder `L²` class are strongly continuous at zero in both
spatial coordinates together. -/
theorem tendsto_planeShiftL2_centered {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.L2v c) :
    Tendsto (fun w : Plane => planeShiftL2 hc w x) (𝓝 (0 : Plane)) (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hqarg : Tendsto (fun w : Plane => -(w.1)) (𝓝 (0 : Plane)) (𝓝 (0 : ℝ)) := by
    convert (continuous_neg.comp continuous_fst).tendsto (0 : Plane) using 1
    · ext w; rfl
    · congr 1; simp
  have hetaarg : Tendsto (fun w : Plane => -(w.2)) (𝓝 (0 : Plane)) (𝓝 (0 : ℝ)) := by
    convert (continuous_neg.comp continuous_snd).tendsto (0 : Plane) using 1
    · ext w; rfl
    · congr 1; simp
  have hqComp := (tendsto_qShiftL2_centered hc x).comp hqarg
  have hqFun : (fun w : Plane => UnforcedLeray.TrainB.qShiftL2 hc (-(w.1)) x) =
      (fun h => UnforcedLeray.TrainB.qShiftL2 hc h x) ∘ (fun w : Plane => -(w.1)) := by
    funext w
    rfl
  have hq : Tendsto (fun w : Plane =>
      UnforcedLeray.TrainB.qShiftL2 hc (-(w.1)) x)
      (𝓝 (0 : Plane)) (𝓝 x) := by
    rw [hqFun]
    exact hqComp
  have hetaComp := (tendsto_etaShiftL2_centered hc x).comp hetaarg
  have hetaFun : (fun w : Plane => UnforcedLeray.TrainB.etaShiftL2 c (-(w.2)) x) =
      (fun h => UnforcedLeray.TrainB.etaShiftL2 c h x) ∘ (fun w : Plane => -(w.2)) := by
    funext w
    rfl
  have heta : Tendsto (fun w : Plane =>
      UnforcedLeray.TrainB.etaShiftL2 c (-(w.2)) x)
      (𝓝 (0 : Plane)) (𝓝 x) := by
    rw [hetaFun]
    exact hetaComp
  have hqnorm : Tendsto (fun w : Plane =>
      ‖UnforcedLeray.TrainB.qShiftL2 hc (-(w.1)) x - x‖)
      (𝓝 (0 : Plane)) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hq
  have hetanorm : Tendsto (fun w : Plane =>
      ‖UnforcedLeray.TrainB.etaShiftL2 c (-(w.2)) x - x‖)
      (𝓝 (0 : Plane)) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp heta
  have hsum : Tendsto (fun w : Plane =>
      ‖UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x - x‖ +
        ‖UnforcedLeray.TrainB.qShiftL2 hc (-w.1) x - x‖)
      (𝓝 (0 : Plane)) (𝓝 0) := by
    simpa using hetanorm.add hqnorm
  exact (tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Plane => (0 : ℝ)) (𝓝 (0 : Plane)) (𝓝 0)) hsum
    (Filter.Eventually.of_forall fun w => norm_nonneg (planeShiftL2 hc w x - x))
    (Filter.Eventually.of_forall fun w => norm_planeShiftL2_sub_le hc w x))

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.norm_planeShiftL2_sub_le
#print axioms UnforcedLeray.HeatCylinder.tendsto_planeShiftL2_centered
