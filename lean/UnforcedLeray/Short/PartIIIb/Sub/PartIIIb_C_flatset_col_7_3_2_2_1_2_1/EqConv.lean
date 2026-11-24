import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2_1
import UnforcedLeray.Units.B0284.Defs
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.Gaussian.Kernel
import UnforcedLeray.Lib.HeatCylinder.HeatVecConvolution
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# `PlaneHeatEqConv` (source `the November 2 reference manuscript` line 3373,
lines 1650-1656)

For `θ > 0` the planar heat `planeHeat θ` (Gaussian average over `Euc 2` through `planeι`) equals the
Gaussian convolution `heatVecConvolution θ` over `Plane = ℝ × ℝ` with `B0284.heatKernel2`.
The two integrals are related by the change of variables `planeι` (measure preserving measurable
equivalence `Euc 2 ≃ᵐ ℝ × ℝ`), and `gaussKernel 2 θ y = heatKernel2 θ (planeι y)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The measurable equivalence `Euc 2 ≃ᵐ ℝ × ℝ` underlying `planeι`. -/
def eqConvPlaneEquiv : Euc 2 ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem eqConvPlaneEquiv_apply (y : Euc 2) :
    eqConvPlaneEquiv y = UnforcedLeray.B0224.planeι y := rfl

theorem eqConv_planeι_mp :
    MeasurePreserving (UnforcedLeray.B0224.planeι : Euc 2 → ℝ × ℝ) volume volume := by
  have h := (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp
    (PiLp.volume_preserving_ofLp (Fin 2))
  exact h

theorem eqConv_planeι_emb :
    MeasurableEmbedding (UnforcedLeray.B0224.planeι : Euc 2 → ℝ × ℝ) :=
  eqConvPlaneEquiv.measurableEmbedding

/-- The Gaussian kernel on `Euc 2` is the product heat kernel at the image point. -/
theorem eqConv_gaussKernel_eq {θ : ℝ} (hθ : 0 < θ) (y : Euc 2) :
    gaussKernel 2 θ y = UnforcedLeray.B0284.heatKernel2 θ (UnforcedLeray.B0224.planeι y) := by
  have hn : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
  have ha : (0 : ℝ) < 4 * Real.pi * θ := by positivity
  have hs : Real.sqrt (4 * Real.pi * θ) * Real.sqrt (4 * Real.pi * θ) = 4 * Real.pi * θ :=
    Real.mul_self_sqrt ha.le
  have hp : (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2)
      = (Real.sqrt (4 * Real.pi * θ))⁻¹ * (Real.sqrt (4 * Real.pi * θ))⁻¹ := by
    rw [show -((2 : ℕ) : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one, ← mul_inv, hs]
  have he : Real.exp (-(y 0 ^ 2 + y 1 ^ 2) / (4 * θ))
      = Real.exp (-(y 0) ^ 2 / (4 * θ)) * Real.exp (-(y 1) ^ 2 / (4 * θ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold gaussKernel UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
  simp only [UnforcedLeray.B0224.planeι_apply, mul_one]
  rw [hn, hp, he]
  ring

theorem planeHeatEqConv_holds :
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.PlaneHeatEqConv := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.PlaneHeatEqConv
  intro θ hθ u z
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  unfold UnforcedLeray.HeatCylinder.heatVecConvolution
  have h := eqConv_planeι_mp.integral_comp eqConv_planeι_emb
    (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ w • u (z - w))
  rw [← h]
  congr 1
  funext y
  rw [eqConv_gaussKernel_eq hθ y]

end UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong
