import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.RealBiotSavart
import UnforcedLeray.Units.B0581

/-!
# The nonzero-mode part of the actual real cylinder Biot–Savart map

The Fourier/nonzero-mode contribution is already a bounded linear map. This file transports the
real weighted vorticity into the complex unweighted cell pivot, applies the existing Fourier
Biot–Savart CLM, and projects componentwise to real vectors. The separate zero-mode primitive is
the remaining linearity step for the full `K_c` operator.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0581 (cellVol)
open UnforcedLeray.B0579 (X)
open UnforcedLeray.Train (Vec)

/-- Complexification of the real weighted vorticity into unweighted cylinder `L²`. -/
def complexifyXCLM (c m : ℝ) (hm : 0 ≤ m) : X c m →L[ℝ] Lp ℂ 2 (cellVol c) := by
  let L : X c m →ₗ[ℝ] Lp ℂ 2 (cellVol c) := {
    toFun := fun w => UnforcedLeray.B0581.ofX c m hm w
    map_add' := by
      intro w z
      apply Lp.ext
      filter_upwards [UnforcedLeray.B0581.coeFn_ofX c m hm (w + z),
        Lp.coeFn_add (UnforcedLeray.B0581.ofX c m hm w) (UnforcedLeray.B0581.ofX c m hm z),
        UnforcedLeray.B0581.coeFn_ofX c m hm w, UnforcedLeray.B0581.coeFn_ofX c m hm z,
        (Measure.absolutelyContinuous_of_le
          (UnforcedLeray.B0581.cellVol_le_cellMeasure c hm)).ae_le (Lp.coeFn_add w z)]
        with x h1 h2 h3 h4 h5
      rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
      simp only [← Complex.ofReal_add]
    map_smul' := by
      intro a w
      apply Lp.ext
      filter_upwards [UnforcedLeray.B0581.coeFn_ofX c m hm (a • w),
        UnforcedLeray.B0581.coeFn_ofX c m hm w,
        (Measure.absolutelyContinuous_of_le
          (UnforcedLeray.B0581.cellVol_le_cellMeasure c hm)).ae_le (Lp.coeFn_smul a w),
        Lp.coeFn_smul a (UnforcedLeray.B0581.ofX c m hm w)] with x h1 h2 h3 h4
      rw [h1, h3]
      simp only [RingHom.id_apply] at h4 ⊢
      rw [h4]
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      rw [h2]
      simp [Complex.ofReal_mul]
  }
  refine L.mkContinuous 1 ?_
  intro w
  exact (UnforcedLeray.B0581.norm_ofX_le c m hm w).trans_eq (one_mul _).symm

/-- The actual Fourier/nonzero-mode Biot–Savart contribution, as a real continuous linear map
from weighted vorticity to real vector-valued unweighted cell `L²`. -/
def nonzeroBiotSavartCLM {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) :
    X c m →L[ℝ] Lp Vec 2 (cellVol c) :=
  (realPartVelocityCLM.compLpL 2 (cellVol c)).comp
    (((UnforcedLeray.B0581.velNe c).restrictScalars ℝ).comp
      (complexifyXCLM c m (zero_le_one.trans hm)))

theorem nonzeroBiotSavartCLM_apply {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (w : X c m) :
    nonzeroBiotSavartCLM hm w =
      realPartVelocityLp (UnforcedLeray.B0581.velNe c
        (UnforcedLeray.B0581.nonzeroPart c (UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w))) := by
  exact congrArg realPartVelocityLp
    (UnforcedLeray.B0581.velNe_nonzeroPart c
      (UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w)).symm

theorem norm_nonzeroBiotSavartCLM_le {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (w : X c m) :
    ‖nonzeroBiotSavartCLM hm w‖ ≤ c / (2 * Real.pi) * ‖w‖ := by
  have hcpos : 0 < c := Fact.out
  have hN := UnforcedLeray.B0581.norm_velNe_le c
    (UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w)
  have hR := norm_realPartVelocityLp_le (UnforcedLeray.B0581.velNe c
    (UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w))
  have hX := UnforcedLeray.B0581.norm_ofX_le c m (zero_le_one.trans hm) w
  rw [nonzeroBiotSavartCLM_apply]
  calc
    ‖realPartVelocityLp (UnforcedLeray.B0581.velNe c
        (UnforcedLeray.B0581.nonzeroPart c (UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w)))‖
      ≤ ‖UnforcedLeray.B0581.velNe c
          (UnforcedLeray.B0581.nonzeroPart c (UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w))‖ := by
          exact norm_realPartVelocityLp_le _
    _ = ‖UnforcedLeray.B0581.velNe c
        (UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w)‖ := by
          rw [UnforcedLeray.B0581.velNe_nonzeroPart]
    _ ≤ c / (2 * Real.pi) * ‖UnforcedLeray.B0581.ofX c m (zero_le_one.trans hm) w‖ := hN
    _ ≤ c / (2 * Real.pi) * ‖w‖ := by
          exact mul_le_mul_of_nonneg_left hX (by positivity)

#print axioms nonzeroBiotSavartCLM_apply
#print axioms norm_nonzeroBiotSavartCLM_le

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
