import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjDensityOf
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Pointwise triangle inequality for the enorm of a difference of three vectors. -/
theorem enorm_sub_le_three (u v w : CVec3) : ‖u - w‖ₑ ≤ ‖u - v‖ₑ + ‖v - w‖ₑ := by
  calc ‖u - w‖ₑ = ‖(u - v) + (v - w)‖ₑ := by rw [sub_add_sub_cancel]
    _ ≤ ‖u - v‖ₑ + ‖v - w‖ₑ := enorm_add_le _ _

/-- Minkowski inequality for `phaseLpNorm P 2`, written through `phaseLpNorm_eq`. -/
theorem phaseLpNorm_tri_aux (P : ℝ) (a b c : ℝ × Space → CVec3)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hc : AEStronglyMeasurable c volume) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => a x - c x) ≤
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => a x - b x) +
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => b x - c x) := by
  rw [phaseLpNorm_eq P (fun x => a x - c x) (ha.sub hc),
    phaseLpNorm_eq P (fun x => a x - b x) (ha.sub hb),
    phaseLpNorm_eq P (fun x => b x - c x) (hb.sub hc)]
  have hu : AEMeasurable (fun z => ‖a z - b z‖ₑ) (muP P) :=
    (aesm_muP (ha.sub hb)).enorm
  have hv : AEMeasurable (fun z => ‖b z - c z‖ₑ) (muP P) :=
    (aesm_muP (hb.sub hc)).enorm
  have hpt : ∀ z, ‖a z - c z‖ₑ ^ (2 : ℝ) ≤ (‖a z - b z‖ₑ + ‖b z - c z‖ₑ) ^ (2 : ℝ) :=
    fun z => ENNReal.rpow_le_rpow (enorm_sub_le_three (a z) (b z) (c z)) (by norm_num)
  have hint : ∫⁻ z, ‖a z - c z‖ₑ ^ (2 : ℝ) ∂(muP P) ≤
      ∫⁻ z, (‖a z - b z‖ₑ + ‖b z - c z‖ₑ) ^ (2 : ℝ) ∂(muP P) :=
    lintegral_mono hpt
  have hM := ENNReal.lintegral_Lp_add_le hu hv (by norm_num : (1 : ℝ) ≤ 2)
  have h1 : (∫⁻ z, ‖a z - c z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) ≤
      (∫⁻ z, ‖a z - b z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) +
        (∫⁻ z, ‖b z - c z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) :=
    (ENNReal.rpow_le_rpow hint (by norm_num)).trans hM
  have hmul : ∀ X : ℝ≥0∞, (ENNReal.ofReal P⁻¹ * X) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) :=
    fun X => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  rw [hmul, hmul, hmul, ← mul_add]
  gcongr

/-- The triangle inequality for the `Y_2` norm `phaseLpNorm P 2` (Minkowski in `L²` of the cell
`(0,P] × ℝ³` with the normalised measure). -/
theorem phaseLpTri2 : PhaseLpTri2 := by
  intro P a b c _hP ha hb hc
  exact phaseLpNorm_tri_aux P a b c ha hb hc

end UnforcedLeray.Short.PartIIIb.Concrete
