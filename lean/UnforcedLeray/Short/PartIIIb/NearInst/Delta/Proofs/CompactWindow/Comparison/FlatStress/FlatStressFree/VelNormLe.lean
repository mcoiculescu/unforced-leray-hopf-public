import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4

/-!
# `velNormLe` (item `PartIII-b:C/near/delta/8/2/3/4/org/6`)

The velocity transport is bounded: `‖velF c g‖_𝓗 ≤ (c⁻¹)^{1/2} ‖g‖_H`.
Source `the November 2 reference manuscript` 1641-1646, 2676-2679.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (vnorm2 hCalNorm)

/-- The Euclidean norm of a meridional value is the norm of its two components. -/
theorem vel_vnorm2_eq (g : Profile → MeridC) (y : Profile) :
    vnorm2 (fun i => g y i) = ‖g y‖ := by
  rw [fsf_vnorm2_eq_norm]

/-- **`velNormLe`** (source 1641-1646, 2676-2679): the velocity transport is bounded. -/
theorem velNormLe : VelNormLe := by
  intro c hc hH
  refine ⟨c⁻¹ ^ (1 / 2 : ℝ), Real.rpow_nonneg (inv_nonneg.2 hc.le) _, ?_⟩
  intro g hg
  have hmapm : Measure.map (Masked.cellPtInv c) (ageμ c (-3 / 2)) =
      ENNReal.ofReal c⁻¹ • measureH c := hH
  have hf : Measurable (Masked.cellPtInv c) := Masked.measurable_cellPtInv c
  have hgm : AEStronglyMeasurable (fun p => ‖g p‖)
      (Measure.map (Masked.cellPtInv c) (ageμ c (-3 / 2))) := by
    rw [hmapm]
    exact hg.norm.smul_measure _
  apply le_of_eq
  calc hCalNorm c (velF c g)
      = eLpNorm (fun x => ‖g (Masked.cellPtInv c x)‖) 2 (ageμ c (-3 / 2)) := by
        unfold hCalNorm
        congr 1
        funext x
        exact vel_vnorm2_eq g (Masked.cellPtInv c x)
    _ = eLpNorm (fun p => ‖g p‖) 2 (Measure.map (Masked.cellPtInv c) (ageμ c (-3 / 2))) := by
        rw [eLpNorm_map_measure hgm hf.aemeasurable]
        rfl
    _ = eLpNorm (fun p => ‖g p‖) 2 (ENNReal.ofReal c⁻¹ • measureH c) := by rw [hmapm]
    _ = (ENNReal.ofReal c⁻¹) ^ (1 / 2 : ℝ) * eLpNorm (fun p => ‖g p‖) 2 (measureH c) := by
        rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofNat_ne_top, smul_eq_mul]
        congr 2
        simp [one_div, ENNReal.toReal_inv]
    _ = ENNReal.ofReal (c⁻¹ ^ (1 / 2 : ℝ)) * eLpNorm g 2 (measureH c) := by
        rw [eLpNorm_norm, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hc.le) (by norm_num)]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
