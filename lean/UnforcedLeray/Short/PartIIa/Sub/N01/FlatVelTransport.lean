import UnforcedLeray.Short.PartIIa.Sub.N01.FlatReduction
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll

/-!
# `PartII-a:N01/10` — the velocity norm under recentring

Proves `FlatVelTransport` (`Sub/N01/FlatReduction.lean`): if `b` is a.e. the recentred field
`Delta.velF c g`, then `‖g‖_H = √c ‖b‖_𝓗`.  Source 1644-1646, 2676-2679.  The route is the accepted
`velNormLe` (`FlatStressFree/VelNormLe.lean`) with equality in place of the bound, plus the a.e.
replacement of `b` by `velF c g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

theorem flatVelTransport : FlatVelTransport := by
  intro c hc g b hb
  have hmapm : Measure.map (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c)
      (UnforcedLeray.Axi.ageμ c (-3 / 2)) =
        ENNReal.ofReal c⁻¹ • UnforcedLeray.B0220.measureH c :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.cpcInvH_eq c hc
  have hf : Measurable (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c) :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPtInv c
  -- the a.e. replacement of `b` by the recentred field
  have hae : (fun p => UnforcedLeray.Short.IIIa.vnorm2 (b p)) =ᵐ[UnforcedLeray.Axi.ageμ c (-3 / 2)]
      (fun p => UnforcedLeray.Short.IIIa.vnorm2
        (UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF c g p)) :=
    hb.mono (fun x hx => by simp only [hx])
  have hcal : UnforcedLeray.Short.IIIa.hCalNorm c b =
      UnforcedLeray.Short.IIIa.hCalNorm c
        (UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF c g) := by
    unfold UnforcedLeray.Short.IIIa.hCalNorm
    exact eLpNorm_congr_ae hae
  -- the norm identity for the recentred field (as in `velNormLe`)
  have hv : ∀ y : UnforcedLeray.B0220.Profile,
      UnforcedLeray.Short.IIIa.vnorm2 (fun i => g y i) = ‖g y‖ := fun y => by
    rw [UnforcedLeray.Short.PartIIIb.NearInst.Delta.fsf_vnorm2_eq_norm]
  have hgm : AEStronglyMeasurable (fun p => ‖g p‖)
      (Measure.map (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c)
        (UnforcedLeray.Axi.ageμ c (-3 / 2))) := by
    rw [hmapm]
    exact (Lp.aestronglyMeasurable g).norm.smul_measure _
  have hvel : UnforcedLeray.Short.IIIa.hCalNorm c
      (UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF c g) =
      ENNReal.ofReal (c⁻¹ ^ (1 / 2 : ℝ)) * eLpNorm g 2 (UnforcedLeray.B0220.measureH c) := by
    calc UnforcedLeray.Short.IIIa.hCalNorm c
          (UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF c g)
        = eLpNorm (fun x => ‖g (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x)‖) 2
            (UnforcedLeray.Axi.ageμ c (-3 / 2)) := by
          unfold UnforcedLeray.Short.IIIa.hCalNorm
          congr 1
          funext x
          exact hv _
      _ = eLpNorm (fun p => ‖g p‖) 2
            (Measure.map (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c)
              (UnforcedLeray.Axi.ageμ c (-3 / 2))) := by
          rw [eLpNorm_map_measure hgm hf.aemeasurable]
          rfl
      _ = eLpNorm (fun p => ‖g p‖) 2
            (ENNReal.ofReal c⁻¹ • UnforcedLeray.B0220.measureH c) := by rw [hmapm]
      _ = (ENNReal.ofReal c⁻¹) ^ (1 / 2 : ℝ) *
            eLpNorm (fun p => ‖g p‖) 2 (UnforcedLeray.B0220.measureH c) := by
          rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofNat_ne_top, smul_eq_mul]
          congr 2
          simp [one_div, ENNReal.toReal_inv]
      _ = ENNReal.ofReal (c⁻¹ ^ (1 / 2 : ℝ)) * eLpNorm g 2 (UnforcedLeray.B0220.measureH c) := by
          rw [eLpNorm_norm, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hc.le) (by norm_num)]
  rw [hcal, hvel]
  have hk : Real.sqrt c * c⁻¹ ^ (1 / 2 : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.mul_rpow hc.le (inv_nonneg.2 hc.le), mul_inv_cancel₀ hc.ne',
      Real.one_rpow]
  have hk' : ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (c⁻¹ ^ (1 / 2 : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg c), hk, ENNReal.ofReal_one]
  rw [← mul_assoc, hk', one_mul, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g)]

end UnforcedLeray.Short.PartIIa.N01
