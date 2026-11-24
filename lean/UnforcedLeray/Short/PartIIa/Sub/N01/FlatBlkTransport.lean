import UnforcedLeray.Short.PartIIa.Sub.N01.FlatReduction
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.BlkNormLe

/-!
# `PartII-a:N01/11` — the planar block norm under recentring

Proves `FlatBlkTransport` (`Sub/N01/FlatReduction.lean`): `√c ‖tblkF c M‖_𝒯 ≤ √2 ‖F‖_{H_T}` for
`F =ᵐ M`.  Source 1644-1646, 1661-1664 at `ε = 0`, 2676-2679.  The route is the accepted
`blkNormLe` (`FlatStressFree/BlkNormLe.lean`), with the sharp constant kept explicit and the a.e.
replacement `M ↦ F` at the end.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

theorem flatBlkTransport : FlatBlkTransport := by
  intro c hc M F hF
  have hT : UnforcedLeray.Short.PartIIIb.NearInst.Masked.CellPtHT c :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.cpcHT_eq c hc
  have hmapm := UnforcedLeray.Short.PartIIIb.NearInst.Delta.blk_cellPtInvHT c hc hT
  have hf : Measurable (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c) :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPtInv c
  -- pointwise bound on the recentred cell
  have hpt : ∀ x, ‖UnforcedLeray.Short.IIIa.tnorm2
      (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M x)‖ ≤
        Real.sqrt 2 * ‖M (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x)‖ := by
    intro x
    have hfun : UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M x =
        UnforcedLeray.Short.PartIIIb.NearInst.Delta.tvBlk
          (M (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x)) := rfl
    rw [hfun, Real.norm_of_nonneg (by unfold UnforcedLeray.Short.IIIa.tnorm2; exact Real.sqrt_nonneg _)]
    exact UnforcedLeray.Short.PartIIIb.NearInst.Delta.blk_tnorm2_le _
  -- measurability of the tensor norm, transported from the Lp representative `F`
  have hgF : AEStronglyMeasurable (fun p => ‖F p‖) (UnforcedLeray.Short.PartIIa.measureHT c) :=
    (Lp.aestronglyMeasurable F).norm
  have hnorm : (fun p => ‖F p‖) =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c]
      (fun p => ‖M p‖) := hF.mono (fun x hx => by simp only [hx])
  have hgM : AEStronglyMeasurable (fun p => ‖M p‖)
      (UnforcedLeray.Short.PartIIa.measureHT c) := hgF.congr hnorm
  have hg : AEStronglyMeasurable (fun p => ‖M p‖)
      (Measure.map (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c)
        (UnforcedLeray.Axi.ageμ c (-1 / 2))) := by
    rw [hmapm]
    exact hgM.smul_measure _
  have hconst := eLpNorm_const_smul (μ := UnforcedLeray.Axi.ageμ c (-1 / 2)) (p := 2)
    (Real.sqrt 2) (fun x => ‖M (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x)‖)
  simp only [Pi.smul_def, smul_eq_mul] at hconst
  rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg 2)] at hconst
  have hMF : eLpNorm (⇑F) 2 (UnforcedLeray.Short.PartIIa.measureHT c) =
      eLpNorm M 2 (UnforcedLeray.Short.PartIIa.measureHT c) := eLpNorm_congr_ae hF
  have hbound : UnforcedLeray.Short.IIIa.tCalNorm c
        (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M) ≤
      ENNReal.ofReal (Real.sqrt 2 * c⁻¹ ^ (1 / 2 : ℝ)) *
        eLpNorm (⇑F) 2 (UnforcedLeray.Short.PartIIa.measureHT c) := by
    rw [hMF]
    calc UnforcedLeray.Short.IIIa.tCalNorm c
          (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M)
        = eLpNorm (fun x => UnforcedLeray.Short.IIIa.tnorm2
            (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M x)) 2
            (UnforcedLeray.Axi.ageμ c (-1 / 2)) := rfl
      _ ≤ eLpNorm (fun x => Real.sqrt 2 *
            ‖M (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x)‖) 2
            (UnforcedLeray.Axi.ageμ c (-1 / 2)) :=
          eLpNorm_mono_real (fun x => hpt x)
      _ = ENNReal.ofReal (Real.sqrt 2) * eLpNorm (fun x =>
            ‖M (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x)‖) 2
            (UnforcedLeray.Axi.ageμ c (-1 / 2)) := hconst
      _ = ENNReal.ofReal (Real.sqrt 2) * eLpNorm (fun p => ‖M p‖) 2
            (Measure.map (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c)
              (UnforcedLeray.Axi.ageμ c (-1 / 2))) := by
          rw [eLpNorm_map_measure hg hf.aemeasurable]
          rfl
      _ = ENNReal.ofReal (Real.sqrt 2) * eLpNorm (fun p => ‖M p‖) 2
            (ENNReal.ofReal c⁻¹ • UnforcedLeray.Short.PartIIa.measureHT c) := by rw [hmapm]
      _ = ENNReal.ofReal (Real.sqrt 2) * ((ENNReal.ofReal c⁻¹) ^ (1 / 2 : ℝ) *
            eLpNorm (fun p => ‖M p‖) 2 (UnforcedLeray.Short.PartIIa.measureHT c)) := by
          rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofNat_ne_top, smul_eq_mul]
          congr 2
          simp [one_div, ENNReal.toReal_inv]
      _ = ENNReal.ofReal (Real.sqrt 2 * c⁻¹ ^ (1 / 2 : ℝ)) *
            eLpNorm M 2 (UnforcedLeray.Short.PartIIa.measureHT c) := by
          rw [eLpNorm_norm, ENNReal.ofReal_mul (Real.sqrt_nonneg 2),
            ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hc.le) (by norm_num)]
          ring
  have hk : Real.sqrt c * c⁻¹ ^ (1 / 2 : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.mul_rpow hc.le (inv_nonneg.2 hc.le), mul_inv_cancel₀ hc.ne',
      Real.one_rpow]
  have hk' : ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (c⁻¹ ^ (1 / 2 : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg c), hk, ENNReal.ofReal_one]
  have h1 : ENNReal.ofReal (Real.sqrt c) * UnforcedLeray.Short.IIIa.tCalNorm c
        (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M) ≤
      ENNReal.ofReal (Real.sqrt c) * (ENNReal.ofReal (Real.sqrt 2 * c⁻¹ ^ (1 / 2 : ℝ)) *
        eLpNorm (⇑F) 2 (UnforcedLeray.Short.PartIIa.measureHT c)) := by
    gcongr
  rw [Lp.norm_def, ENNReal.ofReal_mul (Real.sqrt_nonneg 2),
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)]
  refine le_trans h1 (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  have e : ENNReal.ofReal (Real.sqrt c) * (ENNReal.ofReal (Real.sqrt 2) *
      ENNReal.ofReal (c⁻¹ ^ (1 / 2 : ℝ)) *
        eLpNorm (⇑F) 2 (UnforcedLeray.Short.PartIIa.measureHT c)) =
      ENNReal.ofReal (Real.sqrt 2) * (ENNReal.ofReal (Real.sqrt c) *
        ENNReal.ofReal (c⁻¹ ^ (1 / 2 : ℝ))) *
        eLpNorm (⇑F) 2 (UnforcedLeray.Short.PartIIa.measureHT c) := by ring
  rw [e, hk', mul_one]

end UnforcedLeray.Short.PartIIa.N01
