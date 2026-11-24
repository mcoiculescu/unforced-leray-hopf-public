import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4

/-!
# `blkNormLe` (item `PartIII-b:C/near/delta/8/2/3/4/org/5`)

The planar block transport is bounded: `‖tblkF c m‖_𝒯 ≤ √2 · (c⁻¹)^{1/2} ‖m‖_{H_T}`.
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
open UnforcedLeray.Short.IIIa (tnorm2 tCalNorm)

/-- The inverse recentring carries `ageμ c (-1/2)` to `c⁻¹ · measureHT c`; the analogue of
`ct_cellPtInvH` for the tensor measure, from the hypothesis `CellPtHT c`. -/
theorem blk_cellPtInvHT (c : ℝ) (hc : 0 < c) (hT : Masked.CellPtHT c) :
    Measure.map (Masked.cellPtInv c) (ageμ c (-1 / 2)) = ENNReal.ofReal c⁻¹ • measureHT c := by
  have hH : Measure.map (cellPt c) (measureHT c) = ENNReal.ofReal c • ageμ c (-1 / 2) := hT
  have hcell : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hae : (Masked.cellPtInv c ∘ cellPt c) =ᵐ[measureHT c] id := by
    have hmem : ∀ᵐ q ∂measureHT c, q ∈ UnforcedLeray.B0220.cell c := by
      unfold measureHT
      exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hcell)
    filter_upwards [hmem] with q hq
    obtain ⟨-, ⟨h0, hcq⟩, -⟩ := hq
    exact Masked.cellPtInv_cellPt h0 hcq
  have h1 : Measure.map (Masked.cellPtInv c) (Measure.map (cellPt c) (measureHT c)) =
      measureHT c := by
    rw [Measure.map_map (Masked.measurable_cellPtInv c) (Body.measurable_cellPt' c),
      Measure.map_congr hae, Measure.map_id]
  have h2 : ENNReal.ofReal c • Measure.map (Masked.cellPtInv c) (ageμ c (-1 / 2)) =
      measureHT c := by
    rw [← Measure.map_smul, ← hH, h1]
  rw [← h2, smul_smul, ENNReal.ofReal_inv_of_pos hc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top, one_smul]

/-- The norm bound for one planar block: `tnorm2 (tvBlk v) ≤ √2 ‖v‖`. -/
theorem blk_tnorm2_le (v : TensorVal) : tnorm2 (tvBlk v) ≤ Real.sqrt 2 * ‖v‖ := by
  unfold tnorm2
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.sqrt_le_sqrt
  simp only [tvBlk, Fin.sum_univ_two, Fin.sum_univ_four]
  simp
  nlinarith [sq_nonneg ‖v 0‖, sq_nonneg ‖v 1‖, sq_nonneg ‖v 2‖, sq_nonneg ‖v 3‖]

/-- **`blkNormLe`** (source 1641-1646, 2676-2679): the planar block transport is bounded. -/
theorem blkNormLe : BlkNormLe := by
  intro c hc hT
  refine ⟨Real.sqrt 2 * c⁻¹ ^ (1 / 2 : ℝ),
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (inv_nonneg.2 hc.le) _), ?_⟩
  intro m hm
  have hpt : ∀ x, ‖tnorm2 (tblkF c m x)‖ ≤ Real.sqrt 2 * ‖m (Masked.cellPtInv c x)‖ := by
    intro x
    have hfun : tblkF c m x = tvBlk (m (Masked.cellPtInv c x)) := rfl
    rw [hfun, Real.norm_of_nonneg (by unfold tnorm2; exact Real.sqrt_nonneg _)]
    exact blk_tnorm2_le _
  have hmapm := blk_cellPtInvHT c hc hT
  have hf : Measurable (Masked.cellPtInv c) := Masked.measurable_cellPtInv c
  have hg : AEStronglyMeasurable (fun p => ‖m p‖)
      (Measure.map (Masked.cellPtInv c) (ageμ c (-1 / 2))) := by
    rw [hmapm]
    exact hm.norm.smul_measure _
  have hconst := eLpNorm_const_smul (μ := ageμ c (-1 / 2)) (p := 2) (Real.sqrt 2)
    (fun x => ‖m (Masked.cellPtInv c x)‖)
  simp only [Pi.smul_def, smul_eq_mul] at hconst
  rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg 2)] at hconst
  calc tCalNorm c (tblkF c m)
      = eLpNorm (fun x => tnorm2 (tblkF c m x)) 2 (ageμ c (-1 / 2)) := rfl
    _ ≤ eLpNorm (fun x => Real.sqrt 2 * ‖m (Masked.cellPtInv c x)‖) 2 (ageμ c (-1 / 2)) :=
        eLpNorm_mono_real (fun x => hpt x)
    _ = ENNReal.ofReal (Real.sqrt 2) *
          eLpNorm (fun x => ‖m (Masked.cellPtInv c x)‖) 2 (ageμ c (-1 / 2)) := hconst
    _ = ENNReal.ofReal (Real.sqrt 2) *
          eLpNorm (fun p => ‖m p‖) 2 (Measure.map (Masked.cellPtInv c) (ageμ c (-1 / 2))) := by
        rw [eLpNorm_map_measure hg hf.aemeasurable]
        rfl
    _ = ENNReal.ofReal (Real.sqrt 2) *
          eLpNorm (fun p => ‖m p‖) 2 (ENNReal.ofReal c⁻¹ • measureHT c) := by rw [hmapm]
    _ = ENNReal.ofReal (Real.sqrt 2) *
          ((ENNReal.ofReal c⁻¹) ^ (1 / 2 : ℝ) * eLpNorm (fun p => ‖m p‖) 2 (measureHT c)) := by
        rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofNat_ne_top, smul_eq_mul]
        congr 2
        simp [one_div, ENNReal.toReal_inv]
    _ = ENNReal.ofReal (Real.sqrt 2 * c⁻¹ ^ (1 / 2 : ℝ)) * eLpNorm m 2 (measureHT c) := by
        rw [eLpNorm_norm, ENNReal.ofReal_mul (Real.sqrt_nonneg 2),
          ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hc.le) (by norm_num)]
        ring

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
