import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBareOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_3

/-!
# `PartIII-b:IIIb-D3/2/G3/1/4/1`: additivity of the cell stress readout (`BareCellAdd`)

Source of record: `the November 2 reference manuscript` (lines 4610-4612).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open ConcreteYF FlatSettingInst UnforcedLeray.Axi

private theorem kcMer_add_ae_cell {ν m : ℝ} (hν : 0 < ν) [Fact (0 < cOf ν)] [Fact (1 < m)]
    (ξ ξ' : Xmc (cOf ν) m) :
    kcMer (ξ + ξ') =ᵐ[volume.restrict (B0579.cell (cOf ν))] kcMer ξ + kcMer ξ' := by
  have havg := (kcMerLinear m ν hν ξ ξ' 0).1
  have hcell : UnforcedLeray.Cyl.cell (cOf ν) = B0579.cell (cOf ν) := by
    simp only [UnforcedLeray.Cyl.cell, B0579.cell, neg_div]
  have hne : ENNReal.ofReal (cOf ν)⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 (cOf_pos hν))).ne'
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ Filter.EventuallyEq at havg
  rw [hcell, Measure.ae_ennreal_smul_measure_eq hne] at havg
  exact havg

private theorem symOuter_readout_eq (a b : Merid) :
    2 * IIIa.symOuter a b 2 2 - IIIa.symOuter a b 0 0 =
      4 * (a 1 * b 1) - 2 * (a 0 * b 0) := by
  simp only [IIIa.symOuter, IIIa.embedMerid, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

private theorem merid_coord_abs_le (x : Merid) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have hsq : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    fin_cases i <;> simp <;> linarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (norm_nonneg _))

private theorem integrable_symOuter_readout {μm : Measure (ℝ × ℝ)}
    {v b : ℝ × ℝ → Merid} (hv : MemLp v 2 μm) (hb : MemLp b 2 μm) :
    Integrable (fun p => 2 * IIIa.symOuter (v p) (b p) 2 2 - IIIa.symOuter (v p) (b p) 0 0) μm := by
  have hprod : Integrable (fun p => ‖v p‖ * ‖b p‖) μm := hv.norm.integrable_mul hb.norm
  have hproj : ∀ i : Fin 2, Continuous (fun x : Merid => x i) :=
    fun i => PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i
  have hv_m : ∀ i : Fin 2, AEStronglyMeasurable (fun p => v p i) μm :=
    fun i => (hproj i).comp_aestronglyMeasurable hv.1
  have hb_m : ∀ i : Fin 2, AEStronglyMeasurable (fun p => b p i) μm :=
    fun i => (hproj i).comp_aestronglyMeasurable hb.1
  have hmeas : AEStronglyMeasurable
      (fun p => 2 * IIIa.symOuter (v p) (b p) 2 2 - IIIa.symOuter (v p) (b p) 0 0) μm := by
    simp only [symOuter_readout_eq]
    exact (((hv_m 1).mul (hb_m 1)).const_mul 4).sub (((hv_m 0).mul (hb_m 0)).const_mul 2)
  refine (hprod.const_mul 6).mono' hmeas (Eventually.of_forall fun p => ?_)
  rw [symOuter_readout_eq, Real.norm_eq_abs]
  have h1 : |v p 1 * b p 1| ≤ ‖v p‖ * ‖b p‖ := by
    rw [abs_mul]
    exact mul_le_mul (merid_coord_abs_le (v p) 1) (merid_coord_abs_le (b p) 1)
      (abs_nonneg _) (norm_nonneg _)
  have h0 : |v p 0 * b p 0| ≤ ‖v p‖ * ‖b p‖ := by
    rw [abs_mul]
    exact mul_le_mul (merid_coord_abs_le (v p) 0) (merid_coord_abs_le (b p) 0)
      (abs_nonneg _) (norm_nonneg _)
  have htri := abs_sub (4 * (v p 1 * b p 1)) (2 * (v p 0 * b p 0))
  have h4 : |4 * (v p 1 * b p 1)| = 4 * |v p 1 * b p 1| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h2 : |2 * (v p 0 * b p 0)| = 2 * |v p 0 * b p 0| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Leaf 1 (`G3/1/4/1`): additivity of the cell stress readout** on `levelFlat`. -/
theorem bareCellAdd : G3.BareCellAdd := by
  intro κ ν hν _ m _ tr FI χo ε s ξ ξ'
  let ξ1 : Xmc (cOf ν) m := ξ
  let ξ2 : Xmc (cOf ν) m := ξ'
  change cellInt (cOf ν) (fun p =>
      2 * IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer (ξ1 + ξ2) p) 2 2 -
        IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer (ξ1 + ξ2) p) 0 0) =
    cellInt (cOf ν) (fun p =>
      2 * IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer ξ1 p) 2 2 -
        IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer ξ1 p) 0 0) +
    cellInt (cOf ν) (fun p =>
      2 * IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer ξ2 p) 2 2 -
        IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer ξ2 p) 0 0)
  rw [cellInt_eq_setIntegral_cell, cellInt_eq_setIntegral_cell, cellInt_eq_setIntegral_cell,
    ← mul_add]
  congr 1
  by_cases hs : 0 ≤ s
  · have htr : ∀ p, NearInst.trainMer tr (s, p) = tr.v s p := by
      intro p; ext i; simp [NearInst.trainMer, IIIa.trainVel, hs]
    simp only [htr]
    have hv : MemLp (tr.v s) 2 (volume.restrict (B0579.cell (cOf ν))) :=
      train_v_memLp tr hs
    have hk1 : MemLp (kcMer ξ1) 2 (volume.restrict (B0579.cell (cOf ν))) :=
      (Lp.memLp (kcLp ξ1)).ae_eq (kcMer_ae ξ1).symm
    have hk2 : MemLp (kcMer ξ2) 2 (volume.restrict (B0579.cell (cOf ν))) :=
      (Lp.memLp (kcLp ξ2)).ae_eq (kcMer_ae ξ2).symm
    have hint1 := integrable_symOuter_readout hv hk1
    have hint2 := integrable_symOuter_readout hv hk2
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae ?_
    filter_upwards [kcMer_add_ae_cell hν ξ1 ξ2] with p hp
    rw [hp, Pi.add_apply]
    simp only [symOuter_readout_eq, PiLp.add_apply]
    ring
  · have htr : ∀ p, NearInst.trainMer tr (s, p) = 0 := by
      intro p; ext i; simp [NearInst.trainMer, IIIa.trainVel, hs]
    simp only [htr, symOuter_readout_eq, PiLp.zero_apply, zero_mul, mul_zero, sub_self,
      integral_zero, add_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

end
