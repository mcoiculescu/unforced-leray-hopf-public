import UnforcedLeray.Short.PartI.Sub.T02_1_3

/-!
# Part I, task `PartI:T02/1/3/2`: uniqueness of continuous periodic representatives

Source of record: `the November 2 reference manuscript`, lines 261-288.

The target is `AePeriodicEq` (`Short/PartI/Sub/T02_1_3.lean`, line 80): two continuous
`c`-periodic functions on the plane that agree almost everywhere on the cell
`[-c/2, c/2) × ℝ` are equal.

Proof. The disagreement set `S = {z | g₁ z ≠ g₂ z}` is invariant under the translations by
`(c, 0)ℤ` (periodicity of `g₁` and `g₂`). Its intersection with the cell is null (almost
everywhere agreement on the cell), so the fundamental domain property of the cell
(`UnforcedLeray.Cyl.isAddFundamentalDomain_cell`) makes `S` null on the whole plane. Hence
`g₁ =ᵐ[volume] g₂`, and two continuous functions that agree almost everywhere for the measure
`volume` on `ℝ × ℝ` (an open-positive measure) are equal.
-/

open Set Filter MeasureTheory
open scoped Pointwise

namespace UnforcedLeray.Short.PartI

/-- Integer shifts of a `c`-periodic function: `f (z.1 + n c, z.2) = f z` for `n : ℤ`. -/
theorem aePeriodicEq_shift {E : Type*} {c : ℝ} {f : UnforcedLeray.Cyl.Plane → E}
    (hf : UnforcedLeray.Cyl.IsPeriodic c f) (n : ℤ) (z : UnforcedLeray.Cyl.Plane) :
    f (z.1 + (n : ℝ) * c, z.2) = f z := by
  have h := UnforcedLeray.Cyl.IsPeriodic.add_zsmul hf n z
  rwa [zsmul_eq_mul] at h

/-- **Uniqueness of continuous periodic representatives** (`AePeriodicEq`): two continuous
`c`-periodic functions that agree a.e. on the cell `[-c/2, c/2) × ℝ` are equal. -/
theorem aePeriodicEq : AePeriodicEq := by
  intro c hc g₁ g₂ hg₁ hg₂ hp₁ hp₂ hae
  -- The disagreement set is invariant under the translations by the subgroup `(c, 0) ℤ`.
  have hSinv : ∀ v : AddSubgroup.zmultiples ((c, 0) : UnforcedLeray.Cyl.Plane),
      v +ᵥ {z : UnforcedLeray.Cyl.Plane | ¬ g₁ z = g₂ z} = {z : UnforcedLeray.Cyl.Plane | ¬ g₁ z = g₂ z} := by
    rintro ⟨v, hv⟩
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have e : ((-(⟨m • ((c, 0) : UnforcedLeray.Cyl.Plane), hv⟩ :
        AddSubgroup.zmultiples ((c, 0) : UnforcedLeray.Cyl.Plane))) +ᵥ z :
          UnforcedLeray.Cyl.Plane) = (z.1 + ((-m : ℤ) : ℝ) * c, z.2) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add]
      ext <;> simp <;> ring
    rw [e]
    simp only [Set.mem_ofPred_eq]
    rw [aePeriodicEq_shift hp₁ (-m) z, aePeriodicEq_shift hp₂ (-m) z]
  -- The disagreement set is null on the cell, hence null on the whole plane.
  have hcenter : (volume : Measure UnforcedLeray.Cyl.Plane)
      ({z : UnforcedLeray.Cyl.Plane | ¬ g₁ z = g₂ z} ∩ UnforcedLeray.Cyl.cell c) = 0 := by
    have hzero : (volume.restrict (UnforcedLeray.Cyl.cell c))
        {z : UnforcedLeray.Cyl.Plane | ¬ g₁ z = g₂ z} = 0 := ae_iff.mp hae
    rw [Measure.restrict_apply' (UnforcedLeray.Cyl.measurableSet_cell c)] at hzero
    exact hzero
  have hglobalNull : (volume : Measure UnforcedLeray.Cyl.Plane)
      {z : UnforcedLeray.Cyl.Plane | ¬ g₁ z = g₂ z} = 0 :=
    (UnforcedLeray.Cyl.isAddFundamentalDomain_cell hc).measure_zero_of_invariant _ hSinv hcenter
  -- Continuous functions that agree a.e. on the plane agree everywhere.
  have hae' : g₁ =ᵐ[(volume : Measure UnforcedLeray.Cyl.Plane)] g₂ := ae_iff.mpr hglobalNull
  exact (Continuous.ae_eq_iff_eq (volume : Measure UnforcedLeray.Cyl.Plane) hg₁ hg₂).mp hae'

end UnforcedLeray.Short.PartI
