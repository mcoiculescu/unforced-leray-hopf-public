import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_3.PeriodicExt

/-!
# Periodic fields: a.e. equality on the strip is a.e. equality on the plane

Helper for `pepsC0SliceOrthCell` (source `the November 2 reference manuscript`
1650-1656, 1676).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem ae_vol_of_strip {c : ℝ} (hc : 0 < c) {E : Type*} {f g : ℝ × ℝ → E}
    (hf : UnforcedLeray.Cyl.IsPeriodic c f) (hg : UnforcedLeray.Cyl.IsPeriodic c g)
    (h : f =ᵐ[volume.restrict (stripSet c)] g) : f =ᵐ[volume] g := by
  let S : Set (ℝ × ℝ) := {z | f z ≠ g z}
  have hstrip : volume (S ∩ (Ico 0 (0 + c) ×ˢ (univ : Set ℝ))) = 0 := by
    have h' : f =ᵐ[volume.restrict (Ico 0 (0 + c) ×ˢ (univ : Set ℝ))] g := by
      rw [← UnforcedLeray.B0224.restrict_strip c]; exact h
    have h0 : volume.restrict (Ico 0 (0 + c) ×ˢ (univ : Set ℝ)) S = 0 := ae_iff.mp h'
    rw [Measure.restrict_apply' (measurableSet_Ico.prod MeasurableSet.univ)] at h0
    exact h0
  have hzero := (UnforcedLeray.Cyl.isAddFundamentalDomain_strip hc 0).measure_zero_of_invariant
    S ?_ hstrip
  · exact ae_iff.mpr (by simpa [S] using hzero)
  · rintro ⟨v, hv⟩
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have e : (-(⟨m • ((c, 0) : ℝ × ℝ), hv⟩ : AddSubgroup.zmultiples ((c, 0) : ℝ × ℝ)) +ᵥ z :
        ℝ × ℝ) = (z.1 + (-m) • c, z.2) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add]
      ext <;> simp [add_comm]
    rw [e]
    show f (z.1 + (-m) • c, z.2) ≠ g (z.1 + (-m) • c, z.2) ↔ f z ≠ g z
    rw [hf.add_zsmul, hg.add_zsmul]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
