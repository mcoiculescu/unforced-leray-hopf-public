import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_2_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/2/1/4`: cylinder-smooth fields are bounded

Source `the November 2 reference manuscript`, lines 261-288.

A field `f` with `Sob.IsCylSmooth c f` is continuous, `c`-periodic in the first coordinate and zero
for `|η| > R`.  Periodicity reduces the first coordinate to `[-c/2, c/2)`, and the vertical support
reduces the second to `[-R', R']` with `R' = max R 0`; on that compact box `‖f‖` is bounded.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace CylSmoothBddAux

open UnforcedLeray

theorem cylSmoothBdd_aux (c : ℝ) (hc : 0 < c) (f : Cyl.Plane → Cyl.Vec2)
    (hf : Sob.IsCylSmooth c f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖f z‖ ≤ M := by
  obtain ⟨R, hR⟩ := hf.bounded
  let R' : ℝ := max R 0
  let K : Set Cyl.Plane := Set.Icc (-(c / 2)) (c / 2) ×ˢ Set.Icc (-R') R'
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hg : Continuous fun z : Cyl.Plane => ‖f z‖ := hf.smooth.continuous.norm
  obtain ⟨M, hM⟩ := hK.bddAbove_image hg.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun z => ?_⟩
  by_cases hη : R' < |z.2|
  · have hzero : f z = 0 := hR z (lt_of_le_of_lt (le_max_left R 0) hη)
    rw [hzero, norm_zero]
    exact le_max_right _ _
  · push Not at hη
    have hη' : z.2 ∈ Set.Icc (-R') R' := abs_le.mp hη
    let q₀ : ℝ := toIcoMod hc (-(c / 2)) z.1
    have hq₀ : q₀ ∈ Set.Icc (-(c / 2)) (c / 2) := by
      have hmem := toIcoMod_mem_Ico hc (-(c / 2)) z.1
      constructor
      · exact hmem.1
      · have : -(c / 2) + c = c / 2 := by ring
        rw [this] at hmem
        exact hmem.2.le
    have hq : q₀ = z.1 - (toIcoDiv hc (-(c / 2)) z.1 : ℤ) * c := by
      have h := toIcoMod_add_toIcoDiv_zsmul hc (-(c / 2)) z.1
      rw [zsmul_eq_mul] at h
      show toIcoMod hc (-(c / 2)) z.1 = _
      linarith
    have hper : Function.Periodic (fun q : ℝ => f (q, z.2)) c := fun q => by
      show f (q + c, z.2) = f (q, z.2)
      have h := hf.periodic (q, z.2)
      simpa only [Prod.mk_add_mk, add_zero] using h
    have hval : f (q₀, z.2) = f z := by
      have h := hper.sub_int_mul_eq (x := z.1) (n := toIcoDiv hc (-(c / 2)) z.1)
      rw [← hq] at h
      exact h
    have hz₀K : (q₀, z.2) ∈ K := ⟨hq₀, hη'⟩
    have hbound : ‖f (q₀, z.2)‖ ≤ M := hM ⟨(q₀, z.2), hz₀K, rfl⟩
    rw [← hval]
    exact le_trans hbound (le_max_left _ _)

end CylSmoothBddAux

/-- **Leaf B (cylinder-smooth fields are bounded; source lines 261-288).** -/
theorem cylSmoothBdd : UnforcedLeray.Short.PartI.CylSmoothBdd := by
  unfold UnforcedLeray.Short.PartI.CylSmoothBdd
  intro c hc f hf
  exact CylSmoothBddAux.cylSmoothBdd_aux c hc f hf
