import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!

bounded.

Source: `the November 2 reference manuscript` lines 2100-2105.

`IsCylTest c f` gives continuity, `c`-periodicity in `x.1`, and vanishing for `|x.2| > R`.  The
values on the plane are therefore controlled by the continuous values on the compact box
`[0, c] × [-|R|, |R|]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem cylTestBounded : UnforcedLeray.Short.IIb.CylTestBounded := by
  intro c f hc hf
  obtain ⟨R, hR⟩ := hf.band
  have hK : IsCompact (Icc 0 c ×ˢ Icc (-|R|) |R| : Set B0579.Plane) :=
    isCompact_Icc.prod isCompact_Icc
  have hfK : ContinuousOn f (Icc 0 c ×ˢ Icc (-|R|) |R|) := hf.continuous.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfK
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : R < |x.2|
  · rw [hR x hx, abs_zero]
    exact le_max_right _ _
  · push_neg at hx
    set k : ℤ := ⌊x.1 / c⌋ with hk
    have hfl1 : (k : ℝ) ≤ x.1 / c := Int.floor_le _
    have hfl2 : x.1 / c < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have hA : (k : ℝ) * c ≤ x.1 := (le_div_iff₀ hc).1 hfl1
    have hB : x.1 < ((k : ℝ) + 1) * c := (div_lt_iff₀ hc).1 hfl2
    have hB' : ((k : ℝ) + 1) * c = (k : ℝ) * c + c := by ring
    have hy0 : 0 ≤ x.1 - (k : ℝ) * c := by linarith
    have hyc : x.1 - (k : ℝ) * c ≤ c := by linarith
    have hp : Function.Periodic (fun u : ℝ => f (u, x.2)) c :=
      fun u => hf.periodic (u, x.2)
    have hshift : f (x.1 - (k : ℝ) * c, x.2) = f x := by
      have h := hp.sub_int_mul_eq (x := x.1) k
      simpa using h
    have hband : -|R| ≤ x.2 ∧ x.2 ≤ |R| := abs_le.1 (hx.trans (le_abs_self R))
    have hmem : (x.1 - (k : ℝ) * c, x.2) ∈ Icc 0 c ×ˢ Icc (-|R|) |R| :=
      ⟨⟨hy0, hyc⟩, hband⟩
    have hbound := hC (x.1 - (k : ℝ) * c, x.2) hmem
    rw [hshift, Real.norm_eq_abs] at hbound
    exact le_trans hbound (le_max_left _ _)

end UnforcedLeray.Short.IIb
