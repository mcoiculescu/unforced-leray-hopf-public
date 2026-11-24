import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/21`: bins with `S ≤ 0` are empty for the age measure

Source `the November 2 reference manuscript` (bins with `S ≤ 0` are empty for the
age measure).  The bin `binSet S h j = {p | binUpper S h (j+1) < p.1 ≤ binUpper S h j}` with
`binUpper S h j = S · e^{-hj} ≤ 0` lies in `{p | p.1 ≤ 0}`.  The age measure
`ageμ c a = ((volume.restrict (Ioi 0)).withDensity _).prod (Cyl.avgμ c)` gives this set measure
zero, since `volume.restrict (Ioi 0)` does not charge `Iic 0` and `withDensity` is absolutely
continuous with respect to its base measure.  Hence the integral over the bin vanishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- The age measure gives `Iic 0 × univ` measure zero. -/
theorem ageμ_Iic_prod_null (c a : ℝ) :
    ageμ c a (Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) = 0 := by
  have hempty : Iic (0 : ℝ) ∩ Ioi (0 : ℝ) = ∅ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hx1' : x ≤ 0 := hx1
      have hx2' : (0 : ℝ) < x := hx2
      exact absurd hx2' (not_lt.mpr hx1')
    · intro hx
      simp at hx
  have hnull1 : (volume.restrict (Ioi (0 : ℝ))) (Iic (0 : ℝ)) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iic, hempty, measure_empty]
  have h0 : ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a))
      (Iic (0 : ℝ)) = 0 :=
    withDensity_absolutelyContinuous _ _ hnull1
  unfold ageμ
  rw [Measure.prod_prod, h0, zero_mul]

/-- For `S ≤ 0` the `j`-th bin is `null` for every age measure, so its integral vanishes. -/
theorem binNull : BinNull := by
  intro c a S h j f hS
  have hbin : binUpper S h j ≤ 0 := by
    unfold binUpper
    exact mul_nonpos_iff.mpr (Or.inr ⟨hS, (Real.exp_pos _).le⟩)
  have hsub : binSet S h j ⊆ Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    intro p hp
    have hp2 : p.1 ≤ binUpper S h j := hp.2
    exact ⟨le_trans hp2 hbin, mem_univ _⟩
  have hnull : ageμ c a (binSet S h j) = 0 :=
    measure_mono_null hsub (ageμ_Iic_prod_null c a)
  exact setLIntegral_measure_zero _ _ hnull

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore
