import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.Age

/-!
# Part III-a: `E1ChangeVar` from the fixed-cell form of `E_1`

Source of record: `the November 2 reference manuscript` (SP), lines 2860-2864,
3036-3037. `revE1 = physE1 ∘ revAge` on the flow window is `adjF1_eq_fixed` (`ChangeVar.lean`) at the
age `revAge ν s ζ ∈ [t, s)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- **`E1ChangeVar`** (SP 2860-2864, 3036-3037). -/
theorem e1ChangeVar_direct (m : ℝ) : E1ChangeVar m := by
  intro ν tr t s φ ζ hζ
  obtain ⟨hν, ht0, hts, ⟨G, hG, hφ⟩, hz⟩ := hζ
  have hr : revAge ν s ζ ∈ Ico t s :=
    (adjAgeMap ν t s hν ht0 hts).2.2 ⟨hz.1, hz.2.le⟩
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  unfold revE1 physE1
  exact adjF1_eq_fixed hν hc (ht0.trans hr.1) (hφ.smooth _ hr)

end UnforcedLeray.Short.IIIa.AdjE1
