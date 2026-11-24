import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs

/-!
# `AePeriodicExtend`

A property holding a.e. on one period and invariant a.e. under the shift `t ↦ t + P` holds a.e.
on the line. Generalises `phaseSliceL2_aeShift` and `phaseSliceL2_aeFin` to a Prop-valued `Q`.
Source `the November 2 reference manuscript` lines 1334-1337 and 1351-1362.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A.e. shift invariance of a Prop-valued `Q` under all integer multiples of `P`. -/
theorem aePeriodicExtend_shift {P : ℝ} {Q : ℝ → Prop} (hper : ∀ᵐ t : ℝ, Q (t + P) ↔ Q t) :
    ∀ n : ℤ, ∀ᵐ t : ℝ, Q (t + (n : ℝ) * P) ↔ Q t := by
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
      filter_upwards [(measurePreserving_add_right volume ((i : ℝ) * P)).quasiMeasurePreserving.ae
        hper, ih] with t h1 h2
      rw [show t + ((((i : ℤ) + 1 : ℤ)) : ℝ) * P = t + (i : ℝ) * P + P by push_cast; ring]
      exact h1.trans h2
  | pred i ih =>
      have h1 := (measurePreserving_add_right volume ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * P)).quasiMeasurePreserving.ae
        hper
      filter_upwards [h1, ih] with t h1 h2
      rw [show t + ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * P) + P = t + (((-(i : ℤ)) : ℤ) : ℝ) * P by
        push_cast; ring] at h1
      exact h1.symm.trans h2

/-- The a.e. statement on one period, pulled back along integer shifts. -/
theorem aePeriodicExtend_pieces {P : ℝ} {Q : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict (Ioc 0 P)), Q t) :
    ∀ᵐ t : ℝ, ∀ n : ℤ, t + (n : ℝ) * P ∈ Ioc 0 P → Q (t + (n : ℝ) * P) := by
  rw [ae_restrict_iff' measurableSet_Ioc] at h
  rw [ae_all_iff]
  intro n
  exact (measurePreserving_add_right volume ((n : ℝ) * P)).quasiMeasurePreserving.ae h

/-- A property true a.e. on one period and a.e. invariant under the shift `t ↦ t + P` holds a.e.
on the line. -/
theorem aePeriodicExtend : AePeriodicExtend := by
  intro P hP Q h hper
  have hall : ∀ᵐ t : ℝ, ∀ n : ℤ, Q (t + (n : ℝ) * P) ↔ Q t := by
    rw [ae_all_iff]
    exact fun n => aePeriodicExtend_shift hper n
  filter_upwards [hall, aePeriodicExtend_pieces h] with t ht hp
  have hm : t + (((-(toIocDiv hP 0 t) : ℤ)) : ℝ) * P ∈ Ioc 0 P := by
    have h0 := sub_toIocDiv_zsmul_mem_Ioc hP 0 t
    rw [zero_add] at h0
    convert h0 using 1
    rw [zsmul_eq_mul]
    push_cast
    ring
  exact (ht _).mp (hp _ hm)

end UnforcedLeray.Short.PartIIIb.Concrete
