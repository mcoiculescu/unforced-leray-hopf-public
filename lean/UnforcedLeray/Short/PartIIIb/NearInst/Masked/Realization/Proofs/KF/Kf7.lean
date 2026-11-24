import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# KF7: null sets of the circle pull back to null sets of `ℝ`

Leaf `KF7` of `Sub1.lean` (source `sep:resolvent`, 3620-3626). The set `{t | s - t ∈ N}` is a
translate-reflection of the preimage of a null set `N ⊆ ℝ/Pℤ` under the coordinate projection
`ℝ → ℝ/Pℤ`. The preimage is null because it is `P`-periodic, and its intersection with one period
`Ioc 0 P` is null by the measure-preservation of the projection on a fundamental domain.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- The preimage of a null measurable set of `ℝ/Pℤ` under the coordinate projection is null in
`ℝ`: it is the countable union of its translates by `k • P` of the piece in one period. -/
theorem kf7_aux_preimage_null (P : ℝ) [Fact (0 < P)] (N : Set (AddCircle P))
    (hmeas : MeasurableSet N) (hN : volume N = 0) :
    volume ((fun x : ℝ => (x : AddCircle P)) ⁻¹' N) = 0 := by
  have hP : (0 : ℝ) < P := Fact.out
  have hcoe : ∀ (y : ℝ) (k : ℤ), ((y - k • P : ℝ) : AddCircle P) = (y : AddCircle P) := by
    intro y k
    have hk : ((k • P : ℝ) : AddCircle P) = 0 := (AddCircle.coe_eq_zero_iff P).2 ⟨k, rfl⟩
    rw [AddCircle.coe_sub, hk, sub_zero]
  have hA : volume (((fun x : ℝ => (x : AddCircle P)) ⁻¹' N) ∩ Ioc 0 P) = 0 := by
    have h := AddCircle.add_projection_respects_measure P 0 hmeas
    rw [zero_add] at h
    exact h.symm.trans hN
  refine measure_mono_null (t := ⋃ k : ℤ,
    (fun x : ℝ => x - k • P) ⁻¹' (((fun x : ℝ => (x : AddCircle P)) ⁻¹' N) ∩ Ioc 0 P)) ?_ ?_
  · intro x hx
    rw [mem_iUnion]
    refine ⟨toIocDiv hP 0 x, ?_⟩
    have hmod : toIocMod hP 0 x = x - toIocDiv hP 0 x • P := by
      have h1 := toIocMod_sub_self hP 0 x
      have h2 : (-toIocDiv hP 0 x) • P = -(toIocDiv hP 0 x • P) := neg_smul _ _
      linarith
    have hmem := toIocMod_mem_Ioc hP 0 x
    show x - toIocDiv hP 0 x • P ∈ ((fun x : ℝ => (x : AddCircle P)) ⁻¹' N) ∩ Ioc 0 P
    rw [← hmod]
    refine ⟨?_, ?_⟩
    · show ((toIocMod hP 0 x : ℝ) : AddCircle P) ∈ N
      rw [hmod, hcoe]
      exact hx
    · simpa using hmem
  · apply measure_iUnion_null
    intro k
    have hfun : (fun x : ℝ => x - k • P) = (fun x : ℝ => x + (-(k • P))) := by
      funext x
      rw [sub_eq_add_neg]
    rw [hfun]
    exact (measure_preimage_add_right volume _ _).trans hA

/-- **KF7** (null sets of the circle pull back to null sets of `ℝ`): for `N ⊆ ℝ/Pℤ` null and `s`,
`{t | s - t ∈ N}` is null. -/
theorem kf7 : KF7 := by
  intro P _ N hN s
  obtain ⟨s0, rfl⟩ : ∃ s0 : ℝ, (s0 : AddCircle P) = s := QuotientAddGroup.mk_surjective s
  obtain ⟨N', hNN', hmeas, hN'0⟩ := exists_measurable_superset_of_null hN
  have hM0 := kf7_aux_preimage_null P N' hmeas hN'0
  refine measure_mono_null (t := {t : ℝ | (s0 : AddCircle P) - (t : AddCircle P) ∈ N'}) ?_ ?_
  · intro t ht
    exact hNN' ht
  · have hset : {t : ℝ | (s0 : AddCircle P) - (t : AddCircle P) ∈ N'} =
        (fun t : ℝ => -t) ⁻¹' ((fun u : ℝ => u + s0) ⁻¹'
          ((fun x : ℝ => (x : AddCircle P)) ⁻¹' N')) := by
      ext t
      simp only [Set.mem_ofPred_eq, mem_preimage]
      rw [← AddCircle.coe_sub, show -t + s0 = s0 - t by ring]
    rw [hset]
    have hmeasX : MeasurableSet ((fun u : ℝ => u + s0) ⁻¹'
        ((fun x : ℝ => (x : AddCircle P)) ⁻¹' N')) :=
      (measurable_add_const s0) (hmeas.preimage AddCircle.measurable_mk')
    exact ((Measure.measurePreserving_neg volume).measure_preimage
      hmeasX.nullMeasurableSet).trans ((measure_preimage_add_right volume _ _).trans hM0)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
