import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9

/-!
# Part III-a, task `PartIII-a:T23/9/1`: `EtaProfileAEMeasurable`

Source: `the November 2 reference manuscript` lines 2706-2717 (`etaL2QSup`).
The `η`-profile `η ↦ essSup_q (W ‖f(s,q,η)‖)` of a jointly measurable slice is measurable.
Proof: `essSup = sInf {a | μ {g > a} = 0}`; testing against a countable dense set `D` of `ℝ≥0∞`
gives `{η | essSup < a} = ⋃_{d ∈ D} {η | d < a} ∩ {η | μ {q | d < g(q,η)} = 0}`, and each
`η ↦ μ {q | d < g(q,η)}` is measurable by `measurable_measure_prodMk_right`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.T23_9_L1

/-- Measurability of the `η`-profile of the essential supremum in `q`, for a jointly measurable
`G : ℝ × ℝ → ℝ≥0∞` and a finite-type measure `μ` on the `q`-line. -/
lemma essSup_profile_measurable (μ : Measure ℝ) [SFinite μ] (G : ℝ × ℝ → ℝ≥0∞)
    (hG : Measurable G) :
    Measurable fun η : ℝ => essSup (fun q : ℝ => G (q, η)) μ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0∞
  have key : ∀ (η : ℝ) (a : ℝ≥0∞), essSup (fun q : ℝ => G (q, η)) μ < a ↔
      ∃ d ∈ D, d < a ∧ μ ((fun q : ℝ => (q, η)) ⁻¹' {p | d < G p}) = 0 := by
    intro η a
    constructor
    · intro h
      rw [essSup_eq_sInf] at h
      obtain ⟨b, hb, hba⟩ := sInf_lt_iff.1 h
      obtain ⟨d, hdD, hbd, hda⟩ := hDd.exists_between hba
      refine ⟨d, hdD, hda, ?_⟩
      exact measure_mono_null (fun x (hx : x ∈ (fun q : ℝ => (q, η)) ⁻¹' {p | d < G p}) =>
        (lt_trans hbd hx : b < G (x, η))) hb
    · rintro ⟨d, _, hda, hd0⟩
      rw [essSup_eq_sInf]
      exact lt_of_le_of_lt (sInf_le hd0) hda
  refine measurable_of_Iio fun a => ?_
  have hset : (fun η : ℝ => essSup (fun q : ℝ => G (q, η)) μ) ⁻¹' Iio a =
      ⋃ d ∈ D, ({η : ℝ | d < a} ∩
        {η : ℝ | μ ((fun q : ℝ => (q, η)) ⁻¹' {p | d < G p}) = 0}) := by
    ext η
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_inter_iff, mem_setOf_eq, exists_prop]
    rw [key η a]
  rw [hset]
  refine MeasurableSet.biUnion hDc fun d _ => ?_
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  have hS : MeasurableSet {p : ℝ × ℝ | d < G p} :=
    measurableSet_lt measurable_const hG
  exact (measurable_measure_prodMk_right (μ := μ) hS) (measurableSet_singleton 0)

end UnforcedLeray.Short.IIIa.T23_9_L1

open UnforcedLeray.Short.IIIa.T23_9_L1 UnforcedLeray.Short.IIIa in
/-- Leaf 1 (SP 2706-2717): the `η`-profile of the weighted `L^∞_q` norm is a.e. measurable. -/
theorem etaProfileAEMeasurable : UnforcedLeray.Short.IIIa.EtaProfileAEMeasurable := by
  intro c mZ f s hf
  have hT : Measurable fun p : ℝ × ℝ => transWeight mZ (s, p) := by
    unfold transWeight
    fun_prop
  have hGm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (transWeight mZ (s, p)) * ‖f (s, p)‖ₑ :=
    (ENNReal.measurable_ofReal.comp hT).mul hf.enorm
  exact (essSup_profile_measurable (volume.restrict (Ico (-(c / 2)) (c / 2)))
    (fun p : ℝ × ℝ => ENNReal.ofReal (transWeight mZ (s, p)) * ‖f (s, p)‖ₑ) hGm).aemeasurable
