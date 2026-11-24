import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1

/-!
# Part II-b, task `PartII-b:T08/1/3`: the `NvC` pairing sees the profile only on `s > 0`

Source of record: `the November 2 reference manuscript`, lines 1902-1906 and
1912-1915.

Target: `driftNvCCongr_proof : UnforcedLeray.Short.IIb.DriftNvCCongr`.

Proof outline. Let `E` be a measurable Lebesgue-null superset of the bad set
`{x | ¬(0 < x.1 → f x = g x)}`. Its `c`-periodic saturation
`M = ⋃_{k ∈ ℤ} (ξ ↦ ξ + k c)⁻¹' E` is measurable, null (translation invariance in `ξ`) and
`q`-periodic. `ChartNullPullback` gives, for a.e. phase `τ` and a.e. `y`, that the chart point
`chart ε⁻¹ τ y` lies outside `M`; it then lies outside `E`, so `f = g` there (the chart point
has `s > 0` off the axis). Hence the integrands agree a.e. and the two pairings coincide.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

namespace DriftNvCCongrHelp

/-- Translation `ξ ↦ ξ + a` in the `q`-variable, as a map of `ℝ × (ℝ × ℝ)`, preserves Lebesgue
measure. -/
lemma shift_measurePreserving (a : ℝ) :
    MeasurePreserving (fun x : Coord => (x.1, (x.2.1 + a, x.2.2))) volume volume := by
  have h1 : MeasurePreserving (fun t : ℝ => t + a) volume volume :=
    measurePreserving_add_right volume a
  have h2 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (Prod.map (fun t : ℝ => t + a) (id : ℝ → ℝ)))
      (volume.prod (volume.prod volume)) (volume.prod (volume.prod volume)) :=
    (MeasurePreserving.id volume).prod (h1.prod (MeasurePreserving.id volume))
  exact h2

/-- The shifted coordinate map is measurable. -/
lemma shift_measurable (a : ℝ) :
    Measurable (fun x : Coord => (x.1, (x.2.1 + a, x.2.2))) :=
  Continuous.measurable (by fun_prop)

end DriftNvCCongrHelp

open DriftNvCCongrHelp in
/-- **Leaf `T08/1/3`.** The `NvC` pairing is unchanged when the profile is altered on a
Lebesgue-null subset of `s > 0`. -/
theorem driftNvCCongr_proof : UnforcedLeray.Short.IIb.DriftNvCCongr := by
  intro hNull c ε f g Φ hc hε hfg
  -- a measurable null superset of the bad set
  have hbad : volume {x : Coord | ¬ (0 < x.1 → f x = g x)} = 0 := ae_iff.1 hfg
  obtain ⟨E, hEsup, hEm, hE0⟩ := exists_measurable_superset_of_null hbad
  -- the `c`-periodic saturation of `E`
  obtain ⟨M, hMdef⟩ : ∃ M : Set Coord, M = {x : Coord | ∃ k : ℤ,
      (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) ∈ E} := ⟨_, rfl⟩
  have hmemM : ∀ x : Coord, x ∈ M ↔ ∃ k : ℤ, (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) ∈ E := by
    intro x
    rw [hMdef]
    rfl
  have hUnion : M = ⋃ k : ℤ, (fun x : Coord => (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) ⁻¹' E := by
    ext x
    simp only [hmemM, Set.mem_iUnion, Set.mem_preimage]
  have hMm : MeasurableSet M := by
    rw [hUnion]
    exact MeasurableSet.iUnion fun k => hEm.preimage (shift_measurable ((k : ℝ) * c))
  have hM0 : volume M = 0 := by
    rw [hUnion]
    refine measure_iUnion_null fun k => ?_
    rw [(shift_measurePreserving ((k : ℝ) * c)).measure_preimage hEm.nullMeasurableSet, hE0]
  have hMper : ∀ s ξ η, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M := by
    intro s ξ η
    rw [hmemM, hmemM]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      have e : ξ + ((k + 1 : ℤ) : ℝ) * c = ξ + c + (k : ℝ) * c := by
        push_cast
        ring
      show (s, (ξ + ((k + 1 : ℤ) : ℝ) * c, η)) ∈ E
      rw [e]
      exact hk
    · rintro ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      have e : ξ + c + ((k - 1 : ℤ) : ℝ) * c = ξ + (k : ℝ) * c := by
        push_cast
        ring
      show (s, (ξ + c + ((k - 1 : ℤ) : ℝ) * c, η)) ∈ E
      rw [e]
      exact hk
  -- off `M`, the profiles agree at the chart point (which has `s > 0` off the axis)
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    field_simp
  have hnull := hNull ε⁻¹ c (2 * ε * c) (inv_pos.2 hε) hc hP M hMm hM0 hMper
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hnull] with t ht
  refine integral_congr_ae ?_
  filter_upwards [ht, Axi.ae_not_mem_axis] with y hy hax
  have hpos : 0 < (Axi.chart ε⁻¹ t y).1 := Axi.age_pos (inv_ne_zero hε.ne') hax
  have hxE : Axi.chart ε⁻¹ t y ∉ E := by
    intro hE
    apply hy
    rw [hmemM]
    refine ⟨0, ?_⟩
    have hx0 : ((Axi.chart ε⁻¹ t y).1, ((Axi.chart ε⁻¹ t y).2.1 + ((0 : ℤ) : ℝ) * c,
        (Axi.chart ε⁻¹ t y).2.2)) = Axi.chart ε⁻¹ t y := by
      simp
    rw [hx0]
    exact hE
  have hfg' : f (Axi.chart ε⁻¹ t y) = g (Axi.chart ε⁻¹ t y) := by
    by_contra hne
    exact hxE (hEsup (show Axi.chart ε⁻¹ t y ∈ {x : Coord | ¬ (0 < x.1 → f x = g x)} from
      fun h => hne (h hpos)))
  have hN : NvC ε⁻¹ f (t, y) = NvC ε⁻¹ g (t, y) := by
    simp only [NvC, Axi.Nv, hfg']
  simp only [hN]

end UnforcedLeray.Short.IIb
