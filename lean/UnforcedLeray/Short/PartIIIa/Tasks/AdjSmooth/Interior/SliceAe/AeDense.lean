import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_9

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem aeDense : UnforcedLeray.Short.IIIa.AeDense := by
  intro t s A hA r₀ hr₀
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨u, hu_open, hr₀u, hu_sub⟩ := mem_nhdsWithin.1 hU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu_open r₀ hr₀u
  have h1 : r₀ - ε < r₀ + ε := by linarith
  have h2 : r₀ - ε < s := by linarith [hr₀.2]
  have h3 : t < r₀ + ε := by linarith [hr₀.1]
  have h4 : t < s := lt_trans hr₀.1 hr₀.2
  have hab : max (r₀ - ε) t < min (r₀ + ε) s :=
    lt_min (max_lt h1 h3) (max_lt h2 h4)
  have hsub : Ioo (max (r₀ - ε) t) (min (r₀ + ε) s) ⊆ Ioo t s := fun r hr =>
    ⟨lt_of_le_of_lt (le_max_right _ _) hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩
  have hpos : volume (Ioo (max (r₀ - ε) t) (min (r₀ + ε) s)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  have hae : ∀ᵐ r ∂(volume.restrict (Ioo (max (r₀ - ε) t) (min (r₀ + ε) s))),
      r ∈ Ioo t s → r ∈ A :=
    ae_restrict_of_ae hA
  obtain ⟨r, hrI, hrP⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (p := fun r => r ∈ Ioo t s → r ∈ A) hae
  have hrts : r ∈ Ioo t s := hsub hrI
  have hrball : r ∈ Metric.ball r₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_left (r₀ - ε) t, hrI.1]
    · linarith [min_le_left (r₀ + ε) s, hrI.2]
  exact ⟨r, hu_sub ⟨hball hrball, hrts⟩, hrP hrts⟩

end UnforcedLeray.Short.IIIa
