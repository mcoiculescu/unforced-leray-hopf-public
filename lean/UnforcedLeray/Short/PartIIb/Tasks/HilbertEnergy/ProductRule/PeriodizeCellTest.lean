import UnforcedLeray.Short.PartIIb.Sub.T15_2

/-!
# Part II-b, task `PartII-b:T15/2/15`: periodization of a cell-supported test

Source of record: `the November 2 reference manuscript`. The target is the Prop
`PeriodizeCellTest` (`Sub/T15_2.lean`, leaf `PartII-b:T15/2/15`). For smooth `ζ` with compact support
inside the slab `ℝ × (-c/2, c/2) × ℝ`, the periodization `Φ(t, q, η) = ∑ₙ ζ(t, q - nc, η)` is a
`LogTest c` that agrees with `ζ` on the cell `q ∈ [-c/2, c/2)`.

Technique (as in `Short/PartII-b/Tasks/FlatUnique/CellStream/Partition.lean`): a compact support
gives a bound on the `q`-coordinate, so near each point only finitely many translates contribute
(smoothness is local and finite); reindexing `n ↦ n - 1` gives periodicity; the `t` and `η`
supports are those of `ζ`; on the cell only the `n = 0` term survives.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The `q`-periodization `∑ₙ ζ(t, q - nc, η)` of `ζ` in the logarithmic chart. -/
def pcellPer (c : ℝ) (ζ : Coord → ℝ) (x : Coord) : ℝ :=
  ∑' n : ℤ, ζ (x.1, (x.2.1 - n * c, x.2.2))

/-- Integers with `|n| c ≤ B` lie in a fixed finite window. -/
theorem pcell_mem_window {c B : ℝ} (hc : 0 < c) {n : ℤ} (h : |(n : ℝ)| * c ≤ B) :
    n ∈ Finset.Icc (-⌈B / c⌉) ⌈B / c⌉ := by
  have h1 : |(n : ℝ)| ≤ B / c := (le_div_iff₀ hc).2 h
  have h2 : B / c ≤ ((⌈B / c⌉ : ℤ) : ℝ) := Int.le_ceil _
  have h3 : |(n : ℝ)| ≤ ((⌈B / c⌉ : ℤ) : ℝ) := h1.trans h2
  have h4 : (n : ℝ) ≤ ((⌈B / c⌉ : ℤ) : ℝ) := (le_abs_self _).trans h3
  have h5 : -(n : ℝ) ≤ ((⌈B / c⌉ : ℤ) : ℝ) := (neg_le_abs _).trans h3
  have h4' : n ≤ ⌈B / c⌉ := by exact_mod_cast h4
  have h5' : -n ≤ ⌈B / c⌉ := by exact_mod_cast h5
  rw [Finset.mem_Icc]
  constructor <;> omega

/-- A continuous coordinate function is bounded on the support of a compactly supported `ζ`. -/
theorem pcell_bound_gen {ζ : Coord → ℝ} (hcs : HasCompactSupport ζ) (f : Coord → ℝ)
    (hf : Continuous f) : ∃ R : ℝ, ∀ y : Coord, ζ y ≠ 0 → |f y| ≤ R := by
  obtain ⟨R, hR⟩ := hcs.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨R, fun y hy => ?_⟩
  have h := hR y (subset_tsupport _ hy)
  rwa [Real.norm_eq_abs] at h

/-- Smoothness of each translate `x ↦ ζ(x.1, x.2.1 - nc, x.2.2)`. -/
theorem pcellPer_term_contDiff {ζ : Coord → ℝ} (hζ : ContDiff ℝ ∞ ζ) (c : ℝ) (n : ℤ) :
    ContDiff ℝ ∞ (fun x : Coord => ζ (x.1, (x.2.1 - n * c, x.2.2))) := by
  have hmap : ContDiff ℝ ∞ (fun x : Coord => (x.1, (x.2.1 - n * c, x.2.2))) := by
    fun_prop
  exact hζ.comp hmap

/-- Smoothness of the periodization: near each point only a finite window of `n` contributes. -/
theorem pcellPer_contDiff {ζ : Coord → ℝ} (hζ : ContDiff ℝ ∞ ζ) {c R : ℝ} (hc : 0 < c)
    (hR : ∀ y : Coord, ζ y ≠ 0 → |y.2.1| ≤ R) : ContDiff ℝ ∞ (pcellPer c ζ) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  have hopen : IsOpen {x : Coord | |x.2.1 - x₀.2.1| < c} :=
    isOpen_lt (by fun_prop) continuous_const
  have hmem : {x : Coord | |x.2.1 - x₀.2.1| < c} ∈ 𝓝 x₀ :=
    hopen.mem_nhds (by simpa using hc)
  have hsum : ContDiff ℝ ∞ (fun x : Coord => ∑ n ∈ Finset.Icc (-⌈(R + |x₀.2.1| + c) / c⌉)
      ⌈(R + |x₀.2.1| + c) / c⌉, ζ (x.1, (x.2.1 - n * c, x.2.2))) :=
    ContDiff.sum fun n _ => pcellPer_term_contDiff hζ c n
  refine hsum.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with x hx
  have hx' : |x.2.1 - x₀.2.1| < c := hx
  unfold pcellPer
  apply tsum_eq_sum
  intro n hn
  show ζ (x.1, (x.2.1 - n * c, x.2.2)) = 0
  by_contra hne
  have hy' : |x.2.1 - n * c| ≤ R := hR _ hne
  have hA : |x.2.1| ≤ |x₀.2.1| + c := by
    have := abs_sub_abs_le_abs_sub x.2.1 x₀.2.1
    linarith
  have hnc : |(n : ℝ) * c| ≤ R + |x₀.2.1| + c := by
    have h1 := abs_le.mp hy'
    have h2 := abs_le.mp hA
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hnc' : |(n : ℝ)| * c ≤ R + |x₀.2.1| + c := by
    rw [abs_mul, abs_of_pos hc] at hnc
    exact hnc
  exact hn (pcell_mem_window hc hnc')

/-- Periodicity: reindexing `n ↦ n - 1` absorbs the shift `q ↦ q + c`. -/
theorem pcellPer_periodic {ζ : Coord → ℝ} (c : ℝ) (x : Coord) :
    pcellPer c ζ (qShift c x) = pcellPer c ζ x := by
  dsimp only [pcellPer, qShift]
  refine (tsum_congr fun n => ?_).trans
    ((Equiv.subRight (1 : ℤ)).tsum_eq (fun m : ℤ => ζ (x.1, (x.2.1 - m * c, x.2.2))))
  show ζ (x.1, (x.2.1 + c - (n : ℝ) * c, x.2.2)) = ζ (x.1, (x.2.1 - ((n - 1 : ℤ) : ℝ) * c, x.2.2))
  rw [show x.2.1 + c - (n : ℝ) * c = x.2.1 - ((n - 1 : ℤ) : ℝ) * c by push_cast; ring]

/-- Vanishing for `|t|` or `|η|` large, from the bounds on the support of `ζ`. -/
theorem pcellPer_compact {c : ℝ} {ζ : Coord → ℝ} {T L : ℝ}
    (hT : ∀ y : Coord, ζ y ≠ 0 → |y.1| ≤ T) (hL : ∀ y : Coord, ζ y ≠ 0 → |y.2.2| ≤ L) :
    ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → pcellPer c ζ x = 0 := by
  intro x hx
  have hz : ∀ n : ℤ, ζ (x.1, (x.2.1 - n * c, x.2.2)) = 0 := by
    intro n
    by_contra hne
    rcases hx with hx | hx
    · have h1 : |x.1| ≤ T := hT (x.1, (x.2.1 - n * c, x.2.2)) hne
      linarith
    · have h2 : |x.2.2| ≤ L := hL (x.1, (x.2.1 - n * c, x.2.2)) hne
      linarith
  unfold pcellPer
  simp only [hz, tsum_zero]

/-- On the cell `q ∈ [-c/2, c/2)` only the `n = 0` term of the periodization survives. -/
theorem pcellPer_cell {c : ℝ} (hc : 0 < c) {ζ : Coord → ℝ}
    (hsupp : tsupport ζ ⊆ (univ : Set ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)))
    (x : Coord) (hx : x.2.1 ∈ Ico (-c / 2) (c / 2)) : pcellPer c ζ x = ζ x := by
  unfold pcellPer
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    by_contra hne
    have hy : (x.1, (x.2.1 - n * c, x.2.2)) ∈ tsupport ζ := subset_tsupport _ hne
    have hA : x.2.1 - (n : ℝ) * c ∈ Ioo (-c / 2) (c / 2) := (hsupp hy).2.1
    obtain ⟨hA1, hA2⟩ := hA
    obtain ⟨hx1, hx2⟩ := hx
    have hn' : n ≥ 1 ∨ n ≤ -1 := by omega
    rcases hn' with h | h
    · have h' : (1 : ℝ) ≤ n := by exact_mod_cast h
      have h'' : (1 : ℝ) * c ≤ n * c := mul_le_mul_of_nonneg_right h' hc.le
      linarith
    · have h' : (n : ℝ) ≤ -1 := by exact_mod_cast h
      have h'' : (n : ℝ) * c ≤ (-1) * c := mul_le_mul_of_nonneg_right h' hc.le
      linarith

/-- **Leaf `PartII-b:T15/2/15`** (periodization of a cell-supported test): `PeriodizeCellTest`. -/
theorem periodizeCellTest : PeriodizeCellTest := by
  unfold PeriodizeCellTest
  intro c ζ hc hζ hcs hsupp
  obtain ⟨R, hR⟩ := pcell_bound_gen hcs (fun y : Coord => y.2.1) (by fun_prop)
  obtain ⟨T, hT⟩ := pcell_bound_gen hcs (fun y : Coord => y.1) (by fun_prop)
  obtain ⟨L, hL⟩ := pcell_bound_gen hcs (fun y : Coord => y.2.2) (by fun_prop)
  refine ⟨pcellPer c ζ, ⟨pcellPer_contDiff hζ hc hR, fun x => pcellPer_periodic c x,
    ⟨T, L, pcellPer_compact (c := c) hT hL⟩⟩, fun x hx => pcellPer_cell hc hsupp x hx⟩

end UnforcedLeray.Short.IIb
