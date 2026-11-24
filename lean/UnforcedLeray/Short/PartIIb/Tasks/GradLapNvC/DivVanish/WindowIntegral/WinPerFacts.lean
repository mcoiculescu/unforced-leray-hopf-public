import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4_2

/-!
# Part II-b, task `PartII-b:T09/4/2/1` (`WinPerFacts`)

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

Measurability, `c`-periodicity in `q`, and the cell identity for the window periodization
`winPer c χ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem winPerFacts : UnforcedLeray.Short.IIb.WinPerFacts := by
  intro c χ hc hχ
  refine ⟨?_, ?_, ?_⟩
  · have hfl : Measurable fun x : Coord => ⌊x.2.1 / c + 1 / 2⌋ :=
      Int.measurable_floor.comp (((measurable_fst.comp measurable_snd).div_const c).add_const _)
    have hcast : Measurable fun x : Coord => ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) :=
      (Measurable.of_discrete (f := fun k : ℤ => (k : ℝ))).comp hfl
    have hmap : Measurable fun x : Coord =>
        (x.1, (x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ), x.2.2)) :=
      measurable_fst.prodMk
        (((measurable_fst.comp measurable_snd).sub (hcast.const_mul c)).prodMk
          (measurable_snd.comp measurable_snd))
    exact hχ.1.smooth.continuous.measurable.comp hmap
  · intro s ξ η
    unfold winPer
    have h1 : (ξ + c) / c + 1 / 2 = ξ / c + 1 / 2 + 1 := by
      rw [add_div, div_self hc.ne']
      ring
    rw [h1, Int.floor_add_one]
    have e : ξ + c - c * ((⌊ξ / c + 1 / 2⌋ + 1 : ℤ) : ℝ) = ξ - c * (⌊ξ / c + 1 / 2⌋ : ℝ) := by
      push_cast
      ring
    rw [e]
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hlo : -1 / 2 ≤ x.2.1 / c := by
      rw [le_div_iff₀ hc]
      linarith
    have hhi : x.2.1 / c < 1 / 2 := by
      rw [div_lt_iff₀ hc]
      linarith
    have hfloor : ⌊x.2.1 / c + 1 / 2⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      constructor <;> linarith
    unfold winPer
    rw [hfloor]
    simp

end UnforcedLeray.Short.IIb
