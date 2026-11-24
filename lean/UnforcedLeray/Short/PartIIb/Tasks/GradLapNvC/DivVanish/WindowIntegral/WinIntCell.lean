import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4_2

/-!
# Part II-b, task `PartII-b:T09/4/2/7` (`WinIntCell`)

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

The window pairing `wInt χ g = ∫ χ s^{-5/2} g` is the cell integral
`∫_{s>0, |q|<c/2} s^{-5/2} · (winPer c χ) · g`:
the integrand of `wInt` vanishes off `tsupport χ ⊆ {s > 0} ∩ {|q| < c/2}`, and on the cell
`q ∈ [-c/2, c/2)` the periodization satisfies `winPer c χ = χ` (floor is `0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem winIntCell : UnforcedLeray.Short.IIb.WinIntCell := by
  intro c χ g hc hχ
  -- the window test vanishes off the half cell `s > 0`, `|q| < c/2`
  have hsupp : ∀ x : Coord, x ∉ Ioi (0 : ℝ) ×ˢ Axi.qCell c → χ x = 0 := by
    intro x hx
    by_contra hne
    apply hx
    have hmem : x ∈ tsupport χ := subset_tsupport χ (Function.mem_support.2 hne)
    have h1 := hχ.1.supp hmem
    have h2 := hχ.2 hmem
    rcases h1 with ⟨h1a, -⟩
    obtain ⟨h2a, h2b⟩ := h2
    exact ⟨h1a, ⟨⟨h2a.le, h2b⟩, trivial⟩⟩
  -- on the cell, the periodization is the identity
  have hwin : ∀ p : Coord, p ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c → winPer c χ p = χ p := by
    intro p hp
    have hq : p.2.1 ∈ Ico (-c / 2) (c / 2) := hp.2.1
    obtain ⟨hq1, hq2⟩ := hq
    have hlo : -1 / 2 ≤ p.2.1 / c := by
      rw [le_div_iff₀ hc]
      linarith
    have hhi : p.2.1 / c < 1 / 2 := by
      rw [div_lt_iff₀ hc]
      linarith
    have hfloor : ⌊p.2.1 / c + 1 / 2⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      constructor <;> linarith
    unfold winPer
    rw [hfloor]
    simp
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) := by
    unfold Axi.qCell
    exact measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hzero : ∀ x : Coord, x ∉ Ioi (0 : ℝ) ×ˢ Axi.qCell c →
      ((χ x : ℂ) * ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) * g x = 0 := by
    intro x hx
    rw [hsupp x hx]
    simp
  unfold wInt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine setIntegral_congr_fun hS ?_
  intro p hp
  dsimp only
  rw [hwin p hp]
  ring

end UnforcedLeray.Short.IIb
