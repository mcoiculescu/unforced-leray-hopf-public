import UnforcedLeray.Units.B0579

/-!
# Periodization of cell values vanishing near the cell boundary (helper for `relB4loc_leaf`)

Source: `the November 2 reference manuscript` lines 2941-2970.  The dense class
used for the local continuity of the relative free evolution consists of fields vanishing near the
boundary lines of the cell; their rescaled cell restrictions, periodized, are cylinder tests.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.RelB4locAux

/-- Reduction of the first coordinate into the cell `[-c/2, c/2)`. -/
def cellReduce (c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1 - c * ⌊x.1 / c + 1 / 2⌋, x.2)

/-- `c`-periodization of the cell values of `h`. -/
def cellPer (c : ℝ) (h : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := h (cellReduce c x)

theorem cellReduce_of_mem {c : ℝ} (hc : 0 < c) {x : ℝ × ℝ} (hx : x ∈ B0579.cell c) :
    cellReduce c x = x := by
  simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hx
  have h0 : ⌊x.1 / c + 1 / 2⌋ = 0 := by
    rw [Int.floor_eq_iff]
    have e1 : -(1 / 2 : ℝ) ≤ x.1 / c := by rw [le_div_iff₀ hc]; linarith [hx.1]
    have e2 : x.1 / c < 1 / 2 := by rw [div_lt_iff₀ hc]; linarith [hx.2]
    push_cast
    constructor <;> linarith
  show (x.1 - c * ⌊x.1 / c + 1 / 2⌋, x.2) = x
  rw [h0]; simp

theorem cellReduce_mem {c : ℝ} (hc : 0 < c) (x : ℝ × ℝ) : cellReduce c x ∈ B0579.cell c := by
  simp only [B0579.cell, cellReduce, mem_prod, mem_Ico, mem_univ, and_true]
  have h1 := Int.floor_le (x.1 / c + 1 / 2)
  have h2 := Int.lt_floor_add_one (x.1 / c + 1 / 2)
  have e : c * (x.1 / c + 1 / 2) = x.1 + c / 2 := by field_simp
  have h1' := mul_le_mul_of_nonneg_left h1 hc.le
  have h2' := mul_lt_mul_of_pos_left h2 hc
  rw [e] at h1' h2'
  constructor <;> nlinarith

theorem abs_cellReduce_le {c : ℝ} (hc : 0 < c) (x : ℝ × ℝ) : |(cellReduce c x).1| ≤ c / 2 := by
  have h := cellReduce_mem hc x
  simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at h
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

theorem cellReduce_add_period {c : ℝ} (hc : 0 < c) (x : ℝ × ℝ) :
    cellReduce c (x.1 + c, x.2) = cellReduce c x := by
  have h : (x.1 + c) / c + 1 / 2 = (x.1 / c + 1 / 2) + 1 := by field_simp; ring
  simp only [cellReduce, h, Int.floor_add_one]
  push_cast
  ext <;> simp; ring

theorem cellPer_periodic {c : ℝ} (hc : 0 < c) (h : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    cellPer c h (x.1 + c, x.2) = cellPer c h x := by
  simp only [cellPer, cellReduce_add_period hc]

theorem cellPer_of_mem {c : ℝ} (hc : 0 < c) (h : ℝ × ℝ → ℝ) {x : ℝ × ℝ}
    (hx : x ∈ B0579.cell c) : cellPer c h x = h x := by
  simp only [cellPer, cellReduce_of_mem hc hx]

theorem cellPer_band {c R : ℝ} {h : ℝ × ℝ → ℝ} (hb : ∀ x : ℝ × ℝ, R < |x.2| → h x = 0)
    (x : ℝ × ℝ) (hx : R < |x.2|) : cellPer c h x = 0 :=
  hb (cellReduce c x) hx

/-- The periodization of a smooth `h` vanishing in the boundary layer `c/2 - η < |x₁| ≤ c/2` of the
cell is smooth. -/
theorem contDiff_cellPer {c η : ℝ} (hc : 0 < c) (hη : 0 < η) (hηc : η < c)
    {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hvan : ∀ x : ℝ × ℝ, c / 2 - η < |x.1| → |x.1| ≤ c / 2 → h x = 0) :
    ContDiff ℝ ∞ (cellPer c h) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  set u₀ := x₀.1 / c + 1 / 2 with hu₀_def
  set n : ℤ := ⌊u₀⌋ with hn_def
  have hηc' : η / c < 1 := by rw [div_lt_one hc]; exact hηc
  have hηc0 : 0 < η / c := div_pos hη hc
  by_cases hn : (n : ℝ) < u₀
  · have hU : IsOpen {x : ℝ × ℝ | (n : ℝ) < x.1 / c + 1 / 2 ∧ x.1 / c + 1 / 2 < n + 1} := by
      apply IsOpen.inter
      · exact isOpen_lt continuous_const
          (show Continuous (fun x : ℝ × ℝ => x.1 / c + 1 / 2) by fun_prop)
      · exact isOpen_lt (show Continuous (fun x : ℝ × ℝ => x.1 / c + 1 / 2) by fun_prop)
          continuous_const
    have hx₀U : x₀ ∈ {x : ℝ × ℝ | (n : ℝ) < x.1 / c + 1 / 2 ∧ x.1 / c + 1 / 2 < n + 1} :=
      ⟨hn, Int.lt_floor_add_one u₀⟩
    have heq : (fun x : ℝ × ℝ => h (x.1 - c * n, x.2)) =ᶠ[𝓝 x₀] cellPer c h := by
      filter_upwards [hU.mem_nhds hx₀U] with x hx
      have hfl : ⌊x.1 / c + 1 / 2⌋ = n := by
        rw [Int.floor_eq_iff]; exact ⟨hx.1.le, hx.2⟩
      simp only [cellPer, cellReduce, hfl]
    have hsmooth : ContDiff ℝ ∞ (fun x : ℝ × ℝ => h (x.1 - c * n, x.2)) :=
      hh.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
    exact hsmooth.contDiffAt.congr_of_eventuallyEq heq.symm
  · have hu₀ : u₀ = n := le_antisymm (not_lt.1 hn) (Int.floor_le u₀)
    have hU : IsOpen {x : ℝ × ℝ |
        (n : ℝ) - η / c < x.1 / c + 1 / 2 ∧ x.1 / c + 1 / 2 < n + η / c} := by
      apply IsOpen.inter
      · exact isOpen_lt continuous_const
          (show Continuous (fun x : ℝ × ℝ => x.1 / c + 1 / 2) by fun_prop)
      · exact isOpen_lt (show Continuous (fun x : ℝ × ℝ => x.1 / c + 1 / 2) by fun_prop)
          continuous_const
    have hx₀U : x₀ ∈ {x : ℝ × ℝ |
        (n : ℝ) - η / c < x.1 / c + 1 / 2 ∧ x.1 / c + 1 / 2 < n + η / c} := by
      show (n : ℝ) - η / c < u₀ ∧ u₀ < n + η / c
      rw [hu₀]; constructor <;> linarith
    have heq : (fun _ : ℝ × ℝ => (0 : ℝ)) =ᶠ[𝓝 x₀] cellPer c h := by
      filter_upwards [hU.mem_nhds hx₀U] with x hx
      symm
      show h (cellReduce c x) = 0
      apply hvan _ _ (abs_cellReduce_le hc x)
      have hxc : x.1 = c * (x.1 / c + 1 / 2) - c / 2 := by field_simp; ring
      rcases le_or_gt (n : ℝ) (x.1 / c + 1 / 2) with hle | hlt
      · have hfl : ⌊x.1 / c + 1 / 2⌋ = n := by
          rw [Int.floor_eq_iff]; exact ⟨hle, by linarith [hx.2]⟩
        simp only [cellReduce, hfl]
        have h1 : 0 ≤ c * (x.1 / c + 1 / 2 - n) :=
          mul_nonneg hc.le (by linarith)
        have h2 : c * (x.1 / c + 1 / 2 - n) < η := by
          have : x.1 / c + 1 / 2 - n < η / c := by linarith [hx.2]
          calc c * (x.1 / c + 1 / 2 - n) < c * (η / c) := mul_lt_mul_of_pos_left this hc
            _ = η := by field_simp
        rw [lt_abs]; right
        nlinarith
      · have hfl : ⌊x.1 / c + 1 / 2⌋ = n - 1 := by
          rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hx.1]
        simp only [cellReduce, hfl]
        push_cast
        have h1 : c * (x.1 / c + 1 / 2 - n) < 0 := mul_neg_of_pos_of_neg hc (by linarith)
        have h2 : -η < c * (x.1 / c + 1 / 2 - n) := by
          have : -(η / c) < x.1 / c + 1 / 2 - n := by linarith [hx.1]
          calc -η = c * (-(η / c)) := by field_simp
            _ < c * (x.1 / c + 1 / 2 - n) := mul_lt_mul_of_pos_left this hc
        rw [lt_abs]; left
        nlinarith
    exact contDiffAt_const.congr_of_eventuallyEq heq.symm

/-- A periodized smooth function vanishing in the boundary layer and outside a band is a cylinder
test. -/
theorem isCylTest_cellPer {c η R : ℝ} (hc : 0 < c) (hη : 0 < η) (hηc : η < c)
    {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hvan : ∀ x : ℝ × ℝ, c / 2 - η < |x.1| → |x.1| ≤ c / 2 → h x = 0)
    (hb : ∀ x : ℝ × ℝ, R < |x.2| → h x = 0) :
    B0579.IsCylTest c (cellPer c h) where
  smooth := contDiff_cellPer hc hη hηc hh hvan
  periodic x := cellPer_periodic hc h x
  band := ⟨R, fun x hx => cellPer_band hb x hx⟩

end UnforcedLeray.Short.IIIa.RelB4locAux
