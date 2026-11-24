import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Helper for `NiceFieldsSeparate` (task `PartII-b:T11/6`): covering a disc by period cells

For a measurable `G : ℂ → ℝ≥0∞` with `G (z + c) = G z`, the lower integral of `G` over a disc of
radius `R ≥ 0` is at most `(2R/c + 2)` times its integral over one period cell
`cellC c = {z | Re z ∈ [-c/2, c/2)}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Complex Filter
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.SeparateCover

/-- The period cell `{Re z ∈ [-c/2, c/2)}` of the plane. -/
def cellC (c : ℝ) : Set ℂ := {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}

/-- The `n`-th translate `{Re z ∈ [-c/2 + nc, c/2 + nc)}` of the period cell. -/
def cellN (c : ℝ) (n : ℤ) : Set ℂ :=
  {z : ℂ | z.re ∈ Ico (-(c / 2) + (n : ℝ) * c) (c / 2 + (n : ℝ) * c)}

theorem measurableSet_cellN (c : ℝ) (n : ℤ) : MeasurableSet (cellN c n) :=
  measurableSet_Ico.preimage Complex.measurable_re

theorem measurableSet_cellC (c : ℝ) : MeasurableSet (cellC c) :=
  measurableSet_Ico.preimage Complex.measurable_re

/-- Integer multiples of the period are periods. -/
theorem periodic_int {G : ℂ → ℝ≥0∞} {c : ℝ} (hper : ∀ z : ℂ, G (z + (c : ℂ)) = G z) :
    ∀ n : ℤ, ∀ z : ℂ, G (z + (n : ℂ) * (c : ℂ)) = G z := by
  intro n
  induction n using Int.induction_on with
  | zero => intro z; simp
  | succ k ih =>
    intro z
    have h := hper (z + ((k : ℤ) : ℂ) * (c : ℂ))
    rw [show z + ((k + 1 : ℤ) : ℂ) * (c : ℂ) = z + ((k : ℤ) : ℂ) * (c : ℂ) + (c : ℂ) by
      push_cast; ring, h, ih z]
  | pred k ih =>
    intro z
    have h := hper (z + ((-(k : ℤ) - 1 : ℤ) : ℂ) * (c : ℂ))
    rw [show z + ((-(k : ℤ) - 1 : ℤ) : ℂ) * (c : ℂ) + (c : ℂ)
        = z + ((-(k : ℤ) : ℤ) : ℂ) * (c : ℂ) by push_cast; ring, ih z] at h
    exact h.symm

/-- **Covering lemma.** The integral of a `c`-periodic measurable `G` over a disc of radius `R ≥ 0`
is at most `(2R/c + 2)` times its integral over one period cell. -/
theorem lintegral_ball_le_cellC_mul {c : ℝ} (hc : 0 < c) {G : ℂ → ℝ≥0∞} (hG : Measurable G)
    (hper : ∀ z : ℂ, G (z + (c : ℂ)) = G z) (z0 : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ z in ball z0 R, G z ≤ ENNReal.ofReal (2 * R / c + 2) * ∫⁻ z in cellC c, G z := by
  set a : ℤ := ⌊(z0.re - R + c / 2) / c⌋ with ha
  set b : ℤ := ⌊(z0.re + R + c / 2) / c⌋ with hb
  set S : Finset ℤ := Finset.Icc a b with hS
  -- Pointwise covering of the disc by the translates `cellN c n`, `n ∈ S`.
  have hpt : ∀ z : ℂ, (ball z0 R).indicator G z ≤ ∑ n ∈ S, (cellN c n).indicator G z := by
    intro z
    by_cases hz : z ∈ ball z0 R
    · have hd : ‖z - z0‖ < R := by
        rw [← dist_eq_norm]
        exact mem_ball.1 hz
      have hre0 : |(z - z0).re| ≤ ‖z - z0‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at hre0
      obtain ⟨hr1, hr2⟩ := abs_lt.1 (lt_of_le_of_lt hre0 hd)
      set n : ℤ := ⌊(z.re + c / 2) / c⌋ with hn
      have h1 : (n : ℝ) ≤ (z.re + c / 2) / c := Int.floor_le _
      have h2 : (z.re + c / 2) / c < (n : ℝ) + 1 := Int.lt_floor_add_one _
      have h1' : (n : ℝ) * c ≤ z.re + c / 2 := (le_div_iff₀ hc).1 h1
      have h2' : z.re + c / 2 < ((n : ℝ) + 1) * c := (div_lt_iff₀ hc).1 h2
      have h2'' : ((n : ℝ) + 1) * c = (n : ℝ) * c + c := by ring
      have hA : (z0.re - R + c / 2) / c ≤ (z.re + c / 2) / c :=
        (div_le_div_iff_of_pos_right hc).2 (by linarith)
      have hB : (z.re + c / 2) / c ≤ (z0.re + R + c / 2) / c :=
        (div_le_div_iff_of_pos_right hc).2 (by linarith)
      have hnS : n ∈ S := by
        rw [hS, Finset.mem_Icc]
        exact ⟨Int.floor_mono hA, Int.floor_mono hB⟩
      have hzmem : z ∈ cellN c n := by
        simp only [cellN, mem_setOf_eq, mem_Ico]
        constructor <;> linarith
      rw [indicator_of_mem hz]
      calc G z = (cellN c n).indicator G z := (indicator_of_mem hzmem _).symm
        _ ≤ ∑ m ∈ S, (cellN c m).indicator G z :=
          Finset.single_le_sum (f := fun m => (cellN c m).indicator G z)
            (fun _ _ => zero_le) hnS
    · rw [indicator_of_notMem hz]
      exact zero_le
  -- Each translate has the same integral as the period cell.
  have hterm : ∀ n : ℤ, ∫⁻ z, (cellN c n).indicator G z = ∫⁻ z in cellC c, G z := by
    intro n
    have key : ∀ z : ℂ, (cellN c n).indicator G z =
        (cellC c).indicator G (z - (n : ℂ) * (c : ℂ)) := by
      intro z
      have hG' : G z = G (z - (n : ℂ) * (c : ℂ)) := by
        have := periodic_int hper n (z - (n : ℂ) * (c : ℂ))
        rw [sub_add_cancel] at this
        exact this
      have hre : (z - (n : ℂ) * (c : ℂ)).re = z.re - (n : ℝ) * c := by simp
      by_cases hz : z ∈ cellN c n
      · have hz' : z - (n : ℂ) * (c : ℂ) ∈ cellC c := by
          simp only [cellN, cellC, mem_setOf_eq, mem_Ico, hre] at hz ⊢
          constructor <;> linarith [hz.1, hz.2]
        rw [indicator_of_mem hz, indicator_of_mem hz', hG']
      · have hz' : z - (n : ℂ) * (c : ℂ) ∉ cellC c := by
          intro h
          apply hz
          simp only [cellN, cellC, mem_setOf_eq, mem_Ico, hre] at h ⊢
          constructor <;> linarith [h.1, h.2]
        rw [indicator_of_notMem hz, indicator_of_notMem hz']
    calc ∫⁻ z, (cellN c n).indicator G z = ∫⁻ z, (cellC c).indicator G (z - (n : ℂ) * (c : ℂ)) :=
          lintegral_congr key
      _ = ∫⁻ z, (cellC c).indicator G z := lintegral_sub_right_eq_self _ _
      _ = ∫⁻ z in cellC c, G z := by rw [lintegral_indicator (measurableSet_cellC c)]
  -- The number of translates is at most `2R/c + 2`.
  have hcardR : ((S.card : ℕ) : ℝ) ≤ 2 * R / c + 2 := by
    rw [hS, Int.card_Icc]
    have hb' : (b : ℝ) ≤ (z0.re + R + c / 2) / c := Int.floor_le _
    have ha' : (z0.re - R + c / 2) / c - 1 < (a : ℝ) := Int.sub_one_lt_floor _
    have key : (z0.re + R + c / 2) / c + 1 - ((z0.re - R + c / 2) / c - 1) = 2 * R / c + 2 := by
      ring
    have hm : ((b + 1 - a : ℤ) : ℝ) < 2 * R / c + 2 := by
      push_cast
      linarith
    by_cases hm0 : 0 ≤ b + 1 - a
    · have hcast : (((b + 1 - a).toNat : ℕ) : ℝ) = ((b + 1 - a : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hm0
      rw [hcast]
      exact hm.le
    · have h0 : (b + 1 - a).toNat = 0 := Int.toNat_eq_zero.2 (not_le.1 hm0).le
      rw [h0]
      have : 0 ≤ 2 * R / c := div_nonneg (by linarith) hc.le
      simp only [Nat.cast_zero]
      linarith
  have hcard : (S.card : ℝ≥0∞) ≤ ENNReal.ofReal (2 * R / c + 2) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcardR
  calc ∫⁻ z in ball z0 R, G z = ∫⁻ z, (ball z0 R).indicator G z := by
        rw [lintegral_indicator measurableSet_ball]
    _ ≤ ∫⁻ z, ∑ n ∈ S, (cellN c n).indicator G z := lintegral_mono hpt
    _ = ∑ n ∈ S, ∫⁻ z, (cellN c n).indicator G z :=
        lintegral_finset_sum S (fun n _ => hG.indicator (measurableSet_cellN c n))
    _ = ∑ n ∈ S, ∫⁻ z in cellC c, G z := Finset.sum_congr rfl (fun n _ => hterm n)
    _ = (S.card : ℝ≥0∞) * ∫⁻ z in cellC c, G z := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (2 * R / c + 2) * ∫⁻ z in cellC c, G z := by gcongr

end UnforcedLeray.Short.IIb.SeparateCover
