import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import Mathlib.Algebra.Order.Chebyshev

/-!
# Part I, `PartI:T04/10/1/2/1/1`: `WordSqJetCompare`

Source of record: `the November 2 reference manuscript`, lines 285-287.
Comparison of the operator norm of the `j`-th jet with the word sum `wordSq j`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

theorem wsjc_len {j : ℕ} {u : List Bool} (hu : u ∈ wordsOfLength j) : u.length = j := by
  unfold wordsOfLength at hu
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hu
  simp

theorem wsjc_card (j : ℕ) : ((wordsOfLength j).card : ℝ) = 2 ^ j := by
  rw [card_wordsOfLength]
  push_cast
  ring

/-- **Target** `wordSqJetCompare_proof`: comparison of operator norm and word sums
(`WordSqJetCompare`, `Sub/PartI_T04_10_1_2_1.lean`). -/
theorem wordSqJetCompare_proof : WordSqJetCompare := by
  intro f hf j z
  have hC : UnforcedLeray.Short.PartI.CylJetWord := cylJetWord_proof
  have hsum := cjw_norm_le_sum f hf j z
  have hcs : (∑ w ∈ wordsOfLength j, |UnforcedLeray.B0151.derivWord w f z|) ^ 2 ≤
      ((wordsOfLength j).card : ℝ) *
        ∑ w ∈ wordsOfLength j, |UnforcedLeray.B0151.derivWord w f z| ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsq : ∑ w ∈ wordsOfLength j, |UnforcedLeray.B0151.derivWord w f z| ^ 2 =
      wordSq j f z := by
    unfold wordSq
    exact Finset.sum_congr rfl (fun w _ => sq_abs _)
  have hb : ∀ w ∈ wordsOfLength j, |UnforcedLeray.B0151.derivWord w f z| ≤
      ‖iteratedFDeriv ℝ j f z‖ := fun w hw => (hC f hf j z).1 w (wsjc_len hw)
  constructor
  · calc ‖iteratedFDeriv ℝ j f z‖ ^ 2
        ≤ (∑ w ∈ wordsOfLength j, |UnforcedLeray.B0151.derivWord w f z|) ^ 2 := by gcongr
      _ ≤ ((wordsOfLength j).card : ℝ) *
            ∑ w ∈ wordsOfLength j, |UnforcedLeray.B0151.derivWord w f z| ^ 2 := hcs
      _ = 2 ^ j * wordSq j f z := by rw [hsq, wsjc_card]
  · have hsq2 : ∀ w ∈ wordsOfLength j,
        UnforcedLeray.B0151.derivWord w f z ^ 2 ≤ ‖iteratedFDeriv ℝ j f z‖ ^ 2 := by
      intro w hw
      calc UnforcedLeray.B0151.derivWord w f z ^ 2
          = |UnforcedLeray.B0151.derivWord w f z| ^ 2 := (sq_abs _).symm
        _ ≤ ‖iteratedFDeriv ℝ j f z‖ ^ 2 := by gcongr; exact hb w hw
    calc wordSq j f z
        = ∑ w ∈ wordsOfLength j, UnforcedLeray.B0151.derivWord w f z ^ 2 := rfl
      _ ≤ ∑ _w ∈ wordsOfLength j, ‖iteratedFDeriv ℝ j f z‖ ^ 2 := Finset.sum_le_sum hsq2
      _ = ((wordsOfLength j).card : ℝ) * ‖iteratedFDeriv ℝ j f z‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = 2 ^ j * ‖iteratedFDeriv ℝ j f z‖ ^ 2 := by rw [wsjc_card]

end UnforcedLeray.Short.PartI
