import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.Geom

/-!
# Leibniz bound for `f • g` on an open set, orders `≤ 2`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem smul_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set Space}
    (hs : IsOpen s) {f : Space → ℝ} {g : Space → F} (hf : ContDiffOn ℝ 2 f s)
    (hg : ContDiffOn ℝ 2 g s) {y : Space} (hy : y ∈ s) {Bf Bg : ℝ} (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (bf : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    (bg : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g y‖ ≤ Bg) (n : ℕ) (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun y' => f y' • g y') y‖ ≤ 4 * Bf * Bg := by
  have h := norm_iteratedFDerivWithin_smul_le hf hg hs.uniqueDiffOn hy (n := n) (by exact_mod_cast hn)
  rw [iteratedFDerivWithin_of_isOpen n hs hy] at h
  have e : ∀ i : ℕ, ‖iteratedFDerivWithin ℝ i f s y‖ = ‖iteratedFDeriv ℝ i f y‖ := fun i => by
    rw [iteratedFDerivWithin_of_isOpen i hs hy]
  have e' : ∀ i : ℕ, ‖iteratedFDerivWithin ℝ i g s y‖ = ‖iteratedFDeriv ℝ i g y‖ := fun i => by
    rw [iteratedFDerivWithin_of_isOpen i hs hy]
  simp only [e, e'] at h
  refine h.trans ?_
  have hb : ∀ i j : ℕ, i ≤ 2 → j ≤ 2 → ‖iteratedFDeriv ℝ i f y‖ * ‖iteratedFDeriv ℝ j g y‖ ≤ Bf * Bg :=
    fun i j hi hj => mul_le_mul (bf i hi) (bg j hj) (norm_nonneg _) hBf
  have hBB : 0 ≤ Bf * Bg := mul_nonneg hBf hBg
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
      ‖iteratedFDeriv ℝ (n - i) g y‖ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Bf * Bg) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    have := hb i (n - i) (by omega) (by omega)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  refine hsum.trans ?_
  rw [← Finset.sum_mul]
  have hc : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [hc]
  have : (2 : ℝ) ^ n ≤ 4 := by
    interval_cases n <;> norm_num
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
