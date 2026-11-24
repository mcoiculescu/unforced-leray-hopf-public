import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs

/-!
# `DrivingOfSmooth` (task `PartIII-b:C/flatset/col/7/1/1/2/1/org2/leray/16`)

A smooth periodic band-supported `W` gives the driving density `G = W/s` of `IsDriving`.
Route: a smooth cutoff `χ` (`ContDiffBump`) equal to `1` on the band `[s₀, b]` (with `b > s₁`
chosen so that the band is an interval of positive length) gives `ψ(s) = χ(s)/s`, smooth with
compact support, and `W p i / p.1 = ψ p.1 * W p i` for every `p`.  Leibniz (`norm_iteratedFDeriv_mul_le`)
then bounds the derivatives of `G` by those of `ψ ∘ fst` and of `W`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `s ↦ χ(s)/s` is smooth when `χ` is smooth and vanishes on `(-∞, a)` with `a > 0`. -/
theorem driving_psi_contDiff {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {a : ℝ} (ha : 0 < a)
    (hz : ∀ x, x < a → χ x = 0) : ContDiff ℝ ∞ (fun s => χ s * s⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < a
  · have hev : (fun s => χ s * s⁻¹) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with s hs
      simp [hz s hs]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hx0 : x ≠ 0 := by
      intro h
      apply hx
      rw [h]
      exact ha
    exact (hχ.contDiffAt).mul (contDiffAt_inv ℝ hx0)

/-- Bounded derivatives of `ψ ∘ fst` for a smooth compactly supported `ψ`. -/
theorem driving_comp_fst_bound {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (i : ℕ) : ∃ C : ℝ, ∀ p : Chart, ‖iteratedFDeriv ℝ i (fun p : Chart => ψ p.1) p‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hψ.continuous_iteratedFDeriv (m := i) (by simp)).bounded_above_of_compact_support
    (hc.iteratedFDeriv i)
  refine ⟨|C|, fun p => ?_⟩
  have hcomp : (fun p : Chart => ψ p.1) = ψ ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hψ p (i := i) (by simp)]
  have hA := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ i ψ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) p))
    (fun _ : Fin i => (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)))
  have hn : ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_fst_le _ _ _
  have hprod : ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hn)
  have hCA : ‖iteratedFDeriv ℝ i ψ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) p)‖ ≤ C := hC _
  calc _ ≤ ‖iteratedFDeriv ℝ i ψ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) p)‖ *
        ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ := hA
    _ ≤ ‖iteratedFDeriv ℝ i ψ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) p)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ |C| := by
        rw [mul_one]
        exact hCA.trans (le_abs_self C)

/-- The driving class of `W/s` (task leaf). -/
theorem drivingOfSmooth : DrivingOfSmooth := by
  intro c W hW hper hband hWb
  obtain ⟨s0, s1, hs0, hbW⟩ := hband
  choose CW hCW using hWb
  set b : ℝ := max s1 s0 + 1 with hb
  have hsb1 : s1 ≤ b := by linarith [le_max_left s1 s0]
  have hsb0 : s0 < b := by linarith [le_max_right s1 s0]
  let χ : ContDiffBump ((s0 + b) / 2) :=
    { rIn := (b - s0) / 2
      rOut := (2 * b - s0) / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hχs : ContDiff ℝ ∞ (⇑χ) := χ.contDiff
  have hχc : HasCompactSupport (⇑χ) := χ.hasCompactSupport
  have hχ1 : ∀ x, x ∈ Icc s0 b → χ x = 1 := by
    intro x hx
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    show -((b - s0) / 2) ≤ x - (s0 + b) / 2 ∧ x - (s0 + b) / 2 ≤ (b - s0) / 2
    constructor <;> linarith [hx.1, hx.2]
  have hχ0 : ∀ x, x < 3 * s0 / 4 → χ x = 0 := by
    intro x hx
    apply χ.zero_of_le_dist
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
    show (2 * b - s0) / 4 ≤ (s0 + b) / 2 - x
    linarith
  have hψs : ContDiff ℝ ∞ (fun s => χ s * s⁻¹) :=
    driving_psi_contDiff hχs (by linarith) hχ0
  have hψc : HasCompactSupport (fun s => χ s * s⁻¹) := hχc.mul_right
  have hG : ∀ (p : Chart) (i : Fin 2), W p i / p.1 = (χ p.1 * p.1⁻¹) * W p i := by
    intro p i
    by_cases h0 : W p i = 0
    · simp [h0]
    · have hWp : W p ≠ 0 := fun h => h0 (by simp [h])
      have h := hbW p hWp
      have hmem : p.1 ∈ Icc s0 b := ⟨h.1, h.2.trans hsb1⟩
      rw [hχ1 p.1 hmem]
      ring
  have hfun : ∀ i : Fin 2, (fun p : Chart => W p i / p.1) =
      fun p => (χ p.1 * p.1⁻¹) * W p i := fun i => funext fun p => hG p i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    show ContDiff ℝ ∞ (fun p : Chart => W p i / p.1)
    rw [hfun i]
    exact (hψs.comp contDiff_fst).mul (hW i)
  · intro s q η
    funext i
    show W (s, (q + c, η)) i / s = W (s, (q, η)) i / s
    rw [hper s q η]
  · refine ⟨s0, s1, hs0, ?_⟩
    intro p hp
    apply hbW p
    intro h0
    apply hp
    funext i
    simp [h0]
  · intro i n
    show ∃ C : ℝ, ∀ p : Chart, ‖iteratedFDeriv ℝ n (fun p : Chart => W p i / p.1) p‖ ≤ C
    rw [hfun i]
    choose Cψ hCψ using fun j : ℕ => driving_comp_fst_bound hψs hψc j
    refine ⟨∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * |Cψ j| * |CW i (n - j)|, fun p => ?_⟩
    have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun p : Chart => χ p.1 * p.1⁻¹)
      (g := fun p : Chart => W p i) ((hψs.comp contDiff_fst)) (hW i) p (n := n) (by simp)
    refine le_trans hL ?_
    apply Finset.sum_le_sum
    intro j _
    have h1 : ‖iteratedFDeriv ℝ j (fun p : Chart => χ p.1 * p.1⁻¹) p‖ ≤ |Cψ j| :=
      (hCψ j p).trans (le_abs_self _)
    have h2 : ‖iteratedFDeriv ℝ (n - j) (fun p : Chart => W p i) p‖ ≤ |CW i (n - j)| :=
      (hCW i (n - j) p).trans (le_abs_self _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
      (by positivity)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
