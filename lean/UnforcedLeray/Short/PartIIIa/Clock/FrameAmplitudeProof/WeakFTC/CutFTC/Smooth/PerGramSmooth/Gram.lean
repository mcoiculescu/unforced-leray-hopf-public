import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PerGramSmooth.Tower

/-!
# The derivative tower of the Gram entries (helper for `PartIII-a:T21/c5/1/1/2/1`)

`G_m(d) = Σ_k (-k)^m T_{∂₁^m L}(k d)` satisfies `G_m' = G_{m+1}` on `d > 1/2`
(`hasDerivAt_gramG`), so `G_0` is `C^∞` there (`contDiffOn_of_hasDerivAt_tower`).
Source `the November 2 reference manuscript`
lines 2891-2905.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.LamJetInf

/-- A function with a derivative tower `G_m' = G_{m+1}` on an open set is `C^∞` there. -/
theorem contDiffOn_of_hasDerivAt_tower {U : Set ℝ} (hU : IsOpen U) (G : ℕ → ℝ → ℂ)
    (hG : ∀ m : ℕ, ∀ x ∈ U, HasDerivAt (G m) (G (m + 1) x) x) :
    ContDiffOn ℝ ∞ (G 0) U := by
  have key : ∀ n : ℕ, ∀ m : ℕ, ContDiffOn ℝ n (G m) U := by
    intro n
    induction n with
    | zero =>
      intro m
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun x hx => (hG m x hx).continuousAt.continuousWithinAt
    | succ n ih =>
      intro m
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun x hx => (hG m x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih (m + 1)).congr fun x hx => (hG m x hx).deriv
  exact contDiffOn_infty.2 fun n => key n 0

/-- The `m`-th tower term `(-k)^m T_{∂₁^m L}(k d)`. -/
def gramTermM (e L : ℝ × ℝ → ℂ) (m : ℕ) (k : ℤ) (d : ℝ) : ℂ :=
  (((-(k : ℝ)) ^ m : ℝ) : ℂ) * crossT e (d1^[m] L) ((k : ℝ) * d)

/-- The `m`-th tower function `G_m(d) = Σ_k (-k)^m T_{∂₁^m L}(k d)`. -/
def gramG (e L : ℝ × ℝ → ℂ) (m : ℕ) (d : ℝ) : ℂ := ∑' k : ℤ, gramTermM e L m k d

section

variable {e : ℝ × ℝ → ℂ} (he : Continuous e) {Ce : ℝ}
    (hCe : ∀ z : ℝ × ℝ, ‖e z‖ ≤ Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8))
    {L : ℝ × ℝ → ℂ} (hL : Good L)
include he hCe hL

theorem hasDerivAt_gramTermM (m : ℕ) (k : ℤ) (d : ℝ) :
    HasDerivAt (gramTermM e L m k) (gramTermM e L (m + 1) k d) d := by
  have hT := hasDerivAt_crossT he hCe (good_iterate_d1 hL m) ((k : ℝ) * d)
  have hin : HasDerivAt (fun d : ℝ => (k : ℝ) * d) (k : ℝ) d := by
    simpa using (hasDerivAt_id d).const_mul (k : ℝ)
  have hc := hT.scomp d hin
  have h := hc.const_mul ((((-(k : ℝ)) ^ m : ℝ) : ℂ))
  have hfun : gramTermM e L m k =
      fun d => (((-(k : ℝ)) ^ m : ℝ) : ℂ) * (crossT e (d1^[m] L) ∘ fun d => (k : ℝ) * d) d := by
    funext d; rfl
  have hval : gramTermM e L (m + 1) k d = (((-(k : ℝ)) ^ m : ℝ) : ℂ) *
      ((k : ℝ) • -crossT e (d1 (d1^[m] L)) ((k : ℝ) * d)) := by
    unfold gramTermM
    rw [Function.iterate_succ_apply', Complex.real_smul]
    push_cast
    ring
  rw [hfun, hval]
  exact h

theorem gramTermM_bound (m : ℕ) : ∃ K : ℝ, ∀ (k : ℤ) (d : ℝ), 1 / 2 < d →
    ‖gramTermM e L m k d‖ ≤ K * ((1 + |(k : ℝ)|) ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := good_iterate_d1_norm_le hL m
  obtain ⟨K, hK0, hK⟩ := crossT_decay he hCe (good_iterate_d1 hL m).1.continuous hC
  refine ⟨K * 2 ^ (m + 2), fun k d hd => ?_⟩
  have hd0 : 0 < d := by linarith
  set t : ℝ := |(k : ℝ)| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hkd : |(k : ℝ) * d| = t * d := by rw [abs_mul, abs_of_pos hd0]
  have hpos1 : 0 < (1 + t * d) ^ (m + 2) := by positivity
  have hpos2 : 0 < (1 + t) ^ 2 := by positivity
  have key : t ^ m * ((1 + t * d) ^ (m + 2))⁻¹ ≤ 2 ^ (m + 2) * ((1 + t) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hpos1 hpos2]
    have h1 : 1 + t ≤ 2 * (1 + t * d) := by nlinarith
    calc t ^ m * (1 + t) ^ 2 ≤ (1 + t) ^ m * (1 + t) ^ 2 := by
          gcongr; linarith
      _ = (1 + t) ^ (m + 2) := by ring
      _ ≤ (2 * (1 + t * d)) ^ (m + 2) := pow_le_pow_left₀ (by positivity) h1 _
      _ = 2 ^ (m + 2) * (1 + t * d) ^ (m + 2) := by rw [mul_pow]
  have hT := hK ((k : ℝ) * d)
  rw [hkd] at hT
  rw [gramTermM, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg, ← ht]
  calc t ^ m * ‖crossT e (d1^[m] L) ((k : ℝ) * d)‖
      ≤ t ^ m * (K * ((1 + t * d) ^ (m + 2))⁻¹) := by gcongr
    _ = K * (t ^ m * ((1 + t * d) ^ (m + 2))⁻¹) := by ring
    _ ≤ K * (2 ^ (m + 2) * ((1 + t) ^ 2)⁻¹) := by gcongr
    _ = K * 2 ^ (m + 2) * ((1 + t) ^ 2)⁻¹ := by ring

theorem hasDerivAt_gramG (m : ℕ) {d : ℝ} (hd : 1 / 2 < d) :
    HasDerivAt (gramG e L m) (gramG e L (m + 1) d) d := by
  obtain ⟨K, hK⟩ := gramTermM_bound he hCe hL (m + 1)
  obtain ⟨K₀, hK₀⟩ := gramTermM_bound he hCe hL m
  have hs : Summable (fun k : ℤ => ((1 + |(k : ℝ)|) ^ 2)⁻¹) :=
    (summable_inv_sq_shift one_ne_zero 0).congr fun k => by simp
  have hg0 : Summable (fun k : ℤ => gramTermM e L m k 1) :=
    Summable.of_norm_bounded (hs.mul_left K₀) fun k => hK₀ k 1 (by norm_num)
  exact hasDerivAt_tsum_of_isPreconnected (hs.mul_left K) isOpen_Ioi isPreconnected_Ioi
    (fun k y _ => hasDerivAt_gramTermM he hCe hL m k y) (fun k y hy => hK k y hy)
    (show (1 : ℝ) ∈ Ioi (1 / 2) by norm_num) hg0 hd

/-- `G_0 = Σ_k T_L(k ·)` is `C^∞` on `d > 1/2`. -/
theorem contDiffOn_gramG_zero : ContDiffOn ℝ ∞ (gramG e L 0) (Ioi (1 / 2)) :=
  contDiffOn_of_hasDerivAt_tower isOpen_Ioi (gramG e L)
    fun m _ hx => hasDerivAt_gramG he hCe hL m hx

end

end UnforcedLeray.Short.IIIa.LamJetInf
