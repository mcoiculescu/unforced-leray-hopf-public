import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_7

/-!
# Part II-a, task `PartII-a:N02/4/4/7/4`: one-mode moments on the strip (`NzFpOneModeInt`)

For `g` with `NzDecay1 g` (band `s ∈ [s0, s1]`, `s0 > 0`, and `g`, `∂_s g` bounded by
`C e^{-κ|η|}`), and `α, j ∈ {0, 1}`, the function `(|η|^j)² ‖(nzS2^[α] g)(s,η)‖² s^{-3/2}` is
integrable on `(0,∞) × ℝ`.

Route: outside the band `s ∈ [s0, s1]` the coefficient `nzS2^[α] g` vanishes (`g` vanishes on the open
half-planes `s < s0` and `s > s1`, so its `s`-derivative does too). On the band the integrand is
dominated by `1_{[s0,s1]}(s) · K (1+|η|)² e^{-2κ|η|}`, whose integrability is the 1D lemma
`UnforcedLeray.B0172.integrable_one_add_abs_pow_mul_exp` times a constant, and the product with
the indicator in `s` (`Integrable.mul_prod`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- `x ↦ e^{-κ|x|}` is integrable on `ℝ` (two half-line exponentials). -/
lemma nzfpOM_exp_abs_int {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun η : ℝ => Real.exp (-κ * |η|)) := by
  have h1 : IntegrableOn (fun η : ℝ => Real.exp (-κ * η)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have h2 : IntegrableOn (fun η : ℝ => Real.exp (κ * η)) (Iic 0) :=
    integrableOn_exp_mul_Iic hκ 0
  have e1 : IntegrableOn (fun η : ℝ => Real.exp (-κ * |η|)) (Ioi 0) :=
    h1.congr_fun (fun η hη => by
      show Real.exp (-κ * η) = Real.exp (-κ * |η|)
      rw [abs_of_pos hη]) measurableSet_Ioi
  have e2 : IntegrableOn (fun η : ℝ => Real.exp (-κ * |η|)) (Iic 0) :=
    h2.congr_fun (fun η hη => by
      show Real.exp (κ * η) = Real.exp (-κ * |η|)
      rw [abs_of_nonpos hη]
      congr 1
      ring) measurableSet_Iic
  have e := e2.union e1
  rw [Set.Iic_union_Ioi] at e
  exact integrableOn_univ.mp e

/-- `(1+|η|)² e^{-2κ|η|}` is integrable on `ℝ`: it is dominated by `(2 + 4/κ²) e^{-κ|η|}`. -/
lemma nzfpOM_poly_int {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun η : ℝ => (1 + |η|) ^ 2 * Real.exp (-(2 * κ * |η|))) := by
  refine Integrable.mono' ((nzfpOM_exp_abs_int hκ).const_mul (2 + 4 / κ ^ 2)) ?_ ?_
  · exact (by fun_prop : Continuous fun η : ℝ =>
      (1 + |η|) ^ 2 * Real.exp (-(2 * κ * |η|))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun η => ?_
    show ‖(1 + |η|) ^ 2 * Real.exp (-(2 * κ * |η|))‖ ≤ (2 + 4 / κ ^ 2) * Real.exp (-κ * |η|)
    have ht : 0 ≤ |η| := abs_nonneg η
    have hnn : 0 ≤ (1 + |η|) ^ 2 * Real.exp (-(2 * κ * |η|)) := by positivity
    rw [Real.norm_of_nonneg hnn]
    have h2 := Real.pow_div_factorial_le_exp (κ * |η|) (mul_nonneg hκ.le ht) 2
    have hk2 : 0 < κ ^ 2 := by positivity
    have h2' : κ ^ 2 * |η| ^ 2 ≤ 2 * Real.exp (κ * |η|) := by
      norm_num [Nat.factorial] at h2
      nlinarith [h2]
    have hA : 2 * |η| ^ 2 ≤ 4 / κ ^ 2 * Real.exp (κ * |η|) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hk2]
      nlinarith [h2']
    have hB : (2 : ℝ) ≤ 2 * Real.exp (κ * |η|) := by
      linarith [Real.one_le_exp (mul_nonneg hκ.le ht)]
    have hsq : (1 + |η|) ^ 2 ≤ 2 + 2 * |η| ^ 2 := by nlinarith [sq_nonneg (|η| - 1)]
    have hsplit : (2 + 4 / κ ^ 2) * Real.exp (κ * |η|) =
        2 * Real.exp (κ * |η|) + 4 / κ ^ 2 * Real.exp (κ * |η|) := by ring
    have hpoly : (1 + |η|) ^ 2 ≤ (2 + 4 / κ ^ 2) * Real.exp (κ * |η|) := by
      rw [hsplit]
      linarith [hA, hB, hsq]
    calc (1 + |η|) ^ 2 * Real.exp (-(2 * κ * |η|))
        ≤ (2 + 4 / κ ^ 2) * Real.exp (κ * |η|) * Real.exp (-(2 * κ * |η|)) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
      _ = (2 + 4 / κ ^ 2) * Real.exp (-κ * |η|) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- Outside the band the one-mode coefficient vanishes (`α ∈ {0,1}`). -/
lemma nzfpOM_zero_out {g : ℝ × ℝ → ℂ} {s0 s1 : ℝ}
    (hsupp : ∀ x : ℝ × ℝ, g x ≠ 0 → x.1 ∈ Icc s0 s1) {α : ℕ} (hα : α = 0 ∨ α = 1)
    (x : ℝ × ℝ) (hin : x.1 ∉ Icc s0 s1) : (nzS2^[α] g) x = 0 := by
  rcases hα with rfl | rfl
  · show g x = 0
    by_contra hne
    exact hin (hsupp x hne)
  · have hcase : x.1 < s0 ∨ s1 < x.1 := by
      by_contra h
      push_neg at h
      exact hin ⟨h.1, h.2⟩
    have hfd : fderiv ℝ g x = 0 := by
      rcases hcase with h | h
      · have hev : g =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
          filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds h] with y hy
          by_contra hne
          exact (not_le.mpr hy) (hsupp y hne).1
        rw [hev.fderiv_eq]
        simp
      · have hev : g =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
          filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds h] with y hy
          by_contra hne
          exact (not_le.mpr hy) (hsupp y hne).2
        rw [hev.fderiv_eq]
        simp
    show x.1 • fderiv ℝ g x (1, 0) = 0
    rw [hfd]
    simp

/-- On the band the one-mode coefficient is dominated by `(max 1 s1 · |C|) e^{-κ|η|}`. -/
lemma nzfpOM_decay_strip {g : ℝ × ℝ → ℂ} {s0 s1 κ C : ℝ} (hs0 : 0 < s0)
    (hbd : ∀ x : ℝ × ℝ, ‖g x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ g x (1, 0)‖ ≤ C * Real.exp (-κ * |x.2|))
    {α : ℕ} (hα : α = 0 ∨ α = 1) (x : ℝ × ℝ) (hin : x.1 ∈ Icc s0 s1) :
    ‖(nzS2^[α] g) x‖ ≤ (max 1 s1 * |C|) * Real.exp (-κ * |x.2|) := by
  have hE : 0 ≤ Real.exp (-κ * |x.2|) := Real.exp_nonneg _
  rcases hα with rfl | rfl
  · show ‖g x‖ ≤ _
    calc ‖g x‖ ≤ C * Real.exp (-κ * |x.2|) := (hbd x).1
      _ ≤ |C| * Real.exp (-κ * |x.2|) := mul_le_mul_of_nonneg_right (le_abs_self C) hE
      _ ≤ (max 1 s1 * |C|) * Real.exp (-κ * |x.2|) := by
        apply mul_le_mul_of_nonneg_right _ hE
        exact le_mul_of_one_le_left (abs_nonneg C) (le_max_left 1 s1)
  · show ‖x.1 • fderiv ℝ g x (1, 0)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    have hx1 : |x.1| ≤ max 1 s1 := by
      rw [abs_of_pos (lt_of_lt_of_le hs0 hin.1)]
      exact hin.2.trans (le_max_right _ _)
    have hfd : ‖fderiv ℝ g x (1, 0)‖ ≤ |C| * Real.exp (-κ * |x.2|) :=
      (hbd x).2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hE)
    calc |x.1| * ‖fderiv ℝ g x (1, 0)‖ ≤ max 1 s1 * (|C| * Real.exp (-κ * |x.2|)) :=
          mul_le_mul hx1 hfd (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _))
      _ = (max 1 s1 * |C|) * Real.exp (-κ * |x.2|) := by ring

/-- Measurability of the integrand. -/
lemma nzfpOM_meas {g : ℝ × ℝ → ℂ} (hgc : ContDiff ℝ ∞ g) {α : ℕ} (hα : α = 0 ∨ α = 1) (j : ℕ) :
    Measurable (fun x : ℝ × ℝ => (|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) := by
  have hNc : Continuous (nzS2^[α] g) := by
    rcases hα with rfl | rfl
    · exact hgc.continuous
    · show Continuous (fun x : ℝ × ℝ => x.1 • fderiv ℝ g x (1, 0))
      exact continuous_fst.smul
        ((hgc.continuous_fderiv (by simp)).clm_apply continuous_const)
  have h1 : Measurable (fun x : ℝ × ℝ => |x.2|) := (continuous_abs.comp continuous_snd).measurable
  have h2 : Measurable (fun x : ℝ × ℝ => ‖(nzS2^[α] g) x‖) := hNc.norm.measurable
  have h3 : Measurable (fun x : ℝ × ℝ => x.1 ^ (-(3 / 2 : ℝ))) := measurable_fst.pow_const _
  exact (((h1.pow_const j).pow_const 2).mul (h2.pow_const 2)).mul h3

theorem nzFpOneModeInt : NzFpOneModeInt := by
  intro g hg α hα j hj
  unfold NzDecay1 at hg
  obtain ⟨hgc, ⟨s0, s1, hs0, hsupp⟩, κ, C, hκ, hbd⟩ := hg
  have hαc : α = 0 ∨ α = 1 := by
    simp only [Finset.mem_range] at hα
    omega
  have hjc : j = 0 ∨ j = 1 := by
    simp only [Finset.mem_range] at hj
    omega
  set K : ℝ := (max 1 s1 * |C|) ^ 2 * s0 ^ (-(3 / 2 : ℝ)) with hKdef
  have hψ : Integrable (fun η : ℝ => K * ((1 + |η|) ^ 2 * Real.exp (-(2 * κ * |η|)))) :=
    (nzfpOM_poly_int hκ).const_mul K
  have hB : Integrable (fun x : ℝ × ℝ =>
      (Icc s0 s1).indicator (fun _ => (1 : ℝ)) x.1 *
        (K * ((1 + |x.2|) ^ 2 * Real.exp (-(2 * κ * |x.2|)))))
      (volume : Measure (ℝ × ℝ)) :=
    Integrable.mul_prod ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)) hψ
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ univ)),
      ‖(|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))‖ ≤
        (Icc s0 s1).indicator (fun _ => (1 : ℝ)) x.1 *
          (K * ((1 + |x.2|) ^ 2 * Real.exp (-(2 * κ * |x.2|)))) := by
    refine (ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)).mpr
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx1 : 0 < x.1 := hx.1
    have hnn : 0 ≤ (|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
      positivity
    rw [Real.norm_of_nonneg hnn]
    by_cases hin : x.1 ∈ Icc s0 s1
    · rw [Set.indicator_of_mem hin, one_mul]
      have e1 : (|x.2| ^ j) ^ 2 ≤ (1 + |x.2|) ^ 2 := by
        rcases hjc with rfl | rfl
        · simp only [pow_zero, one_pow]
          nlinarith [abs_nonneg x.2]
        · simp only [pow_one]
          nlinarith [abs_nonneg x.2]
      have e2 : ‖(nzS2^[α] g) x‖ ^ 2 ≤
          ((max 1 s1 * |C|) * Real.exp (-κ * |x.2|)) ^ 2 := by
        have := nzfpOM_decay_strip (κ := κ) (C := C) hs0 hbd hαc x hin
        gcongr
      have e3 : x.1 ^ (-(3 / 2 : ℝ)) ≤ s0 ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hs0 hin.1 (by norm_num)
      have hexp : (Real.exp (-κ * |x.2|)) ^ 2 = Real.exp (-(2 * κ * |x.2|)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      calc (|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))
          ≤ (1 + |x.2|) ^ 2 * ((max 1 s1 * |C|) * Real.exp (-κ * |x.2|)) ^ 2 *
              s0 ^ (-(3 / 2 : ℝ)) := by
            apply mul_le_mul (mul_le_mul e1 e2 (by positivity) (by positivity)) e3
              (by positivity) (by positivity)
        _ = K * ((1 + |x.2|) ^ 2 * Real.exp (-(2 * κ * |x.2|))) := by
            rw [mul_pow, hexp, hKdef]
            ring
    · have hN0 : (nzS2^[α] g) x = 0 := nzfpOM_zero_out hsupp hαc x hin
      simp [hN0, hin]
  have hmeas := nzfpOM_meas hgc hαc j
  exact Integrable.mono' (hB.mono_measure Measure.restrict_le_self) hmeas.aestronglyMeasurable hbound

end UnforcedLeray.Short.PartIIa
