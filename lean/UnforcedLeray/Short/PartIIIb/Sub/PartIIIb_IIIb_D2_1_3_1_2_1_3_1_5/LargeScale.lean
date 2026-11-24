import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.CurlHelpers

/-!
# Large-scale decay of the smoothed pairing (IIIb-D2 1.3.1.2.1.3.1.5)

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480: `⟪Θ * b_{(s)}, h⟫ → 0` as `s → ∞` for `h ∈ Y_2`.

Estimate (per `s ≥ 1`, all constants independent of `s`):
`|Θ * b_{(s)}| ≤ s⁻³ C₀` pointwise (sup of the kernel times `L¹` of `Θ`), supported in
`‖y‖ ≤ R + s Rb`; the `L²` norm of `h` on that ball is controlled by Cauchy–Schwarz-free
AM–GM with weight `s`, which gives `|⟪Θ * b_{(s)}, h⟫| ≤ C s⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)
open Metric

/-- Bilinear product bound on `ℂ³`. -/
theorem ls_dotL_norm_le (a b : CVec3) : ‖dotL a b‖ ≤ 3 * ‖a‖ * ‖b‖ := by
  rw [dotL_apply]
  calc ‖∑ i : Fin 3, a i * b i‖ ≤ ∑ i : Fin 3, ‖a i * b i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖a‖ * ‖b‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul (PiLp.norm_apply_le a i) (PiLp.norm_apply_le b i) (norm_nonneg _)
          (norm_nonneg _)
    _ = 3 * ‖a‖ * ‖b‖ := by simp; ring

/-- Volume of a closed ball of radius `r ≥ 0` in `ℝ³`. -/
theorem ls_vol_closedBall (r : ℝ) (hr : 0 ≤ r) :
    volume (closedBall (0 : Space) r) = ENNReal.ofReal (r ^ 3) * volume (closedBall (0 : Space) 1) := by
  rw [Measure.addHaar_closedBall' (volume : Measure Space) (0 : Space) hr]
  have hf : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  rw [hf]

/-- Scalar AM–GM in `ℝ≥0∞`. -/
theorem ls_amgm_enn (a : ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    2 * a ≤ ENNReal.ofReal s⁻¹ + ENNReal.ofReal s * a ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · have hpos : ENNReal.ofReal s ≠ 0 := by simpa using hs
    simp [ENNReal.mul_top hpos]
  · set x := a.toReal with hx
    have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
    have ha' : a = ENNReal.ofReal x := (ENNReal.ofReal_toReal ha).symm
    have key : 2 * x ≤ s⁻¹ + s * x ^ 2 := by
      have h1 : s⁻¹ + s * x ^ 2 - 2 * x = (s * x - 1) ^ 2 / s := by
        field_simp
        ring
      have h2 : 0 ≤ (s * x - 1) ^ 2 / s := by positivity
      linarith
    rw [ha']
    calc 2 * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (s⁻¹ + s * x ^ 2) := ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal s⁻¹ + ENNReal.ofReal s * ENNReal.ofReal x ^ 2 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hs.le,
            ENNReal.ofReal_pow hx0]

/-- Integrated AM–GM over a measurable set. -/
theorem ls_amgm_lint (g : Space → ℝ≥0∞) {B : Set Space} (hB : MeasurableSet B) {s : ℝ}
    (hs : 0 < s) :
    2 * ∫⁻ y, B.indicator g y ≤
      ENNReal.ofReal s⁻¹ * volume B + ENNReal.ofReal s * ∫⁻ y, g y ^ 2 := by
  have hpt : ∀ y, 2 * B.indicator g y ≤
      B.indicator (fun _ => ENNReal.ofReal s⁻¹) y + ENNReal.ofReal s * g y ^ 2 := by
    intro y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy, indicator_of_mem hy]
      exact ls_amgm_enn (g y) hs
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero, zero_add]
      exact zero_le
  calc 2 * ∫⁻ y, B.indicator g y = ∫⁻ y, 2 * B.indicator g y :=
        (lintegral_const_mul' _ _ (by norm_num)).symm
    _ ≤ ∫⁻ y, (B.indicator (fun _ => ENNReal.ofReal s⁻¹) y + ENNReal.ofReal s * g y ^ 2) :=
        lintegral_mono hpt
    _ = (∫⁻ y, B.indicator (fun _ => ENNReal.ofReal s⁻¹) y) + ∫⁻ y, ENNReal.ofReal s * g y ^ 2 :=
        lintegral_add_left (measurable_const.indicator hB) _
    _ = ENNReal.ofReal s⁻¹ * volume B + ENNReal.ofReal s * ∫⁻ y, g y ^ 2 := by
        rw [lintegral_indicator_const hB, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]


/-- A continuous phase test is bounded on `[0,P] × ball(R)`, and vanishes beyond it. -/
theorem ls_theta_bound {P : ℝ} (Θ : ℝ × Space → CVec3) (hΘ : IsPhaseTest P Θ) (R : ℝ)
    (hR : ∀ τ y, R < ‖y‖ → Θ (τ, y) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) P, ∀ y : Space, ‖Θ (t, y)‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)).exists_bound_of_continuousOn
    hΘ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht y => ?_⟩
  by_cases hy : ‖y‖ ≤ R
  · exact le_max_of_le_left (hC (t, y) ⟨ht, by simpa [mem_closedBall, dist_zero_right] using hy⟩)
  · rw [hR t y (not_le.1 hy), norm_zero]
    exact le_max_right _ _

/-- A compactly supported function vanishes outside some ball. -/
theorem ls_kernel_support (b : Space → ℝ) (hb : HasCompactSupport b) :
    ∃ Rb : ℝ, 0 ≤ Rb ∧ ∀ z : Space, Rb < ‖z‖ → b z = 0 := by
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : Space)).1 hb.isCompact.isBounded
  refine ⟨max r 0, le_max_right _ _, fun z hz => ?_⟩
  by_contra hne
  have h1 : z ∈ tsupport b := subset_tsupport b (Function.mem_support.2 hne)
  have h2 := hr h1
  rw [mem_closedBall, dist_zero_right] at h2
  linarith [le_max_left r 0]

/-- The convolution in `y` of a bounded kernel with a continuous phase test. -/
theorem ls_convY_bound (b : Space → ℝ) (Θ : ℝ × Space → CVec3) (R Bb M s : ℝ) (hs : 0 < s)
    (hBb : ∀ z, ‖b z‖ ≤ Bb) (hBb0 : 0 ≤ Bb) (hM0 : 0 ≤ M) (t : ℝ)
    (htM : ∀ y : Space, ‖Θ (t, y)‖ ≤ M) (hR : ∀ τ y, R < ‖y‖ → Θ (τ, y) = 0) (y : Space) :
    ‖convY (dilK b s) Θ (t, y)‖ ≤ (s⁻¹) ^ 3 * Bb * M * (volume (closedBall (0 : Space) R)).toReal := by
  have hs3 : 0 ≤ (s⁻¹) ^ 3 := by positivity
  have hg : ∀ z : Space, ‖((dilK b s z : ℝ) : ℂ) • Θ (t, y - z)‖ ≤
      (closedBall y R).indicator (fun _ => (s⁻¹) ^ 3 * Bb * M) z := by
    intro z
    have hκ : ‖dilK b s z‖ ≤ (s⁻¹) ^ 3 * Bb := by
      unfold dilK
      rw [norm_mul, Real.norm_of_nonneg hs3]
      exact mul_le_mul_of_nonneg_left (hBb _) hs3
    rw [norm_smul, Complex.norm_real]
    by_cases hz : z ∈ closedBall y R
    · rw [indicator_of_mem hz]
      exact mul_le_mul hκ (htM _) (norm_nonneg _) (by positivity)
    · rw [indicator_of_notMem hz]
      have hyz : R < ‖y - z‖ := by
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        rwa [norm_sub_rev] at hz
      rw [hR t (y - z) hyz, norm_zero, mul_zero]
  have hint : Integrable ((closedBall y R).indicator (fun _ => (s⁻¹) ^ 3 * Bb * M)) := by
    apply (integrable_indicator_iff measurableSet_closedBall).2
    exact integrableOn_const measure_closedBall_lt_top.ne
  calc ‖convY (dilK b s) Θ (t, y)‖
      = ‖∫ z, ((dilK b s z : ℝ) : ℂ) • Θ (t, y - z)‖ := rfl
    _ ≤ ∫ z, (closedBall y R).indicator (fun _ => (s⁻¹) ^ 3 * Bb * M) z :=
        norm_integral_le_of_norm_le hint (ae_of_all _ hg)
    _ = (volume (closedBall y R)).toReal * ((s⁻¹) ^ 3 * Bb * M) := by
        rw [integral_indicator_const _ measurableSet_closedBall]
        simp [smul_eq_mul, Measure.real]
    _ = (s⁻¹) ^ 3 * Bb * M * (volume (closedBall (0 : Space) R)).toReal := by
        rw [Measure.addHaar_closedBall_center]
        ring

/-- The convolution vanishes outside the ball of radius `R + s Rb`. -/
theorem ls_convY_zero (b : Space → ℝ) (Θ : ℝ × Space → CVec3) (R Rb s : ℝ) (hs : 0 < s)
    (hRb : ∀ z : Space, Rb < ‖z‖ → b z = 0) (hR : ∀ τ y, R < ‖y‖ → Θ (τ, y) = 0)
    (t : ℝ) (y : Space) (hy : R + s * Rb < ‖y‖) : convY (dilK b s) Θ (t, y) = 0 := by
  unfold convY
  have hz0 : ∀ z : Space, ((dilK b s z : ℝ) : ℂ) • Θ (t, y - z) = 0 := by
    intro z
    by_cases hz : ‖z‖ ≤ s * Rb
    · have hyz : R < ‖y - z‖ := by
        linarith [norm_sub_norm_le y z]
      rw [hR t (y - z) hyz, smul_zero]
    · have hzb : Rb < ‖s⁻¹ • z‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
        have h2 : s⁻¹ * (s * Rb) < s⁻¹ * ‖z‖ :=
          mul_lt_mul_of_pos_left (not_le.1 hz) (inv_pos.2 hs)
        have h3 : s⁻¹ * (s * Rb) = Rb := by field_simp
        linarith
      have hk : dilK b s z = 0 := by
        unfold dilK
        rw [hRb _ hzb, mul_zero]
      rw [hk]
      simp
  simp [hz0]


/-- `h ∈ Y_2` gives finiteness of the iterated `L²` integral over one period. -/
theorem ls_H_finite (P : ℝ) (hP : 0 < P) (h : ℝ × Space → CVec3)
    (hh : UnforcedLeray.Short.IIb.IsInYr P 2 h) :
    (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖h (t, y)‖ₑ ^ 2) < ⊤ := by
  have hfin := hh.finite
  unfold UnforcedLeray.Short.IIb.phaseLpNorm at hfin
  have hXt : ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖h (t, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
    by_contra hc
    push_neg at hc
    rw [top_le_iff.1 hc, ENNReal.top_rpow_of_pos (by norm_num)] at hfin
    exact lt_irrefl _ hfin
  have hI : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖h (t, y)‖ₑ ^ (2 : ℝ)) < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.1 hXt with h1 | h1 | h1
    · exact h1.2
    · exfalso
      rw [ENNReal.ofReal_eq_zero] at h1
      exact absurd h1 (not_le.2 (inv_pos.2 hP))
    · rw [h1]
      exact ENNReal.zero_lt_top
  simpa only [ENNReal.rpow_two] using hI

/-- Exact product of three nonnegative reals as `ENNReal` (helper for constants). -/
theorem ls_ofReal_mul3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c = ENNReal.ofReal (a * b * c) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)]


end UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray Metric
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)
open UnforcedLeray.Short.PartIIIb.Concrete

/-- Large-scale decay of the smoothed pairing, for `h ∈ Y_2` and a phase test `Θ`. -/
theorem largeScale : UnforcedLeray.Short.PartIIIb.Concrete.LargeScale := by
  intro P hP h hh b hb Θ hΘ
  obtain ⟨R0, hR0⟩ := hΘ.bounded_support
  set R : ℝ := max R0 0 with hRdef
  have hR : ∀ τ y, R < ‖y‖ → Θ (τ, y) = 0 :=
    fun τ y hy => hR0 τ y (lt_of_le_of_lt (le_max_left _ _) hy)
  have hR0nn : 0 ≤ R := le_max_right _ _
  obtain ⟨M, hM0, hM⟩ := ls_theta_bound (P := P) Θ hΘ R hR
  obtain ⟨Bb0, hBb0⟩ := hb.1.continuous.bounded_above_of_compact_support hb.2
  set Bb : ℝ := max Bb0 0 with hBbdef
  have hBb : ∀ z, ‖b z‖ ≤ Bb := fun z => le_trans (hBb0 z) (le_max_left _ _)
  have hBb0nn : 0 ≤ Bb := le_max_right _ _
  obtain ⟨Rb, hRb0nn, hRb⟩ := ls_kernel_support b hb.2
  have hH := ls_H_finite P hP h hh
  set H : ℝ≥0∞ := ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖h (t, y)‖ₑ ^ 2 with hHdef
  set Hr : ℝ := H.toReal with hHr
  have hHr0 : 0 ≤ Hr := ENNReal.toReal_nonneg
  have hHeq : H = ENNReal.ofReal Hr := (ENNReal.ofReal_toReal hH.ne).symm
  set A : ℝ := (volume (closedBall (0 : Space) 1)).toReal with hAdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hAfin : volume (closedBall (0 : Space) 1) = ENNReal.ofReal A :=
    (ENNReal.ofReal_toReal measure_closedBall_lt_top.ne).symm
  set Vr : ℝ := (volume (closedBall (0 : Space) R)).toReal with hVrdef
  have hVr0 : 0 ≤ Vr := ENNReal.toReal_nonneg
  set C0 : ℝ := Bb * M * Vr with hC0def
  have hC00 : 0 ≤ C0 := mul_nonneg (mul_nonneg hBb0nn hM0) hVr0
  set K : ℝ := R + Rb with hKdef
  have hK0 : 0 ≤ K := add_nonneg hR0nn hRb0nn
  set Q : ℝ := K ^ 3 * A * P + Hr with hQdef
  have hQ0 : 0 ≤ Q := add_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hK0 3) hA0) hP.le) hHr0
  have key : ∀ s : ℝ, 1 ≤ s → ‖pairF P (convY (dilK b s) Θ) h‖ ≤ 3 * P⁻¹ * C0 * Q * s⁻¹ := by
    intro s hs
    have hs0 : 0 < s := by linarith
    have hKs0 : 0 ≤ (s⁻¹) ^ 3 * Bb * M * Vr :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.2 hs0.le) 3) hBb0nn) hM0) hVr0
    have hρ0 : 0 ≤ R + s * Rb := add_nonneg hR0nn (mul_nonneg hs0.le hRb0nn)
    have hρK : R + s * Rb ≤ K * s := by
      have : R * 1 ≤ R * s := mul_le_mul_of_nonneg_left hs hR0nn
      rw [hKdef]
      nlinarith
    set ρ : ℝ := R + s * Rb with hρdef
    set B : Set Space := closedBall (0 : Space) ρ with hBdef
    have hB : MeasurableSet B := measurableSet_closedBall
    have hfpt : ∀ t ∈ Icc (0 : ℝ) P, ∀ y : Space,
        ‖dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖ₑ ≤
          ENNReal.ofReal (3 * ((s⁻¹) ^ 3 * Bb * M * Vr)) * B.indicator (fun y => ‖h (t, y)‖ₑ) y := by
      intro t ht y
      by_cases hy : y ∈ B
      · rw [indicator_of_mem hy]
        have hF := ls_convY_bound b Θ R Bb M s hs0 hBb hBb0nn hM0 t (hM t ht) hR y
        have h1 : ‖dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖ ≤
            3 * ((s⁻¹) ^ 3 * Bb * M * Vr) * ‖h (t, y)‖ := by
          calc ‖dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖
              ≤ 3 * ‖convY (dilK b s) Θ (t, y)‖ * ‖h (t, y)‖ := ls_dotL_norm_le _ _
            _ ≤ 3 * ((s⁻¹) ^ 3 * Bb * M * Vr) * ‖h (t, y)‖ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                exact mul_le_mul_of_nonneg_left hF (by norm_num)
        calc ‖dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖ₑ
            = ENNReal.ofReal ‖dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖ :=
              (ofReal_norm_eq_enorm _).symm
          _ ≤ ENNReal.ofReal (3 * ((s⁻¹) ^ 3 * Bb * M * Vr) * ‖h (t, y)‖) :=
              ENNReal.ofReal_le_ofReal h1
          _ = ENNReal.ofReal (3 * ((s⁻¹) ^ 3 * Bb * M * Vr)) * ‖h (t, y)‖ₑ := by
              rw [ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm]
      · rw [indicator_of_notMem hy]
        have hyR : R + s * Rb < ‖y‖ := by
          have hnot : ¬ ‖y‖ ≤ ρ := fun hle =>
            hy (by simpa [hBdef, mem_closedBall, dist_zero_right] using hle)
          push_neg at hnot
          exact hnot
        rw [ls_convY_zero b Θ R Rb s hs0 hRb hR t y hyR]
        have h0 : dotL (0 : CVec3) (h (t, y)) = 0 := by
          rw [dotL_apply]
          simp
        rw [h0, enorm_zero, mul_zero]
    have hT : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, B.indicator (fun y => ‖h (t, y)‖ₑ) y) ≤
        ENNReal.ofReal (Q * s ^ 2) := by
      have hV : volume B ≤ ENNReal.ofReal ((K * s) ^ 3 * A) := by
        calc volume B = ENNReal.ofReal (ρ ^ 3) * volume (closedBall (0 : Space) 1) :=
              ls_vol_closedBall ρ hρ0
          _ = ENNReal.ofReal (ρ ^ 3) * ENNReal.ofReal A := by rw [hAfin]
          _ ≤ ENNReal.ofReal ((K * s) ^ 3) * ENNReal.ofReal A :=
              by gcongr
          _ = ENNReal.ofReal ((K * s) ^ 3 * A) :=
              (ENNReal.ofReal_mul (by positivity)).symm
      have h2T : 2 * (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, B.indicator (fun y => ‖h (t, y)‖ₑ) y) ≤
          ENNReal.ofReal (Q * s ^ 2) := by
        calc 2 * (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, B.indicator (fun y => ‖h (t, y)‖ₑ) y)
            = ∫⁻ t in Ioc (0 : ℝ) P, 2 * ∫⁻ y : Space, B.indicator (fun y => ‖h (t, y)‖ₑ) y :=
              (lintegral_const_mul' _ _ (by norm_num)).symm
          _ ≤ ∫⁻ t in Ioc (0 : ℝ) P, (ENNReal.ofReal s⁻¹ * volume B +
                ENNReal.ofReal s * ∫⁻ y : Space, ‖h (t, y)‖ₑ ^ 2) :=
              lintegral_mono fun t => ls_amgm_lint (fun y => ‖h (t, y)‖ₑ) hB hs0
          _ = ENNReal.ofReal s⁻¹ * volume B * volume (Ioc (0 : ℝ) P) +
                ENNReal.ofReal s * H := by
              rw [lintegral_add_left measurable_const, setLIntegral_const,
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          _ ≤ ENNReal.ofReal s⁻¹ * ENNReal.ofReal ((K * s) ^ 3 * A) * ENNReal.ofReal P +
                ENNReal.ofReal s * ENNReal.ofReal Hr := by
              rw [Real.volume_Ioc, sub_zero, hHeq]
              gcongr
          _ = ENNReal.ofReal (s⁻¹ * ((K * s) ^ 3 * A) * P + s * Hr) := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity),
                ls_ofReal_mul3 _ _ _ (inv_nonneg.2 hs0.le) (by positivity)]
              rw [ENNReal.ofReal_mul hs0.le]
          _ ≤ ENNReal.ofReal (Q * s ^ 2) := by
              apply ENNReal.ofReal_le_ofReal
              have e : s⁻¹ * ((K * s) ^ 3 * A) * P = K ^ 3 * A * P * s ^ 2 := by
                field_simp
              have hs1 : s ≤ s ^ 2 := by nlinarith
              rw [e, hQdef]
              nlinarith [mul_le_mul_of_nonneg_right hs1 hHr0]
      exact le_trans (le_mul_of_one_le_left (zero_le) (by norm_num)) h2T
    have hbig : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
        ‖dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖ₑ) ≤
        ENNReal.ofReal (3 * ((s⁻¹) ^ 3 * Bb * M * Vr) * (Q * s ^ 2)) := by
      calc (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖ₑ)
          ≤ ∫⁻ t in Ioc (0 : ℝ) P, ENNReal.ofReal (3 * ((s⁻¹) ^ 3 * Bb * M * Vr)) *
              ∫⁻ y : Space, B.indicator (fun y => ‖h (t, y)‖ₑ) y := by
            refine lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_)
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            exact lintegral_mono fun y => hfpt t (Ioc_subset_Icc_self ht) y
        _ = ENNReal.ofReal (3 * ((s⁻¹) ^ 3 * Bb * M * Vr)) *
              (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, B.indicator (fun y => ‖h (t, y)‖ₑ) y) :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (3 * ((s⁻¹) ^ 3 * Bb * M * Vr)) * ENNReal.ofReal (Q * s ^ 2) :=
              by gcongr
        _ = ENNReal.ofReal (3 * ((s⁻¹) ^ 3 * Bb * M * Vr) * (Q * s ^ 2)) :=
              (ENNReal.ofReal_mul (by positivity)).symm
    have hne : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
        ‖dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖ₑ) ≠ ⊤ :=
      ((hbig.trans_lt ENNReal.ofReal_lt_top)).ne
    have hpair : ‖pairF P (convY (dilK b s) Θ) h‖ ≤
        P⁻¹ * (3 * ((s⁻¹) ^ 3 * Bb * M * Vr) * (Q * s ^ 2)) := by
      unfold pairF phaseInt
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hP.le)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hP.le)
      calc ‖∫ t in Ioc (0 : ℝ) P, ∫ y : Space, dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖
          ≤ (∫⁻ t in Ioc (0 : ℝ) P,
              ENNReal.ofReal ‖∫ y : Space, dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖).toReal :=
            norm_integral_le_lintegral_norm _
        _ ≤ (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
              ‖dotL (convY (dilK b s) Θ (t, y)) (h (t, y))‖ₑ).toReal :=
            ENNReal.toReal_mono hne (lintegral_mono fun t => by
              rw [ofReal_norm_eq_enorm]
              exact enorm_integral_le_lintegral_enorm _)
        _ ≤ 3 * ((s⁻¹) ^ 3 * Bb * M * Vr) * (Q * s ^ 2) :=
            ENNReal.toReal_le_of_le_ofReal (by positivity) hbig
    calc ‖pairF P (convY (dilK b s) Θ) h‖
        ≤ P⁻¹ * (3 * ((s⁻¹) ^ 3 * Bb * M * Vr) * (Q * s ^ 2)) := hpair
      _ = 3 * P⁻¹ * C0 * Q * s⁻¹ := by
          rw [hC0def]
          field_simp
  have hlim : Tendsto (fun s : ℝ => 3 * P⁻¹ * C0 * Q * s⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (3 * P⁻¹ * C0 * Q)
  exact squeeze_zero_norm' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs using key s hs)
    hlim
