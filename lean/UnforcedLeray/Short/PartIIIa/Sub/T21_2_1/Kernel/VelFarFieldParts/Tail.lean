import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.TailFar

/-!
# Part III-a, `KerVelTail`: exponential tail of `K_dψ - meanShear` (SP 3052-3057, 2084)

The far-field kernel estimate `kerD_far_abs` (helper `TailFar.lean`) gives, for `|z.2| ≥ 1`,
`|K_d(z) - meanShear d 1 z| ≤ C_d exp(-(2π/d)|z.2|)`. For `|x.2| ≥ R + 1`, the test `ψ` (supported in
`|y.2| ≤ R`) has `sign((x-y).2) = sign(x.2)`, so the difference `K_dψ(x) - meanShear(∫ψ)(x)` is
`∫_cell ψ(y) (K_d(x-y) - meanShear(x))`, whose integrand is bounded by the exponential tail on the
strip `|y.2| ≤ R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A test is bounded, and vanishes beyond a band of width `R ≥ 0`. -/
theorem test_data {d : ℝ} (hd : 1 ≤ d) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest d ψ) :
    ∃ M R : ℝ, 0 ≤ M ∧ 0 ≤ R ∧ (∀ x : ℝ × ℝ, |ψ x| ≤ M) ∧
      (∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0) := by
  obtain ⟨R0, hR0⟩ := hψ.band
  have hd0 : 0 < d := by linarith
  have hR : ∀ x : ℝ × ℝ, |R0| < |x.2| → ψ x = 0 := fun x hx =>
    hR0 x (lt_of_le_of_lt (le_abs_self R0) hx)
  have hcpt : IsCompact (Icc (-(d / 2)) (d / 2) ×ˢ Icc (-|R0|) |R0|) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hψ.continuous.continuousOn
  refine ⟨max C 0, |R0|, le_max_right _ _, abs_nonneg _, fun x => ?_, hR⟩
  by_cases hx : |R0| < |x.2|
  · rw [hR x hx, abs_zero]
    exact le_max_right _ _
  · push Not at hx
    have hper : Function.Periodic (fun t : ℝ => ψ (t, x.2)) d := fun t => hψ.periodic (t, x.2)
    obtain ⟨y, hy, hyeq⟩ := hper.exists_mem_Ico hd0 x.1 (-(d / 2))
    have hmem : (y, x.2) ∈ Icc (-(d / 2)) (d / 2) ×ˢ Icc (-|R0|) |R0| := by
      refine ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
      exact abs_le.mp hx
    have h1 := hC (y, x.2) hmem
    have hxeq : ψ x = ψ (y, x.2) := hyeq
    have h2 : |ψ (y, x.2)| ≤ C := by simpa [Real.norm_eq_abs] using h1
    rw [hxeq]
    exact le_trans h2 (le_max_left _ _)

/-- The far-field constant `1/(c(1 - e^{-2π/c}))`. -/
def farC (c : ℝ) : ℝ := 1 / (c * (1 - Real.exp (-(2 * Real.pi / c))))

theorem farC_nonneg {c : ℝ} (hc : 1 ≤ c) : 0 ≤ farC c := by
  unfold farC
  have h1 : Real.exp (-(2 * Real.pi / c)) < 1 := by
    have := Real.exp_lt_exp.2 (show -(2 * Real.pi / c) < 0 by
      have : 0 < 2 * Real.pi / c := by positivity
      linarith)
    simpa using this
  have h2 : 0 < c * (1 - Real.exp (-(2 * Real.pi / c))) := mul_pos (by linarith) (by linarith)
  exact div_nonneg zero_le_one h2.le

theorem kerD_neg (c : ℝ) (z : ℝ × ℝ) (j : Fin 2) : kerD c (-z) j = -kerD c z j :=
  bsKernel_neg' c z j

theorem meanShear_neg (c Γ : ℝ) (z : ℝ × ℝ) (j : Fin 2) :
    meanShear c Γ (-z) j = -meanShear c Γ z j := by
  unfold meanShear
  rw [Prod.snd_neg, Real.sign_neg]
  split_ifs <;> ring

theorem meanShear_mul (c Γ : ℝ) (x : ℝ × ℝ) (j : Fin 2) :
    meanShear c Γ x j = Γ * meanShear c 1 x j := by
  unfold meanShear
  split_ifs <;> ring

theorem sign_sub_eq_of_band (a b R : ℝ) (hb : |b| ≤ R) (ha : R < |a|) :
    Real.sign (a - b) = Real.sign a := by
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  rcases le_or_gt 0 a with h | h
  · rw [abs_of_nonneg h] at ha
    rw [Real.sign_of_pos (by linarith), Real.sign_of_pos (by linarith)]
  · rw [abs_of_neg h] at ha
    rw [Real.sign_of_neg (by linarith), Real.sign_of_neg (by linarith)]

theorem meanShear_sub_eq (c : ℝ) (x y : ℝ × ℝ) (j : Fin 2) (R : ℝ) (hy : |y.2| ≤ R)
    (hx : R < |x.2|) : meanShear c 1 (x - y) j = meanShear c 1 x j := by
  unfold meanShear
  rw [Prod.snd_sub, sign_sub_eq_of_band x.2 y.2 R hy hx]

/-- The far-field bound with the modulus of the argument, for `1 ≤ |z.2|`. -/
theorem kerD_far_abs (c : ℝ) (hc : 1 ≤ c) (z : ℝ × ℝ) (hz : 1 ≤ |z.2|) (j : Fin 2) :
    |kerD c z j - meanShear c 1 z j| ≤
      farC c * Real.exp (-(2 * Real.pi / c * |z.2|)) := by
  rcases le_or_gt 0 z.2 with h | h
  · rw [abs_of_nonneg h] at hz ⊢
    exact kerD_far_pos c hc z hz j
  · rw [abs_of_neg h] at hz ⊢
    have h' := kerD_far_pos c hc (-z) (by rw [Prod.snd_neg]; linarith) j
    rw [Prod.snd_neg, kerD_neg, meanShear_neg] at h'
    have e2 : -kerD c z j - -meanShear c 1 z j = -(kerD c z j - meanShear c 1 z j) := by ring
    rw [e2, abs_neg] at h'
    rw [neg_mul_eq_mul_neg] at h' ⊢
    exact h'

/-- The volume of a strip of the cell. -/
theorem tail_vol_strip (d R t : ℝ) :
    volume (Ico (-(d / 2)) (d / 2) ×ˢ Icc (t - R) (t + R)) =
      ENNReal.ofReal d * ENNReal.ofReal (2 * R) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc,
    show d / 2 - -(d / 2) = d by ring, show t + R - (t - R) = 2 * R by ring]

theorem tail_vol_strip0 (d R : ℝ) :
    volume (Ico (-(d / 2)) (d / 2) ×ˢ Icc (-R) R) = ENNReal.ofReal d * ENNReal.ofReal (2 * R) := by
  have := tail_vol_strip d R 0
  rw [zero_sub, zero_add] at this
  exact this

/-- Lebesgue integral over the cell of a function vanishing off the band `|y.2| ≤ R`. -/
theorem tail_lintegral_band_le (d R : ℝ) {B : ℝ} {f : ℝ × ℝ → ℝ} (hb : ∀ y, |f y| ≤ B)
    (hs : ∀ y : ℝ × ℝ, R < |y.2| → f y = 0) :
    ∫⁻ y in B0579.cell d, ‖f y‖ₑ ≤
      ENNReal.ofReal B * (ENNReal.ofReal d * ENNReal.ofReal (2 * R)) := by
  have hmeas : MeasurableSet ((fun y : ℝ × ℝ => y.2) ⁻¹' Icc (-R) R) :=
    measurableSet_Icc.preimage measurable_snd
  calc ∫⁻ y in B0579.cell d, ‖f y‖ₑ
      ≤ ∫⁻ y in B0579.cell d,
          ((fun y : ℝ × ℝ => y.2) ⁻¹' Icc (-R) R).indicator (fun _ => ENNReal.ofReal B) y := by
        refine lintegral_mono fun y => ?_
        by_cases hs' : y ∈ (fun y : ℝ × ℝ => y.2) ⁻¹' Icc (-R) R
        · rw [indicator_of_mem hs', Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hb y)
        · rw [indicator_of_notMem hs']
          have hR : R < |y.2| := by
            by_contra hcon
            push Not at hcon
            exact hs' (abs_le.mp hcon)
          rw [hs y hR]
          simp
    _ = ENNReal.ofReal B *
          volume ((fun y : ℝ × ℝ => y.2) ⁻¹' Icc (-R) R ∩ B0579.cell d) := by
        rw [lintegral_indicator_const hmeas, Measure.restrict_apply hmeas]
    _ ≤ ENNReal.ofReal B * volume (Ico (-(d / 2)) (d / 2) ×ˢ Icc (-R) R) := by
        refine mul_le_mul_of_nonneg_left (measure_mono ?_) (by positivity)
        intro y hy
        exact ⟨hy.2.1, hy.1⟩
    _ = ENNReal.ofReal B * (ENNReal.ofReal d * ENNReal.ofReal (2 * R)) := by
        rw [tail_vol_strip0]

theorem tail_integrableOn_band (d R : ℝ) {B : ℝ} {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ y, |f y| ≤ B) (hs : ∀ y : ℝ × ℝ, R < |y.2| → f y = 0) :
    IntegrableOn f (B0579.cell d) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  show ∫⁻ y in B0579.cell d, ‖f y‖ₑ < ⊤
  exact lt_of_le_of_lt (tail_lintegral_band_le d R hb hs)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

/-- **Exponential tail of the kernel velocity** (`KerVelTail`, SP 3056-3057, 2084). -/
theorem kerVelTail : UnforcedLeray.Short.IIIa.KerVelTail := by
  intro d hd ψ hψ
  have hd0 : 0 < d := by linarith
  obtain ⟨M, R, hM0, hR0, hMb, hRb⟩ := test_data hd hψ
  have hCf : 0 ≤ farC d := farC_nonneg hd
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hkj : ∀ j : Fin 2, Measurable fun z : ℝ × ℝ => kerD d z j := fun j =>
    ((PiLp.continuous_apply 2 _ j).measurable).comp (UnforcedLeray.Cyl.measurable_bsKernel d)
  refine ⟨R + 1, M * farC d * Real.exp (2 * Real.pi / d * R) * (d * (2 * R)), fun x hx j => ?_⟩
  -- the integrals in the statement
  have hB1 : 0 ≤ M * (|(1 : ℝ)| / (2 * |d|) + farC d) :=
    mul_nonneg hM0 (add_nonneg (by positivity) hCf)
  have hB2 : 0 ≤ M * (|(1 : ℝ)| / (2 * |d|)) := mul_nonneg hM0 (by positivity)
  have hi1 : IntegrableOn (fun y => ψ y * kerD d (x - y) j) (B0579.cell d) := by
    refine tail_integrableOn_band d R (hψm.mul ((hkj j).comp (measurable_const.sub measurable_id)))
      (B := M * (|(1 : ℝ)| / (2 * |d|) + farC d)) ?_ ?_
    · intro y
      by_cases hy : |y.2| ≤ R
      · have hxy : 1 ≤ |(x - y).2| := by
          rw [Prod.snd_sub]
          have := abs_sub_abs_le_abs_sub x.2 y.2
          linarith
        have hfar := kerD_far_abs d hd (x - y) hxy j
        have hm := meanShear_abs_le d 1 (x - y) j
        have hexp : Real.exp (-(2 * Real.pi / d * |(x - y).2|)) ≤ 1 := by
          apply Real.exp_le_one_iff.2
          have : 0 ≤ 2 * Real.pi / d * |(x - y).2| := by positivity
          linarith
        have hK : |kerD d (x - y) j| ≤ |(1 : ℝ)| / (2 * |d|) + farC d := by
          have h1 : |kerD d (x - y) j| ≤
              |kerD d (x - y) j - meanShear d 1 (x - y) j| + |meanShear d 1 (x - y) j| := by
            have := abs_add_le (kerD d (x - y) j - meanShear d 1 (x - y) j) (meanShear d 1 (x - y) j)
            rwa [sub_add_cancel] at this
          have h2 : |kerD d (x - y) j - meanShear d 1 (x - y) j| ≤ farC d :=
            le_trans hfar (by nlinarith [farC_nonneg hd])
          linarith
        rw [abs_mul]
        exact mul_le_mul (hMb y) hK (abs_nonneg _) hM0
      · have hy' : R < |y.2| := not_le.mp hy
        rw [hRb y hy', zero_mul, abs_zero]
        exact hB1
    · intro y hy
      rw [hRb y hy, zero_mul]
  have hi2 : IntegrableOn (fun y => ψ y * meanShear d 1 x j) (B0579.cell d) := by
    refine tail_integrableOn_band d R (hψm.mul measurable_const)
      (B := M * (|(1 : ℝ)| / (2 * |d|))) ?_ ?_
    · intro y
      rw [abs_mul]
      exact mul_le_mul (hMb y) (meanShear_abs_le d 1 x j) (abs_nonneg _) hM0
    · intro y hy
      rw [hRb y hy, zero_mul]
  have hid : kerVel d ψ x j - meanShear d (∫ y in B0579.cell d, ψ y) x j =
      ∫ y in B0579.cell d, ψ y * (kerD d (x - y) j - meanShear d 1 x j) := by
    rw [meanShear_mul, ← integral_mul_const]
    unfold kerVel
    rw [← integral_sub hi1 hi2]
    congr 1
    funext y
    ring
  have hK3 : 0 ≤ M * farC d * Real.exp (2 * Real.pi / d * R) *
      Real.exp (-(2 * Real.pi / d * |x.2|)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hM0 hCf) (Real.exp_pos _).le) (Real.exp_pos _).le
  have hF : ∀ y : ℝ × ℝ, |ψ y * (kerD d (x - y) j - meanShear d 1 x j)| ≤
      M * farC d * Real.exp (2 * Real.pi / d * R) * Real.exp (-(2 * Real.pi / d * |x.2|)) := by
    intro y
    by_cases hy : |y.2| ≤ R
    · have hxy : 1 ≤ |(x - y).2| := by
        rw [Prod.snd_sub]
        have := abs_sub_abs_le_abs_sub x.2 y.2
        linarith
      have hm : meanShear d 1 x j = meanShear d 1 (x - y) j :=
        (meanShear_sub_eq d x y j R hy (by linarith)).symm
      rw [hm, abs_mul]
      have hfar := kerD_far_abs d hd (x - y) hxy j
      have hpos : 0 < 2 * Real.pi / d := by positivity
      have hexp : Real.exp (-(2 * Real.pi / d * |(x - y).2|)) ≤
          Real.exp (2 * Real.pi / d * R) * Real.exp (-(2 * Real.pi / d * |x.2|)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have hab : |x.2| - R ≤ |(x - y).2| := by
          rw [Prod.snd_sub]
          have := abs_sub_abs_le_abs_sub x.2 y.2
          linarith
        have h5 : (2 * Real.pi / d) * (|x.2| - R) ≤ (2 * Real.pi / d) * |(x - y).2| :=
          mul_le_mul_of_nonneg_left hab hpos.le
        nlinarith [h5]
      calc |ψ y| * |kerD d (x - y) j - meanShear d 1 (x - y) j|
          ≤ M * (farC d * Real.exp (-(2 * Real.pi / d * |(x - y).2|))) :=
            mul_le_mul (hMb y) hfar (abs_nonneg _) hM0
        _ ≤ M * (farC d * (Real.exp (2 * Real.pi / d * R) *
              Real.exp (-(2 * Real.pi / d * |x.2|)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hCf) hM0
        _ = M * farC d * Real.exp (2 * Real.pi / d * R) *
              Real.exp (-(2 * Real.pi / d * |x.2|)) := by ring
    · have hy' : R < |y.2| := not_le.mp hy
      rw [hRb y hy', zero_mul, abs_zero]
      exact hK3
  have hs : ∀ y : ℝ × ℝ, R < |y.2| →
      ψ y * (kerD d (x - y) j - meanShear d 1 x j) = 0 := fun y hy => by
    rw [hRb y hy, zero_mul]
  have hnorm : ‖∫ y in B0579.cell d, ψ y * (kerD d (x - y) j - meanShear d 1 x j)‖ₑ ≤
      ENNReal.ofReal (M * farC d * Real.exp (2 * Real.pi / d * R) *
        Real.exp (-(2 * Real.pi / d * |x.2|)) * (d * (2 * R))) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine (tail_lintegral_band_le d R hF hs).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hK3, ENNReal.ofReal_mul hd0.le]
  have hq : 0 ≤ M * farC d * Real.exp (2 * Real.pi / d * R) *
      Real.exp (-(2 * Real.pi / d * |x.2|)) * (d * (2 * R)) :=
    mul_nonneg hK3 (mul_nonneg hd0.le (by linarith : (0:ℝ) ≤ 2 * R))
  have hreal : |∫ y in B0579.cell d, ψ y * (kerD d (x - y) j - meanShear d 1 x j)| ≤
      M * farC d * Real.exp (2 * Real.pi / d * R) *
        Real.exp (-(2 * Real.pi / d * |x.2|)) * (d * (2 * R)) :=
    (ENNReal.ofReal_le_ofReal_iff hq).1 (by rw [← Real.enorm_eq_ofReal_abs]; exact hnorm)
  rw [hid]
  calc _ ≤ _ := hreal
    _ = M * farC d * Real.exp (2 * Real.pi / d * R) * (d * (2 * R)) *
          Real.exp (-(2 * Real.pi / d) * |x.2|) := by
        rw [show -(2 * Real.pi / d * |x.2|) = -(2 * Real.pi / d) * |x.2| by ring]
        ring

end UnforcedLeray.Short.IIIa
