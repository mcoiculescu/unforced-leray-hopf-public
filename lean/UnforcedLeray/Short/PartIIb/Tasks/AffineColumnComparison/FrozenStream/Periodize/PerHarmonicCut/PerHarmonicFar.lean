import UnforcedLeray.Short.PartIIb.Sub.G4_2_3_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerHarmonicCut.PerHarmonicExact
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerHarmonicCut.CscSqBound
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerHarmonicCut.CauchyPlanar

/-!
# Part II-b, task `PartII-b:G4/2/3/4/3`: `perHarmonicFar`

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

For `|x₂| ≥ 2ρ` the periodization of `Hc` equals the periodization of `M (y₁ - i y₂)^{-2}`
(all shifted points lie in `|y₂| > ρ`), which is `M (π/c)² / sin²(π z/c)` with `z = x₁ - i x₂`
(`perC_harmonic_exact`). On the closed disc of radius `ρ` about `z` the imaginary part satisfies
`|Im w| ≥ |x₂| - ρ ≥ ρ`, so `csc_sq_bound` gives a uniform bound of the form
`C c² e^{-2π|x₂|/c}`; Cauchy's estimate (`cauchy_planar`) then bounds the `j`-th derivative.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- `sin (π w / c)` does not vanish when `Im w ≠ 0`. -/
lemma phf_sin_ne (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : w.im ≠ 0) :
    Complex.sin (Real.pi * w / c) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have h2 : (Real.pi * w / (c : ℂ)).im = Real.pi * w.im / c := by
    simp [Complex.div_ofReal_im, Complex.mul_im]
  have h3 : (Real.pi * w / (c : ℂ)).im = 0 := by
    rw [hk]
    simp
  rw [h2] at h3
  rcases div_eq_zero_iff.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact Real.pi_ne_zero h5
    · exact hw h5
  · exact hc.ne' h4

/-- The function `v ↦ (π/c)² / sin(π v / c)²` is differentiable off the real axis. -/
lemma phf_G_diff (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : w.im ≠ 0) :
    DifferentiableAt ℂ (fun v : ℂ => ((Real.pi : ℂ) / c) ^ 2 / Complex.sin (Real.pi * v / c) ^ 2) w := by
  have hs := phf_sin_ne c hc w hw
  have h0 : DifferentiableAt ℂ (fun v : ℂ => Real.pi * v / c) w :=
    (differentiableAt_id.const_mul (Real.pi : ℂ)).div_const (c : ℂ)
  have h1 : DifferentiableAt ℂ (fun v : ℂ => Complex.sin (Real.pi * v / c)) w :=
    h0.csin
  have h2 : DifferentiableAt ℂ (fun v : ℂ => Complex.sin (Real.pi * v / c) ^ 2) w :=
    h1.pow 2
  exact (differentiableAt_const _).div h2 (pow_ne_zero 2 hs)

/-- Algebra for the constant: `1 / (1 - e^{-2πρ/c}) ≤ c (1 + 1/(2πρ))` for `c ≥ 1`. -/
lemma phf_poly (c ρ : ℝ) (hc : 1 ≤ c) (hρ : 0 < ρ) :
    0 < 1 - Real.exp (-(2 * Real.pi * ρ / c)) ∧
      1 / (1 - Real.exp (-(2 * Real.pi * ρ / c))) ≤ c * (1 + 1 / (2 * Real.pi * ρ)) := by
  have hc0 : 0 < c := by linarith
  have hpi := Real.pi_pos
  have htpos : 0 < 2 * Real.pi * ρ / c := div_pos (mul_pos (mul_pos two_pos hpi) hρ) hc0
  have hexp1 : 1 + 2 * Real.pi * ρ / c ≤ Real.exp (2 * Real.pi * ρ / c) := by
    linarith [Real.add_one_le_exp (2 * Real.pi * ρ / c)]
  have hexpm : Real.exp (-(2 * Real.pi * ρ / c)) * (1 + 2 * Real.pi * ρ / c) ≤ 1 := by
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    linarith
  have hD : (2 * Real.pi * ρ / c) / (1 + 2 * Real.pi * ρ / c)
      ≤ 1 - Real.exp (-(2 * Real.pi * ρ / c)) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hDpos : 0 < 1 - Real.exp (-(2 * Real.pi * ρ / c)) :=
    lt_of_lt_of_le (div_pos htpos (by linarith)) hD
  refine ⟨hDpos, ?_⟩
  have htne : 2 * Real.pi * ρ / c ≠ 0 := htpos.ne'
  have hsplit : c / (2 * Real.pi * ρ) = c * (1 / (2 * Real.pi * ρ)) := by ring
  calc 1 / (1 - Real.exp (-(2 * Real.pi * ρ / c)))
      ≤ 1 / ((2 * Real.pi * ρ / c) / (1 + 2 * Real.pi * ρ / c)) :=
        one_div_le_one_div_of_le (div_pos htpos (by linarith)) hD
    _ = 1 / (2 * Real.pi * ρ / c) + 1 := by
        rw [one_div_div, add_div, div_self htne]
    _ = c / (2 * Real.pi * ρ) + 1 := by rw [one_div_div]
    _ ≤ c * (1 + 1 / (2 * Real.pi * ρ)) := by
        rw [hsplit]
        nlinarith

/-- Points of a closed disc of radius `r` about `z` have `|Im w| ≥ |Im z| - r`. -/
lemma phf_ball (z w : ℂ) (r : ℝ) (hw : w ∈ Metric.closedBall z r) :
    |z.im| - r ≤ |w.im| := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h1 := Complex.abs_im_le_norm (w - z)
  rw [Complex.sub_im] at h1
  have h2 := abs_sub_abs_le_abs_sub z.im w.im
  have h3 : |z.im - w.im| = |w.im - z.im| := abs_sub_comm _ _
  linarith

/-- Pointwise bound for `(π/c)² / sin²(π w/c)` on `|Im w| ≥ a - ρ`. -/
lemma phf_gbound (c ρ a : ℝ) (hc : 1 ≤ c) (hρ : 0 < ρ) (ha : 2 * ρ ≤ a) (w : ℂ)
    (hw : a - ρ ≤ |w.im|) :
    ‖((Real.pi : ℂ) / c) ^ 2 / Complex.sin (Real.pi * w / c) ^ 2‖
      ≤ 4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2 * c ^ 2
        * Real.exp (-(2 * Real.pi * a / c)) := by
  have hc0 : 0 < c := by linarith
  have hpi := Real.pi_pos
  have hρu : ρ ≤ |w.im| := by linarith
  have hwne : w.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hρu
    linarith
  have h1 := csc_sq_bound c hc0 w hwne
  have hE0 : Real.exp (-(2 * Real.pi * |w.im| / c))
      ≤ Real.exp (-(2 * Real.pi * (a - ρ) / c)) := by
    apply Real.exp_le_exp.mpr
    have h2 : 2 * Real.pi * (a - ρ) ≤ 2 * Real.pi * |w.im| :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h3 := div_le_div_of_nonneg_right h2 hc0.le
    linarith
  have hE1 : Real.exp (-(2 * Real.pi * |w.im| / c)) ≤ Real.exp (-(2 * Real.pi * ρ / c)) := by
    apply Real.exp_le_exp.mpr
    have h2 : 2 * Real.pi * ρ ≤ 2 * Real.pi * |w.im| :=
      mul_le_mul_of_nonneg_left hρu (by positivity)
    have h3 := div_le_div_of_nonneg_right h2 hc0.le
    linarith
  have hDpos : 0 < 1 - Real.exp (-(2 * Real.pi * ρ / c)) := (phf_poly c ρ hc hρ).1
  have hDle : 1 - Real.exp (-(2 * Real.pi * ρ / c))
      ≤ 1 - Real.exp (-(2 * Real.pi * |w.im| / c)) := by linarith
  have hD2 : (1 - Real.exp (-(2 * Real.pi * ρ / c))) ^ 2
      ≤ (1 - Real.exp (-(2 * Real.pi * |w.im| / c))) ^ 2 :=
    pow_le_pow_left₀ hDpos.le hDle 2
  have hfrac : Real.exp (-(2 * Real.pi * |w.im| / c))
      / (1 - Real.exp (-(2 * Real.pi * |w.im| / c))) ^ 2
      ≤ Real.exp (-(2 * Real.pi * (a - ρ) / c)) / (1 - Real.exp (-(2 * Real.pi * ρ / c))) ^ 2 := by
    calc Real.exp (-(2 * Real.pi * |w.im| / c)) / (1 - Real.exp (-(2 * Real.pi * |w.im| / c))) ^ 2
        ≤ Real.exp (-(2 * Real.pi * (a - ρ) / c))
            / (1 - Real.exp (-(2 * Real.pi * |w.im| / c))) ^ 2 :=
          div_le_div_of_nonneg_right hE0 (sq_nonneg _)
      _ ≤ Real.exp (-(2 * Real.pi * (a - ρ) / c)) / (1 - Real.exp (-(2 * Real.pi * ρ / c))) ^ 2 :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos hDpos 2) hD2
  have e0 : Real.exp (-(2 * Real.pi * (a - ρ) / c))
      = Real.exp (2 * Real.pi * ρ / c) * Real.exp (-(2 * Real.pi * a / c)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hY1 : Real.exp (2 * Real.pi * ρ / c) ≤ Real.exp (2 * Real.pi * ρ) := by
    apply Real.exp_le_exp.mpr
    exact div_le_self (mul_pos (mul_pos two_pos hpi) hρ).le hc
  have hsq : ∀ a d : ℝ, a / d ^ 2 = a * (1 / d) ^ 2 := fun a d => by
    rw [one_div_pow, mul_one_div]
  have hX1 : ((Real.pi : ℝ) / c) ^ 2 ≤ Real.pi ^ 2 := by
    have h5 : Real.pi / c ≤ Real.pi := div_le_self hpi.le hc
    exact pow_le_pow_left₀ (div_pos hpi hc0).le h5 2
  have hZ := (phf_poly c ρ hc hρ).2
  have hZ0 : 0 ≤ 1 / (1 - Real.exp (-(2 * Real.pi * ρ / c))) :=
    (one_div_pos.mpr hDpos).le
  have hZ2 : (1 / (1 - Real.exp (-(2 * Real.pi * ρ / c)))) ^ 2
      ≤ (c * (1 + 1 / (2 * Real.pi * ρ))) ^ 2 :=
    pow_le_pow_left₀ hZ0 hZ 2
  have hF : 0 ≤ Real.exp (-(2 * Real.pi * a / c)) := (Real.exp_pos _).le
  have key : 4 * ((Real.pi : ℝ) / c) ^ 2 * (Real.exp (2 * Real.pi * ρ / c) * Real.exp (-(2 * Real.pi * a / c)))
      * (1 / (1 - Real.exp (-(2 * Real.pi * ρ / c)))) ^ 2
      ≤ 4 * Real.pi ^ 2 * (Real.exp (2 * Real.pi * ρ) * Real.exp (-(2 * Real.pi * a / c)))
        * (c * (1 + 1 / (2 * Real.pi * ρ))) ^ 2 := by
    apply mul_le_mul _ hZ2 (by positivity) (by positivity)
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · exact mul_le_mul_of_nonneg_left hX1 (by norm_num)
    · exact mul_le_mul_of_nonneg_right hY1 hF
  calc ‖((Real.pi : ℂ) / c) ^ 2 / Complex.sin (Real.pi * w / c) ^ 2‖
      ≤ 4 * (Real.pi / c) ^ 2 * Real.exp (-(2 * Real.pi * |w.im| / c))
          / (1 - Real.exp (-(2 * Real.pi * |w.im| / c))) ^ 2 := h1
    _ = 4 * (Real.pi / c) ^ 2 * (Real.exp (-(2 * Real.pi * |w.im| / c))
          / (1 - Real.exp (-(2 * Real.pi * |w.im| / c))) ^ 2) := by ring
    _ ≤ 4 * (Real.pi / c) ^ 2 * (Real.exp (-(2 * Real.pi * (a - ρ) / c))
          / (1 - Real.exp (-(2 * Real.pi * ρ / c))) ^ 2) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = 4 * ((Real.pi : ℝ) / c) ^ 2 * (Real.exp (2 * Real.pi * ρ / c) * Real.exp (-(2 * Real.pi * a / c)))
          * (1 / (1 - Real.exp (-(2 * Real.pi * ρ / c)))) ^ 2 := by
          rw [e0, hsq]
          ring
    _ ≤ 4 * Real.pi ^ 2 * (Real.exp (2 * Real.pi * ρ) * Real.exp (-(2 * Real.pi * a / c)))
          * (c * (1 + 1 / (2 * Real.pi * ρ))) ^ 2 := key
    _ = 4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2 * c ^ 2
          * Real.exp (-(2 * Real.pi * a / c)) := by
          ring

/-- **`perHarmonicFar`** (SP 2349-2358): exponential transverse decay of the derivatives of the
periodization of `Hc`, for `|x₂| ≥ 2ρ`, with polynomial cost `c²`. -/
theorem perHarmonicFar : UnforcedLeray.Short.IIb.PerHarmonicFar := by
  intro Hc ρ M _hHc hρ hout j
  obtain ⟨A, hA⟩ := cauchy_planar j
  have hpi := Real.pi_pos
  refine ⟨|A| * ‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2)
      / ρ ^ j + 1, 2 * Real.pi, 2, ?_, by positivity, ?_⟩
  · have h0 : 0 ≤ |A| * ‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ)
        * (1 + 1 / (2 * Real.pi * ρ)) ^ 2) / ρ ^ j :=
      div_nonneg (by positivity) (pow_nonneg hρ.le j)
    linarith
  · intro c hc x hx
    have hρx : ρ < |x.2| := by linarith
    have hx2 : x.2 ≠ 0 := by
      intro h
      rw [h, abs_zero] at hρx
      linarith
    have hc0 : 0 < c := by linarith
    have hU : {y : ℝ × ℝ | ρ < |y.2|} ∈ nhds x :=
      IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd.abs) hρx
    have hEq1 : UnforcedLeray.Short.IIb.perC c Hc =ᶠ[nhds x]
        UnforcedLeray.Short.IIb.perC c
          (fun y : ℝ × ℝ => M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) := by
      filter_upwards [hU] with y hy
      have hy' : ρ < |y.2| := hy
      have hy2 : ρ ^ 2 < y.2 ^ 2 := by
        have := sq_abs y.2
        nlinarith [abs_nonneg y.2]
      unfold UnforcedLeray.Short.IIb.perC
      apply tsum_congr
      intro k
      exact hout (y.1 + (k : ℝ) * c, y.2) (by
        show ρ ^ 2 < (y.1 + (k : ℝ) * c) ^ 2 + y.2 ^ 2
        nlinarith [sq_nonneg (y.1 + (k : ℝ) * c)])
    have hEq2 : ∀ y : ℝ × ℝ, y.2 ≠ 0 →
        UnforcedLeray.Short.IIb.perC c
            (fun y : ℝ × ℝ => M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) y
          = M * (((Real.pi : ℂ) / c) ^ 2 / Complex.sin (Real.pi * ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) / c) ^ 2) := by
      intro y hy
      have hA' : UnforcedLeray.Short.IIb.perC c
            (fun y : ℝ × ℝ => M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) y
          = M * UnforcedLeray.Short.IIb.perC c
            (fun y : ℝ × ℝ => (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) y := by
        unfold UnforcedLeray.Short.IIb.perC
        exact tsum_mul_left
      rw [hA', perC_harmonic_exact c hc0 y hy]
    have hEq3 : UnforcedLeray.Short.IIb.perC c
          (fun y : ℝ × ℝ => M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) =ᶠ[nhds x]
        (fun y : ℝ × ℝ => M * (((Real.pi : ℂ) / c) ^ 2
          / Complex.sin (Real.pi * ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) / c) ^ 2)) := by
      filter_upwards [hU] with y hy
      have hy' : ρ < |y.2| := hy
      exact hEq2 y (fun h => by
        rw [h, abs_zero] at hy'
        linarith)
    have hEq := hEq1.trans hEq3
    have hIt : iteratedFDeriv ℝ j (UnforcedLeray.Short.IIb.perC c Hc) x
        = iteratedFDeriv ℝ j (fun y : ℝ × ℝ => M * (((Real.pi : ℂ) / c) ^ 2
          / Complex.sin (Real.pi * ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) / c) ^ 2)) x :=
      (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq j).eq_of_nhds
    let z : ℂ := ⟨x.1, -x.2⟩
    have hzx : (z.re, -z.im) = x := by
      ext <;> simp [z]
    have hzabs : |z.im| = |x.2| := by
      simp [z]
    have hd : DifferentiableOn ℂ
        (fun v : ℂ => M * (((Real.pi : ℂ) / c) ^ 2 / Complex.sin (Real.pi * v / c) ^ 2))
        (Metric.closedBall z ρ) := by
      intro w hw
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_mul
      have hwb := phf_ball z w ρ hw
      rw [hzabs] at hwb
      have hwne : w.im ≠ 0 := by
        intro h
        rw [h, abs_zero] at hwb
        linarith
      exact phf_G_diff c hc0 w hwne
    have hB : ∀ w ∈ Metric.closedBall z ρ,
        ‖M * (((Real.pi : ℂ) / c) ^ 2 / Complex.sin (Real.pi * w / c) ^ 2)‖
          ≤ ‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2
              * c ^ 2 * Real.exp (-(2 * Real.pi * |x.2| / c))) := by
      intro w hw
      have hwb := phf_ball z w ρ hw
      rw [hzabs] at hwb
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (phf_gbound c ρ |x.2| hc hρ hx w hwb) (norm_nonneg M)
    have hbound := hA (fun v : ℂ => M * (((Real.pi : ℂ) / c) ^ 2 / Complex.sin (Real.pi * v / c) ^ 2))
      ρ (‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2
              * c ^ 2 * Real.exp (-(2 * Real.pi * |x.2| / c)))) z hρ hd hB
    rw [hzx] at hbound
    rw [hIt]
    have hF : 0 ≤ c ^ 2 * Real.exp (-(2 * Real.pi * |x.2| / c)) := by positivity
    have hB0 : 0 ≤ ‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2
              * c ^ 2 * Real.exp (-(2 * Real.pi * |x.2| / c))) := by positivity
    calc ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => M * (((Real.pi : ℂ) / c) ^ 2
          / Complex.sin (Real.pi * ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) / c) ^ 2)) x‖
        ≤ A * (‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2
              * c ^ 2 * Real.exp (-(2 * Real.pi * |x.2| / c)))) / ρ ^ j := hbound
      _ ≤ |A| * (‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2
              * c ^ 2 * Real.exp (-(2 * Real.pi * |x.2| / c)))) / ρ ^ j :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self A) hB0)
            (pow_nonneg hρ.le j)
      _ = (|A| * ‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2)
            / ρ ^ j) * (c ^ 2 * Real.exp (-(2 * Real.pi * |x.2| / c))) := by
          ring
      _ ≤ (|A| * ‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2)
            / ρ ^ j + 1) * (c ^ 2 * Real.exp (-(2 * Real.pi * |x.2| / c))) :=
          mul_le_mul_of_nonneg_right (by linarith) hF
      _ = (|A| * ‖M‖ * (4 * Real.pi ^ 2 * Real.exp (2 * Real.pi * ρ) * (1 + 1 / (2 * Real.pi * ρ)) ^ 2)
            / ρ ^ j + 1) * c ^ 2 * Real.exp (-(2 * Real.pi * |x.2| / c)) := by
          ring

end UnforcedLeray.Short.IIb
