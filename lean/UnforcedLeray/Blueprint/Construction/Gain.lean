import UnforcedLeray.Blueprint.Construction.Steps

/-!
# The window and the gain of the explicit leading return (C4 and C5, proved)

`paper/main.tex`, lines 13627–13659 (`eq:st18-t00764`–`eq:st18-t00765`), with
`eq:m2-leading-return` and `eq:st18-t00754`; blueprint units B0998, B0999, B1000.

* The window `σ₀ + z/(2ℓ_n)`, `|z| ≤ 1`, lies in `(0,1/4)` for large `n` (line 13650,
  `eventually_window_subset`); `ε_n > 0`, `P_n > 0`.
* `tr K₀(σ) = 2ρ_{ν,ε}(σ) Re[𝒞(σ)N_ν]` (`eq:st18-t00754`, `trace_K0`).
* `2ρ|N_ν| = ν^{2(σ-σ₀)}/|C₀|` (`twice_returnScale_mul_exp`), and on the phase-locked
  sequence `tr K₀(σ) = ν^{2(σ-σ₀)}Re(𝒞(σ)e^{-i arg C₀})/|C₀|` (`trace_K0_phase`).
* At `σ = σ₀ + z/(2ℓ_n)` this is `e^{-z}Re(𝒞(σ)/C₀) → e^{-z}` uniformly for `|z| ≤ 1`
  (`stepGainTrace_of`: step C4 follows from C1 and C2).
* The entries of `K₀` are bounded on the window uniformly in `n` (`stepGainBound_of`: step C5
  follows from C1 and C2).

So C4 and C5 are no longer open: they are theorems about the explicit `K₀` built from the
pinned planar data. (The window lemmas are adapted from
`SkeletonDesignC/ConstructionSteps.lean`, `eventually_window_subset`.)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Matrix Complex
open scoped ContDiff Topology

namespace UnforcedLeray.Blueprint

open MatrixCrossing Planar

namespace ConstructionData

variable (F : ConstructionData)

/-! ## The window (lines 13633–13651) -/

theorem ell_nonneg (n : ℕ) : 0 ≤ F.ell n := abs_nonneg _

theorem point_le (n : ℕ) : F.point n (-1) ≤ F.point n 1 := by
  unfold point
  have h : 0 ≤ 2 * F.ell n := by have := F.ell_nonneg n; linarith
  have : (-1 : ℝ) / (2 * F.ell n) ≤ 1 / (2 * F.ell n) :=
    div_le_div_of_nonneg_right (by norm_num) h
  linarith

variable {F}

theorem ell_tendsto (h2 : StepPhaseLocked F) : Tendsto F.ell atTop atTop := by
  have hne : Tendsto F.ν atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h2.2.1, Eventually.of_forall fun n => (h2.1 n).ne'⟩
  exact tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp hne)

theorem point_tendsto (h2 : StepPhaseLocked F) (z : ℝ) :
    Tendsto (fun n => F.point n z) atTop (𝓝 F.σ₀) := by
  have h2' : Tendsto (fun n => 2 * F.ell n) atTop atTop :=
    (ell_tendsto h2).const_mul_atTop two_pos
  have h := (tendsto_const_nhds (x := z)).div_atTop h2'
  simpa [point] using (tendsto_const_nhds (x := F.σ₀)).add h

/-- For large `n` the whole window lies in `(0, 1/4)` (line 13650). -/
theorem eventually_window_subset (h1 : StepReferenceChoice F) (h2 : StepPhaseLocked F) :
    ∀ᶠ n in atTop, F.window n ⊆ Ioo 0 (1 / 4) := by
  obtain ⟨-, -, hσ₀, -, -⟩ := h1
  have hmem : Ioo (0 : ℝ) (1 / 4) ∈ 𝓝 F.σ₀ :=
    isOpen_Ioo.mem_nhds ⟨by linarith [hσ₀.1], by linarith [hσ₀.2]⟩
  filter_upwards [(point_tendsto h2 (-1)).eventually hmem,
    (point_tendsto h2 1).eventually hmem] with n hl hr
  intro σ hσ
  exact ⟨hl.1.trans_le hσ.1, hσ.2.trans_lt hr.2⟩

/-- `ε_n > 0`. -/
theorem amplitude_pos (h1 : StepReferenceChoice F) {n : ℕ} (hν : 0 < F.ν n) :
    0 < F.amplitude n := by
  unfold amplitude
  apply Real.rpow_pos_of_pos
  have hC : 0 < ‖F.C₀‖ := norm_pos_iff.mpr h1.2.2.2.1
  have := Real.exp_pos (-(F.growth / F.ν n))
  have := Real.rpow_pos_of_pos hν (F.κ.re - 5 - 2 * F.σ₀)
  positivity

/-- `P_n = 2ε_n c_n > 0`. -/
theorem period_pos (h1 : StepReferenceChoice F) {n : ℕ} (hν : 0 < F.ν n) :
    0 < F.period n := by
  unfold period spacing
  have := amplitude_pos h1 hν
  have : 0 < F.ν n ^ 2 := pow_pos hν 2
  positivity

/-! ## The leading return `K₀` (`eq:m2-leading-return`) -/

variable (F)

/-- `eq:st18-t00754`: `tr K₀(σ) = 2ρ(σ) Re[𝒞(σ)N_ν]`. -/
theorem trace_K0 (n : ℕ) (σ : ℝ) :
    (F.K0 n σ).trace = 2 * F.returnScale n σ * (F.coeff σ * F.gauge n).re := by
  simp only [K0, outerProduct, Matrix.trace_fin_two, gainA, gainB, coeff,
    PlanarData.signedCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

/-- `N_ν = e^{γ/ν - Re κ log ν} e^{i(ω/ν - Im κ log ν)}` for `ν > 0`. -/
theorem gauge_eq {n : ℕ} (hν : 0 < F.ν n) :
    F.gauge n = Complex.exp ((F.growth / F.ν n - F.κ.re * Real.log (F.ν n) : ℝ) : ℂ) *
      Complex.exp (((F.frequency / F.ν n - F.κ.im * Real.log (F.ν n) : ℝ) : ℂ) * I) := by
  unfold gauge PlanarData.gaugeFactor
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hν.ne'), ← ofReal_log hν.le,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp only [growth, κ, Complex.add_re, Complex.div_ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul]
    simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofReal_re, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofReal_im]
    ring
  · simp only [frequency, κ, Complex.add_im, Complex.div_ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul]
    simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofReal_re, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofReal_im]
    ring

/-- `ε_n³ = e^{-γ/ν}ν^{Re κ - 5 - 2σ₀}/(2|C₀|)` (`eq:st18-t00764`). -/
theorem amplitude_cube {n : ℕ} (hν : 0 < F.ν n) :
    F.amplitude n ^ 3 =
      Real.exp (-(F.growth / F.ν n)) * F.ν n ^ (F.κ.re - 5 - 2 * F.σ₀) / (2 * ‖F.C₀‖) := by
  have hX : 0 ≤ Real.exp (-(F.growth / F.ν n)) * F.ν n ^ (F.κ.re - 5 - 2 * F.σ₀) /
      (2 * ‖F.C₀‖) := by
    have := Real.rpow_pos_of_pos hν (F.κ.re - 5 - 2 * F.σ₀)
    have := Real.exp_pos (-(F.growth / F.ν n))
    positivity
  unfold amplitude
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
  norm_num

/-- `2ρ_{ν,ε}(σ)|N_ν| = ν^{2(σ-σ₀)}/|C₀|`, with `|N_ν| = e^{γ/ν - Re κ log ν}`. -/
theorem twice_returnScale_mul_exp (hC : F.C₀ ≠ 0) {n : ℕ} (hν : 0 < F.ν n) (σ : ℝ) :
    2 * F.returnScale n σ * Real.exp (F.growth / F.ν n - F.κ.re * Real.log (F.ν n)) =
      Real.exp (Real.log (F.ν n) * (2 * (σ - F.σ₀))) / ‖F.C₀‖ := by
  have hCn : ‖F.C₀‖ ≠ 0 := norm_ne_zero_iff.mpr hC
  have hsq : F.ν n ^ 2 = Real.exp (Real.log (F.ν n) * 2) := by
    rw [show Real.log (F.ν n) * 2 = Real.log (F.ν n) + Real.log (F.ν n) by ring,
      Real.exp_add, Real.exp_log hν]
    ring
  unfold returnScale spacing
  rw [F.amplitude_cube hν, Real.rpow_def_of_pos hν, Real.rpow_def_of_pos hν, hsq]
  have e : ∀ a b c d e : ℝ, Real.exp a * Real.exp b * Real.exp c * Real.exp d * Real.exp e =
      Real.exp (a + b + c + d + e) := by
    intro a b c d e
    simp only [Real.exp_add]
  calc 2 * (Real.exp (-(F.growth / F.ν n)) * Real.exp (Real.log (F.ν n) *
          (F.κ.re - 5 - 2 * F.σ₀)) / (2 * ‖F.C₀‖) *
          Real.exp (Real.log (F.ν n) * (3 + 2 * σ)) / (Real.exp (Real.log (F.ν n) * 2))⁻¹) *
          Real.exp (F.growth / F.ν n - F.κ.re * Real.log (F.ν n))
        = Real.exp (-(F.growth / F.ν n)) * Real.exp (Real.log (F.ν n) *
            (F.κ.re - 5 - 2 * F.σ₀)) * Real.exp (Real.log (F.ν n) * (3 + 2 * σ)) *
            Real.exp (Real.log (F.ν n) * 2) *
            Real.exp (F.growth / F.ν n - F.κ.re * Real.log (F.ν n)) / ‖F.C₀‖ := by
          field_simp
    _ = Real.exp (-(F.growth / F.ν n) + Real.log (F.ν n) * (F.κ.re - 5 - 2 * F.σ₀) +
            Real.log (F.ν n) * (3 + 2 * σ) + Real.log (F.ν n) * 2 +
            (F.growth / F.ν n - F.κ.re * Real.log (F.ν n))) / ‖F.C₀‖ := by rw [e]
    _ = Real.exp (Real.log (F.ν n) * (2 * (σ - F.σ₀))) / ‖F.C₀‖ := by
          congr 2
          ring

/-- `C₀e^{-i arg C₀} = |C₀|`. -/
theorem coeff_mul_exp_neg_arg :
    F.C₀ * Complex.exp (-(Complex.arg F.C₀ : ℂ) * I) = (‖F.C₀‖ : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I F.C₀]
  rw [mul_assoc, ← Complex.exp_add]
  simp

/-- On the phase-locked sequence (`ω < 0`, so `sign ω = -1`):
`tr K₀(σ) = ν^{2(σ-σ₀)}Re(𝒞(σ)e^{-i arg C₀})/|C₀|`. -/
theorem trace_K0_phase (hC : F.C₀ ≠ 0) (hω : F.frequency < 0) {n : ℕ} (hν : 0 < F.ν n)
    (hphase : F.frequency / F.ν n - F.κ.im * Real.log (F.ν n) + Complex.arg F.C₀ =
      2 * Real.pi * Real.sign F.frequency * n) (σ : ℝ) :
    (F.K0 n σ).trace = Real.exp (Real.log (F.ν n) * (2 * (σ - F.σ₀))) / ‖F.C₀‖ *
      (F.coeff σ * Complex.exp (-(Complex.arg F.C₀ : ℂ) * I)).re := by
  rw [Real.sign_of_neg hω] at hphase
  have hx : F.frequency / F.ν n - F.κ.im * Real.log (F.ν n) =
      -(Complex.arg F.C₀) + (-(n : ℤ) : ℤ) * (2 * Real.pi) := by
    push_cast
    linarith
  have hexp : Complex.exp (((F.frequency / F.ν n - F.κ.im * Real.log (F.ν n) : ℝ) : ℂ) * I) =
      Complex.exp (-(Complex.arg F.C₀ : ℂ) * I) := by
    rw [hx]
    push_cast
    rw [show (-(Complex.arg F.C₀ : ℂ) + -(n : ℂ) * (2 * (Real.pi : ℂ))) * I =
        -(Complex.arg F.C₀ : ℂ) * I + ((-(n : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [F.trace_K0, F.gauge_eq hν, hexp, ← Complex.ofReal_exp,
    ← F.twice_returnScale_mul_exp hC hν σ]
  rw [show F.coeff σ * (((Real.exp (F.growth / F.ν n - F.κ.re * Real.log (F.ν n)) : ℝ) : ℂ) *
      Complex.exp (-(Complex.arg F.C₀ : ℂ) * I)) =
      ((Real.exp (F.growth / F.ν n - F.κ.re * Real.log (F.ν n)) : ℝ) : ℂ) *
        (F.coeff σ * Complex.exp (-(Complex.arg F.C₀ : ℂ) * I)) by ring, Complex.re_ofReal_mul]
  have hCn : ‖F.C₀‖ ≠ 0 := norm_ne_zero_iff.mpr hC
  field_simp

/-- `|N_ν| = e^{γ/ν - Re κ log ν}`. -/
theorem norm_gauge {n : ℕ} (hν : 0 < F.ν n) :
    ‖F.gauge n‖ = Real.exp (F.growth / F.ν n - F.κ.re * Real.log (F.ν n)) := by
  rw [F.gauge_eq hν, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp,
    Complex.ofReal_re, mul_one]

/-- The points of the window are within `1/(2ℓ_n)` of `σ₀`. -/
theorem abs_sub_le_of_mem_window {n : ℕ} {σ : ℝ}
    (hσ : σ ∈ F.window n) : |σ - F.σ₀| ≤ 1 / (2 * F.ell n) := by
  obtain ⟨hl, hr⟩ := hσ
  unfold point at hl hr
  rw [abs_le]
  constructor
  · have : -1 / (2 * F.ell n) = -(1 / (2 * F.ell n)) := by ring
    linarith
  · linarith

/-- `ℓ_n = -log ν_n > 0` once `0 < ν_n < 1`. -/
theorem ell_eq_neg_log {n : ℕ} (hν : 0 < F.ν n) (hν1 : F.ν n < 1) :
    F.ell n = -Real.log (F.ν n) := by
  unfold ell
  exact abs_of_neg (Real.log_neg hν hν1)

end ConstructionData

open ConstructionData in
/-- `𝒞` is continuous at `σ₀` (C1 and the proved continuity of `𝓛`). -/
theorem continuousAt_coeff_of_C1 {F : ConstructionData} (h1 : StepReferenceChoice F) :
    ContinuousAt F.coeff F.σ₀ ∧ ContinuousAt F.planar.couplingL F.σ₀ := by
  obtain ⟨href, -, hσ₀, -, hJ⟩ := h1
  have hlam : F.planar.eigenvalue ≠ 0 := fun h => by
    have := href.eigenpair.re_pos
    rw [h] at this
    simp at this
  have hL := F.planar.continuousAt_couplingL hlam (by linarith [hσ₀.1] : -(5 / 2 : ℝ) < F.σ₀)
  exact ⟨(continuousAt_const.mul hL).mul hJ, hL⟩

/-- **Step C4 is proved** from C1 and C2: `tr K₀(σ₀ + z/(2ℓ_n)) → e^{-z}` uniformly for
`|z| ≤ 1` (`eq:st18-t00765`). -/
theorem stepGainTrace_of {F : ConstructionData} (h1 : StepReferenceChoice F)
    (h2 : StepPhaseLocked F) : StepGainTrace F := by
  have hcoeff := (continuousAt_coeff_of_C1 h1).1
  obtain ⟨-, hfreq, -, hC, -⟩ := h1
  intro δ hδ
  have hCpos : 0 < ‖F.C₀‖ := norm_pos_iff.mpr hC
  set ε' : ℝ := δ * ‖F.C₀‖ / Real.exp 1 with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.mp hcoeff ε' hε'pos
  have hν1 : ∀ᶠ n in atTop, F.ν n < 1 := h2.2.1.eventually (Iio_mem_nhds one_pos)
  have hell : ∀ᶠ n in atTop, 1 / (2 * η) < F.ell n :=
    (ConstructionData.ell_tendsto h2).eventually (eventually_gt_atTop _)
  filter_upwards [hν1, hell, h2.2.2] with n hn1 hnell hphase z hz
  have hν := h2.1 n
  have hlog : Real.log (F.ν n) < 0 := Real.log_neg hν hn1
  have hellv := F.ell_eq_neg_log hν hn1
  have hellpos : 0 < F.ell n := by rw [hellv]; linarith
  rw [F.trace_K0_phase hC hfreq.2 hν hphase]
  have hexpo : Real.log (F.ν n) * (2 * (F.point n z - F.σ₀)) = -z := by
    unfold ConstructionData.point
    rw [hellv]
    have hlog0 : Real.log (F.ν n) ≠ 0 := hlog.ne
    field_simp
    ring
  rw [hexpo]
  have hdist : dist (F.point n z) F.σ₀ < η := by
    rw [Real.dist_eq]
    unfold ConstructionData.point
    rw [show F.σ₀ + z / (2 * F.ell n) - F.σ₀ = z / (2 * F.ell n) by ring, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * F.ell n), div_lt_iff₀ (by positivity)]
    have hz1 : |z| ≤ 1 := abs_le.mpr ⟨hz.1, hz.2⟩
    have h2η : 0 < 2 * η := by positivity
    have : 1 < 2 * η * F.ell n := by
      rw [div_lt_iff₀ h2η] at hnell
      linarith
    nlinarith
  have hc : ‖F.coeff (F.point n z) - F.C₀‖ < ε' := by
    have := hball hdist
    rwa [dist_eq_norm] at this
  set u : ℂ := Complex.exp (-(Complex.arg F.C₀ : ℂ) * I) with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, show -(Complex.arg F.C₀ : ℂ) * I = ((-(Complex.arg F.C₀) : ℝ) : ℂ) * I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hC0u : (F.C₀ * u).re = ‖F.C₀‖ := by
    rw [hudef, F.coeff_mul_exp_neg_arg, Complex.ofReal_re]
  have hident : Real.exp (-z) / ‖F.C₀‖ * (F.coeff (F.point n z) * u).re - Real.exp (-z) =
      Real.exp (-z) / ‖F.C₀‖ * ((F.coeff (F.point n z) - F.C₀) * u).re := by
    rw [sub_mul, Complex.sub_re, hC0u]
    field_simp
  rw [hident, abs_mul, abs_of_nonneg (by positivity)]
  have hre : |((F.coeff (F.point n z) - F.C₀) * u).re| ≤ ‖F.coeff (F.point n z) - F.C₀‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, hu, mul_one]
  have hez : Real.exp (-z) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [hz.1])
  calc Real.exp (-z) / ‖F.C₀‖ * |((F.coeff (F.point n z) - F.C₀) * u).re|
      ≤ Real.exp 1 / ‖F.C₀‖ * ε' :=
        mul_le_mul (div_le_div_of_nonneg_right hez hCpos.le) (hre.trans hc.le)
          (abs_nonneg _) (by positivity)
    _ = δ := by
        rw [hε']
        field_simp

/-- **Step C5 is proved** from C1 and C2: the entries of the explicit `K₀` are bounded on the
window uniformly in `n` (lines 13658–13659). -/
theorem stepGainBound_of {F : ConstructionData} (h1 : StepReferenceChoice F)
    (h2 : StepPhaseLocked F) : StepGainBound F := by
  obtain ⟨-, hL⟩ := continuousAt_coeff_of_C1 h1
  obtain ⟨-, -, -, hC, hJ⟩ := h1
  have hCpos : 0 < ‖F.C₀‖ := norm_pos_iff.mpr hC
  obtain ⟨η₁, hη₁, hL1⟩ := Metric.continuousAt_iff.mp hL 1 one_pos
  obtain ⟨η₂, hη₂, hJ1⟩ := Metric.continuousAt_iff.mp hJ 1 one_pos
  set η : ℝ := min η₁ η₂ with hηdef
  have hη : 0 < η := lt_min hη₁ hη₂
  set A : ℝ := ‖F.planar.couplingL F.σ₀‖ + 1 with hA
  set B : ℝ := ‖F.planar.mellinJ F.σ₀‖ + 1 with hB
  refine ⟨(63 * Real.pi / 64) * (Real.exp 1 / (2 * ‖F.C₀‖)) * A * B, ?_⟩
  have hν1 : ∀ᶠ n in atTop, F.ν n < 1 := h2.2.1.eventually (Iio_mem_nhds one_pos)
  have hell : ∀ᶠ n in atTop, 1 / (2 * η) < F.ell n :=
    (ConstructionData.ell_tendsto h2).eventually (eventually_gt_atTop _)
  filter_upwards [hν1, hell] with n hn1 hnell σ hσ i j
  have hν := h2.1 n
  have hlog : Real.log (F.ν n) < 0 := Real.log_neg hν hn1
  have hellv := F.ell_eq_neg_log hν hn1
  have hellpos : 0 < F.ell n := by rw [hellv]; linarith
  have hσd := F.abs_sub_le_of_mem_window hσ
  have hdist : dist σ F.σ₀ < η := by
    rw [Real.dist_eq]
    refine hσd.trans_lt ?_
    have h2η : 0 < 2 * η := by positivity
    rw [div_lt_iff₀ h2η] at hnell
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hLb : ‖F.planar.couplingL σ‖ ≤ A := by
    have h := hL1 (hdist.trans_le (min_le_left _ _))
    rw [dist_eq_norm] at h
    have := norm_le_norm_add_norm_sub' (F.planar.couplingL σ) (F.planar.couplingL F.σ₀)
    rw [hA]
    linarith
  have hJb : ‖F.planar.mellinJ σ‖ ≤ B := by
    have h := hJ1 (hdist.trans_le (min_le_right _ _))
    rw [dist_eq_norm] at h
    have := norm_le_norm_add_norm_sub' (F.planar.mellinJ σ) (F.planar.mellinJ F.σ₀)
    rw [hB]
    linarith
  set a : ℝ := F.growth / F.ν n - F.κ.re * Real.log (F.ν n) with hadef
  have hscale := F.twice_returnScale_mul_exp hC hν σ
  have hexpo : Real.log (F.ν n) * (2 * (σ - F.σ₀)) ≤ 1 := by
    have h1' : |Real.log (F.ν n) * (2 * (σ - F.σ₀))| ≤ 1 := by
      rw [abs_mul, abs_of_neg hlog, abs_mul, abs_two, ← hellv]
      calc F.ell n * (2 * |σ - F.σ₀|) ≤ F.ell n * (2 * (1 / (2 * F.ell n))) := by
            gcongr
        _ = 1 := by field_simp
    exact (le_abs_self _).trans h1'
  have hρa : F.returnScale n σ * Real.exp a ≤ Real.exp 1 / (2 * ‖F.C₀‖) := by
    have h := hscale
    have he : Real.exp (Real.log (F.ν n) * (2 * (σ - F.σ₀))) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr hexpo
    rw [le_div_iff₀ (by positivity)]
    have : 2 * F.returnScale n σ * Real.exp a * ‖F.C₀‖ =
        Real.exp (Real.log (F.ν n) * (2 * (σ - F.σ₀))) := by
      rw [h]
      field_simp
    nlinarith
  have hρ : 0 ≤ F.returnScale n σ := by
    have hpos : 0 < 2 * F.returnScale n σ * Real.exp a := by
      rw [hscale]
      positivity
    have := Real.exp_pos a
    rcases le_or_gt 0 (F.returnScale n σ) with h | h
    · exact h
    · nlinarith
  have hN := F.norm_gauge hν
  have hgA : ∀ i, |F.gainA n σ i| ≤ (63 * Real.pi / 64) * F.returnScale n σ *
      ‖F.planar.couplingL σ‖ := by
    have hc : 0 ≤ (63 * Real.pi / 64) * F.returnScale n σ := by positivity
    intro i
    fin_cases i
    · simp only [ConstructionData.gainA, Fin.zero_eta, Matrix.cons_val_zero]
      rw [show -(63 * Real.pi / 64) * F.returnScale n σ * (F.planar.couplingL σ).re =
        -((63 * Real.pi / 64) * F.returnScale n σ * (F.planar.couplingL σ).re) by ring,
        abs_neg, abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc
    · simp only [ConstructionData.gainA, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [show -(63 * Real.pi / 64) * F.returnScale n σ * (F.planar.couplingL σ).im =
        -((63 * Real.pi / 64) * F.returnScale n σ * (F.planar.couplingL σ).im) by ring,
        abs_neg, abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) hc
  have hgB : ∀ j, |F.gainB n σ j| ≤ Real.exp a * ‖F.planar.mellinJ σ‖ := by
    have hNJ : ‖F.gauge n * F.planar.mellinJ σ‖ = Real.exp a * ‖F.planar.mellinJ σ‖ := by
      rw [norm_mul, hN]
    intro j
    fin_cases j
    · simp only [ConstructionData.gainB, Fin.zero_eta, Matrix.cons_val_zero]
      rw [← hNJ]
      exact Complex.abs_im_le_norm _
    · simp only [ConstructionData.gainB, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← hNJ]
      exact Complex.abs_re_le_norm _
  show |F.gainA n σ i * F.gainB n σ j| ≤ _
  rw [abs_mul]
  have hLn := norm_nonneg (F.planar.couplingL σ)
  have hJn := norm_nonneg (F.planar.mellinJ σ)
  have hea := Real.exp_pos a
  calc |F.gainA n σ i| * |F.gainB n σ j|
      ≤ ((63 * Real.pi / 64) * F.returnScale n σ * ‖F.planar.couplingL σ‖) *
          (Real.exp a * ‖F.planar.mellinJ σ‖) :=
        mul_le_mul (hgA i) (hgB j) (abs_nonneg _) (by positivity)
    _ = (63 * Real.pi / 64) * (F.returnScale n σ * Real.exp a) *
          ‖F.planar.couplingL σ‖ * ‖F.planar.mellinJ σ‖ := by ring
    _ ≤ (63 * Real.pi / 64) * (Real.exp 1 / (2 * ‖F.C₀‖)) * A * B := by
        gcongr

end UnforcedLeray.Blueprint
