import UnforcedLeray.Lib.Parabolic.Duhamel
import UnforcedLeray.Lib.Parabolic.TimeYoung
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The `L²` bound `‖ν ∂_i∂_j u‖₂ ≤ ‖f‖₂` on test functions (INF02 T6, BP-A)


and §5 target T6 (`norm_secondDerivOp_le`). Manuscript: the `q = 2` case of eq:free-stress-11
(`paper/main.tex` lines 7447–7477, blueprint unit B0423), with the constant independent of `ν`.

For tests `f, g` on `ℝ × ℝ^d` and `ν > 0`:
`|∫ g · ∂_i∂_j (H_ν ⋆ f)| ≤ ν⁻¹ ‖f‖₂ ‖g‖₂` (`enorm_pairing_secondDerivTest_le`).

Proof (no Calderón–Zygmund theory): for each time `t` and lag `s > 0` the spatial pairing
`∫ g(t,·) (G_{νs} ∗ ∂_i∂_j f(t-s,·))` is, by Fourier inversion of the Gaussian, bounded by
`∫ 4π²|ξ_i||ξ_j| e^{-4π²νs|ξ|²} |f̂(t-s,ξ)| |ĝ(t,ξ)| dξ`; the kernel has
`∫_0^∞ 4π²|ξ_i||ξ_j| e^{-4π²νs|ξ|²} ds ≤ ν⁻¹`; Young in time (`lintegral_time_conv_le`) and
Plancherel on each slice (`lintegral_enorm_fourier_sq`) conclude.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Complex
open scoped ENNReal NNReal ContDiff RealInnerProductSpace FourierTransform

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

/-- The slice Fourier transform `(s, ξ) ↦ ‖(f(s,·))^(ξ)‖ₑ`. -/
def sliceFT (f : PS d → ℝ) (p : ℝ × Euc d) : ℝ≥0∞ := ‖𝓕 (cplx fun x => f (p.1, x)) p.2‖ₑ

theorem measurable_sliceFT {f : PS d → ℝ} (hf : IsSTTest f) : Measurable (sliceFT f) :=
  (continuous_fourier_slice hf.continuous hf.2).enorm.measurable

/-- Plancherel on slices: `∫⁻ |sliceFT f|² = ∫⁻ |f|²`. -/
theorem lintegral_sliceFT_sq {f : PS d → ℝ} (hf : IsSTTest f) :
    ∫⁻ p, sliceFT f p ^ (2 : ℝ) ∂(volume.prod volume) = ∫⁻ X, ‖f X‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_prod _ ((measurable_sliceFT hf).pow_const _).aemeasurable]
  have h2 : ∫⁻ X : PS d, ‖f X‖ₑ ^ (2 : ℝ) = ∫⁻ s, ∫⁻ x, ‖f (s, x)‖ₑ ^ (2 : ℝ) :=
    lintegral_prod _ (hf.continuous.enorm.measurable.pow_const _).aemeasurable
  rw [h2]
  congr 1; funext s
  exact lintegral_enorm_fourier_sq (hf.slice_contDiff s) (hf.slice_hasCompactSupport s)

theorem eLpNorm_two_eq_sliceFT {f : PS d → ℝ} (hf : IsSTTest f) :
    eLpNorm f 2 volume = (∫⁻ p, sliceFT f p ^ (2 : ℝ) ∂(volume.prod volume)) ^ (1 / 2 : ℝ) := by
  rw [lintegral_sliceFT_sq hf, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num

/-- The time kernel `k(s, ξ) = 4π²|ξ_i||ξ_j| e^{-4π²νs|ξ|²}`. -/
def timeKernel (ν : ℝ) (i j : Fin d) (s : ℝ) (ξ : Euc d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(4 * π ^ 2 * (ν * s)) * ‖ξ‖ ^ 2) *
    (4 * π ^ 2 * |ξ.ofLp i| * |ξ.ofLp j|))

theorem measurable_timeKernel (ν : ℝ) (i j : Fin d) :
    Measurable (Function.uncurry (timeKernel (d := d) ν i j)) := by
  unfold timeKernel Function.uncurry
  refine Measurable.ennreal_ofReal ?_
  refine Measurable.mul (by fun_prop) ?_
  have hi : Measurable fun p : ℝ × Euc d => p.2.ofLp i :=
    ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp continuous_snd).measurable
  have hj : Measurable fun p : ℝ × Euc d => p.2.ofLp j :=
    ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).comp continuous_snd).measurable
  exact (measurable_const.mul hi.abs).mul hj.abs

/-- `∫_0^∞ k(s, ξ) ds ≤ ν⁻¹`. -/
theorem lintegral_timeKernel_le {ν : ℝ} (hν : 0 < ν) (i j : Fin d) (ξ : Euc d) :
    ∫⁻ s in Ioi 0, timeKernel ν i j s ξ ≤ ENNReal.ofReal ν⁻¹ := by
  set c : ℝ := 4 * π ^ 2 * |ξ.ofLp i| * |ξ.ofLp j| with hc
  have hi : |ξ.ofLp i| ≤ ‖ξ‖ := by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le ξ i
  have hj : |ξ.ofLp j| ≤ ‖ξ‖ := by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le ξ j
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [timeKernel]
  have hξ' : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set a : ℝ := 4 * π ^ 2 * ν * ‖ξ‖ ^ 2 with ha
  have hapos : 0 < a := by positivity
  have hrw : ∀ s, timeKernel ν i j s ξ = ENNReal.ofReal (Real.exp (-a * s) * c) := by
    intro s; unfold timeKernel; congr 2; rw [ha]; ring_nf
  simp_rw [hrw]
  have hint : IntegrableOn (fun s => Real.exp (-a * s) * c) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hapos).mul_const c
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun s => by
    positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_mul_const, integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  rw [show -1 / -a * c = c / a by field_simp, div_le_iff₀ hapos, hc, ha]
  have hij : |ξ.ofLp i| * |ξ.ofLp j| ≤ ‖ξ‖ ^ 2 := by
    rw [sq]; exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
  calc 4 * π ^ 2 * |ξ.ofLp i| * |ξ.ofLp j| = 4 * π ^ 2 * (|ξ.ofLp i| * |ξ.ofLp j|) := by ring
    _ ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by gcongr
    _ = ν⁻¹ * (4 * π ^ 2 * ν * ‖ξ‖ ^ 2) := by field_simp

section Pairing

variable {ν : ℝ} {f g : PS d → ℝ}

/-- The slice pairing `P(t,s) = ∫_x g(t,x) ∫_y causalHeat ν (s,y) A(t-s, x-y)`. -/
def slicePairing (ν : ℝ) (g A : PS d → ℝ) (t s : ℝ) : ℝ :=
  ∫ x, g (t, x) * ∫ y, causalHeat ν (s, y) * A (t - s, x - y)

/-- `|∫ causalHeat ν (s,·) A(r, x - ·)| ≤ M` and it vanishes when `A(r, ·) = 0`. -/
theorem abs_heatSlice_le (hν : 0 < ν) {A : PS d → ℝ} {M : ℝ} (hM : ∀ X, |A X| ≤ M) (s r : ℝ)
    (x : Euc d) : |∫ y, causalHeat ν (s, y) * A (r, x - y)| ≤ M := by
  rcases le_or_gt s 0 with hs | hs
  · simp only [causalHeat_of_nonpos ν (Y := (s, _)) hs, zero_mul, integral_zero, abs_zero]
    exact (abs_nonneg _).trans (hM (0, 0))
  · have hGi : Integrable (fun y : Euc d => causalHeat ν (s, y)) volume := by
      simp only [causalHeat_of_pos ν (Y := (s, _)) hs]
      exact Gaussian.integrable_gaussKernel (mul_pos hν hs)
    calc |∫ y, causalHeat ν (s, y) * A (r, x - y)|
        ≤ ∫ y, causalHeat ν (s, y) * M := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le (hGi.mul_const M) (Filter.Eventually.of_forall
            fun y => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (causalHeat_nonneg hν _)]
          exact mul_le_mul_of_nonneg_left (hM _) (causalHeat_nonneg hν _)
      _ = M := by rw [integral_mul_const, integral_causalHeat_slice hν hs, one_mul]

/-- **Per-time Fubini.** `∫_x g(t,x) (H_ν ⋆ A)(t,x) = ∫_s P(t,s)`. -/
theorem integral_slice_eq (hν : 0 < ν) (hg : IsSTTest g) {A : PS d → ℝ} (hA : IsSTTest A)
    (t : ℝ) :
    ∫ x, g (t, x) * duhamel ν A (t, x) = ∫ s, slicePairing ν g A t s := by
  obtain ⟨M, hM0, hM⟩ := hA.bounded
  obtain ⟨R, hR0, hR⟩ := hA.timeBound
  have e1 : ∀ x, g (t, x) * duhamel ν A (t, x) =
      ∫ s, g (t, x) * ∫ y, causalHeat ν (s, y) * A (t - s, x - y) := by
    intro x; rw [duhamel_eq_iterated hν hA.continuous hA.2, ← integral_const_mul]
  simp_rw [e1]
  set Q : Euc d × ℝ → ℝ := fun p => g (t, p.1) * ∫ y, causalHeat ν (p.2, y) * A (t - p.2, p.1 - y)
  have hQm : StronglyMeasurable Q := by
    have h1 : StronglyMeasurable fun q : (Euc d × ℝ) × Euc d =>
        causalHeat ν (q.1.2, q.2) * A (t - q.1.2, q.1.1 - q.2) := by
      refine Measurable.stronglyMeasurable ?_
      exact ((measurable_causalHeat ν).comp (measurable_fst.snd.prodMk measurable_snd)).mul
        (hA.continuous.measurable.comp ((measurable_const.sub measurable_fst.snd).prodMk
          (measurable_fst.fst.sub measurable_snd)))
    exact ((hg.continuous.comp (continuous_const.prodMk continuous_fst)).stronglyMeasurable).mul
      h1.integral_prod_right'
  have hint : Integrable (Function.uncurry fun (x : Euc d) (s : ℝ) =>
      g (t, x) * ∫ y, causalHeat ν (s, y) * A (t - s, x - y)) (volume.prod volume) := by
    have hgi : Integrable (fun x : Euc d => g (t, x)) volume :=
      (hg.slice_contDiff t).continuous.integrable_of_hasCompactSupport
        (hg.slice_hasCompactSupport t)
    have hind : Integrable ((Icc (t - R) (t + R)).indicator fun _ : ℝ => M) volume :=
      (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) (by simp))
    refine (hgi.norm.mul_prod hind).mono' hQm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    change |g (t, p.1) * ∫ y, causalHeat ν (p.2, y) * A (t - p.2, p.1 - y)| ≤
      ‖g (t, p.1)‖ * (Icc (t - R) (t + R)).indicator (fun _ : ℝ => M) p.2
    rw [abs_mul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    by_cases hp : p.2 ∈ Icc (t - R) (t + R)
    · rw [indicator_of_mem hp]; exact abs_heatSlice_le hν hM _ _ _
    · rw [indicator_of_notMem hp]
      have hz : ∀ y, A (t - p.2, p.1 - y) = 0 := by
        intro y; by_contra h
        have := hR _ h
        simp only at this
        obtain ⟨h1, h2⟩ := abs_le.1 this
        exact hp ⟨by linarith, by linarith⟩
      simp [hz]
  exact integral_integral_swap hint

/-- For `s > 0` the slice pairing is the Gaussian pairing of the slices. -/
theorem slicePairing_of_pos (ν : ℝ) (g A : PS d → ℝ) (t : ℝ) {s : ℝ} (hs : 0 < s) :
    slicePairing ν g A t s =
      ∫ x, g (t, x) * ∫ y, gaussKernel d (ν * s) y * A (t - s, x - y) := by
  unfold slicePairing
  congr 1; funext x; congr 1; congr 1; funext y
  rw [causalHeat_of_pos ν (Y := (s, y)) hs]

theorem slicePairing_of_nonpos (ν : ℝ) (g A : PS d → ℝ) (t : ℝ) {s : ℝ} (hs : s ≤ 0) :
    slicePairing ν g A t s = 0 := by
  unfold slicePairing
  simp [causalHeat_of_nonpos ν (Y := (s, _)) hs]

/-- **Fourier bound for the slice pairing.** -/
theorem enorm_slicePairing_le (hν : 0 < ν) (hf : IsSTTest f) (hg : IsSTTest g) (i j : Fin d)
    (t : ℝ) {s : ℝ} (hs : 0 < s) :
    ‖slicePairing ν g (sD2 i j f) t s‖ₑ ≤
      ∫⁻ ξ, timeKernel ν i j s ξ * sliceFT f (t - s, ξ) * sliceFT g (t, ξ) := by
  rw [slicePairing_of_pos ν g _ t hs]
  have hA := hf.sD2 i j
  have h := enorm_pairing_heat_le (mul_pos hν hs) (hg.slice_contDiff t).continuous
    (hg.slice_hasCompactSupport t) (hA.slice_contDiff (t - s)).continuous
    (hA.slice_hasCompactSupport (t - s))
  refine h.trans (le_of_eq ?_)
  congr 1; funext ξ
  have hslice : (fun x => sD2 i j f (t - s, x)) =
      fun y => fderiv ℝ (fun y' => fderiv ℝ (fun x => f (t - s, x)) y' (ev j)) y (ev i) := by
    funext y; exact sD2_slice hf i j (t - s) y
  rw [hslice, ← ofReal_norm, norm_fourier_second_deriv (hf.slice_contDiff (t - s))
    (hf.slice_hasCompactSupport (t - s)) i j ξ, timeKernel, sliceFT, sliceFT]
  simp only
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

/-- **INF02 T6, BP-A: the `L²` pairing bound.** For tests `f, g` on `ℝ × ℝ^d` and `ν > 0`,
`‖∫ g · ∂_i∂_j(H_ν ⋆ f)‖ₑ ≤ ν⁻¹ ‖f‖₂ ‖g‖₂`. -/
theorem enorm_pairing_secondDerivTest_le (hν : 0 < ν) (hf : IsSTTest f) (hg : IsSTTest g)
    (i j : Fin d) :
    ‖∫ X, g X * secondDerivTest ν i j f X‖ₑ ≤
      ENNReal.ofReal ν⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have hA := hf.sD2 i j
  have hcont : Continuous fun X => g X * secondDerivTest ν i j f X :=
    hg.continuous.mul (continuous_secondDerivTest hν hf i j)
  have hgD : Integrable (fun X => g X * secondDerivTest ν i j f X) volume :=
    hcont.integrable_of_hasCompactSupport hg.2.mul_right
  -- step 1: Fubini in `(t, x)` and per-time swap
  have h1 : ∫ X, g X * secondDerivTest ν i j f X =
      ∫ t, ∫ s, slicePairing ν g (sD2 i j f) t s := by
    refine (integral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Euc d))) _
      hgD).trans ?_
    congr 1; funext t
    exact integral_slice_eq hν hg hA t
  rw [h1]
  -- step 2: pass to lower integrals
  have h2 : ‖∫ t, ∫ s, slicePairing ν g (sD2 i j f) t s‖ₑ ≤
      ∫⁻ t, ∫⁻ s in Ioi 0, ∫⁻ ξ, timeKernel ν i j s ξ * sliceFT f (t - s, ξ) *
        sliceFT g (t, ξ) := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t => ?_)
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_mono fun s => ?_
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hs]
      exact enorm_slicePairing_le hν hf hg i j t hs
    · rw [indicator_of_notMem hs, slicePairing_of_nonpos ν g _ t (not_lt.1 hs), enorm_zero]
  refine h2.trans ?_
  -- steps 3–4: Young in time and Plancherel
  have h3 := lintegral_time_conv_le (μ := (volume : Measure (Euc d))) (measurable_sliceFT hf)
    (measurable_sliceFT hg) (measurable_timeKernel ν i j) (lintegral_timeKernel_le hν i j)
  refine h3.trans (le_of_eq ?_)
  rw [eLpNorm_two_eq_sliceFT hf, eLpNorm_two_eq_sliceFT hg]

end Pairing

end UnforcedLeray.Parabolic
