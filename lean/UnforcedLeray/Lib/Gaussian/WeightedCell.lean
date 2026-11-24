import UnforcedLeray.Lib.Gaussian.PeriodizationCell
import UnforcedLeray.Lib.Gaussian.Absorb
import UnforcedLeray.Lib.Gaussian.GammaToolkit

/-!
# Weighted cell bounds for periodized Gaussians (INF22 G7, lemma 6, weighted part)


target G7 lemma 6: "weighted cell `L²` and `L^∞` bounds from Gaussian translate bounds, uniform in
`c ≥ 2` and `1 ≤ a ≤ c²`" (B0147, tex 2217–2234: "the same holds with any fixed transverse weight
measured in units of `√a`"; B0894, tex 14002–14016: the periodized mass-one Gaussian has uniformly
bounded weighted norms).

The unweighted sup and cell `L²` bounds are `norm_periodize_le_of_gauss` and
`lintegral_cell_sq_norm_periodize_le_of_gauss`. Here, for every fixed `m ≥ 0`, with a constant
`K_m` depending only on `m`, and for `‖f(q,η)‖ ≤ A e^{-(q²+η²)/(4a)}`, `0 < a ≤ c²`:
* `weight_mul_norm_periodize_le_of_gauss`: `(1 + η²/a)^m ‖P_c f(q,η)‖ ≤ K_m A`;
* `lintegral_cell_weight_sq_norm_periodize_le_of_gauss`:
  `∫_{[0,c)×ℝ} (1 + η²/a)^m ‖P_c f‖² ≤ K_m A² a`;
* `jbracket_mul_norm_periodize_le_of_gauss`,
  `lintegral_cell_jbracket_sq_norm_periodize_le_of_gauss`:
  in the fixed weight `⟨η⟩^{2m} = (1+η²)^m`, for `1 ≤ a ≤ c²`,
  `(1+η²)^m ‖P_c f‖ ≤ K_m A a^m` and `∫_cell (1+η²)^m ‖P_c f‖² ≤ K_m A² a^{1+m}`
  (i.e. `‖⟨η⟩^m P_c f‖_{L²(cell)}² ≤ K_m A² a^{1+m}`).
The general device is `lintegral_cell_weight_sq_norm_periodize_le`: a weighted sup bound
`w ‖P_c f‖ ≤ B` gives `∫_cell w ‖P_c f‖² ≤ B ∫_{ℝ²} ‖f‖`. Integrals are lower integrals, which need
no measurability of `P_c f`; only `f` is assumed `AEStronglyMeasurable`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Set Real
open scoped ENNReal

/-! ### Polynomial weights against a Gaussian -/

/-- `(1+u)^m e^{-u/4} ≤ K_m` for `u ≥ 0`, `m ≥ 0`. -/
theorem one_add_rpow_mul_exp_neg_quarter_le {m : ℝ} (hm : 0 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 0 ≤ u → (1 + u) ^ m * Real.exp (-u / 4) ≤ K := by
  obtain ⟨C, hC0, hC⟩ := rpow_mul_exp_neg_le hm
  refine ⟨2 ^ m * (1 + 4 ^ m * C), by positivity, fun u hu => ?_⟩
  have h1 := one_add_rpow_le hm hu
  have he : 0 < Real.exp (-u / 4) := Real.exp_pos _
  have he1 : Real.exp (-u / 4) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  have h2 : u ^ m * Real.exp (-u / 4) ≤ 4 ^ m * C := by
    have h := hC (u / 4) (by positivity)
    rw [Real.div_rpow hu (by norm_num), show -(u / 4) = -u / 4 by ring, div_mul_eq_mul_div,
      div_le_iff₀ h4] at h
    linarith
  have hum : 0 ≤ u ^ m := by positivity
  calc (1 + u) ^ m * Real.exp (-u / 4) ≤ 2 ^ m * (1 + u ^ m) * Real.exp (-u / 4) :=
        mul_le_mul_of_nonneg_right h1 he.le
    _ = 2 ^ m * (Real.exp (-u / 4) + u ^ m * Real.exp (-u / 4)) := by ring
    _ ≤ 2 ^ m * (1 + 4 ^ m * C) := by gcongr

/-- `(1+η²)^m ≤ a^m (1+η²/a)^m` for `a ≥ 1`, `m ≥ 0`. -/
theorem one_add_sq_rpow_le_scaled {m a : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) (η : ℝ) :
    (1 + η ^ 2) ^ m ≤ a ^ m * (1 + η ^ 2 / a) ^ m := by
  have ha0 : 0 < a := by linarith
  rw [← Real.mul_rpow ha0.le (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ hm
  rw [mul_add, mul_one, mul_div_cancel₀ _ ha0.ne']
  linarith

section Bounds

variable {E : Type*} [NormedAddCommGroup E]

omit [NormedAddCommGroup E] in
theorem nonneg_of_gauss_bound {F : Type*} [NormedAddCommGroup F] {f : ℝ × ℝ → F} {A a : ℝ}
    (hf : ∀ z : ℝ × ℝ, ‖f z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) : 0 ≤ A := by
  have h := hf 0
  simp only [Prod.fst_zero, Prod.snd_zero] at h
  norm_num at h
  exact (norm_nonneg _).trans h

/-- **G7, lemma 6 (weighted sup part; B0147).** For every `m ≥ 0` there is `K_m` such that
`‖f(q,η)‖ ≤ A e^{-(q²+η²)/(4a)}` with `0 < a ≤ c²` implies
`(1 + η²/a)^m ‖P_c f(q,η)‖ ≤ K_m A`, uniformly in `c`, `a`, `q`, `η`. -/
theorem weight_mul_norm_periodize_le_of_gauss {m : ℝ} (hm : 0 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ × ℝ → E) (A a c : ℝ), 0 < a → a ≤ c ^ 2 →
      (∀ z : ℝ × ℝ, ‖f z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) →
      ∀ z : ℝ × ℝ, (1 + z.2 ^ 2 / a) ^ m * ‖periodize c f z‖ ≤ K * A := by
  obtain ⟨K, hK0, hK⟩ := one_add_rpow_mul_exp_neg_quarter_le hm
  refine ⟨10 * K, by positivity, fun f A a c ha hac hf z => ?_⟩
  have hA := nonneg_of_gauss_bound hf
  have h := norm_periodize_le_of_gauss ha hac hf z
  have hu : 0 ≤ z.2 ^ 2 / a := by positivity
  have hw := hK (z.2 ^ 2 / a) hu
  have he : Real.exp (-z.2 ^ 2 / (4 * a)) = Real.exp (-(z.2 ^ 2 / a) / 4) := by
    congr 1; ring
  calc (1 + z.2 ^ 2 / a) ^ m * ‖periodize c f z‖
      ≤ (1 + z.2 ^ 2 / a) ^ m * (10 * A * Real.exp (-z.2 ^ 2 / (4 * a))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 10 * A * ((1 + z.2 ^ 2 / a) ^ m * Real.exp (-(z.2 ^ 2 / a) / 4)) := by rw [he]; ring
    _ ≤ 10 * A * K := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = 10 * K * A := by ring

/-- **G7, lemma 6 (fixed weight `⟨η⟩^{2m}`, sup part).** For `1 ≤ a ≤ c²`:
`(1+η²)^m ‖P_c f(q,η)‖ ≤ K_m A a^m`. -/
theorem jbracket_mul_norm_periodize_le_of_gauss {m : ℝ} (hm : 0 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ × ℝ → E) (A a c : ℝ), 1 ≤ a → a ≤ c ^ 2 →
      (∀ z : ℝ × ℝ, ‖f z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) →
      ∀ z : ℝ × ℝ, (1 + z.2 ^ 2) ^ m * ‖periodize c f z‖ ≤ K * A * a ^ m := by
  obtain ⟨K, hK0, hK⟩ := weight_mul_norm_periodize_le_of_gauss (E := E) hm
  refine ⟨K, hK0, fun f A a c ha hac hf z => ?_⟩
  have ha0 : 0 < a := by linarith
  have hw := one_add_sq_rpow_le_scaled hm ha z.2
  have hP := hK f A a c ha0 hac hf z
  have ham : 0 ≤ a ^ m := by positivity
  calc (1 + z.2 ^ 2) ^ m * ‖periodize c f z‖
      ≤ a ^ m * (1 + z.2 ^ 2 / a) ^ m * ‖periodize c f z‖ :=
        mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = a ^ m * ((1 + z.2 ^ 2 / a) ^ m * ‖periodize c f z‖) := by ring
    _ ≤ a ^ m * (K * A) := mul_le_mul_of_nonneg_left hP ham
    _ = K * A * a ^ m := by ring

/-- **G7, lemma 6 (general weighted cell device).** If `w ≥ 0` and `w(z)‖P_c f(z)‖ ≤ B` for all
`z`, then `∫_{[0,c)×ℝ} w ‖P_c f‖² ≤ B ∫_{ℝ²} ‖f‖` (lower integrals), for `c > 0`. -/
theorem lintegral_cell_weight_sq_norm_periodize_le {f : ℝ × ℝ → E} {c B : ℝ} (hc : 0 < c)
    (hfm : AEStronglyMeasurable f) (w : ℝ × ℝ → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hB : ∀ z, w z * ‖periodize c f z‖ ≤ B) :
    ∫⁻ z in cell c, ENNReal.ofReal (w z) * ‖periodize c f z‖ₑ ^ 2 ≤
      ENNReal.ofReal B * ∫⁻ z, ‖f z‖ₑ := by
  have hpt : ∀ z : ℝ × ℝ, ENNReal.ofReal (w z) * ‖periodize c f z‖ₑ ^ 2 ≤
      ENNReal.ofReal B * ∑' n : ℤ, ‖f (z - shiftVec c n)‖ₑ := by
    intro z
    have h1 : ENNReal.ofReal (w z) * ‖periodize c f z‖ₑ ^ 2 =
        ENNReal.ofReal (w z * ‖periodize c f z‖) * ‖periodize c f z‖ₑ := by
      rw [ENNReal.ofReal_mul (hw z), ofReal_norm]
      ring
    rw [h1]
    gcongr
    · exact hB z
    · rw [periodize_eq]; exact enorm_tsum_le_tsum_enorm
  have hmeas : ∀ n : ℤ, AEMeasurable (fun z => ‖f (z - shiftVec c n)‖ₑ)
      (volume.restrict (cell c)) := fun n =>
    ((hfm.comp_measurePreserving (measurePreserving_sub_right volume (shiftVec c n))).enorm).restrict
  calc ∫⁻ z in cell c, ENNReal.ofReal (w z) * ‖periodize c f z‖ₑ ^ 2
      ≤ ∫⁻ z in cell c, ENNReal.ofReal B * ∑' n : ℤ, ‖f (z - shiftVec c n)‖ₑ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal B * ∑' n : ℤ, ∫⁻ z in cell c, ‖f (z - shiftVec c n)‖ₑ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeas]
    _ = ENNReal.ofReal B * ∫⁻ z, ‖f z‖ₑ := by
        rw [tsum_setLIntegral_cell_translate (fun w => ‖f w‖ₑ) hc]

/-- `∫_{ℝ²} ‖f‖ ≤ 4πaA` under the Gaussian bound `‖f(z)‖ ≤ A e^{-|z|²/(4a)}`. -/
theorem lintegral_enorm_le_of_gauss {f : ℝ × ℝ → E} {A a : ℝ} (ha : 0 < a)
    (hf : ∀ z : ℝ × ℝ, ‖f z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) :
    ∫⁻ z, ‖f z‖ₑ ≤ ENNReal.ofReal (A * (4 * π * a)) := by
  have hA := nonneg_of_gauss_bound hf
  have hint := (integrable_gauss_plane ha).const_mul A
  calc ∫⁻ z, ‖f z‖ₑ
      ≤ ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) := by
        refine lintegral_mono fun z => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hf z)
    _ = ENNReal.ofReal (A * (4 * π * a)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun z => by positivity)]
        rw [integral_const_mul, integral_gauss_plane ha]

/-- **G7, lemma 6 (weighted cell `L²` part; B0147, B0894).** For every `m ≥ 0` there is `K_m`
such that `‖f(q,η)‖ ≤ A e^{-(q²+η²)/(4a)}` with `0 < a ≤ c²`, `c > 0`, implies
`∫_{[0,c)×ℝ} (1 + η²/a)^m ‖P_c f‖² ≤ K_m A² a`, uniformly in `c` and `a`. -/
theorem lintegral_cell_weight_sq_norm_periodize_le_of_gauss {m : ℝ} (hm : 0 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ × ℝ → E) (A a c : ℝ), 0 < a → 0 < c → a ≤ c ^ 2 →
      AEStronglyMeasurable f →
      (∀ z : ℝ × ℝ, ‖f z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) →
      ∫⁻ z in cell c, ENNReal.ofReal ((1 + z.2 ^ 2 / a) ^ m) * ‖periodize c f z‖ₑ ^ 2 ≤
        ENNReal.ofReal (K * A ^ 2 * a) := by
  obtain ⟨K, hK0, hK⟩ := weight_mul_norm_periodize_le_of_gauss (E := E) hm
  refine ⟨4 * π * K, by positivity, fun f A a c ha hc hac hfm hf => ?_⟩
  have hA := nonneg_of_gauss_bound hf
  have hcell := lintegral_cell_weight_sq_norm_periodize_le hc hfm
    (fun z => (1 + z.2 ^ 2 / a) ^ m) (fun z => by positivity) (hK f A a c ha hac hf)
  refine hcell.trans ?_
  calc ENNReal.ofReal (K * A) * ∫⁻ z, ‖f z‖ₑ
      ≤ ENNReal.ofReal (K * A) * ENNReal.ofReal (A * (4 * π * a)) := by
        gcongr; exact lintegral_enorm_le_of_gauss ha hf
    _ = ENNReal.ofReal (4 * π * K * A ^ 2 * a) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-- **G7, lemma 6 (fixed weight `⟨η⟩^{2m}`, cell `L²` part).** For `1 ≤ a ≤ c²`, `c > 0`:
`∫_{[0,c)×ℝ} (1+η²)^m ‖P_c f‖² ≤ K_m A² a^{1+m}`, i.e.
`‖⟨η⟩^m P_c f‖²_{L²(cell)} ≤ K_m A² a^{1+m}`. -/
theorem lintegral_cell_jbracket_sq_norm_periodize_le_of_gauss {m : ℝ} (hm : 0 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ × ℝ → E) (A a c : ℝ), 1 ≤ a → 0 < c → a ≤ c ^ 2 →
      AEStronglyMeasurable f →
      (∀ z : ℝ × ℝ, ‖f z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) →
      ∫⁻ z in cell c, ENNReal.ofReal ((1 + z.2 ^ 2) ^ m) * ‖periodize c f z‖ₑ ^ 2 ≤
        ENNReal.ofReal (K * A ^ 2 * a ^ (1 + m)) := by
  obtain ⟨K, hK0, hK⟩ := lintegral_cell_weight_sq_norm_periodize_le_of_gauss (E := E) hm
  refine ⟨K, hK0, fun f A a c ha hc hac hfm hf => ?_⟩
  have ha0 : 0 < a := by linarith
  have hA := nonneg_of_gauss_bound hf
  calc ∫⁻ z in cell c, ENNReal.ofReal ((1 + z.2 ^ 2) ^ m) * ‖periodize c f z‖ₑ ^ 2
      ≤ ∫⁻ z in cell c, ENNReal.ofReal (a ^ m) *
          (ENNReal.ofReal ((1 + z.2 ^ 2 / a) ^ m) * ‖periodize c f z‖ₑ ^ 2) := by
        refine lintegral_mono fun z => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact one_add_sq_rpow_le_scaled hm ha z.2
    _ = ENNReal.ofReal (a ^ m) *
          ∫⁻ z in cell c, ENNReal.ofReal ((1 + z.2 ^ 2 / a) ^ m) * ‖periodize c f z‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (a ^ m) * ENNReal.ofReal (K * A ^ 2 * a) := by
        gcongr; exact hK f A a c ha0 hc hac hfm hf
    _ = ENNReal.ofReal (K * A ^ 2 * a ^ (1 + m)) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_add ha0, Real.rpow_one]
        congr 1; ring

end Bounds

end UnforcedLeray.Gaussian
