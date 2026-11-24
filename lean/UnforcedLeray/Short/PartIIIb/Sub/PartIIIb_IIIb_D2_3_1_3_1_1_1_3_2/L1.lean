import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# One-dimensional vertical integral (`PartIII-b:IIIb-D2/3/1/3/1/1/1/3/2/1`)

Source 3631-3646: `∫_ℝ (a²+u²)^{-k} du = c_k a^{1-2k}` with `k = 4+n`.
Proof: scale `u = a s` (`farVert_scale`), factor `(a²+a²s²)^{-k} = a^{-2k} (1+s²)^{-k}`,
and the remaining integral is finite by `integrable_rpow_neg_one_add_norm_sq` (`finrank ℝ ℝ = 1 < 2k`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Linear scaling on `ℝ` for lower integrals (copy of the scaling step used in the
neighbouring leaves). -/
theorem farVert_scale (H : ℝ → ℝ≥0∞) (hH : Measurable H) (R : ℝ) (hR : 0 < R) :
    ∫⁻ s, H (R * s) = ENNReal.ofReal R⁻¹ * ∫⁻ u, H u := by
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hR.ne'
  rw [Module.finrank_self, pow_one, abs_of_pos (inv_pos.2 hR)] at hmap
  have h1 : ∫⁻ s, H (R * s) = ∫⁻ y, H y ∂(Measure.map (fun x : ℝ => R • x) volume) := by
    rw [lintegral_map hH (measurable_const_smul R)]
    simp only [smul_eq_mul]
  rw [h1, hmap, lintegral_smul_measure, smul_eq_mul]

/-- The density `s ↦ (1+s²)^{-(4+n)}` is integrable on `ℝ`. -/
theorem farVert_integrable (n : ℕ) :
    Integrable (fun s : ℝ => (1 + s ^ 2) ^ (-(4 + (n : ℝ)))) := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 8 + 2 * (n : ℝ) := by
    rw [Module.finrank_self]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    linarith
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := (volume : Measure ℝ)) hr
  have e : ∀ s : ℝ, ((1 : ℝ) + ‖s‖ ^ 2) ^ (-(8 + 2 * (n : ℝ)) / 2) =
      (1 + s ^ 2) ^ (-(4 + (n : ℝ))) := by
    intro s
    rw [Real.norm_eq_abs, sq_abs, show -(8 + 2 * (n : ℝ)) / 2 = -(4 + (n : ℝ)) by ring]
  simpa only [e] using h

theorem farVert (n : ℕ) (hn : n ≤ 1) : ∃ c : ℝ, 0 ≤ c ∧ ∀ a : ℝ, 0 < a → ∫⁻ u : ℝ, ENNReal.ofReal ((a ^ 2 + u ^ 2) ^ (-(4 + (n : ℝ)))) ≤ ENNReal.ofReal (c * a ^ (-(7 + 2 * (n : ℝ)))) := by
  have hJfin : (∫⁻ s : ℝ, ENNReal.ofReal ((1 + s ^ 2) ^ (-(4 + (n : ℝ))))) < ⊤ :=
    (farVert_integrable n).lintegral_lt_top
  set J : ℝ≥0∞ := ∫⁻ s : ℝ, ENNReal.ofReal ((1 + s ^ 2) ^ (-(4 + (n : ℝ)))) with hJ
  refine ⟨J.toReal, ENNReal.toReal_nonneg, fun a ha => ?_⟩
  have hIeq : ENNReal.ofReal J.toReal = J := ENNReal.ofReal_toReal hJfin.ne
  have hmeas : Measurable (fun u : ℝ => ENNReal.ofReal ((a ^ 2 + u ^ 2) ^ (-(4 + (n : ℝ))))) := by
    apply Measurable.ennreal_ofReal
    fun_prop
  have hsc : ∫⁻ s : ℝ, ENNReal.ofReal ((a ^ 2 + (a * s) ^ 2) ^ (-(4 + (n : ℝ)))) =
      ENNReal.ofReal a⁻¹ * ∫⁻ u : ℝ, ENNReal.ofReal ((a ^ 2 + u ^ 2) ^ (-(4 + (n : ℝ)))) :=
    farVert_scale _ hmeas a ha
  have hpt : ∀ s : ℝ, ENNReal.ofReal ((a ^ 2 + (a * s) ^ 2) ^ (-(4 + (n : ℝ)))) =
      ENNReal.ofReal (a ^ (-(8 + 2 * (n : ℝ)))) * ENNReal.ofReal ((1 + s ^ 2) ^ (-(4 + (n : ℝ)))) := by
    intro s
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le (-(8 + 2 * (n : ℝ))))]
    congr 1
    have hfac : a ^ 2 + (a * s) ^ 2 = a ^ 2 * (1 + s ^ 2) := by ring
    have hp : (a ^ 2) ^ (-(4 + (n : ℝ))) = a ^ (-(8 + 2 * (n : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
      congr 1
      push_cast
      ring
    rw [hfac, Real.mul_rpow (by positivity) (by positivity), hp]
  have hpull : ∫⁻ s : ℝ, ENNReal.ofReal ((a ^ 2 + (a * s) ^ 2) ^ (-(4 + (n : ℝ)))) =
      ENNReal.ofReal (a ^ (-(8 + 2 * (n : ℝ)))) * J := by
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hexp : a * a ^ (-(8 + 2 * (n : ℝ))) = a ^ (-(7 + 2 * (n : ℝ))) := by
    have h' : a ^ (-(7 + 2 * (n : ℝ))) = a ^ ((1 : ℝ) + -(8 + 2 * (n : ℝ))) := by
      congr 1
      ring
    rw [h', Real.rpow_add ha, Real.rpow_one]
  have key : ∫⁻ u : ℝ, ENNReal.ofReal ((a ^ 2 + u ^ 2) ^ (-(4 + (n : ℝ)))) =
      ENNReal.ofReal (a ^ (-(7 + 2 * (n : ℝ)))) * J := by
    rw [← hexp]
    have hinv : ENNReal.ofReal a * ENNReal.ofReal a⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one]
    calc ∫⁻ u : ℝ, ENNReal.ofReal ((a ^ 2 + u ^ 2) ^ (-(4 + (n : ℝ))))
        = ENNReal.ofReal a * (ENNReal.ofReal a⁻¹ * ∫⁻ u : ℝ, ENNReal.ofReal ((a ^ 2 + u ^ 2) ^ (-(4 + (n : ℝ))))) := by
          rw [← mul_assoc, hinv, one_mul]
      _ = ENNReal.ofReal a * ∫⁻ s : ℝ, ENNReal.ofReal ((a ^ 2 + (a * s) ^ 2) ^ (-(4 + (n : ℝ)))) := by
          rw [hsc]
      _ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ (-(8 + 2 * (n : ℝ)))) * J) := by
          rw [hpull]
      _ = ENNReal.ofReal (a * a ^ (-(8 + 2 * (n : ℝ)))) * J := by
          rw [← mul_assoc, ENNReal.ofReal_mul ha.le]
  rw [key, ENNReal.ofReal_mul ENNReal.toReal_nonneg, hIeq, mul_comm]

end UnforcedLeray.Short.PartIIIb.Concrete
