import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_2

/-!
# Transverse weight integral `SLTrans` (source 4934-4936)

Source `the November 2 reference manuscript` lines 4934-4936.  The `(q,η)`-factor
`avgμ c` has `η`-marginal Lebesgue measure (`Cyl.avgμ_univ_prod`), so the integral reduces to a
one-dimensional integral in `η`; the substitution `η = √(1+u) t` and the integrability of
`(1+t²)^{-m_Z}` give the bound with `C` the value of that integral.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The inverse squared transverse weight depends on the cell point only through `η`. -/
theorem slTrans_inv_sq_eq (mZ u : ℝ) (x : ℝ × ℝ) :
    (UnforcedLeray.Short.IIIa.transWeight mZ (u, x) ^ 2)⁻¹
      = (1 + (x.2 / Real.sqrt (1 + u)) ^ 2) ^ (-mZ) := by
  obtain ⟨q, η⟩ := x
  dsimp only
  have h0 : (0 : ℝ) ≤ 1 + (η / Real.sqrt (1 + u)) ^ 2 := by positivity
  have hpow : ∀ B : ℝ, 0 < B → (B ^ (mZ / 2)) ^ 2 = B ^ mZ := by
    intro B hB
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
    congr 1
    push_cast
    ring
  have hsq : UnforcedLeray.Short.IIIa.transWeight mZ (u, (q, η)) ^ 2
      = (1 + (η / Real.sqrt (1 + u)) ^ 2) ^ mZ := by
    unfold UnforcedLeray.Short.IIIa.transWeight
    exact hpow _ (by positivity)
  rw [hsq, Real.rpow_neg h0]

/-- The `η`-marginal of `avgμ c` is Lebesgue measure. -/
theorem slTrans_lintegral_snd {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x : ℝ × ℝ, f x.2 ∂(Cyl.avgμ c) = ∫⁻ η : ℝ, f η := by
  have hmap : (Cyl.avgμ c).map Prod.snd = volume := by
    refine Measure.ext fun B hB => ?_
    rw [Measure.map_apply measurable_snd hB, ← Set.univ_prod, Cyl.avgμ_univ_prod hc B]
  rw [← lintegral_map hf measurable_snd, hmap]

/-- **Transverse weight integral** (source 4934-4936): for `m_Z > 3/2` there is `C` with
`∫ W⁻² davgμ_c(q,η) ≤ C √(1+u)` for all `c > 0`, `u ≥ 0`. -/
theorem slTrans (mZ : ℝ) : SLTrans mZ := by
  unfold SLTrans
  intro hm
  have hG : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-mZ)) := by
    have h := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℝ)) (E := ℝ)
      (r := 2 * mZ) (by rw [Module.finrank_self, Nat.cast_one]; linarith)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
    rw [show (-(2 * mZ)) / 2 = -mZ by ring]
  refine ⟨∫ t : ℝ, (1 + t ^ 2) ^ (-mZ), fun c hc u hu => ?_⟩
  have hs : 0 < Real.sqrt (1 + u) := Real.sqrt_pos.2 (by linarith)
  have hint : ∫⁻ x : ℝ × ℝ,
      ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ (u, x) ^ 2)⁻¹) ∂(Cyl.avgμ c)
      = ∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + u)) ^ 2) ^ (-mZ)) := by
    simp_rw [slTrans_inv_sq_eq]
    exact slTrans_lintegral_snd hc
      (fun η : ℝ => ENNReal.ofReal ((1 + (η / Real.sqrt (1 + u)) ^ 2) ^ (-mZ)))
      (by fun_prop)
  have hI : Integrable (fun η : ℝ => (1 + (η / Real.sqrt (1 + u)) ^ 2) ^ (-mZ)) := by
    have h := hG.comp_mul_left' (inv_ne_zero hs.ne')
    refine h.congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [div_eq_inv_mul]
  have hnn : 0 ≤ᵐ[volume] (fun η : ℝ => (1 + (η / Real.sqrt (1 + u)) ^ 2) ^ (-mZ)) :=
    Filter.Eventually.of_forall (fun η : ℝ => by positivity)
  have key : ∫ η : ℝ, (1 + (η / Real.sqrt (1 + u)) ^ 2) ^ (-mZ)
      = |Real.sqrt (1 + u)| • ∫ t : ℝ, (1 + t ^ 2) ^ (-mZ) :=
    Measure.integral_comp_div (fun t : ℝ => (1 + t ^ 2) ^ (-mZ)) (Real.sqrt (1 + u))
  rw [hint, ← ofReal_integral_eq_lintegral_ofReal hI hnn, key, abs_of_pos hs, smul_eq_mul]
  apply le_of_eq
  congr 1
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
