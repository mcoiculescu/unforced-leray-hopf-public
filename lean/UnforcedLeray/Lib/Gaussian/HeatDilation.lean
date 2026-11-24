import UnforcedLeray.Lib.Gaussian.PeriodizationCell

/-!
# Heat dilation and the transverse second moment (INF22 G7, item 5)


target G7 item 5 and §2.10 row B0364 (tex 6788–6801): the functional
`Q_c(w) = -(2/π)∫_cell η² w` is invariant under `P_c` and under the heat dilation
`Z ↦ a^{-2} Z(x/√a)`; B0317/B0333 (tex 6113–6147, 6317–6330) use `H_{s,c} = P_c[a^{-2}H_0(x/√a)]`.

Main results:
* `integral_sq_snd_heatDilation`: `∫_{ℝ²} η² a^{-2} f(x/√a) = ∫_{ℝ²} η² f(x)` for `a > 0`
  (Q_∞ is dilation invariant; no integrability hypothesis is needed, since both sides are
  related by the change of variables formula, which Mathlib states for all `f`);
* `integral_cell_sq_periodize_heatDilation`: `∫_cell η² P_c[a^{-2} f(·/√a)] = ∫_{ℝ²} η² f`,
  i.e. `Q_c(P_c[a^{-2}Z(x/√a)]) = Q_∞(Z)` (B0364), for `c > 0` and `η² f` integrable.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The heat dilation `a^{-2} f(x/√a)` of a planar function. -/
def heatDilation (a : ℝ) (f : ℝ × ℝ → E) (z : ℝ × ℝ) : E := (a⁻¹ ^ 2) • f ((Real.sqrt a)⁻¹ • z)

/-- **G7 item 5 (B0364).** `∫ η² a^{-2} f(x/√a) dx = ∫ η² f(x) dx` for `a > 0`. -/
theorem integral_sq_snd_heatDilation (f : ℝ × ℝ → E) {a : ℝ} (ha : 0 < a) :
    ∫ z : ℝ × ℝ, z.2 ^ 2 • heatDilation a f z = ∫ z : ℝ × ℝ, z.2 ^ 2 • f z := by
  set R : ℝ := (Real.sqrt a)⁻¹ with hR
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hR0 : R ≠ 0 := inv_ne_zero hs.ne'
  have hR2 : R ^ 2 = a⁻¹ := by rw [hR, inv_pow, Real.sq_sqrt ha.le]
  set g : ℝ × ℝ → E := fun z => z.2 ^ 2 • f z with hg
  have hpt : ∀ z : ℝ × ℝ, z.2 ^ 2 • heatDilation a f z = (a⁻¹ ^ 2 * (R ^ 2)⁻¹) • g (R • z) := by
    intro z
    simp only [heatDilation, hg, Prod.smul_snd, smul_eq_mul, smul_smul]
    congr 1
    field_simp
  simp_rw [hpt]
  rw [integral_smul, Measure.integral_comp_smul volume g R]
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hfin, smul_smul]
  have hc : a⁻¹ ^ 2 * (R ^ 2)⁻¹ * |(R ^ 2)⁻¹| = 1 := by
    rw [hR2, inv_inv, abs_of_pos ha]
    field_simp
  rw [hc, one_smul]

/-- **G7 item 5 (B0364).** `Q_c(P_c[a^{-2}Z(x/√a)]) = Q_∞(Z)`:
`∫_{[0,c)×ℝ} η² P_c[a^{-2} f(·/√a)] = ∫_{ℝ²} η² f` for `c > 0`, `a > 0`, whenever `η² f` is
integrable. -/
theorem integral_cell_sq_periodize_heatDilation [CompleteSpace E] {f : ℝ × ℝ → E}
    (hf : Integrable (fun z : ℝ × ℝ => z.2 ^ 2 • f z)) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫ z in cell c, z.2 ^ 2 • periodize c (heatDilation a f) z = ∫ z : ℝ × ℝ, z.2 ^ 2 • f z := by
  have hint : Integrable (fun z : ℝ × ℝ => z.2 ^ 2 • heatDilation a f z) := by
    set R : ℝ := (Real.sqrt a)⁻¹ with hR
    have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    have hR0 : R ≠ 0 := inv_ne_zero hs.ne'
    have h1 := (hf.comp_smul hR0).smul (a⁻¹ ^ 2 * (R ^ 2)⁻¹)
    refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [heatDilation, Pi.smul_apply, Prod.smul_snd, smul_eq_mul, smul_smul]
    congr 1
    field_simp
  rw [integral_cell_weight_periodize (fun η => η ^ 2) hint hc,
    integral_sq_snd_heatDilation f ha]

end UnforcedLeray.Gaussian
