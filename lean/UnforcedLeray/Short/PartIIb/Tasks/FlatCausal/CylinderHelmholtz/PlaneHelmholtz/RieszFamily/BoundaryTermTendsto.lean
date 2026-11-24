import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs

/-!
# The cutoff boundary term vanishes in the limit

Source of record: `the November 2 reference manuscript`, line 1670 (the planar
projection `P_0 = I - ∇Δ⁻¹ div`) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory, Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

For a cutoff family `χ_R` (`1` on `‖x‖ ≤ R`, `0` on `‖x‖ ≥ 2R`, `‖∇χ_R‖ ≤ M / R`) and a
smooth `ψ` with `ψ = O(1/|x|)` and `∇ψ = O(|x|⁻²)`, the term `∫ ψ ∂_iχ_R ∂_iψ` is supported in
the annulus `R ≤ ‖x‖ ≤ 2R`, where the integrand is at most `C'/R⁴`; the annulus has volume
`16 R²`, so the term is `O(1/R²)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/28`.** The cutoff boundary term tends to zero. -/
theorem boundaryTermTendsto : BoundaryTermTendsto := by
  intro χ hχ ψ _ hdecay i
  obtain ⟨C, R0, hC⟩ := hdecay
  unfold IsCutoffFamily at hχ
  obtain ⟨_, _, hχ1, hχ2, M, hM⟩ := hχ
  -- `χ R` is locally constant off the annulus, so its gradient vanishes there.
  have hvan : ∀ R : ℝ, 1 ≤ R → ∀ x : Pl, (‖x‖ < R ∨ 2 * R < ‖x‖) →
      fderiv ℝ (χ R) x = 0 := by
    intro R hR x hx
    rcases hx with hx | hx
    · have hev : χ R =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
        Filter.eventually_of_mem
          ((isOpen_lt continuous_norm continuous_const).mem_nhds
            (show x ∈ {b : Pl | ‖b‖ < R} from hx))
          (fun y hy => hχ1 R y hR (le_of_lt (show ‖y‖ < R from hy)))
      rw [hev.fderiv_eq, fderiv_const_apply]
    · have hev : χ R =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem
          ((isOpen_lt continuous_const continuous_norm).mem_nhds
            (show x ∈ {b : Pl | 2 * R < ‖b‖} from hx))
          (fun y hy => hχ2 R y hR (le_of_lt (show 2 * R < ‖y‖ from hy)))
      rw [hev.fderiv_eq, fderiv_const_apply]
  have hg0 : ∀ R : ℝ, 1 ≤ R → ∀ x : Pl, (‖x‖ < R ∨ 2 * R < ‖x‖) →
      ψ x * pd i (χ R) x * pd i ψ x = 0 := by
    intro R hR x hx
    simp [pd, hvan R hR x hx]
  have hsingle : ‖(Pi.single i (1 : ℝ) : Pl)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun j => ?_)
    simp only [Pi.single_apply]
    split_ifs <;> simp
  -- pointwise bound on the closed annulus region `‖x‖ ≤ 2R`
  have hbound : ∀ R : ℝ, 1 ≤ R → R0 ≤ R → ∀ x : Pl, ‖x‖ ≤ 2 * R →
      ‖ψ x * pd i (χ R) x * pd i ψ x‖ ≤
        (|C| * R⁻¹) * (|M| * R⁻¹) * (|C| * (R ^ 2)⁻¹) := by
    intro R hR hR0 x _hx2
    have hRpos : 0 < R := by linarith
    by_cases hxR : ‖x‖ < R
    · rw [hg0 R hR x (Or.inl hxR), norm_zero]
      positivity
    · replace hxR : R ≤ ‖x‖ := not_lt.1 hxR
      have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hRpos hxR
      have hψb : |ψ x| ≤ |C| * R⁻¹ := by
        obtain ⟨h1, _⟩ := hC x (le_trans hR0 hxR)
        calc |ψ x| ≤ C * ‖x‖⁻¹ := h1
          _ ≤ |C| * ‖x‖⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.2 hxpos.le)
          _ ≤ |C| * R⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hRpos hxR) (abs_nonneg C)
      have hdψb : |pd i ψ x| ≤ |C| * (R ^ 2)⁻¹ := by
        obtain ⟨_, h2⟩ := hC x (le_trans hR0 hxR)
        have h3 := h2 i
        have e : ‖x‖ ^ (-2 : ℝ) = (‖x‖ ^ 2)⁻¹ := by
          rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two]
        have hsq : R ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith
        have h4 : (‖x‖ ^ 2)⁻¹ ≤ (R ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
        calc |pd i ψ x| ≤ C * ‖x‖ ^ (-2 : ℝ) := h3
          _ = C * (‖x‖ ^ 2)⁻¹ := by rw [e]
          _ ≤ |C| * (‖x‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
          _ ≤ |C| * (R ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h4 (abs_nonneg C)
      have hdχb : |pd i (χ R) x| ≤ |M| * R⁻¹ := by
        have h5 : ‖fderiv ℝ (χ R) x (Pi.single i (1 : ℝ))‖ ≤ (M / R) * 1 :=
          calc ‖fderiv ℝ (χ R) x (Pi.single i (1 : ℝ))‖
              ≤ ‖fderiv ℝ (χ R) x‖ * ‖(Pi.single i (1 : ℝ) : Pl)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ (M / R) * 1 :=
                mul_le_mul (hM R x hR) hsingle (norm_nonneg _)
                  (le_trans (norm_nonneg _) (hM R x hR))
        rw [← Real.norm_eq_abs]
        calc ‖pd i (χ R) x‖ = ‖fderiv ℝ (χ R) x (Pi.single i (1 : ℝ))‖ := rfl
          _ ≤ (M / R) * 1 := h5
          _ = M / R := mul_one _
          _ ≤ |M| * R⁻¹ := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (le_abs_self M) (inv_nonneg.2 hRpos.le)
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul hψb hdχb (abs_nonneg _) (by positivity))
        hdψb (abs_nonneg _) (by positivity)
  -- integral bound: the integrand vanishes off the closed ball of radius `2R`
  have hint : ∀ R : ℝ, 1 ≤ R → R0 ≤ R →
      ‖∫ x, ψ x * pd i (χ R) x * pd i ψ x‖ ≤ 16 * |C| ^ 2 * |M| / R ^ 2 := by
    intro R hR hR0
    have hRpos : 0 < R := by linarith
    have hcompl : ∀ x, x ∉ Metric.closedBall (0 : Pl) (2 * R) →
        ψ x * pd i (χ R) x * pd i ψ x = 0 := by
      intro x hx
      apply hg0 R hR x (Or.inr _)
      rw [mem_closedBall_zero_iff, not_le] at hx
      exact hx
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
    have hbd := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Metric.closedBall (0 : Pl) (2 * R))
      (f := fun x => ψ x * pd i (χ R) x * pd i ψ x)
      (C := (|C| * R⁻¹) * (|M| * R⁻¹) * (|C| * (R ^ 2)⁻¹))
      (measure_closedBall_lt_top)
      (fun x hx => hbound R hR hR0 x (mem_closedBall_zero_iff.1 hx))
    have hvol : volume.real (Metric.closedBall (0 : Pl) (2 * R)) = 16 * R ^ 2 := by
      rw [measureReal_def, Real.volume_pi_closedBall _ (by linarith),
        ENNReal.toReal_ofReal (by positivity)]
      simp only [Fintype.card_fin]
      ring
    rw [hvol] at hbd
    calc _ ≤ _ := hbd
      _ = 16 * |C| ^ 2 * |M| / R ^ 2 := by
        field_simp
  -- squeeze to zero
  have hlim : Tendsto (fun R : ℝ => 16 * |C| ^ 2 * |M| / R ^ 2) atTop (𝓝 0) :=
    (tendsto_const_nhds).div_atTop (tendsto_pow_atTop two_ne_zero)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hlim
  rw [Filter.eventually_atTop]
  refine ⟨max 1 R0, fun R hR => hint R (le_trans (le_max_left _ _) hR)
    (le_trans (le_max_right _ _) hR)⟩

end UnforcedLeray.Short.IIb.PlaneRiesz
