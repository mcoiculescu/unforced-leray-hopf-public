import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.VDef

/-!
# Mean part helper: bounds for the integrand of `sepVmu0` (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mp_norm_e (k : Fin 3) : ‖coordinateVector k‖ = 1 := by
  simp [coordinateVector]

theorem mp_sum9 (f : Fin 3 → Fin 3 → ℂ) (M : ℝ) (h : ∀ j k, ‖f j k‖ ≤ M) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, f j k‖ ≤ 9 * M := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ j : Fin 3, ‖∑ k : Fin 3, f j k‖ ≤ 3 * M := fun j => by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k : Fin 3, ‖f j k‖ ≤ ∑ _k : Fin 3, M := Finset.sum_le_sum fun k _ => h j k
      _ = 3 * M := by simp
  calc ∑ j : Fin 3, ‖∑ k : Fin 3, f j k‖ ≤ ∑ _j : Fin 3, 3 * M := Finset.sum_le_sum fun j _ => this j
    _ = 9 * M := by simp; ring

theorem mp_clm_bound (c : Fin 3 → Fin 3 → ℝ) (B : Fin 3 → Space →L[ℝ] (Space →L[ℝ] ℝ))
    (M tn : ℝ) (hc : ∀ j k, |c j k| ≤ tn) (hB : ∀ j, ‖B j‖ ≤ M) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, (c j k : ℂ) • (Complex.ofRealCLM.comp
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).comp (B j)))‖ ≤ 9 * tn * M := by
  have htn : 0 ≤ tn := (abs_nonneg _).trans (hc 0 0)
  have hM : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg _).trans (hB 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, Complex.ofRealCLM_apply,
    smul_eq_mul]
  have key := mp_sum9 (fun j k => (c j k : ℂ) * (((B j v) (coordinateVector k) : ℝ) : ℂ))
    (tn * (M * ‖v‖)) (fun j k => by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |(B j v) (coordinateVector k)| ≤ ‖B j v‖ * ‖coordinateVector k‖ :=
        (Real.norm_eq_abs _).symm ▸ (B j v).le_opNorm _
      rw [mp_norm_e, mul_one] at h1
      have h2 : ‖B j v‖ ≤ M * ‖v‖ := ((B j).le_opNorm v).trans (by gcongr; exact hB j)
      exact mul_le_mul (hc j k) (h1.trans h2) (abs_nonneg _) htn)
  calc _ ≤ 9 * (tn * (M * ‖v‖)) := key
    _ = 9 * tn * M * ‖v‖ := by ring

/-- The weight `|λ^{2μ+2}| ≤ 1`. -/
theorem mp_norm_cpow_le (μ : ℂ) (hμ : -(1 / 4) < μ.re) (l : ℝ) (hl : l ∈ Ioo (0 : ℝ) 1) :
    ‖(l : ℂ) ^ (2 * μ + 2)‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hl.1]
  exact Real.rpow_le_one hl.1.le hl.2.le (by simp; linarith)

/-- The horizontal gap for the mean integrand. -/
theorem mp_gap (ρo ρi : ℝ) (xo x : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (l : ℝ)
    (hl : l ∈ Ioo (0 : ℝ) 1) (w : (ℝ × ℝ) × ℝ)
    (hw : Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) ≤ ρo) :
    ρi - ρo - ‖xo - x‖ ≤ Real.sqrt ((x - l • mpV3 w) 0 ^ 2 + (x - l • mpV3 w) 1 ^ 2) := by
  have h1 := rho_add_le (x - l • mpV3 w) (l • mpV3 w + (xo - x))
  have h2 := rho_add_le (l • mpV3 w) (xo - x)
  have h3 := rho_le_norm (xo - x)
  have e1 : (x - l • mpV3 w) + (l • mpV3 w + (xo - x)) = xo := by abel
  have e2 : Real.sqrt ((l • mpV3 w) 0 ^ 2 + (l • mpV3 w) 1 ^ 2) =
      l * Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) := by
    have : (l • mpV3 w) 0 ^ 2 + (l • mpV3 w) 1 ^ 2 = l ^ 2 * (w.1.1 ^ 2 + w.1.2 ^ 2) := by
      simp [mpV3]; ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hl.1.le]
  have e3 : Real.sqrt ((xo - x) 0 ^ 2 + (xo - x) 1 ^ 2) ≤ ‖xo - x‖ := rho_le_norm _
  have hlw : l * Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) ≤ ρo := by
    have := Real.sqrt_nonneg (w.1.1 ^ 2 + w.1.2 ^ 2)
    nlinarith [hl.2, hl.1]
  have e4 : (x - l • mpV3 w) + (l • mpV3 w + (xo - x)) = xo := e1
  have c0 : (x - l • mpV3 w).ofLp 0 + (l • mpV3 w + (xo - x)).ofLp 0 = xo.ofLp 0 := by
    simp; ring
  have c1 : (x - l • mpV3 w).ofLp 1 + (l • mpV3 w + (xo - x)).ofLp 1 = xo.ofLp 1 := by
    simp; ring
  rw [c0, c1] at h1
  rw [e2] at h2
  have h2' : Real.sqrt ((l • mpV3 w + (xo - x)) 0 ^ 2 + (l • mpV3 w + (xo - x)) 1 ^ 2) ≤
      l * Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) + Real.sqrt ((xo - x) 0 ^ 2 + (xo - x) 1 ^ 2) := by
    have := rho_add_le (l • mpV3 w) (xo - x)
    rw [e2] at this
    simpa using this
  linarith

end UnforcedLeray.Short.IIIa

end
