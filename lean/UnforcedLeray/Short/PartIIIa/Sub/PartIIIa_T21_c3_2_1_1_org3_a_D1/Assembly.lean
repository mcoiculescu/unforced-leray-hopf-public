import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Drift
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Transport
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: norms, cells and energies

Source: SP 2861 (`J_a`), 2937-2958 (`eq:short-causal-free-moving`), 2962-2964.

* `norm_eq_sqrt_movEnergy`: an `L²_m` element represented by the zero extension of `J_a⁻¹ g` has
  norm `√(a³ ∫_{C_c} g² (1+|x|²/a)^m)` (`fmeScale`, `ofReal_norm_eq_xNorm_of_ae_cellZeroExt`).
* `radius_lt_half_cell`: for `ν` small and `θ ≥ b ≥ 1` the ball of radius `R √a` lies in the
  cell `C_c`, `c = ν⁻²`; equivalently `R < d/2`, `d = c/√a`.
* `energy_le`: the free moving energy bound in real form (`freeMovingEnergy`, `fmeScale`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

theorem movEnergy_nonneg (c m a : ℝ) (ha : 0 < a) (g : ℝ × ℝ → ℝ) : 0 ≤ movEnergy c m a g := by
  unfold movEnergy
  refine setIntegral_nonneg (B0579.measurableSet_cell c) fun x _ => ?_
  have h1 : 0 ≤ 1 + (x.1 ^ 2 + x.2 ^ 2) / a := by positivity
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg h1 _)

/-- An `L²_m` element represented by the zero extension of `J_a⁻¹ g` has norm
`√(a³ movEnergy c m a g)`. -/
theorem norm_eq_sqrt_movEnergy {m c a : ℝ} (hc : 0 < c) (ha : 0 < a) {g : ℝ × ℝ → ℝ}
    (hint : IntegrableOn (fun x : ℝ × ℝ => g x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ m)
      (B0579.cell c))
    {V : ℝ × ℝ → ℂ} (hV : AEStronglyMeasurable V (B0579.cellMeasure (cellLen c a) m))
    (hVJ : ∀ y ∈ B0579.cell (cellLen c a), V y = JscaleInv a (fun x => ((g x : ℝ) : ℂ)) y)
    (W : Planar.L2w m)
    (hW : ⇑W =ᵐ[Planar.wMeasure m] fun z => cellZeroExt (cellLen c a) V (cToPlane z)) :
    ‖W‖ = Real.sqrt (a ^ 3 * movEnergy c m a g) := by
  have h1 := VariationOfConstantsSub.ofReal_norm_eq_xNorm_of_ae_cellZeroExt hV W hW
  have h2 : xNorm (cellLen c a) m V =
      xNorm (cellLen c a) m (JscaleInv a (fun x => ((g x : ℝ) : ℂ))) := by
    unfold xNorm
    refine eLpNorm_congr_ae ?_
    have hae : ∀ᵐ y ∂(volume.restrict (B0579.cell (cellLen c a))),
        V y = JscaleInv a (fun x => ((g x : ℝ) : ℂ)) y := by
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with y hy
      exact hVJ y hy
    exact (B0579.cellMeasure_ac _ m).ae_le hae
  have h3 := fmeScale c m a hc ha g hint
  rw [h2, h3] at h1
  exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (Real.sqrt_nonneg _)).1 h1

/-! ## Cells -/

theorem mem_cell_of_mem_closedBall {c r : ℝ} (h : r < c / 2) {x : ℝ × ℝ}
    (hx : x ∈ Metric.closedBall (0 : ℝ × ℝ) r) : x ∈ B0579.cell c := by
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have h1 : |x.1| ≤ r := by
    have := norm_fst_le x
    rw [Real.norm_eq_abs] at this
    linarith
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
  · linarith [neg_abs_le x.1]
  · linarith [le_abs_self x.1]

theorem rpow_neg_two_eq {ν : ℝ} (hν : 0 < ν) : ν ^ (-2 : ℝ) = (ν ^ 2)⁻¹ := by
  rw [Real.rpow_neg hν.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem clockA_le_inv {ν b σ : ℝ} (hν : 0 < ν) (hb : 1 ≤ b) (hσ : 0 ≤ σ)
    (hθ : b ≤ clockTheta ν σ) : clockA ν σ ≤ ν⁻¹ := by
  have ha := clockA_pos hν.le hσ
  unfold clockTheta at hθ
  have h1 : 1 ≤ (ν * clockA ν σ)⁻¹ := hb.trans hθ
  have h2 : ν * clockA ν σ ≤ 1 := by
    have hp : 0 < ν * clockA ν σ := mul_pos hν ha
    rwa [one_le_inv₀ hp] at h1
  rw [le_inv_comm₀ ha hν]
  calc ν = ν * clockA ν σ / clockA ν σ := by field_simp
    _ ≤ 1 / clockA ν σ := div_le_div_of_nonneg_right h2 ha.le
    _ = (clockA ν σ)⁻¹ := one_div _

theorem radius_lt_half_cell {ν b R σ : ℝ} (hν : 0 < ν) (hνR : ν * (2 * R + 1) ≤ 1)
    (hR : 0 ≤ R) (hb : 1 ≤ b) (hσ : 0 ≤ σ) (hθ : b ≤ clockTheta ν σ) :
    R * Real.sqrt (clockA ν σ) < ν ^ (-2 : ℝ) / 2 := by
  have ha1 := one_le_clockA' hν.le hσ
  have haν := clockA_le_inv hν hb hσ hθ
  have hsq : Real.sqrt (clockA ν σ) ≤ clockA ν σ := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have h1 : R * Real.sqrt (clockA ν σ) ≤ R * ν⁻¹ :=
    mul_le_mul_of_nonneg_left (hsq.trans haν) hR
  rw [rpow_neg_two_eq hν]
  have h2 : R * ν⁻¹ < (ν ^ 2)⁻¹ / 2 := by
    rw [show (ν ^ 2)⁻¹ / 2 = ν⁻¹ * (1 / (2 * ν)) by field_simp]
    rw [mul_comm R]
    refine mul_lt_mul_of_pos_left ?_ (inv_pos.2 hν)
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  linarith

theorem radius_lt_half_cellLen {ν b R σ : ℝ} (hν : 0 < ν) (hνR : ν * (2 * R + 1) ≤ 1)
    (hR : 0 ≤ R) (hb : 1 ≤ b) (hσ : 0 ≤ σ) (hθ : b ≤ clockTheta ν σ) :
    R < cellLen (ν ^ (-2 : ℝ)) (clockA ν σ) / 2 := by
  have h := radius_lt_half_cell hν hνR hR hb hσ hθ
  have hsa := Real.sqrt_pos.2 (clockA_pos hν.le hσ)
  unfold cellLen
  rw [div_div, lt_div_iff₀ (by positivity)]
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- Outside the moving cell, a function supported in the Euclidean ball of radius `R` vanishes. -/
theorem eq_zero_of_not_mem_cell {d R : ℝ} (hR : 0 ≤ R) (hd : R < d / 2) {G : ℝ × ℝ → ℝ}
    (hG : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → G y = 0) {y : ℝ × ℝ}
    (hy : y ∉ B0579.cell d) : G y = 0 := by
  apply hG
  have h1 : d / 2 ≤ |y.1| := by
    by_contra hcon
    push_neg at hcon
    exact hy ⟨⟨by linarith [neg_abs_le y.1], by linarith [le_abs_self y.1]⟩, Set.mem_univ _⟩
  have h2 : R < |y.1| := lt_of_lt_of_le hd h1
  have h3 : R ^ 2 < |y.1| ^ 2 := by nlinarith
  rw [sq_abs] at h3
  nlinarith [sq_nonneg y.2]

/-! ## The free moving energy in real form -/

/-- `√A ≤ e^{kΔ} √B` with `A, B ≥ 0` gives `A ≤ e^{2kΔ} B`. -/
theorem le_of_sqrt_le {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ENNReal.ofReal (Real.sqrt A) ≤ ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.sqrt B)) :
    A ≤ Real.exp (2 * x) * B := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))] at h
  have h2 : Real.sqrt A ^ 2 ≤ (Real.exp x * Real.sqrt B) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB, ← Real.exp_nat_mul] at h2
  simpa [mul_comm] using h2

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
