import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_5_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.FlatHeatContraction

/-!
# Part II-b, task `PartII-b:T12/7/5/3/2` (`deqpdTailD`): uniform Gaussian envelope of `deqSmoothD`

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Fix `s > t`, take `ε = (s-t)/2`. For `s'` in the ball, the age `θ' = ν(s'-t)` lies in `[θ/2, 3θ/2]`
with `θ = ν(s-t)`. The integrand `K_{θ'}(w) G(s', z-w)` (with `G` the derivative-side test, bounded
by `M` and vanishing outside a box of radius `R₀` in space) is majorised by
`4 M exp(-E²/(24θ)) K_{2θ}(w)`, where `E = max 0 (‖z‖ - R₀)`, because `K_{θ'}(w) ≤ 4 K_{2θ}(w)
exp(-E²/(24θ))` for `‖w‖ ≥ E` and `θ/2 ≤ θ' ≤ 3θ/2`. Integrating against `K_{2θ}` (mass 1) gives
the bound with `C = 4M`, `R = R₀`, `a = 1/(24θ)`, uniformly in `s'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- A vector of norm at least `d ≥ 0` has `d² ≤ w₁² + w₂²`. -/
private theorem deqpd_sq_le (d : ℝ) (w : ℝ × ℝ) (hd : 0 ≤ d) (hdw : d ≤ ‖w‖) :
    d ^ 2 ≤ w.1 ^ 2 + w.2 ^ 2 := by
  rw [Prod.norm_def] at hdw
  rcases le_max_iff.mp hdw with h | h
  · rw [Real.norm_eq_abs] at h
    nlinarith [sq_abs w.1, sq_nonneg w.2, abs_nonneg w.1, mul_le_mul h h hd (abs_nonneg _)]
  · rw [Real.norm_eq_abs] at h
    nlinarith [sq_abs w.2, sq_nonneg w.1, abs_nonneg w.2, mul_le_mul h h hd (abs_nonneg _)]

/-- Pointwise kernel comparison: for `θ/2 ≤ θ' ≤ 3θ/2` and `E² ≤ q`,
`(4πθ')⁻¹ e^{-q/(4θ')} ≤ 4 (4π·2θ)⁻¹ e^{-q/(4·2θ)} e^{-E²/(24θ)}`. -/
private theorem deqpd_kernel (θ θ' : ℝ) (hθ : 0 < θ) (hθ' : 0 < θ') (h1 : θ / 2 ≤ θ')
    (h2 : θ' ≤ 3 * θ / 2) (q E : ℝ) (hq : E ^ 2 ≤ q) :
    (4 * Real.pi * θ')⁻¹ * Real.exp (-q / (4 * θ')) ≤
      4 * ((4 * Real.pi * (2 * θ))⁻¹ * Real.exp (-q / (4 * (2 * θ)))) *
        Real.exp (-(1 / (24 * θ)) * E ^ 2) := by
  have hpi := Real.pi_pos
  have hθne : θ ≠ 0 := hθ.ne'
  have hpine : Real.pi ≠ 0 := hpi.ne'
  have hq0 : 0 ≤ q := le_trans (sq_nonneg E) hq
  have hA : (4 * Real.pi * θ')⁻¹ ≤ 4 * (4 * Real.pi * (2 * θ))⁻¹ := by
    have e : 4 * (4 * Real.pi * (2 * θ))⁻¹ = (2 * Real.pi * θ)⁻¹ := by
      first | (field_simp; ring) | field_simp
    rw [e]
    apply inv_anti₀ (by have := mul_pos hpi hθ; linarith)
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * Real.pi)
    nlinarith
  have hB : Real.exp (-q / (4 * θ')) ≤
      Real.exp (-q / (4 * (2 * θ))) * Real.exp (-(1 / (24 * θ)) * E ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h4θ' : 0 < 4 * θ' := by linarith
    have hh1 : q / (6 * θ) ≤ q / (4 * θ') := div_le_div_of_nonneg_left hq0 h4θ' (by linarith)
    have hh2 : q / (6 * θ) = q / (4 * (2 * θ)) + q / (24 * θ) := by
      first | (field_simp; ring) | field_simp
    have hh3 : E ^ 2 / (24 * θ) ≤ q / (24 * θ) :=
      div_le_div_of_nonneg_right hq (by linarith)
    have hh4 : -(1 / (24 * θ)) * E ^ 2 = -(E ^ 2 / (24 * θ)) := by ring
    have hh5 : -q / (4 * θ') = -(q / (4 * θ')) := neg_div _ _
    have hh6 : -q / (4 * (2 * θ)) = -(q / (4 * (2 * θ))) := neg_div _ _
    have hh7 : -q / (6 * θ) = -(q / (6 * θ)) := neg_div _ _
    linarith
  have hA0 : 0 ≤ 4 * (4 * Real.pi * (2 * θ))⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr (by linarith [mul_pos hpi hθ]))
  calc (4 * Real.pi * θ')⁻¹ * Real.exp (-q / (4 * θ'))
      ≤ (4 * (4 * Real.pi * (2 * θ))⁻¹) *
          (Real.exp (-q / (4 * (2 * θ))) * Real.exp (-(1 / (24 * θ)) * E ^ 2)) :=
        mul_le_mul hA hB (Real.exp_pos _).le hA0
    _ = 4 * ((4 * Real.pi * (2 * θ))⁻¹ * Real.exp (-q / (4 * (2 * θ)))) *
          Real.exp (-(1 / (24 * θ)) * E ^ 2) := by ring

/-- A bounded function on `Coord` (continuous, compact support) is bounded by `M`, and vanishes
at `(s, y)` once `‖y‖ > R₀`. -/
private theorem deqpd_bounded_support (G : Coord → ℝ) (hG : Continuous G)
    (hGc : HasCompactSupport G) :
    ∃ M R0 : ℝ, 0 ≤ M ∧ (∀ x : Coord, ‖G x‖ ≤ M) ∧
      ∀ (s : ℝ) (y : ℝ × ℝ), R0 < ‖y‖ → G (s, y) = 0 := by
  obtain ⟨M, hM⟩ := hG.bounded_above_of_compact_support hGc
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).mp
    hGc.isCompact.isBounded
  refine ⟨M, R0, (norm_nonneg _).trans (hM 0), hM, ?_⟩
  intro s y hy
  by_contra hne
  have hmem : ((s, y) : Coord) ∈ tsupport G := subset_tsupport _ (Function.mem_support.mpr hne)
  have h1 := hR0 hmem
  rw [mem_closedBall_zero_iff] at h1
  have h2 : ‖y‖ ≤ ‖((s, y) : Coord)‖ := norm_snd_le (s, y)
  linarith

/-- Uniform Gaussian envelope of the smoothed derivative-side integral, for ages
`θ' ∈ [θ/2, 3θ/2]`. -/
private theorem deqpd_gauss (G : Coord → ℝ) (M R0 θ θ' s' : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x : Coord, ‖G x‖ ≤ M)
    (hsupp : ∀ (s : ℝ) (y : ℝ × ℝ), R0 < ‖y‖ → G (s, y) = 0)
    (hθ : 0 < θ) (hθ' : 0 < θ') (h1 : θ / 2 ≤ θ') (h2 : θ' ≤ 3 * θ / 2) (z : ℝ × ℝ) :
    |∫ w : ℝ × ℝ, flatHeatKernel θ' w * G (s', z - w)| ≤
      4 * M * Real.exp (-(1 / (24 * θ)) * (max 0 (‖z‖ - R0)) ^ 2) := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = max 0 (‖z‖ - R0) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact le_max_left _ _
  have h2θ : 0 < 2 * θ := by linarith
  have hfh : Integrable (fun w : ℝ × ℝ => flatHeatKernel (2 * θ) w) :=
    (UnforcedLeray.B0284.integrable_heatKernel2 h2θ).congr
      (ae_of_all _ fun w => (flatHeat_kernel_eq h2θ w).symm)
  have hint : Integrable (fun w : ℝ × ℝ =>
      4 * M * Real.exp (-(1 / (24 * θ)) * E ^ 2) * flatHeatKernel (2 * θ) w) :=
    hfh.const_mul _
  have hI : ∫ w : ℝ × ℝ, flatHeatKernel (2 * θ) w = 1 := by
    simp only [flatHeat_kernel_eq h2θ]
    exact UnforcedLeray.B0284.integral_heatKernel2 h2θ
  have hpt : ∀ w : ℝ × ℝ, |flatHeatKernel θ' w * G (s', z - w)| ≤
      4 * M * Real.exp (-(1 / (24 * θ)) * E ^ 2) * flatHeatKernel (2 * θ) w := by
    intro w
    have hKnn : 0 ≤ flatHeatKernel θ' w := by
      rw [flatHeat_kernel_eq hθ']; exact UnforcedLeray.B0284.heatKernel2_nonneg hθ' w
    have hKnn2 : 0 ≤ flatHeatKernel (2 * θ) w := by
      rw [flatHeat_kernel_eq h2θ]; exact UnforcedLeray.B0284.heatKernel2_nonneg h2θ w
    rw [abs_mul, abs_of_nonneg hKnn]
    by_cases hz : R0 < ‖z - w‖
    · rw [hsupp s' (z - w) hz, abs_zero, mul_zero]
      exact mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) hKnn2
    · push_neg at hz
      have hEw : E ≤ ‖w‖ := by
        rw [hE]
        refine max_le (norm_nonneg w) ?_
        linarith [norm_sub_norm_le z w]
      have hQ := deqpd_sq_le E w hE0 hEw
      have hGb : |G (s', z - w)| ≤ M := by simpa [Real.norm_eq_abs] using hM (s', z - w)
      have hK : flatHeatKernel θ' w ≤
          4 * flatHeatKernel (2 * θ) w * Real.exp (-(1 / (24 * θ)) * E ^ 2) := by
        unfold flatHeatKernel
        exact deqpd_kernel θ θ' hθ hθ' h1 h2 (w.1 ^ 2 + w.2 ^ 2) E hQ
      calc flatHeatKernel θ' w * |G (s', z - w)|
          ≤ flatHeatKernel θ' w * M := mul_le_mul_of_nonneg_left hGb hKnn
        _ ≤ (4 * flatHeatKernel (2 * θ) w * Real.exp (-(1 / (24 * θ)) * E ^ 2)) * M :=
            mul_le_mul_of_nonneg_right hK hM0
        _ = 4 * M * Real.exp (-(1 / (24 * θ)) * E ^ 2) * flatHeatKernel (2 * θ) w := by ring
  have hbound : ‖∫ w : ℝ × ℝ, flatHeatKernel θ' w * G (s', z - w)‖ ≤
      4 * M * Real.exp (-(1 / (24 * θ)) * E ^ 2) := by
    calc ‖∫ w : ℝ × ℝ, flatHeatKernel θ' w * G (s', z - w)‖
        ≤ ∫ w : ℝ × ℝ, 4 * M * Real.exp (-(1 / (24 * θ)) * E ^ 2) * flatHeatKernel (2 * θ) w :=
          norm_integral_le_of_norm_le hint
            (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hpt w)
      _ = 4 * M * Real.exp (-(1 / (24 * θ)) * E ^ 2) := by
          rw [integral_const_mul, hI, mul_one]
  rw [← hE, ← Real.norm_eq_abs]
  exact hbound

theorem deqpdTailD : UnforcedLeray.Short.IIb.DeqpdTailD := by
  intro ν t hν ht Ψ hΨ i s hs
  have hF : ContDiff ℝ ∞ (fun x : Coord => Ψ x i) := (hΨ.smooth i).smooth
  have hFc : HasCompactSupport (fun x : Coord => Ψ x i) := (hΨ.smooth i).compact
  have c1 : HasCompactSupport (fun y : Coord => cpd 1 (fun x => Ψ x i) y) :=
    HasCompactSupport.fderiv_apply ℝ hFc (cdir 1)
  have c2 : HasCompactSupport (fun y : Coord => cpd 2 (fun x => Ψ x i) y) :=
    HasCompactSupport.fderiv_apply ℝ hFc (cdir 2)
  have c0 : HasCompactSupport (fun x : Coord => cpd 0 (fun y => Ψ y i) x) :=
    HasCompactSupport.fderiv_apply ℝ hFc (cdir 0)
  have c11 : HasCompactSupport (fun x : Coord => cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) x) :=
    HasCompactSupport.fderiv_apply ℝ c1 (cdir 1)
  have c22 : HasCompactSupport (fun x : Coord => cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) x) :=
    HasCompactSupport.fderiv_apply ℝ c2 (cdir 2)
  have hgcs : HasCompactSupport (fun x : Coord =>
      cpd 0 (fun y => Ψ y i) x +
        ν * (cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) x +
          cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) x)) :=
    c0.add ((c11.add c22).mul_left)
  have hc0 : Continuous (fun x : Coord => cpd 0 (fun y => Ψ y i) x) :=
    (deqT_cpd_contDiff hF 0).continuous
  have hc11 : Continuous (fun x : Coord => cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) x) :=
    (deqT_cpd_contDiff (deqT_cpd_contDiff hF 1) 1).continuous
  have hc22 : Continuous (fun x : Coord => cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) x) :=
    (deqT_cpd_contDiff (deqT_cpd_contDiff hF 2) 2).continuous
  have hgc : Continuous (fun x : Coord =>
      cpd 0 (fun y => Ψ y i) x +
        ν * (cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) x +
          cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) x)) :=
    hc0.add (continuous_const.mul (hc11.add hc22))
  obtain ⟨M, R0, hM0, hM, hsupp⟩ := deqpd_bounded_support _ hgc hgcs
  have hθ : 0 < ν * (s - t) := mul_pos hν (by linarith)
  refine ⟨(s - t) / 2, by linarith, by linarith, 4 * M, R0, 1 / (24 * (ν * (s - t))),
    one_div_pos.mpr (by linarith), ?_⟩
  intro s' hs' z
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs'
  obtain ⟨hl, hr⟩ := hs'
  have hθ' : 0 < ν * (s' - t) := mul_pos hν (by linarith)
  have hA1 : ν * ((s - t) / 2) ≤ ν * (s' - t) := mul_le_mul_of_nonneg_left (by linarith) hν.le
  have hA2 : ν * (s' - t) ≤ ν * (3 * (s - t) / 2) := mul_le_mul_of_nonneg_left (by linarith) hν.le
  unfold deqSmoothD
  exact deqpd_gauss _ M R0 (ν * (s - t)) (ν * (s' - t)) s' hM0 hM hsupp hθ hθ'
    (by linarith) (by linarith) z

end UnforcedLeray.Short.IIb

end
