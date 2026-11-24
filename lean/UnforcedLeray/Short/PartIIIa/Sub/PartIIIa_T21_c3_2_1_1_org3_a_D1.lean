import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Bound

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: the free transport limit on compact tests

Source: `the November 2 reference manuscript` (SP) 2962-2964 ("compact smooth
tests and Duhamel give direct strong convergence to radial Euler transport in the successive
limit"), moving-frame generator SP 2861-2863, velocity errors SP 2954-2956, free moving energy
SP 2937-2958 (`eq:short-causal-free-moving`).

`freeMovingTransportLimit : FreeMovingTransportLimit` (statement in
`Sub/PartIII-a_T21_c3_2_1_1_org3_a_D.lean`).

Route (a weak-strong comparison in place of the Duhamel formula):
* the transported test `Ψ(z) = φ ∘ flow(z)` with the weight `P = (1+|y|²)^m` solves the radial Euler
  transport `∂_zΦ + V·∇_yΦ = 0`, `V = Ω(|y|)(-y₂, y₁)` (`fderiv_tprof_vort`); in physical
  variables `cmp = a Φ(z - z_s, x/√a)` has residual `∂_σ cmp + νΔ cmp + v·∇cmp =
  ν(Φ + Δ_yΦ - ½y·∇_yΦ) + √a (v - V_iso)·∇_yΦ` (`cmpRes_eq`);
* the free cylinder flow agrees a.e. with the regular flow (`cylClassicalExists`,
  `cylWeakEqClassical`), and the pairing `I(σ) = ∫ ω(σ) cmp(σ)` has right derivative
  `∫ ω cmpRes` (`pairing_hasDeriv`: differentiation under the integral sign and integration by
  parts against the compactly supported `cmp`); with `ν ≤ (ba)⁻¹` on `θ ≥ b`, the velocity gap
  `ε' a^{-3/2}` (`fmrVelGap`) and the energy bound (`freeMovingEnergy`) it moves by at most
  `2RL(C_Q/b + ε'C_Y)(z_t - z_s)` (`drift_bound`);
* `‖X - T Wφ‖² = E(t) - 2 I(t) + ‖ψ‖²` with `E(t) ≤ e^{2κB}‖Wφ‖²`, `‖ψ‖ = ‖T Wφ‖ ≤ ‖Wφ‖`,
  `I(s) = ‖Wφ‖²` (`point_bound`), and the constants are chosen in the successive limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub

open D1Aux

theorem freeMovingTransportLimit : UnforcedLeray.Short.IIIa.RelFreeTestSub.FreeMovingTransportLimit := by
  intro m hm B hB ε hε φ hφs hφc Wφ hWφ
  -- the support radius
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, tsupport φ ⊆ Metric.closedBall 0 R₀ :=
    hφc.isCompact.isBounded.subset_closedBall 0
  set R : ℝ := 2 * |R₀| + 1 with hRdef
  have hR : 0 < R := by positivity
  have hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0 := by
    intro y hy
    by_contra hne
    have hy' := hR₀ (subset_tsupport φ hne)
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs] at hy'
    have h1 : |y.1| ≤ |R₀| := (le_max_left _ _).trans (hy'.trans (le_abs_self _))
    have h2 : |y.2| ≤ |R₀| := (le_max_right _ _).trans (hy'.trans (le_abs_self _))
    have h3 : y.1 ^ 2 ≤ |R₀| ^ 2 := by
      rw [← sq_abs y.1]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h4 : y.2 ^ 2 ≤ |R₀| ^ 2 := by
      rw [← sq_abs y.2]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h5 : R ^ 2 = 4 * |R₀| ^ 2 + 4 * |R₀| + 1 := by rw [hRdef]; ring
    nlinarith [abs_nonneg R₀]
  -- the transported weighted profile and its slab bounds
  set Φ := tprof (gP m φ) with hΦdef
  have hΦ2 : ContDiff ℝ 2 Φ := contDiff_infty.1 (contDiff_tprof (contDiff_gP m hφs)) 2
  have hsupp : SuppIn R Φ := fun p hp => tprof_eq_zero (gP_eq_zero hφR) hp
  have hQc : Continuous (bracketQ Φ) := by
    have hD : Continuous (fun p => fderiv ℝ Φ p) := hΦ2.continuous_fderiv (by norm_num)
    have hdYY : ∀ j : Fin 2, Continuous (dYY Φ j) := fun j =>
      ((contDiff_dY hΦ2 j).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have e : bracketQ Φ = fun p => Φ p + (dYY Φ 0 p + dYY Φ 1 p) -
        1 / 2 * fderiv ℝ Φ p (0, p.2) := rfl
    rw [e]
    exact (hΦ2.continuous.add ((hdYY 0).add (hdYY 1))).sub
      (continuous_const.mul (hD.clm_apply (continuous_const.prodMk continuous_snd)))
  obtain ⟨CQ, hCQ0, hCQ⟩ := exists_bound_slab hQc hR.le (suppIn_bracketQ hsupp) B
  obtain ⟨CY0, hCY00, hCY0⟩ :=
    exists_bound_slab (contDiff_dY hΦ2 0).continuous hR.le (suppIn_dY hsupp 0) B
  obtain ⟨CY1, hCY10, hCY1⟩ :=
    exists_bound_slab (contDiff_dY hΦ2 1).continuous hR.le (suppIn_dY hsupp 1) B
  set CY := CY0 + CY1 with hCYdef
  have hCY : ∀ j : Fin 2, ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 → p.1 ≤ B → |dY Φ j p| ≤ CY := by
    intro j p h1 h2
    have e0 := hCY0 p h1 h2
    have e1 := hCY1 p h1 h2
    match j with
    | 0 => linarith
    | 1 => linarith
  have hCYnn : 0 ≤ CY := by positivity
  -- the constants of the successive limit
  set N := ‖Wφ‖ with hNdef
  have hq : 0 < ε ^ 2 / (2 * (N ^ 2 + 1)) := by positivity
  have hlogpos : 0 < Real.log (1 + ε ^ 2 / (2 * (N ^ 2 + 1))) := Real.log_pos (by linarith)
  set κ : ℝ := min 1 (Real.log (1 + ε ^ 2 / (2 * (N ^ 2 + 1))) / (2 * B)) with hκdef
  have hκ : 0 < κ := lt_min one_pos (div_pos hlogpos (by linarith))
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκB : 2 * κ * B ≤ Real.log (1 + ε ^ 2 / (2 * (N ^ 2 + 1))) := by
    have h := min_le_right 1 (Real.log (1 + ε ^ 2 / (2 * (N ^ 2 + 1))) / (2 * B))
    rw [← hκdef, le_div_iff₀ (by linarith)] at h
    linarith
  set Lb : ℝ := Real.exp B * N + 1 with hLbdef
  have hLb0 : 0 < Lb := by positivity
  have hLbN : Real.exp B * N ≤ Lb := by linarith
  set ε' : ℝ := ε ^ 2 / (16 * R * Lb * B * (CY + 1)) with hε'def
  have hε'0 : 0 < ε' := by positivity
  set ε₁ : ℝ := κ / 2 with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  obtain ⟨b₁, H1⟩ := freeMovingEnergy m hm ε₁ hε₁
  obtain ⟨b₂, H2⟩ := fmeRate m hm ε₁ hε₁
  refine ⟨max (max 1 (max b₁ b₂)) (max (2 * normGrowthConst m / κ)
    (16 * R * Lb * B * CQ / ε ^ 2 + 1)), le_trans (le_max_left _ _) (le_max_left _ _),
    fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb
  have hbb₁ : b₁ ≤ b :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hb
  have hbb₂ : b₂ ≤ b :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hb
  have hbC : 2 * normGrowthConst m / κ ≤ b :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hbQ : 16 * R * Lb * B * CQ / ε ^ 2 + 1 ≤ b :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  have hb0 : 0 < b := by linarith
  have hk : normGrowthConst m / b + ε₁ ≤ κ := by
    have h1 : normGrowthConst m / b ≤ κ / 2 := by
      rw [div_le_iff₀ hb0]
      rw [div_le_iff₀ hκ] at hbC
      linarith
    linarith
  obtain ⟨ν₁, hν₁, H1'⟩ := H1 b hbb₁
  obtain ⟨ν₂, hν₂, H2'⟩ := H2 b hbb₂
  obtain ⟨ν₃, hν₃, H3'⟩ := fmrVelGap b hb0 ε' hε'0
  obtain ⟨ν₄, hν₄, H4'⟩ := fmrTrainClose b hb0
  have hRν : 0 < 1 / (2 * R + 1) := by positivity
  refine ⟨min (min ν₁ ν₂) (min (min ν₃ ν₄) (min 1 (1 / (2 * R + 1)))),
    lt_min (lt_min hν₁ hν₂) (lt_min (lt_min hν₃ hν₄) (lt_min one_pos hRν)),
    fun ν hν tr htr s t hs hst hθ hBz f hf hfφ ω₀ hω₀ X hX => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hνν₁ : ν ≤ ν₁ := hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνν₂ : ν ≤ ν₂ := hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνν₃ : ν ≤ ν₃ :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hνν₄ : ν ≤ ν₄ :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hν1 : ν ≤ 1 :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνR' : ν ≤ 1 / (2 * R + 1) :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hνR : ν * (2 * R + 1) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hνR'
    exact hνR'
  have hPB := point_bound hm hB hφs hR hφR Wφ hWφ hCQ hCY hκ1 hLb0 hLbN hb1 hε₁ hk hε'0.le
    hνpos hν1 hνR tr htr (H1' ν ⟨hνpos, hνν₁⟩ tr htr)
    (fun t' s' ht' hts' hθ' f' hf' w hw =>
      ⟨(H2' ν ⟨hνpos, hνν₂⟩ tr htr t' s' ht' hts' hθ' f' hf' w hw).1,
        (H2' ν ⟨hνpos, hνν₂⟩ tr htr t' s' ht' hts' hθ' f' hf' w hw).2.1⟩)
    (H3' ν ⟨hνpos, hνν₃⟩ tr htr) (H4' ν ⟨hνpos, hνν₄⟩ tr htr) hs hst hθ hBz hf hfφ hω₀ X hX
  -- the numerics
  have hA : (Real.exp (2 * κ * B) - 1) * N ^ 2 ≤ ε ^ 2 / 2 := by
    have h1 : Real.exp (2 * κ * B) ≤ 1 + ε ^ 2 / (2 * (N ^ 2 + 1)) := by
      calc Real.exp (2 * κ * B) ≤ Real.exp (Real.log (1 + ε ^ 2 / (2 * (N ^ 2 + 1)))) :=
            Real.exp_le_exp.2 hκB
        _ = 1 + ε ^ 2 / (2 * (N ^ 2 + 1)) := Real.exp_log (by linarith)
    calc (Real.exp (2 * κ * B) - 1) * N ^ 2 ≤ ε ^ 2 / (2 * (N ^ 2 + 1)) * N ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ ε ^ 2 / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          have := sq_nonneg ε
          linarith
  have hBQ : 2 * B * (2 * R * Lb * (CQ / b)) ≤ ε ^ 2 / 4 := by
    have h1 : 16 * R * Lb * B * CQ / ε ^ 2 < b := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    rw [show 2 * B * (2 * R * Lb * (CQ / b)) = 4 * R * Lb * B * CQ / b by ring,
      div_le_iff₀ hb0]
    linarith
  have hBY : 2 * B * (2 * R * Lb * (ε' * CY)) ≤ ε ^ 2 / 4 := by
    have e : 2 * B * (2 * R * Lb * (ε' * CY)) = ε ^ 2 * CY / (4 * (CY + 1)) := by
      rw [hε'def]
      field_simp
      ring
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := sq_nonneg ε
    linarith
  have hfin : (Real.exp (2 * κ * B) - 1) * ‖Wφ‖ ^ 2 +
      2 * B * (2 * R * Lb * (CQ / b + ε' * CY)) ≤ ε ^ 2 := by
    have e : (Real.exp (2 * κ * B) - 1) * ‖Wφ‖ ^ 2 + 2 * B * (2 * R * Lb * (CQ / b + ε' * CY)) =
        (Real.exp (2 * κ * B) - 1) * N ^ 2 + 2 * B * (2 * R * Lb * (CQ / b)) +
          2 * B * (2 * R * Lb * (ε' * CY)) := by rw [hNdef]; ring
    rw [e]
    linarith
  have hsq := hPB.trans hfin
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 hsq

end UnforcedLeray.Short.IIIa.RelFreeTestSub
