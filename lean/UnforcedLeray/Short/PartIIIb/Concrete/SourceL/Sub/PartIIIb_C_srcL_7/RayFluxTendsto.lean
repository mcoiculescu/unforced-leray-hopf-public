import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7

/-!
# `RayFluxTendsto`: the boundary term at infinity vanishes (task `PartIII-b:C/srcL/7/14`)

Source of record: `the November 2 reference manuscript`, lines 4184-4185.
For `ρ ≥ max r 1` (`r = cylR y`) the point `p = rayPt y ρ` has `cylR p = ρ`, `ρ ≤ 2‖p‖`, and the
`k = 0` decay gives `‖Z p‖ ≤ |C| (1+‖p‖)^{-4} ≤ 16 |C| ρ^{-4}`, so
`|ρ Z_r(p)| ≤ 2ρ‖Z p‖ ≤ 32|C| (ρ⁻¹)^3 → 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rayFluxTendsto : RayFluxTendsto := by
  intro b Z hb hdec y hy
  have hr : 0 < cylR y := cylR_pos_of_lt hb hy
  obtain ⟨C, hC⟩ := hdec (cylR y ^ 2) hy 0
  have hC' : ∀ w : Vec3, cylR y ^ 2 ≤ cylR w ^ 2 → ‖Z w‖ ≤ |C| * (1 + ‖w‖) ^ (-(4 : ℝ)) := by
    intro w hw
    have h := hC w hw
    rw [norm_iteratedFDeriv_zero] at h
    have hexp : (-(4 + ((0 : ℕ) : ℝ))) = (-(4 : ℝ)) := by norm_num
    rw [hexp] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hyy0 : |y 0| ≤ cylR y := by
    have h2 := cylR_sq_sum y
    nlinarith [sq_abs (y 0), abs_nonneg (y 0), sq_nonneg (y 1)]
  have hyy1 : |y 1| ≤ cylR y := by
    have h2 := cylR_sq_sum y
    nlinarith [sq_abs (y 1), abs_nonneg (y 1), sq_nonneg (y 0)]
  have hu0 : |y 0 / cylR y| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]; exact hyy0
  have hu1 : |y 1 / cylR y| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]; exact hyy1
  have hbound : ∀ ρ : ℝ, max (cylR y) 1 ≤ ρ → |rayFlux Z y ρ| ≤ 32 * |C| * (ρ⁻¹) ^ 3 := by
    intro ρ hρ
    have hr1 : cylR y ≤ ρ := le_trans (le_max_left _ _) hρ
    have hρ1 : 1 ≤ ρ := le_trans (le_max_right _ _) hρ
    have hρpos : 0 < ρ := by linarith
    have hcp : cylR (rayPt y ρ) = ρ := by rw [cylR_rayPt y ρ hr, abs_of_pos hρpos]
    have hw : cylR y ^ 2 ≤ cylR (rayPt y ρ) ^ 2 := by rw [hcp]; nlinarith
    have hZ := hC' (rayPt y ρ) hw
    have hsq := cylR_sq_sum (rayPt y ρ)
    rw [hcp] at hsq
    have hn0 : |rayPt y ρ 0| ≤ ‖rayPt y ρ‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (rayPt y ρ) 0
    have hn1 : |rayPt y ρ 1| ≤ ‖rayPt y ρ‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (rayPt y ρ) 1
    have hρn : ρ ≤ 2 * ‖rayPt y ρ‖ := by
      have s0 : rayPt y ρ 0 ^ 2 ≤ ‖rayPt y ρ‖ ^ 2 := by
        nlinarith [sq_abs (rayPt y ρ 0), abs_nonneg (rayPt y ρ 0), norm_nonneg (rayPt y ρ)]
      have s1 : rayPt y ρ 1 ^ 2 ≤ ‖rayPt y ρ‖ ^ 2 := by
        nlinarith [sq_abs (rayPt y ρ 1), abs_nonneg (rayPt y ρ 1), norm_nonneg (rayPt y ρ)]
      nlinarith [norm_nonneg (rayPt y ρ)]
    have hx : ρ / 2 ≤ 1 + ‖rayPt y ρ‖ := by linarith
    -- rewrite the rpow bound as an inverse power
    have hpow : (1 + ‖rayPt y ρ‖) ^ (-(4 : ℝ)) = ((1 + ‖rayPt y ρ‖) ^ 4)⁻¹ := by
      rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast]
    rw [hpow] at hZ
    have hinv : ((1 + ‖rayPt y ρ‖) ^ 4)⁻¹ ≤ 16 * (ρ⁻¹) ^ 4 := by
      have hA : 0 < ρ / 2 := by linarith
      have hp : (ρ / 2) ^ 4 ≤ (1 + ‖rayPt y ρ‖) ^ 4 := pow_le_pow_left₀ hA.le hx 4
      have h1 := inv_anti₀ (pow_pos hA 4) hp
      have h2 : ((ρ / 2) ^ 4)⁻¹ = 16 * (ρ⁻¹) ^ 4 := by
        field_simp
        ring
      rw [h2] at h1
      exact h1
    have hZn : ‖Z (rayPt y ρ)‖ ≤ |C| * (16 * (ρ⁻¹) ^ 4) :=
      hZ.trans (mul_le_mul_of_nonneg_left hinv (abs_nonneg C))
    have k0 : |y 0 / cylR y * Z (rayPt y ρ) 0| ≤ ‖Z (rayPt y ρ)‖ := by
      have ha : |Z (rayPt y ρ) 0| ≤ ‖Z (rayPt y ρ)‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (Z (rayPt y ρ)) 0
      rw [abs_mul]
      nlinarith [abs_nonneg (y 0 / cylR y), abs_nonneg (Z (rayPt y ρ) 0), norm_nonneg (Z (rayPt y ρ))]
    have k1 : |y 1 / cylR y * Z (rayPt y ρ) 1| ≤ ‖Z (rayPt y ρ)‖ := by
      have ha : |Z (rayPt y ρ) 1| ≤ ‖Z (rayPt y ρ)‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (Z (rayPt y ρ)) 1
      rw [abs_mul]
      nlinarith [abs_nonneg (y 1 / cylR y), abs_nonneg (Z (rayPt y ρ) 1), norm_nonneg (Z (rayPt y ρ))]
    have hsum : |y 0 / cylR y * Z (rayPt y ρ) 0 + y 1 / cylR y * Z (rayPt y ρ) 1| ≤
        2 * ‖Z (rayPt y ρ)‖ :=
      le_trans (abs_add_le _ _) (by linarith)
    unfold rayFlux
    rw [abs_mul, abs_of_pos hρpos]
    have hρ4 : ρ * (16 * (ρ⁻¹) ^ 4) = 16 * (ρ⁻¹) ^ 3 := by
      field_simp
    calc ρ * |y 0 / cylR y * Z (rayPt y ρ) 0 + y 1 / cylR y * Z (rayPt y ρ) 1|
        ≤ ρ * (2 * ‖Z (rayPt y ρ)‖) := mul_le_mul_of_nonneg_left hsum hρpos.le
      _ ≤ ρ * (2 * (|C| * (16 * (ρ⁻¹) ^ 4))) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hρpos.le
      _ = 2 * |C| * (ρ * (16 * (ρ⁻¹) ^ 4)) := by ring
      _ = 32 * |C| * (ρ⁻¹) ^ 3 := by rw [hρ4]; ring
  have hlim : Tendsto (fun ρ : ℝ => 32 * |C| * (ρ⁻¹) ^ 3) atTop (𝓝 0) := by
    have h1 : Tendsto (fun ρ : ℝ => ρ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have h2 : Tendsto (fun ρ : ℝ => (ρ⁻¹) ^ 3) atTop (𝓝 ((0 : ℝ) ^ 3)) :=
      (((continuous_pow 3).tendsto (0 : ℝ)).comp h1)
    have h3 := h2.const_mul (32 * |C|)
    simpa using h3
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (max (cylR y) 1)] with ρ hρ
  rw [Real.norm_eq_abs]
  exact hbound ρ hρ

end UnforcedLeray.Short.PartIIIb.Concrete
