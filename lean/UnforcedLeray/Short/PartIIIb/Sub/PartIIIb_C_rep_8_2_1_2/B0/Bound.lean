import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.B0.Core

/-!
# The common `j = 0, 2` bound for the raw ring derivative (`PartIII-b:C/rep/8/2/1/2/7`, `/9`)

With `D₀ := ∂_{chart}` of `b_raw` at the chart point (`Core.lean`), the `j = 0` difference is
`s · merSp(ε V − ε² U)` where `V = H_q e₁ − v − 2∂_σv − η∂_η v` and `U = (H + 2∂_σH·… ) e₁`
(source 2073-2077, 5462-5476).  Its norm is at most `18 ε s 𝔴₃` for `ε ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

theorem rawD1_dQ (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    UnforcedLeray.Axi.dQ (bRaw L) p =
      fderiv ℝ (trainFv L) (Real.log p.1, p.2) (0, (1, 0)) +
        (L.ε * fderiv ℝ (rawH L) (Real.log p.1, p.2) (0, (1, 0))) • rawE1 := by
  unfold UnforcedLeray.Axi.dQ
  rw [bRaw_fderiv_apply L hp]
  dsimp only
  rw [mul_zero, rawPhi_fderiv_apply]

theorem rawD1_dS (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    p.1 • UnforcedLeray.Axi.dS (bRaw L) p =
      fderiv ℝ (trainFv L) (Real.log p.1, p.2) (1, (0, 0)) +
        (L.ε * fderiv ℝ (rawH L) (Real.log p.1, p.2) (1, (0, 0))) • rawE1 := by
  unfold UnforcedLeray.Axi.dS
  rw [bRaw_fderiv_apply L hp]
  dsimp only
  have hsm : ((p.1)⁻¹ * (1 : ℝ), ((0 : ℝ), (0 : ℝ))) = (p.1)⁻¹ • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
    simp
  rw [hsm, map_smul, rawPhi_fderiv_apply, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

theorem rawD1_dEta (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    UnforcedLeray.Axi.dEta (bRaw L) p =
      fderiv ℝ (trainFv L) (Real.log p.1, p.2) (0, (0, 1)) +
        (L.ε * fderiv ℝ (rawH L) (Real.log p.1, p.2) (0, (0, 1))) • rawE1 := by
  unfold UnforcedLeray.Axi.dEta
  rw [bRaw_fderiv_apply L hp]
  dsimp only
  rw [mul_zero, rawPhi_fderiv_apply]

theorem rawD1_flat0 (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    vecSp (flatD1 L p.1 p.2 0) =
      merSp (fderiv ℝ (trainFv L) (Real.log p.1, p.2) (0, (1, 0))) := by
  rw [vecSp_flatD1 L hp 0]
  rfl

theorem rawD1_flat2 (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    vecSp (flatD1 L p.1 p.2 2) =
      merSp (fderiv ℝ (trainFv L) (Real.log p.1, p.2) (0, (0, 1))) := by
  rw [vecSp_flatD1 L hp 2]
  rfl

/-- Triangle inequality for real numbers, via the norm. -/
theorem abs_add3_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  simp only [Real.norm_eq_abs] at h1 h2
  linarith

/-- The `j = 0` core estimate (source 2073-2077, 5462-5476). -/
theorem rawD1Core (L : ReturnLevel) (hε : L.ε ≤ 1) {p : Chart} (hp : 0 < p.1) :
    ‖p.1 • merSp (UnforcedLeray.Axi.dQ (bRaw L) p - L.ε • (bRaw L p + (2 * p.1) •
        UnforcedLeray.Axi.dS (bRaw L) p + p.2.2 • UnforcedLeray.Axi.dEta (bRaw L) p)) -
        p.1 • vecSp (flatD1 L p.1 p.2 0)‖ ≤ 18 * L.ε * p.1 * trainWeight 3 L p := by
  have hε0 : 0 < L.ε := L.ε_pos
  have hbR : bRaw L p = trainFv L (Real.log p.1, p.2) +
      (L.ε * rawH L (Real.log p.1, p.2)) • rawE1 := by
    rw [bRaw_eq_phi L hp]
    rfl
  rw [show (2 * p.1) • UnforcedLeray.Axi.dS (bRaw L) p =
      (2 : ℝ) • (p.1 • UnforcedLeray.Axi.dS (bRaw L) p) from mul_smul _ _ _,
    rawD1_dQ L hp, rawD1_dS L hp, rawD1_dEta L hp, hbR, rawD1_flat0 L hp]
  rw [← smul_sub, ← merSp_sub']
  set G0 := trainFv L (Real.log p.1, p.2) with hG0
  set Gq := fderiv ℝ (trainFv L) (Real.log p.1, p.2) (0, (1, 0)) with hGq
  set Gs := fderiv ℝ (trainFv L) (Real.log p.1, p.2) (1, (0, 0)) with hGs
  set Ge := fderiv ℝ (trainFv L) (Real.log p.1, p.2) (0, (0, 1)) with hGe
  set H0 := rawH L (Real.log p.1, p.2) with hH0
  set Hq := fderiv ℝ (rawH L) (Real.log p.1, p.2) (0, (1, 0)) with hHq
  set Hs := fderiv ℝ (rawH L) (Real.log p.1, p.2) (1, (0, 0)) with hHs
  set He := fderiv ℝ (rawH L) (Real.log p.1, p.2) (0, (0, 1)) with hHe
  set S := ringS L (Real.log p.1, p.2) with hS
  set η := p.2.2 with hη
  have hXeq : Gq + (L.ε * Hq) • rawE1 - L.ε • (G0 + (L.ε * H0) • rawE1 +
      (2 : ℝ) • (Gs + (L.ε * Hs) • rawE1) + η • (Ge + (L.ε * He) • rawE1)) - Gq =
      L.ε • (Hq • rawE1 - G0 - (2 : ℝ) • Gs - η • Ge) -
        (L.ε * L.ε) • ((H0 + 2 * Hs + η * He) • rawE1) := by
    module
  rw [hXeq, norm_smul, Real.norm_of_nonneg hp.le, merSp_norm]
  -- scalar and vector bounds
  have hS0 : 0 ≤ S := ringS_nonneg L (Real.log p.1, p.2)
  have hw1 : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hw2 : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hw3 : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hG0S : ‖G0‖ ≤ S := trainFv_val_le L (Real.log p.1, p.2)
  have hGsS : ‖Gs‖ ≤ S := trainFv_deriv_le L (Real.log p.1, p.2) hw2
  have hGeS : ‖Ge‖ ≤ S := trainFv_deriv_le L (Real.log p.1, p.2) hw3
  have hHqS : |Hq| ≤ 4 * S + |η| * S := rawH_deriv_le L (Real.log p.1, p.2) hw1
  have hHsS : |Hs| ≤ 4 * S + |η| * S := rawH_deriv_le L (Real.log p.1, p.2) hw2
  have hHeS : |He| ≤ 4 * S + |η| * S := rawH_deriv_le L (Real.log p.1, p.2) hw3
  have hH0S : |H0| ≤ 3 * ((1 + |η|) ^ 3 * S) := rawH_val_le L hp
  have ha1 : 1 + |η| ≤ (1 + |η|) ^ 3 :=
    le_self_pow₀ (by linarith [abs_nonneg η]) (by norm_num)
  have ha2 : (1 + |η|) ^ 2 ≤ (1 + |η|) ^ 3 :=
    pow_le_pow_right₀ (by linarith [abs_nonneg η]) (by norm_num)
  have hk1 : (1 + |η|) * S ≤ (1 + |η|) ^ 3 * S := mul_le_mul_of_nonneg_right ha1 hS0
  have hk2 : (1 + |η|) ^ 2 * S ≤ (1 + |η|) ^ 3 * S := mul_le_mul_of_nonneg_right ha2 hS0
  -- the vector V and the scalar U
  have hV : ‖Hq • rawE1 - G0 - (2 : ℝ) • Gs - η • Ge‖ ≤
      |Hq| + ‖G0‖ + 2 * ‖Gs‖ + |η| * ‖Ge‖ := by
    have h1 := norm_sub_le (Hq • rawE1 - G0 - (2 : ℝ) • Gs) (η • Ge)
    have h2 := norm_sub_le (Hq • rawE1 - G0) ((2 : ℝ) • Gs)
    have h3 := norm_sub_le (Hq • rawE1) G0
    have h4 : ‖Hq • rawE1‖ = |Hq| := by
      rw [norm_smul, rawE1_norm, mul_one, Real.norm_eq_abs]
    have h5 : ‖(2 : ℝ) • Gs‖ = 2 * ‖Gs‖ := by
      rw [norm_smul]
      norm_num
    have h6 : ‖η • Ge‖ = |η| * ‖Ge‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    linarith
  have hU : ‖(H0 + 2 * Hs + η * He) • rawE1‖ ≤ |H0| + 2 * |Hs| + |η| * |He| := by
    rw [norm_smul, rawE1_norm, mul_one, Real.norm_eq_abs]
    have h1 : |H0 + 2 * Hs + η * He| ≤ |H0 + 2 * Hs| + |η * He| := by
      have := norm_add_le (H0 + 2 * Hs) (η * He)
      simpa only [Real.norm_eq_abs] using this
    have h2 : |H0 + 2 * Hs| ≤ |H0| + |2 * Hs| := by
      have := norm_add_le H0 (2 * Hs)
      simpa only [Real.norm_eq_abs] using this
    have h3 : |2 * Hs| = 2 * |Hs| := by
      rw [abs_mul, abs_two]
    have h4 : |η * He| = |η| * |He| := abs_mul _ _
    linarith
  -- the two bounds `B1 ≤ 7 a S`, `B2 ≤ 11 a S`
  have hB1 : |Hq| + ‖G0‖ + 2 * ‖Gs‖ + |η| * ‖Ge‖ ≤ 7 * ((1 + |η|) ^ 3 * S) := by
    have h := mul_le_mul_of_nonneg_left hGeS (abs_nonneg η)
    linarith [mul_nonneg (abs_nonneg η) hS0]
  have hB2 : |H0| + 2 * |Hs| + |η| * |He| ≤ 11 * ((1 + |η|) ^ 3 * S) := by
    have h := mul_le_mul_of_nonneg_left hHeS (abs_nonneg η)
    linarith [mul_nonneg (abs_nonneg η) hS0,
      mul_nonneg (mul_nonneg (abs_nonneg η) (abs_nonneg η)) hS0]
  have hB2nn : 0 ≤ |H0| + 2 * |Hs| + |η| * |He| := by positivity
  -- the norm of the combination
  have hX : ‖L.ε • (Hq • rawE1 - G0 - (2 : ℝ) • Gs - η • Ge) -
      (L.ε * L.ε) • ((H0 + 2 * Hs + η * He) • rawE1)‖ ≤
      L.ε * (|Hq| + ‖G0‖ + 2 * ‖Gs‖ + |η| * ‖Ge‖) +
        (L.ε * L.ε) * (|H0| + 2 * |Hs| + |η| * |He|) := by
    have h := norm_sub_le (L.ε • (Hq • rawE1 - G0 - (2 : ℝ) • Gs - η • Ge))
      ((L.ε * L.ε) • ((H0 + 2 * Hs + η * He) • rawE1))
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hε0.le,
      Real.norm_of_nonneg (mul_nonneg hε0.le hε0.le)] at h
    have e1 := mul_le_mul_of_nonneg_left hV hε0.le
    have e2 := mul_le_mul_of_nonneg_left hU (mul_nonneg hε0.le hε0.le)
    linarith
  have hεε : L.ε * L.ε ≤ L.ε := mul_le_of_le_one_right hε0.le hε
  have hX18 : ‖L.ε • (Hq • rawE1 - G0 - (2 : ℝ) • Gs - η • Ge) -
      (L.ε * L.ε) • ((H0 + 2 * Hs + η * He) • rawE1)‖ ≤
      18 * (L.ε * ((1 + |η|) ^ 3 * S)) := by
    have e3 : (L.ε * L.ε) * (|H0| + 2 * |Hs| + |η| * |He|) ≤
        L.ε * (|H0| + 2 * |Hs| + |η| * |He|) :=
      mul_le_mul_of_nonneg_right hεε hB2nn
    have e4 := mul_le_mul_of_nonneg_left hB1 hε0.le
    have e5 := mul_le_mul_of_nonneg_left hB2 hε0.le
    linarith [hX, e3, e4, e5]
  calc p.1 * ‖L.ε • (Hq • rawE1 - G0 - (2 : ℝ) • Gs - η • Ge) -
        (L.ε * L.ε) • ((H0 + 2 * Hs + η * He) • rawE1)‖
      ≤ p.1 * (18 * (L.ε * ((1 + |η|) ^ 3 * S))) := mul_le_mul_of_nonneg_left hX18 hp.le
    _ = 18 * L.ε * p.1 * trainWeight 3 L p := by
      have htw : trainWeight 3 L p = (1 + |η|) ^ 3 * S := rfl
      rw [htw]
      ring

end UnforcedLeray.Short.PartIIIb.Concrete
