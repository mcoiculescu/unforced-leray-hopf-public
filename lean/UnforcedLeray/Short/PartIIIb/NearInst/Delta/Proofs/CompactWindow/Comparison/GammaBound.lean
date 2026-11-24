import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2

/-!
# `gammaWindowBound` (source 3962-3967: `Γ^K ≤ P_ν ε^{-K(a+b)}`)

With `m = 3`, `c = ν^{-2}`, `σ = l/2`, `H₁ = r+1`, `L₁ = |L_⊥|+1`, `M = γ_* = 1/4`:
every term of `Γ` is bounded by a universal multiple of `G := ν^{-3} ε^{-8(a+b)}`, using
`ν^{-1} ≥ 1`, `ε^{-a} ≤ ε^{-8(a+b)}`, `ε^{-b} ≤ ε^{-8(a+b)}`, `(ε^{-a})^8 = ε^{-8a} ≤ ε^{-8(a+b)}`,
`1/l ≤ ε^{-a}` (from `ε^a ≤ l`), `r ≤ ε^{-b}`, `√S ≤ S` for `S ≥ 1`, and the cutoff norm hypothesis
`‖χ‖_{C⁸} + ‖χ₁‖_{C⁸} ≤ C₀(1+l⁻¹)⁸ ≤ 256 C₀ ε^{-8a}`. The constant is
`A = 20 + 3|C_⊥| + 256 C₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartIIa in
theorem gammaWindowBound : GammaWindowBound := by
  intro C0 hC0
  refine ⟨3, fun Cperp => ⟨20 + 3 * |Cperp| + 256 * C0, ?_, ?_⟩⟩
  · have := abs_nonneg Cperp
    linarith
  intro ν c ε a b l r χ χ1 hν hν1 hc hε hε1 ha hb hal hr hn
  have hεa : 0 < ε ^ a := Real.rpow_pos_of_pos hε a
  have hl : 0 < l := lt_of_lt_of_le hεa hal
  have hli : 0 < l⁻¹ := inv_pos.2 hl
  have hu0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hu1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hcu : c = ν⁻¹ ^ 2 := by rw [hc, inv_pow]
  have hci : c⁻¹ = ν ^ 2 := by rw [hc, inv_inv]
  -- the exponential quantities
  have hE1 : 1 ≤ ε ^ (-(8 * (a + b))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hP1 : 1 ≤ ε ^ (-a) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hQ1 : 1 ≤ ε ^ (-b) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hPE : ε ^ (-a) ≤ ε ^ (-(8 * (a + b))) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hQE : ε ^ (-b) ≤ ε ^ (-(8 * (a + b))) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hlP : l⁻¹ ≤ ε ^ (-a) := by
    rw [Real.rpow_neg hε.le]
    exact inv_anti₀ hεa hal
  have hP8 : (ε ^ (-a)) ^ 8 ≤ ε ^ (-(8 * (a + b))) := by
    have h1 : (ε ^ (-a)) ^ 8 = ε ^ (-(8 * a)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      congr 1
      push_cast
      ring
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  -- the common bound `G`
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = ν⁻¹ ^ 3 * ε ^ (-(8 * (a + b))) := ⟨_, rfl⟩
  have hu3 : 1 ≤ ν⁻¹ ^ 3 := one_le_pow₀ hu1
  have hG1 : 1 ≤ G := by
    rw [hGdef]; exact one_le_mul_of_one_le_of_one_le hu3 hE1
  have hEG : ε ^ (-(8 * (a + b))) ≤ G := by
    rw [hGdef]; exact le_mul_of_one_le_left (by linarith) hu3
  have hu3G : ν⁻¹ ^ 3 ≤ G := by
    rw [hGdef]; exact le_mul_of_one_le_right (by linarith) hE1
  have hu1G : ν⁻¹ ≤ G :=
    le_trans (le_self_pow₀ hu1 (by norm_num : (3 : ℕ) ≠ 0)) hu3G
  have hu2G : ν⁻¹ ^ 2 ≤ G :=
    le_trans (pow_le_pow_right₀ hu1 (by norm_num : 2 ≤ 3)) hu3G
  have hνG : ν ≤ G := le_trans hν1 hG1
  have hν2G : ν ^ 2 ≤ G := le_trans (pow_le_one₀ hν.le hν1) hG1
  have hc1 : c ≤ G := by rw [hcu]; exact hu2G
  have hc1' : c⁻¹ ≤ G := by rw [hci]; exact hν2G
  -- the window pieces
  have hsig : (l / 2)⁻¹ = 2 * l⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hσG : (l / 2)⁻¹ ≤ 2 * G := by
    rw [hsig]; linarith [hlP, hPE, hEG]
  have hH1G : r + 1 ≤ 2 * G := by linarith [hr, hQE, hEG, hG1]
  have hT : c / ν = ν⁻¹ ^ 3 := by
    rw [hcu, div_eq_mul_inv]; ring
  have hsqrt : Real.sqrt (ε ^ (-b)) ≤ ε ^ (-(8 * (a + b))) :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith [hQE, hE1]⟩
  have hLabs : |transL Cperp c ν (ε ^ (-b))| =
      |Cperp| * (ν⁻¹ ^ 3 + Real.sqrt (ε ^ (-b)) + 1) := by
    unfold transL
    rw [hT, abs_mul]
    congr 1
    rw [abs_of_nonneg]
    have := Real.sqrt_nonneg (ε ^ (-b))
    have := pow_nonneg hu0 3
    linarith
  have hin : ν⁻¹ ^ 3 + Real.sqrt (ε ^ (-b)) + 1 ≤ 3 * G := by
    linarith [hu3G, hsqrt, hEG, hG1]
  have hLG : |transL Cperp c ν (ε ^ (-b))| ≤ 3 * |Cperp| * G := by
    rw [hLabs]
    calc |Cperp| * (ν⁻¹ ^ 3 + Real.sqrt (ε ^ (-b)) + 1)
        ≤ |Cperp| * (3 * G) := mul_le_mul_of_nonneg_left hin (abs_nonneg _)
      _ = 3 * |Cperp| * G := by ring
  -- the cutoff norms
  have h2P : 1 + l⁻¹ ≤ 2 * ε ^ (-a) := by linarith [hlP, hP1]
  have hpow : (1 + l⁻¹) ^ 8 ≤ 256 * (ε ^ (-a)) ^ 8 := by
    calc (1 + l⁻¹) ^ 8 ≤ (2 * ε ^ (-a)) ^ 8 :=
          pow_le_pow_left₀ (by linarith) h2P 8
      _ = 256 * (ε ^ (-a)) ^ 8 := by rw [mul_pow]; norm_num
  have hcN : cNorm8 χ + cNorm8 χ1 ≤ 256 * C0 * G := by
    have h1 : (1 + l⁻¹) ^ 8 ≤ 256 * G := by linarith [hpow, hP8, hEG]
    have h2 := mul_le_mul_of_nonneg_left h1 hC0
    linarith [hn, h2]
  -- assemble
  have hRHS : (20 + 3 * |Cperp| + 256 * C0) * ν⁻¹ ^ 3 * ε ^ (-(8 * (a + b)))
      = (20 + 3 * |Cperp| + 256 * C0) * G := by
    rw [hGdef]; ring
  have h14 : (1 / 4 : ℝ) ⁻¹ = 4 := by norm_num
  unfold Gamma GammaBox
  rw [hRHS]
  linarith [hσG, hH1G, hLG, hc1, hc1', hu1G, hνG, hcN, hG1, h14, hu0]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
