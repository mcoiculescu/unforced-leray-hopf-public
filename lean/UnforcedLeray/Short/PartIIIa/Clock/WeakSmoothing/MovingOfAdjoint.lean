import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint

/-!
# Part III-a full clock: the moving weak-to-strong bound from the adjoint energies (SP 3060-3082)

`movingWeakStrong_of`: the scalar chain `AdjointEnergyChain` (SP 3072-3073), the energy
inequalities `AdjointEnergyIneqs` (SP 3060-3071), the duality facts `AdjointDuality`
(SP 3036-3040, 3044, 3074-3075) and the existence of the adjoint `AdjointExists` give
`MovingWeakStrong m` (SP 3074-3075), with the clock identities `deltaZ_eq` and
`betaMin_mul_deltaZ` (SP 3077-3082).

Proof. Take `b ≥ max b₀ 1`. For a terminal datum `G` with `‖G‖_{X_{-m,d_s}} ≤ 1` take the adjoint
`φ`; its energies satisfy the chain hypotheses with `β = β_min = ν a_t ≤ ν a_s = θ(s)⁻¹ ≤ 1` and
`0 < Δz ≤ s - t ≤ 1`. The chain gives `E_0(Δz) + E_1(Δz) ≤ 2K(β_minΔz)⁻¹E_0(0)` (`β_minΔz ≤ 1`),
the terminal bound gives `E_0(0) ≤ C_t`, the pairing bound gives
`|∫ W(z_s) G| ≤ ‖J_{a_t}⁻¹f‖_{(H^1)^*} C_p (2KC_t)^{1/2} (β_minΔz)^{-1/2}`, and
`β_minΔz = ν(s-t)/a_s`. Take the supremum over `G` (`XNormDuality`). The smallness `ν ≤ ν₀` is
the minimum of those of the energy inequalities, the existence of the adjoint and the pairing bound
(each for the BUC trains `PartI.IsBUCTrain`, SP 270-288).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `√(x⁻¹) = x^{-1/2}` for `x ≥ 0`. -/
theorem sqrt_inv_eq_rpow {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x⁻¹ = x ^ (-1 / 2 : ℝ) := by
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
    Real.rpow_neg hx]

/-- The real step: with `A ≤ K E`, `B ≤ K y⁻¹ E`, `0 ≤ E ≤ C_t`, `0 < y ≤ 1`,
`C_p √(A + B) ≤ C_p √(2 K C_t) y^{-1/2}`. -/
theorem chain_real_step {A B E K Ct Cp y : ℝ} (hK : 0 ≤ K) (hCp : 0 ≤ Cp) (hE : 0 ≤ E)
    (hECt : E ≤ Ct) (hy0 : 0 < y) (hy1 : y ≤ 1) (hA : A ≤ K * E) (hB : B ≤ K * y⁻¹ * E) :
    Cp * Real.sqrt (A + B) ≤ Cp * Real.sqrt (2 * K * Ct) * y ^ (-1 / 2 : ℝ) := by
  have hyinv : 1 ≤ y⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hy1 (inv_nonneg.2 hy0.le)
    rwa [inv_mul_cancel₀ hy0.ne', mul_one] at h
  have hCt : 0 ≤ Ct := le_trans hE hECt
  have h1 : K * E ≤ K * y⁻¹ * E := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyinv hK) hE
    simpa [mul_one] using this
  have h2 : K * y⁻¹ * E ≤ K * y⁻¹ * Ct :=
    mul_le_mul_of_nonneg_left hECt (mul_nonneg hK (inv_nonneg.2 hy0.le))
  have hsum : A + B ≤ 2 * K * Ct * y⁻¹ := by nlinarith
  have hsq : Real.sqrt (A + B) ≤ Real.sqrt (2 * K * Ct) * Real.sqrt y⁻¹ := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hsum
  rw [sqrt_inv_eq_rpow hy0.le] at hsq
  calc Cp * Real.sqrt (A + B) ≤ Cp * (Real.sqrt (2 * K * Ct) * y ^ (-1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq hCp
    _ = Cp * Real.sqrt (2 * K * Ct) * y ^ (-1 / 2 : ℝ) := by ring

theorem revE0_nonneg (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) : 0 ≤ revE0 ν c m φ s ζ :=
  adjE0_nonneg _ _ _

theorem revE1_nonneg (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) : 0 ≤ revE1 ν c m φ s ζ :=
  adjE1_nonneg _ _ _

theorem revE2_nonneg (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) : 0 ≤ revE2 ν c m φ s ζ :=
  adjE2_nonneg _ _ _

/-- **The moving weak-to-strong bound from the adjoint energies** (SP 3060-3082). -/
theorem movingWeakStrong_of (m : ℝ) (hOde : AdjointEnergyChain) (hIneq : AdjointEnergyIneqs m)
    (hDual : AdjointDuality m) (hEx : AdjointExists m) : MovingWeakStrong m := by
  obtain ⟨hX, ⟨Ct, hCt0, hT⟩, ⟨Cp, νP, hCp0, hνP, hP⟩⟩ := hDual
  obtain ⟨b₀, hb₀⟩ := hIneq
  obtain ⟨νE, hνE, hEx⟩ := hEx
  refine ⟨max b₀ 1, fun b hb => ?_⟩
  obtain ⟨C, ν₀, hC0, hν₀, hE⟩ := hb₀ b (le_trans (le_max_left _ _) hb)
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  obtain ⟨K, hK0, hK⟩ := hOde C hC0
  refine ⟨Cp * Real.sqrt (2 * K * Ct), min (min ν₀ νE) νP, lt_min (lt_min hν₀ hνE) hνP, ?_⟩
  intro ν hν' tr htr t s ht hts hs1 hbs f hf hz w u hw
  have hν : ν ∈ Ioc 0 ν₀ :=
    ⟨hν'.1, hν'.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hνE' : ν ∈ Ioc 0 νE :=
    ⟨hν'.1, hν'.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hνP' : ν ∈ Ioc 0 νP := ⟨hν'.1, hν'.2.trans (min_le_right _ _)⟩
  have hν0 : 0 < ν := hν.1
  have hat1 : 1 ≤ clockA ν t := by
    unfold clockA; nlinarith [mul_nonneg hν0.le ht]
  have has1 : 1 ≤ clockA ν s := by
    unfold clockA; nlinarith [mul_nonneg hν0.le (le_trans ht hts.le)]
  have hat : 0 < clockA ν t := lt_of_lt_of_le one_pos hat1
  have has : 0 < clockA ν s := lt_of_lt_of_le one_pos has1
  have hats : clockA ν t ≤ clockA ν s := by
    unfold clockA; nlinarith [mul_le_mul_of_nonneg_left hts.le hν0.le]
  -- `β_min ≤ ν a_s = θ(s)⁻¹ ≤ 1`
  have hνas : ν * clockA ν s ≤ 1 := by
    have hpos : 0 < ν * clockA ν s := mul_pos hν0 has
    have h1 : 1 ≤ (ν * clockA ν s)⁻¹ := le_trans hb1 hbs
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rwa [mul_one, mul_inv_cancel₀ hpos.ne'] at h2
  have hβ0 : 0 < betaMin ν t := mul_pos hν0 hat
  have hβ1 : betaMin ν t ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hats hν0.le) hνas
  -- `0 < Δz ≤ s - t ≤ 1`
  have hΔeq := deltaZ_eq ν t s hat.ne' has.ne'
  have hΔ0 : 0 < deltaZ ν t s := by
    rw [hΔeq]; exact div_pos (by linarith) (mul_pos has hat)
  have hΔ1 : deltaZ ν t s ≤ 1 := by
    rw [hΔeq]
    exact le_trans (div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le has1 hat1)) hs1
  have hβΔ := betaMin_mul_deltaZ ν t s hat.ne' has.ne'
  have hy0 : 0 < betaMin ν t * deltaZ ν t s := mul_pos hβ0 hΔ0
  have hy1 : betaMin ν t * deltaZ ν t s ≤ 1 := by
    calc betaMin ν t * deltaZ ν t s ≤ 1 * 1 :=
          mul_le_mul hβ1 hΔ1 hΔ0.le zero_le_one
      _ = 1 := one_mul 1
  refine le_trans (hX ν hν0 tr t s ht hts.le f hf w u hw) ?_
  refine iSup_le fun G => iSup_le fun hG => iSup_le fun hG1 => ?_
  obtain ⟨φ, hφ⟩ := hEx ν hνE' tr htr t s ht hts G hG
  obtain ⟨hc0, hc1, hd0, hd1⟩ := hE ν hν tr htr t s ht hts hs1 hbs G hG φ hφ
  obtain ⟨hK1, hK2⟩ := hK (betaMin ν t) (deltaZ ν t s) hβ0 hβ1 hΔ0 hΔ1 _ _ _ hc0 hc1
    (fun ζ _ => revE0_nonneg _ _ _ _ _ ζ) (fun ζ _ => revE1_nonneg _ _ _ _ _ ζ)
    (fun ζ _ => revE2_nonneg _ _ _ _ _ ζ) hd0 hd1
  have hTb := hT ν hν0 tr t s ht hts G hG φ hφ
  have hG1' : (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m) G).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hG1
    simpa using this
  have hE00 : revE0 ν (ν ^ (-2 : ℝ)) m φ s 0 ≤ Ct := by
    refine le_trans hTb ?_
    have h0 : 0 ≤ (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m) G).toReal :=
      ENNReal.toReal_nonneg
    have hsq : (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m) G).toReal ^ 2 ≤ 1 :=
      pow_le_one₀ h0 hG1'
    exact le_trans (mul_le_mul_of_nonneg_left hsq hCt0) (le_of_eq (mul_one Ct))
  have hPb := hP ν hνP' tr htr t s ht hts G hG φ hφ f hf hz w u hw
  refine le_trans hPb ?_
  rw [mul_comm]
  gcongr ENNReal.ofReal ?_ * _
  rw [← hβΔ]
  exact chain_real_step hK0 hCp0 (revE0_nonneg _ _ _ _ _ _) hE00 hy0 hy1 hK1 hK2

end UnforcedLeray.Short.IIIa
