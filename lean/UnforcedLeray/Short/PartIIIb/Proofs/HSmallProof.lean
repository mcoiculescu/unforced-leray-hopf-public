import UnforcedLeray.Short.PartIIIb.Tasks
import UnforcedLeray.Short.PartIIIb.Proofs.PolyExp
import UnforcedLeray.Short.PartIIIb.Proofs.AstarExact

/-!
# Proof of `T_hsmall` (target `hsmallProof`)

Source: `the November 2 reference manuscript`, lines 5883-5909 (budget
`1.1 a_s < min{c_N, c_Q}/4`, `c_Q = γ/100`, `closure:Q-small`, `closure:K-rank-one`).

`HSmall S` is `sup_z ‖Rdef‖ + sup_z (‖Lg‖‖Q∘P‖) / (1 - sup_z ‖Q‖) → 0` over `z ∈ [-1,1]`.

* Remainder: `Rdef = (Lg∘P - Kflat) + (Kflat - Lam.smulRight aMu)`. The first summand is
  `≤ C₁ ν⁻¹^{k₁} e^{-(c_N-1.1a_s)/ν}` (`CurvedFlatComparison`). The second is
  `≤ |C₂| A₀ |ν + ω_can + X + Y|` by `FlatLimit`, where `A_* = e^{-z}/(2‖𝒞(σ₀)‖) ≤ A₀ :=
  e/(2‖𝒞(σ₀)‖)` by `astarExact` (for `ν < 1`, `z ∈ [-1,1]`). Both tend to `0` by `polyExp`.
* Quotient: `‖Q∘P‖ ≤ ‖Q‖‖P‖` (`opNorm_comp_le`), `‖Lg‖ ≤ C ν⁻¹^k` and
  `‖P‖ ≤ C ν⁻¹^k e^{1.1a_s/ν}` (`PLBound`), `‖Q‖ ≤ C_Q ν⁻¹^{k_Q} e^{-(γ/100)/ν}` (`QSmall`).
  The product is `≤ C² C_Q ν⁻¹^{2k+k_Q} e^{-(γ/100-1.1a_s)/ν} → 0`. Since `sup‖Q‖ → 0`,
  `1 - sup‖Q‖ ≥ 1/2` eventually.
* Suprema: `ciSup_le` with the pointwise bounds (uniform in `z`), and the squeeze theorem.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- Absolute-value form of a bound `x ≤ C a b` with `0 ≤ a ≤ A`. -/
theorem hsmall_abs_helper (x C a A b : ℝ) (hx : x ≤ C * a * b) (ha0 : 0 ≤ a) (haA : a ≤ A) :
    x ≤ |C| * A * |b| := by
  have h1 : C * a * b ≤ |C| * A * |b| := by
    calc C * a * b ≤ |C * a * b| := le_abs_self _
      _ = |C| * a * |b| := by rw [abs_mul, abs_mul, abs_of_nonneg ha0]
      _ ≤ |C| * A * |b| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haA (abs_nonneg C)) (abs_nonneg b)
  linarith

/-- The quotient step: `0 ≤ s ≤ d` and `q < 1/2` give `0 ≤ s/(1-q) ≤ 2d`. -/
theorem hsmall_quot (s q d : ℝ) (hs : 0 ≤ s) (hsd : s ≤ d) (hq : q < 1 / 2) :
    0 ≤ s / (1 - q) ∧ s / (1 - q) ≤ 2 * d := by
  have h1q : 0 < 1 - q := by linarith
  have hd : 0 ≤ d := le_trans hs hsd
  refine ⟨div_nonneg hs h1q.le, ?_⟩
  rw [div_le_iff₀ h1q]
  nlinarith [mul_nonneg hd (by linarith : (0 : ℝ) ≤ 1 / 2 - q)]

theorem hsmallProof : UnforcedLeray.Short.PartIIIb.T_hsmall := by
  unfold T_hsmall
  intro S lam κ ell J σ₀ a_s cN hlam ha hC hν0 hν hbud hQS hPL hCF hFL
  unfold HSmall
  unfold CurvedFlatComparison at hCF
  unfold FlatLimit at hFL
  unfold PLBound at hPL
  unfold QSmall at hQS
  obtain ⟨hcN, C1, k1, N1, hN1⟩ := hCF
  obtain ⟨ωcan, C2, k2, γ', b, N2, hω, hγ'0, -, -, hN2⟩ := hFL
  obtain ⟨CL, kL, NL, hPL'⟩ := hPL
  obtain ⟨CQ, kQ, NQ, hQ'⟩ := hQS
  set Cσ : ℂ := mellinC lam ell J (σ₀ : ℂ) with hCσ
  have : Nonempty (Icc (-1 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
  -- budget
  have hm1 := min_le_left cN (lam.re / 100)
  have hm2 := min_le_right cN (lam.re / 100)
  have hc1 : 0 < cN - 1.1 * a_s := by linarith
  have hc2 : 0 < lam.re / 100 - 1.1 * a_s := by linarith
  have hc3 : 0 < 4 * a_s / 5 := by linarith
  have hQc : 0 < lam.re / 100 := div_pos hlam (by norm_num)
  have hCσpos : 0 < ‖Cσ‖ := norm_pos_iff.mpr hC
  have hν1 : ∀ᶠ n in atTop, S.ν n < 1 := hν.eventually_lt_const one_pos
  -- the Astar factor on the window
  have hAst : ∀ n, S.ν n < 1 → ∀ z ∈ Icc (-1 : ℝ) 1,
      0 ≤ Astar lam κ Cσ σ₀ (S.ν n) z ∧ Astar lam κ Cσ σ₀ (S.ν n) z ≤ Real.exp 1 / (2 * ‖Cσ‖) := by
    intro n hlt z hz
    rw [astarExact lam κ Cσ σ₀ (S.ν n) z hC (hν0 n) hlt]
    refine ⟨by positivity, ?_⟩
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact Real.exp_le_exp.mpr (by linarith [hz.1, hz.2])
  -- limits of the sequences
  have hbrT : Tendsto (fun n => S.ν n + ωcan n + (S.ν n)⁻¹ ^ k2 * Real.exp (-γ' / Real.sqrt (S.ν n))
      + (S.ν n)⁻¹ ^ k2 * Real.exp (-(4 * a_s / 5) / S.ν n)) atTop (𝓝 0) := by
    have h2 := (polyExp k2 γ' S.ν hγ'0 hν0 hν).2
    have h3 := (polyExp k2 (4 * a_s / 5) S.ν hc3 hν0 hν).1
    have := ((hν.add hω).add h2).add h3
    simpa only [add_zero] using this
  have habsT : Tendsto (fun n => |S.ν n + ωcan n + (S.ν n)⁻¹ ^ k2 * Real.exp (-γ' / Real.sqrt (S.ν n))
      + (S.ν n)⁻¹ ^ k2 * Real.exp (-(4 * a_s / 5) / S.ν n)|) atTop (𝓝 0) := by
    have := (continuous_abs.tendsto 0).comp hbrT
    rw [abs_zero] at this
    exact this
  have hRBT : Tendsto (fun n => C1 * (S.ν n)⁻¹ ^ k1 * Real.exp (-(cN - 1.1 * a_s) / S.ν n)
      + |C2| * (Real.exp 1 / (2 * ‖Cσ‖)) * |S.ν n + ωcan n + (S.ν n)⁻¹ ^ k2 * Real.exp (-γ' / Real.sqrt (S.ν n))
      + (S.ν n)⁻¹ ^ k2 * Real.exp (-(4 * a_s / 5) / S.ν n)|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => C1 * (S.ν n)⁻¹ ^ k1 * Real.exp (-(cN - 1.1 * a_s) / S.ν n))
        atTop (𝓝 0) := by
      have := ((polyExp k1 (cN - 1.1 * a_s) S.ν hc1 hν0 hν).1).const_mul C1
      rw [mul_zero] at this
      exact Tendsto.congr (fun n => by ring) this
    have h2 := habsT.const_mul (|C2| * (Real.exp 1 / (2 * ‖Cσ‖)))
    rw [mul_zero] at h2
    have := h1.add h2
    rw [add_zero] at this
    exact this
  have hQBT : Tendsto (fun n => CQ * (S.ν n)⁻¹ ^ kQ * Real.exp (-(lam.re / 100) / S.ν n))
      atTop (𝓝 0) := by
    have := ((polyExp kQ (lam.re / 100) S.ν hQc hν0 hν).1).const_mul CQ
    rw [mul_zero] at this
    exact Tendsto.congr (fun n => by ring) this
  have hDBT : Tendsto (fun n => (CL * CL * CQ) * ((S.ν n)⁻¹ ^ (2 * kL + kQ)
      * Real.exp (-(lam.re / 100 - 1.1 * a_s) / S.ν n))) atTop (𝓝 0) := by
    have := ((polyExp (2 * kL + kQ) (lam.re / 100 - 1.1 * a_s) S.ν hc2 hν0 hν).1).const_mul
      (CL * CL * CQ)
    rw [mul_zero] at this
    exact this
  have hQlt : ∀ᶠ n in atTop, CQ * (S.ν n)⁻¹ ^ kQ * Real.exp (-(lam.re / 100) / S.ν n) < 1 / 2 :=
    hQBT.eventually_lt_const (by norm_num)
  -- the Rdef term
  have hRdef : ∀ᶠ n in atTop, (⨆ z : Icc (-1 : ℝ) 1, ‖Rdef (S.ops n z)‖) ≤
      C1 * (S.ν n)⁻¹ ^ k1 * Real.exp (-(cN - 1.1 * a_s) / S.ν n)
      + |C2| * (Real.exp 1 / (2 * ‖Cσ‖)) * |S.ν n + ωcan n + (S.ν n)⁻¹ ^ k2 * Real.exp (-γ' / Real.sqrt (S.ν n))
      + (S.ν n)⁻¹ ^ k2 * Real.exp (-(4 * a_s / 5) / S.ν n)| := by
    filter_upwards [eventually_ge_atTop N1, eventually_ge_atTop N2, hν1] with n hn1 hn2 hlt
    apply ciSup_le
    intro z
    have hz : (z : ℝ) ∈ Icc (-1 : ℝ) 1 := z.2
    have h1 := hN1 n hn1 (z : ℝ) hz
    have hA := hAst n hlt (z : ℝ) hz
    have h2 := hsmall_abs_helper _ _ _ _ _ (hN2 n hn2 (z : ℝ) hz).1 hA.1 hA.2
    have hsplit : Rdef (S.ops n z) = ((S.ops n z).Lg ∘L (S.ops n z).P - (S.ops n z).Kflat) +
        ((S.ops n z).Kflat - (S.ops n z).Lam.smulRight (S.ops n z).aMu) := by
      unfold Rdef
      rw [sub_add_sub_cancel]
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hSRT : Tendsto (fun n => ⨆ z : Icc (-1 : ℝ) 1, ‖Rdef (S.ops n z)‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRBT
      (Eventually.of_forall fun n => Real.iSup_nonneg fun z => norm_nonneg _) hRdef
  -- the quotient term
  have hSLQnn : ∀ n, 0 ≤ (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Lg‖ * ‖(S.ops n z).Q ∘L (S.ops n z).P‖) :=
    fun n => Real.iSup_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hSLQ : ∀ᶠ n in atTop, (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Lg‖ * ‖(S.ops n z).Q ∘L (S.ops n z).P‖)
      ≤ (CL * CL * CQ) * ((S.ν n)⁻¹ ^ (2 * kL + kQ) * Real.exp (-(lam.re / 100 - 1.1 * a_s) / S.ν n)) := by
    filter_upwards [eventually_ge_atTop NL, eventually_ge_atTop NQ] with n hnL hnQ
    apply ciSup_le
    intro z
    have hz : (z : ℝ) ∈ Icc (-1 : ℝ) 1 := z.2
    have hLg := (hPL' n hnL (z : ℝ) hz).2
    have hP := (hPL' n hnL (z : ℝ) hz).1
    have hQ := hQ' n hnQ (z : ℝ) hz
    have hQP : ‖(S.ops n z).Q ∘L (S.ops n z).P‖ ≤ ‖(S.ops n z).Q‖ * ‖(S.ops n z).P‖ :=
      (S.ops n z).Q.opNorm_comp_le (S.ops n z).P
    have hAQ0 : 0 ≤ CQ * (S.ν n)⁻¹ ^ kQ * Real.exp (-(lam.re / 100) / S.ν n) :=
      le_trans (norm_nonneg _) hQ
    have hAL0 : 0 ≤ CL * (S.ν n)⁻¹ ^ kL := le_trans (norm_nonneg _) hLg
    have hprod := mul_le_mul hLg (hQP.trans (mul_le_mul hQ hP (norm_nonneg _) hAQ0))
      (norm_nonneg _) hAL0
    refine hprod.trans (le_of_eq ?_)
    have hexp : Real.exp (-(lam.re / 100) / S.ν n) * Real.exp (1.1 * a_s / S.ν n) =
        Real.exp (-(lam.re / 100 - 1.1 * a_s) / S.ν n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hpow : (S.ν n)⁻¹ ^ (2 * kL + kQ) = (S.ν n)⁻¹ ^ kL * (S.ν n)⁻¹ ^ kQ * (S.ν n)⁻¹ ^ kL := by
      rw [show 2 * kL + kQ = kL + kQ + kL by ring, pow_add, pow_add]
    rw [hpow, ← hexp]
    ring
  have hWev : ∀ᶠ n in atTop,
      0 ≤ (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Lg‖ * ‖(S.ops n z).Q ∘L (S.ops n z).P‖) /
          (1 - ⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Q‖) ∧
      (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Lg‖ * ‖(S.ops n z).Q ∘L (S.ops n z).P‖) /
          (1 - ⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Q‖) ≤
        2 * ((CL * CL * CQ) * ((S.ν n)⁻¹ ^ (2 * kL + kQ) * Real.exp (-(lam.re / 100 - 1.1 * a_s) / S.ν n))) := by
    have hSQ : ∀ᶠ n in atTop, (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Q‖) ≤
        CQ * (S.ν n)⁻¹ ^ kQ * Real.exp (-(lam.re / 100) / S.ν n) := by
      filter_upwards [eventually_ge_atTop NQ] with n hnQ
      apply ciSup_le
      intro z
      exact hQ' n hnQ (z : ℝ) z.2
    filter_upwards [hSLQ, hSQ, hQlt] with n h1 h2 h3
    exact hsmall_quot _ _ _ (hSLQnn n) h1 (lt_of_le_of_lt h2 h3)
  have hWT : Tendsto (fun n => (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Lg‖ * ‖(S.ops n z).Q ∘L (S.ops n z).P‖) /
      (1 - ⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Q‖)) atTop (𝓝 0) := by
    have h2DB : Tendsto (fun n => 2 * ((CL * CL * CQ) * ((S.ν n)⁻¹ ^ (2 * kL + kQ)
        * Real.exp (-(lam.re / 100 - 1.1 * a_s) / S.ν n)))) atTop (𝓝 0) := by
      have := hDBT.const_mul 2
      rw [mul_zero] at this
      exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2DB
      (hWev.mono fun n h => h.1) (hWev.mono fun n h => h.2)
  have := hSRT.add hWT
  rw [add_zero] at this
  exact this

end UnforcedLeray.Short.PartIIIb
