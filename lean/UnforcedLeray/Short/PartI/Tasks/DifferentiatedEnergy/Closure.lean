import UnforcedLeray.Short.PartI.Sub.T08Statement

/-!
# Part I, task `PartI:T08`: the real-analysis closure `EnergyClosure` (leaf 11)

Proof of `EnergyClosure` from `Sub/T08Statement.lean`: product rule for the weights,
the dissipation shift `Nδ ≤ 1/4`, the transport bound and the forcing by AM-GM.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace UnforcedLeray.Short.PartI

theorem energyClosure_proof : UnforcedLeray.Short.PartI.EnergyClosure := by
  intro N ν δ s K B X J T F hν hs hδ hNδ hδ1 hK hB hX hJ0 hJd hT hF
  have hw : ∀ r : ℝ, UnforcedLeray.Train.width ν r = 1 + ν * r := fun r => rfl
  have hν0 : ν ≠ 0 := hν.ne'
  have hinv : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν0
  have ha : 0 < UnforcedLeray.Train.width ν s := by
    rw [hw]; have := mul_pos hν hs; linarith
  set a := UnforcedLeray.Train.width ν s with ha_def
  have ha0 : a ≠ 0 := ha.ne'
  -- derivative of each weighted jet energy
  have hd : ∀ j ∈ range (N + 1), HasDerivAt (fun r => (δ * UnforcedLeray.Train.width ν r) ^ j * J j r)
      ((j : ℝ) * (δ * a) ^ (j - 1) * (δ * ν) * J j s
        + (δ * a) ^ j * (2 * (ν * -J (j + 1) s - T j - F j))) s := by
    intro j hj
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    have h1 : HasDerivAt (fun r => δ * UnforcedLeray.Train.width ν r) (δ * ν) s := by
      simp only [hw]
      have h := (((hasDerivAt_id s).const_mul ν).const_add 1).const_mul δ
      simpa using h
    have h2 := h1.pow j
    have h3 := h2.mul (hJd j hjN)
    exact h3
  have hDs := HasDerivAt.fun_sum hd
  refine ⟨∑ j ∈ range (N + 1), ((j : ℝ) * (δ * a) ^ (j - 1) * (δ * ν) * J j s
        + (δ * a) ^ j * (2 * (ν * -J (j + 1) s - T j - F j))), hDs, ?_⟩
  -- nonnegativity facts
  have hδa : 0 ≤ δ * a := mul_nonneg hδ.le ha.le
  have hEnn : 0 ≤ ∑ j ∈ range (N + 1), (δ * a) ^ j * J j s :=
    Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hδa _) (hJ0 j)
  have hwJnn : 0 ≤ ∑ j ∈ range (N + 1), (δ * a) ^ j * J (j + 1) s :=
    Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hδa _) (hJ0 (j + 1))
  -- dissipation shift: the weight derivative is absorbed by the dissipation
  have hshift : ∑ j ∈ range (N + 1), (j : ℝ) * (δ * a) ^ (j - 1) * δ * J j s
      ≤ 1 / 4 * ∑ j ∈ range (N + 1), (δ * a) ^ j * J (j + 1) s := by
    have hL : ∑ j ∈ range (N + 1), (j : ℝ) * (δ * a) ^ (j - 1) * δ * J j s
        = ∑ i ∈ range N, ((i : ℝ) + 1) * (δ * a) ^ i * δ * J (i + 1) s := by
      rw [Finset.sum_range_succ']
      simp
    have hR : ∑ j ∈ range (N + 1), (δ * a) ^ j * J (j + 1) s
        = ∑ i ∈ range N, (δ * a) ^ i * J (i + 1) s + (δ * a) ^ N * J (N + 1) s :=
      Finset.sum_range_succ _ _
    have hlast : 0 ≤ (δ * a) ^ N * J (N + 1) s := mul_nonneg (pow_nonneg hδa _) (hJ0 (N + 1))
    have h1 : ∑ i ∈ range N, ((i : ℝ) + 1) * (δ * a) ^ i * δ * J (i + 1) s
        ≤ ∑ i ∈ range N, 1 / 4 * ((δ * a) ^ i * J (i + 1) s) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < N := Finset.mem_range.mp hi
      have hiN : ((i : ℝ) + 1) ≤ N := by exact_mod_cast hi'
      have hk : ((i : ℝ) + 1) * δ ≤ 1 / 4 := by
        have := mul_le_mul_of_nonneg_right hiN hδ.le
        linarith
      have hp : 0 ≤ (δ * a) ^ i * J (i + 1) s := mul_nonneg (pow_nonneg hδa _) (hJ0 (i + 1))
      have key := mul_le_mul_of_nonneg_right hk hp
      nlinarith [key]
    have h2 : ∑ i ∈ range N, 1 / 4 * ((δ * a) ^ i * J (i + 1) s)
        = 1 / 4 * ∑ i ∈ range N, (δ * a) ^ i * J (i + 1) s := by
      rw [Finset.mul_sum]
    rw [hL, hR]
    linarith
  -- per-term identity and bound
  have hper : ∀ j ∈ range (N + 1),
      ν⁻¹ * ((j : ℝ) * (δ * a) ^ (j - 1) * (δ * ν) * J j s
          + (δ * a) ^ j * (2 * (ν * -J (j + 1) s - T j - F j)))
        + (δ * a) ^ j * J (j + 1) s
      ≤ (j : ℝ) * (δ * a) ^ (j - 1) * δ * J j s - 1 / 2 * ((δ * a) ^ j * J (j + 1) s)
        + 2 * ν⁻¹ * ((δ * a) ^ j * |T j|) + 2 * (ν⁻¹) ^ 2 * (B * X / a ^ 5) := by
    intro j hj
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    have hJ1 : 0 ≤ J (j + 1) s := hJ0 (j + 1)
    have hwj : 0 ≤ (δ * a) ^ j := pow_nonneg hδa _
    have hid : ν⁻¹ * ((j : ℝ) * (δ * a) ^ (j - 1) * (δ * ν) * J j s
          + (δ * a) ^ j * (2 * (ν * -J (j + 1) s - T j - F j)))
        + (δ * a) ^ j * J (j + 1) s
        = (j : ℝ) * (δ * a) ^ (j - 1) * δ * J j s - (δ * a) ^ j * J (j + 1) s
          - 2 * ν⁻¹ * ((δ * a) ^ j * T j) - 2 * ν⁻¹ * ((δ * a) ^ j * F j) := by
      linear_combination ((j : ℝ) * (δ * a) ^ (j - 1) * δ * J j s
        - 2 * (δ * a) ^ j * J (j + 1) s) * hinv
    -- transport
    have hTb : -(T j) ≤ |T j| := neg_le_abs _
    have hc2 : 0 ≤ 2 * ν⁻¹ * (δ * a) ^ j :=
      mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hν.le)) (pow_nonneg hδa _)
    have hTt : 2 * ν⁻¹ * (δ * a) ^ j * (-(T j)) ≤ 2 * ν⁻¹ * (δ * a) ^ j * |T j| :=
      mul_le_mul_of_nonneg_left hTb hc2
    -- forcing: AM-GM with u = √J, v = √Y
    have hY : 0 ≤ B / a ^ (5 + j) * X := by
      have : 0 ≤ B / a ^ (5 + j) := div_nonneg hB (pow_nonneg ha.le _)
      exact mul_nonneg this hX
    have hu2 : Real.sqrt (J (j + 1) s) ^ 2 = J (j + 1) s := Real.sq_sqrt hJ1
    have hv2 : Real.sqrt (B / a ^ (5 + j) * X) ^ 2 = B / a ^ (5 + j) * X := Real.sq_sqrt hY
    have hFu : -F j ≤ Real.sqrt (J (j + 1) s) * Real.sqrt (B / a ^ (5 + j) * X) :=
      le_trans (neg_le_abs _) (hF j hjN)
    have hc3 : 0 ≤ 2 * ν⁻¹ * (δ * a) ^ j := hc2
    have hFt : 2 * ν⁻¹ * (δ * a) ^ j * (-F j)
        ≤ 2 * ν⁻¹ * (δ * a) ^ j * (Real.sqrt (J (j + 1) s) * Real.sqrt (B / a ^ (5 + j) * X)) :=
      mul_le_mul_of_nonneg_left hFu hc3
    have hAM : 2 * ν⁻¹ * (δ * a) ^ j * (Real.sqrt (J (j + 1) s) * Real.sqrt (B / a ^ (5 + j) * X))
        ≤ (δ * a) ^ j * (Real.sqrt (J (j + 1) s)) ^ 2 / 2
          + 2 * (ν⁻¹) ^ 2 * ((δ * a) ^ j * (Real.sqrt (B / a ^ (5 + j) * X)) ^ 2) := by
      nlinarith [mul_nonneg hwj (sq_nonneg (Real.sqrt (J (j + 1) s) - 2 * ν⁻¹ * Real.sqrt (B / a ^ (5 + j) * X)))]
    rw [hu2, hv2] at hAM
    -- the weighted data term
    have hvw : (δ * a) ^ j * (B / a ^ (5 + j) * X) ≤ B * X / a ^ 5 := by
      have heq : (δ * a) ^ j * (B / a ^ (5 + j) * X) = δ ^ j * (B * X / a ^ 5) := by
        rw [mul_pow, pow_add]
        field_simp
      rw [heq]
      have hδj : δ ^ j ≤ 1 := pow_le_one₀ hδ.le hδ1
      have hc : 0 ≤ B * X / a ^ 5 := div_nonneg (mul_nonneg hB hX) (pow_nonneg ha.le _)
      exact mul_le_of_le_one_left hc hδj
    have hcst : 2 * (ν⁻¹) ^ 2 * ((δ * a) ^ j * (B / a ^ (5 + j) * X))
        ≤ 2 * (ν⁻¹) ^ 2 * (B * X / a ^ 5) :=
      mul_le_mul_of_nonneg_left hvw (by positivity)
    rw [hid]
    linarith [hTt, hFt, hAM, hcst]
  -- sum the per-term bounds
  have hsumD : ν⁻¹ * (∑ j ∈ range (N + 1), ((j : ℝ) * (δ * a) ^ (j - 1) * (δ * ν) * J j s
        + (δ * a) ^ j * (2 * (ν * -J (j + 1) s - T j - F j))))
      + ∑ j ∈ range (N + 1), (δ * a) ^ j * J (j + 1) s
      = ∑ j ∈ range (N + 1), (ν⁻¹ * ((j : ℝ) * (δ * a) ^ (j - 1) * (δ * ν) * J j s
          + (δ * a) ^ j * (2 * (ν * -J (j + 1) s - T j - F j)))
          + (δ * a) ^ j * J (j + 1) s) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsumD]
  refine le_trans (Finset.sum_le_sum hper) ?_
  have hνinv : 0 ≤ 2 * ν⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.mpr hν.le)
  have hT' : 2 * ν⁻¹ * ∑ j ∈ range (N + 1), (δ * a) ^ j * |T j|
      ≤ 2 * ν⁻¹ * (K / a ^ 2 * ∑ j ∈ range (N + 1), (δ * a) ^ j * J j s) :=
    mul_le_mul_of_nonneg_left hT hνinv
  have e1 : 2 * ν⁻¹ * (K / a ^ 2 * ∑ j ∈ range (N + 1), (δ * a) ^ j * J j s)
      = 2 * K / (ν * a ^ 2) * ∑ j ∈ range (N + 1), (δ * a) ^ j * J j s := by
    field_simp
  have e2 : ((N : ℝ) + 1) * (2 * (ν⁻¹) ^ 2 * (B * X / a ^ 5))
      = 2 * ((N : ℝ) + 1) * B / (ν ^ 2 * a ^ 5) * X := by
    field_simp
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  linarith [hshift, hT', e1, e2, hwJnn]
end UnforcedLeray.Short.PartI
