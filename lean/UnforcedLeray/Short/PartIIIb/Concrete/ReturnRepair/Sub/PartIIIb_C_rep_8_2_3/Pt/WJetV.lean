import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/18`: the weighted velocity jets `WJetV` from `TailW` and `SupV`

Source of record: `the November 2 reference manuscript` 5477-5495 and 460-478.
Tail region `|η| ≥ C_p/ν + 2`: `TailW` (the `v` term). Band region: the weight is `≤ (C_p+3)^4 ν⁻⁴`
and `SupV` bounds the jet uniformly in `η`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- Monotonicity of the power bound in the exponent, `t = ν⁻¹ ≥ 1`. -/
theorem wJetV_mono {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (C : ℝ) {k K : ℕ} (hk : k ≤ K) :
    C * ν⁻¹ ^ k ≤ |C| * ν⁻¹ ^ K := by
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  calc C * ν⁻¹ ^ k ≤ |C| * ν⁻¹ ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (inv_nonneg.2 hν.le) _)
    _ ≤ |C| * ν⁻¹ ^ K := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hk) (abs_nonneg C)

/-- **Weighted velocity jets** (source 5477-5495, 460-478): from the tail bound `TailW` for `|η|` large
and `SupV` for `|η|` bounded. -/
theorem wJetV_of (h1 : TailW) (h2 : SupV) : WJetV := by
  intro ℓ m
  obtain ⟨Cp, C₁, k₁, a₁, hCp, ha₁, H1⟩ := h1 ℓ m
  obtain ⟨C₂, k₂, a₂, ha₂, H2⟩ := h2 ℓ m
  refine ⟨|C₁| + (Cp + 3) ^ 4 * |C₂|, k₁ + k₂ + 8, min (min a₁ a₂) 1,
    lt_min (lt_min ha₁ ha₂) one_pos, ?_⟩
  intro ν hν hνle tr htr s hs hsS z
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hνa1 : ν ≤ a₁ := hνle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνa2 : ν ≤ a₂ := hνle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have ht0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hK : 0 ≤ ν⁻¹ ^ (k₁ + k₂ + 8) := pow_nonneg ht0 _
  have hC1 : 0 ≤ |C₁| := abs_nonneg C₁
  have hC2 : 0 ≤ (Cp + 3) ^ 4 * |C₂| := mul_nonneg (by positivity) (abs_nonneg C₂)
  have e : (|C₁| + (Cp + 3) ^ 4 * |C₂|) * ν⁻¹ ^ (k₁ + k₂ + 8) =
      |C₁| * ν⁻¹ ^ (k₁ + k₂ + 8) + (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 8) := by ring
  rw [e]
  by_cases hcase : Cp / ν + 2 ≤ |z.2|
  · have h := H1 ν hν hνa1 tr htr s hs hsS z hcase
    have hw : 0 ≤ (1 + |z.2|) ^ 4 := by positivity
    have hp0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ m tr.p s z)
    have hψ0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ m tr.ψ s z)
    have hv0 := norm_nonneg (UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z)
    have hsub : (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ ≤
        (1 + |z.2|) ^ 4 * (‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ +
          ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.p s z‖ +
          ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.ψ s z‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hw
    have hm := wJetV_mono hν hν1 C₁ (show k₁ ≤ k₁ + k₂ + 8 by omega)
    have hC1K : 0 ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 8) := mul_nonneg hC1 hK
    have hX : 0 ≤ (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 8) := mul_nonneg hC2 hK
    linarith
  · rw [not_le] at hcase
    have hbound : 1 + |z.2| ≤ (Cp + 3) * ν⁻¹ := by
      have hd : Cp / ν = Cp * ν⁻¹ := div_eq_mul_inv Cp ν
      rw [hd] at hcase
      nlinarith
    have hw4 : (1 + |z.2|) ^ 4 ≤ (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := by
      calc (1 + |z.2|) ^ 4 ≤ ((Cp + 3) * ν⁻¹) ^ 4 :=
            pow_le_pow_left₀ (by positivity) hbound 4
        _ = (Cp + 3) ^ 4 * ν⁻¹ ^ 4 := by ring
    have hv2 := H2 ν hν hνa2 tr htr s hs hsS z
    have hvm := wJetV_mono hν hν1 C₂ (show k₂ ≤ k₂ + 4 by omega)
    have hA : (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ ≤
        (Cp + 3) ^ 4 * ν⁻¹ ^ 4 * (|C₂| * ν⁻¹ ^ (k₂ + 4)) :=
      mul_le_mul hw4 (le_trans hv2 hvm) (norm_nonneg _)
        (mul_nonneg (by positivity) (pow_nonneg ht0 _))
    have e2 : (Cp + 3) ^ 4 * ν⁻¹ ^ 4 * (|C₂| * ν⁻¹ ^ (k₂ + 4)) =
        (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (4 + k₂ + 4) := by ring
    have hmono : (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (4 + k₂ + 4) ≤
        (Cp + 3) ^ 4 * |C₂| * ν⁻¹ ^ (k₁ + k₂ + 8) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) hC2
    have hC1K : 0 ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂ + 8) := mul_nonneg hC1 hK
    linarith [hA, e2, hmono, hC1K]

end UnforcedLeray.Short.PartIIIb.Concrete
