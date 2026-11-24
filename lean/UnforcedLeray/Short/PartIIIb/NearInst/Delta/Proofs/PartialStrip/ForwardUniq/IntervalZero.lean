import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.WeightFamily
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.OneWeight
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.ZeroEntranceSmall

/-!
# `FUIntervalZero` (item `PartIII-b:C/near/delta/9/1/7`)

Source 3541-3545.  Assemble the weight family (`fuWeightFamily`), the one-weight inequality
(`fuOneWeight`) and the entrance smallness (`fuZeroEntranceSmall`): for `2δ ≤ ε < t₁ < t₂ < T`,
`(κ/t₁) ∫_ε^{t₁} E ≤ (K/δ) (2δ)^{3/2} I` with `I` the finite entrance integral, and the right side
is `K 2^{3/2} I δ^{1/2} → 0` as `δ → 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem fuIntervalZero : FUIntervalZero := by
  intro κ T E hκ hT hE hloc hZ hw ε t₁ hε hεt₁ ht₁T
  obtain ⟨δ₀, hδ₀, hfin⟩ := hZ
  have hfam : FUWeightFamily := fuWeightFamily
  obtain ⟨K, hK, hfam⟩ := hfam
  have hpos₁ : 0 < t₁ := lt_trans hε hεt₁
  have hc : 0 < κ / t₁ := div_pos hκ hpos₁
  set t₂ : ℝ := (t₁ + T) / 2 with ht₂def
  have ht₁t₂ : t₁ < t₂ := by rw [ht₂def]; linarith
  have ht₂T : t₂ < T := by rw [ht₂def]; linarith
  -- the pointwise bound along δ ↓ 0
  have hm : (0 : ℝ) < min (ε / 2) (δ₀ / 2) := lt_min (by linarith) (by linarith)
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      κ / t₁ * (∫ s in Icc ε t₁, E s) ≤
        K * 2 ^ (3 / 2 : ℝ) * (∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s)).toReal *
          δ ^ (1 / 2 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT hm] with δ hδ
    obtain ⟨hδpos, hδm⟩ := hδ
    have hδε : 2 * δ ≤ ε := by
      have := lt_min_iff.1 hδm
      linarith [this.1]
    have hδδ₀ : 2 * δ < δ₀ := by
      have := lt_min_iff.1 hδm
      linarith [this.2]
    have h2δt₁ : 2 * δ < t₁ := by linarith
    obtain ⟨w, hwc, hwcs, hwts, hw01, hw1, hwd⟩ := hfam δ t₁ t₂ hδpos h2δt₁ ht₁t₂
    have hts : tsupport w ⊆ Ioo 0 T := fun x hx =>
      ⟨lt_of_lt_of_le hδpos (hwts hx).1, lt_of_le_of_lt (hwts hx).2 ht₂T⟩
    have hwineq := hw w hwc hwcs hts (fun s => (hw01 s).1)
    have hOne := fuOneWeight κ K δ ε t₁ t₂ E w hκ hδpos hδε hεt₁ ht₁t₂ hE hloc hwc hwts hw01 hw1 hwd
      hwineq
    have hSmall := fuZeroEntranceSmall δ δ₀ E hδpos hδδ₀ hE (hloc δ (2 * δ) hδpos (by linarith))
      hfin
    have hKd : 0 ≤ K / δ := div_nonneg hK.le hδpos.le
    have hpow : (2 * δ) ^ (3 / 2 : ℝ) = 2 ^ (3 / 2 : ℝ) * (δ * δ ^ (1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hδpos.le]
      congr 1
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hδpos, Real.rpow_one]
    calc κ / t₁ * (∫ s in Icc ε t₁, E s)
        ≤ K / δ * ∫ s in Icc δ (2 * δ), E s := hOne
      _ ≤ K / δ * ((2 * δ) ^ (3 / 2 : ℝ) *
            (∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s)).toReal) :=
          mul_le_mul_of_nonneg_left hSmall hKd
      _ = K * 2 ^ (3 / 2 : ℝ) *
            (∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s)).toReal *
            δ ^ (1 / 2 : ℝ) := by
          rw [hpow]
          field_simp
  -- the right-hand side tends to zero as δ ↓ 0
  have hlim : Tendsto (fun δ : ℝ => K * 2 ^ (3 / 2 : ℝ) *
      (∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s)).toReal * δ ^ (1 / 2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun δ : ℝ => K * 2 ^ (3 / 2 : ℝ) *
        (∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s)).toReal * δ ^ (1 / 2 : ℝ))
        (𝓝 0) (𝓝 (K * 2 ^ (3 / 2 : ℝ) *
          (∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s)).toReal *
          (0 : ℝ) ^ (1 / 2 : ℝ))) :=
      (continuous_const.mul (Real.continuous_rpow_const (by norm_num))).tendsto 0
    rw [Real.zero_rpow (by norm_num), mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hA : κ / t₁ * (∫ s in Icc ε t₁, E s) ≤ 0 := ge_of_tendsto hlim hev
  have hnn : 0 ≤ ∫ s in Icc ε t₁, E s := setIntegral_nonneg measurableSet_Icc (fun s _ => hE s)
  exact le_antisymm (le_of_mul_le_mul_left (by linarith : κ / t₁ * (∫ s in Icc ε t₁, E s)
    ≤ κ / t₁ * 0) hc) hnn

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
