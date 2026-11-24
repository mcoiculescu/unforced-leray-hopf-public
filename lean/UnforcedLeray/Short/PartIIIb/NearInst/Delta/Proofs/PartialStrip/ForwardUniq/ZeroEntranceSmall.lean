import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props

/-!
# `FUZeroEntranceSmall` (item `PartIII-b:C/near/delta/9/1/6`)

The entrance layer is small (source 3541-3543): on `[δ, 2δ] ⊂ (0, δ₀)` one has
`s^{-3/2} ≥ (2δ)^{-3/2}`, so `E(s) ≤ (2δ)^{3/2} s^{-3/2} E(s)` and
`∫_δ^{2δ} E ≤ (2δ)^{3/2} ∫_0^{δ₀} s^{-3/2} E`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem fuZeroEntranceSmall : UnforcedLeray.Short.PartIIIb.NearInst.Delta.FUZeroEntranceSmall := by
  intro δ δ₀ E hδ hδ₀ hE0 hEint hJ
  have hc0 : 0 < (2 * δ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hpt : ∀ s ∈ Icc δ (2 * δ), ENNReal.ofReal (E s) ≤
      ENNReal.ofReal ((2 * δ) ^ (3 / 2 : ℝ)) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hδ hs.1
    have hanti : (2 * δ) ^ (-3 / 2 : ℝ) ≤ s ^ (-3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hs0 hs.2 (by norm_num)
    have hinv : (2 * δ) ^ (-3 / 2 : ℝ) = ((2 * δ) ^ (3 / 2 : ℝ))⁻¹ := by
      rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, Real.rpow_neg (by linarith)]
    rw [hinv] at hanti
    have h1 : 1 ≤ (2 * δ) ^ (3 / 2 : ℝ) * s ^ (-3 / 2 : ℝ) := by
      calc (1 : ℝ) = (2 * δ) ^ (3 / 2 : ℝ) * ((2 * δ) ^ (3 / 2 : ℝ))⁻¹ :=
            (mul_inv_cancel₀ hc0.ne').symm
        _ ≤ (2 * δ) ^ (3 / 2 : ℝ) * s ^ (-3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hanti hc0.le
    rw [← ENNReal.ofReal_mul hc0.le]
    apply ENNReal.ofReal_le_ofReal
    have hE := hE0 s
    calc E s = 1 * E s := (one_mul _).symm
      _ ≤ ((2 * δ) ^ (3 / 2 : ℝ) * s ^ (-3 / 2 : ℝ)) * E s := mul_le_mul_of_nonneg_right h1 hE
      _ = (2 * δ) ^ (3 / 2 : ℝ) * (s ^ (-3 / 2 : ℝ) * E s) := by ring
  have hsub : Icc δ (2 * δ) ⊆ Ioo 0 δ₀ := fun s hs =>
    Set.mem_Ioo.2 ⟨lt_of_lt_of_le hδ hs.1, lt_of_le_of_lt hs.2 hδ₀⟩
  have hlin : ∫⁻ s in Icc δ (2 * δ), ENNReal.ofReal (E s) ≤
      ENNReal.ofReal ((2 * δ) ^ (3 / 2 : ℝ)) *
        ∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s) := by
    calc ∫⁻ s in Icc δ (2 * δ), ENNReal.ofReal (E s)
        ≤ ∫⁻ s in Icc δ (2 * δ),
            ENNReal.ofReal ((2 * δ) ^ (3 / 2 : ℝ)) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s) :=
          setLIntegral_mono' measurableSet_Icc (fun s hs => hpt s hs)
      _ = ENNReal.ofReal ((2 * δ) ^ (3 / 2 : ℝ)) *
            ∫⁻ s in Icc δ (2 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((2 * δ) ^ (3 / 2 : ℝ)) *
            ∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) bot_le

  have hEm : 0 ≤ᵐ[volume.restrict (Icc δ (2 * δ))] E :=
    (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s _ => hE0 s)
  rw [integral_eq_lintegral_of_nonneg_ae hEm hEint.aestronglyMeasurable]
  have hmono := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ.ne) hlin
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0.le] at hmono
  exact hmono

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
