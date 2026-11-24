import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11_4_3.SmallTime

/-!


Source: `the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
On the window `r ∈ [τ - 2|h|/ν, τ]` the ages are `≤ (2+ν)|h|`, so by the small-time estimate
`|H_u F - H_v F| ≤ 2 M B √((2+ν)|h|)`; the window has length `≤ 2|h|/ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE

theorem convTD_Tail_Window : UnforcedLeray.Short.IIb.CylPDE.ConvTD_Tail_Window := by
  intro ν s T hν hsT B F hF hb τ hτ x
  obtain ⟨M, hM0, hM⟩ := heatSG_small_time_sqrt
  have hB : 0 ≤ B := by
    have h0 := (hb s ⟨le_rfl, hsT⟩).1 0
    simp only [Prod.snd_zero, Real.cosh_zero, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  refine ⟨4 * M * B * Real.sqrt (2 + ν) / ν, 1, one_pos, ?_⟩
  intro η hη t ht htne _
  have hh : 0 < |t - τ| := abs_pos.2 (sub_ne_zero.2 htne)
  set h := |t - τ| with hhdef
  have h2ν : 0 ≤ 2 * h / ν := by positivity
  set b := max (max s (τ - η)) (τ - 2 * h / ν) with hbdef
  have hbτ : b ≤ τ := max_le (max_le hτ.1 (by linarith)) (by linarith)
  have hτb : τ - 2 * h / ν ≤ b := le_max_right _ _
  have hsb : s ≤ b := (le_max_left s (τ - η)).trans (le_max_left _ _)
  have hsq : ∀ u : ℝ, max u 0 ≤ (2 + ν) * h → Real.sqrt (max u 0) ≤ Real.sqrt (2 + ν) * Real.sqrt h := by
    intro u hu
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hu
  have hpt : ∀ r ∈ Set.uIoc b τ,
      ‖heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x‖
        ≤ 2 * M * B * Real.sqrt (2 + ν) * Real.sqrt h := by
    intro r hr
    rw [Set.uIoc_of_le hbτ] at hr
    obtain ⟨hr1, hr2⟩ := hr
    have hrF : r ∈ Icc s T := ⟨hsb.trans hr1.le, hr2.trans hτ.2⟩
    have hFr := hF.c1 r hrF
    obtain ⟨hw, hw1⟩ := hb r hrF
    have hlt : ν * (τ - r) < 2 * h := by
      have : τ - r < 2 * h / ν := by linarith
      calc ν * (τ - r) < ν * (2 * h / ν) := mul_lt_mul_of_pos_left this hν
        _ = 2 * h := by field_simp
    have hv : max (ν * (τ - r)) 0 ≤ (2 + ν) * h := by
      refine max_le ?_ (by positivity)
      nlinarith
    have hu : max (ν * (t - r)) 0 ≤ (2 + ν) * h := by
      refine max_le ?_ (by positivity)
      have : t - τ ≤ h := le_abs_self _
      nlinarith
    have e1 := hM B (F r) hFr hw hw1 (ν * (t - r)) x
    have e2 := hM B (F r) hFr hw hw1 (ν * (τ - r)) x
    have s1 := hsq _ hu
    have s2 := hsq _ hv
    rw [Real.norm_eq_abs]
    calc |heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x|
        = |(heatSG (ν * (t - r)) (F r) x - F r x) - (heatSG (ν * (τ - r)) (F r) x - F r x)| := by
          congr 1; ring
      _ ≤ |heatSG (ν * (t - r)) (F r) x - F r x| + |heatSG (ν * (τ - r)) (F r) x - F r x| :=
          abs_sub _ _
      _ ≤ M * B * (Real.sqrt (2 + ν) * Real.sqrt h) + M * B * (Real.sqrt (2 + ν) * Real.sqrt h) :=
          add_le_add (e1.trans (mul_le_mul_of_nonneg_left s1 (by positivity)))
            (e2.trans (mul_le_mul_of_nonneg_left s2 (by positivity)))
      _ = _ := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_mul, abs_inv]
  rw [Real.norm_eq_abs] at hint
  have hlen : |τ - b| ≤ 2 * h / ν := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hK : 0 ≤ 2 * M * B * Real.sqrt (2 + ν) * Real.sqrt h := by positivity
  have h3 : |∫ r in b..τ, (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)|
      ≤ 2 * M * B * Real.sqrt (2 + ν) * Real.sqrt h * (2 * h / ν) :=
    hint.trans (mul_le_mul_of_nonneg_left hlen hK)
  calc h⁻¹ * |∫ r in b..τ, (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)|
      ≤ h⁻¹ * (2 * M * B * Real.sqrt (2 + ν) * Real.sqrt h * (2 * h / ν)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 4 * M * B * Real.sqrt (2 + ν) / ν * Real.sqrt h := by
        field_simp
        ring

end UnforcedLeray.Short.IIb.CylPDE
