import UnforcedLeray.Short.PartIIIa.Sub.T15
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Short.PartIIIa.T04_GaussInvIntegral
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailIterated

/-!
# Part III-a, task `PartIII-a:T15/5`: decay of the heat tail

Proves `heatTailBound : HeatTailBound` (`Sub/T15.lean`; SP 3604-3606). For each `m : ℕ` there is
`C ≥ 0` with `‖D^m(heatTail t)(x)‖ ≤ C ‖x‖^{-1-m}` for all `t ≥ 0` and `x ≠ 0`.

Proof (SP 3604-3606, "substitution `a = |x|²r`"). Let `r = ‖x‖ > 0` and `s = (3+m)/2 > 1`.

1. (`HeatTailIterated`) `D^m(heatTail t)(x) = ∫_{(t,∞)} D^m G_a(x) da`.
2. (Norm.) `‖D^m G_a(x)‖ ≤ C0 a^{-s} e^{-r²/(8a)}` (`HeatGBound`, T14), so
   `‖∫_{(t,∞)} D^m G_a(x) da‖ ≤ ∫_{(t,∞)} g` with `g a = C0 a^{-s} e^{-r²/(8a)}`
   (`norm_integral_le_of_norm_le`), and `g` is integrable on `(t,∞)`.
3. (Enlarge the domain.) `g ≥ 0` and `(t,∞) ⊆ (0,∞)`, so `∫_{(t,∞)} g ≤ ∫_{(0,∞)} g`.
4. (Scaling, T04.) `∫_{(0,∞)} a^{-s} e^{-r²/(8a)} da = r^{2-2s} J` with
   `J = ∫⁻_{(0,∞)} ρ^{-s} e^{-1/(8ρ)} dρ` finite (`GaussInvIntegral`). Since `2 - 2s = -1 - m`,
   the constant is `C = C0 · J.toReal`, which depends on `m` only.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The scaling identity of `gaussInvIntegral` (T04) as a real integral: for `s > 1`, `r > 0`,
`∫_{(0,∞)} a^{-s} e^{-r²/(8a)} da = r^{2-2s} · J_s`, with `J_s = ∫⁻_{(0,∞)} ρ^{-s}e^{-1/(8ρ)} dρ`. -/
lemma htb_integral_gauss {s r : ℝ} (hs : 1 < s) (hr : 0 < r) :
    ∫ a in Ioi (0 : ℝ), a ^ (-s) * Real.exp (-r ^ 2 / (8 * a)) =
      r ^ (2 - 2 * s) *
        (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (-s) * Real.exp (-1 / (8 * ρ)))).toReal := by
  have H : GaussInvIntegral := gaussInvIntegral
  obtain ⟨h1, _⟩ := H s r hs hr
  have hmeas : Measurable (fun a : ℝ => a ^ (-s) * Real.exp (-r ^ 2 / (8 * a))) := by
    fun_prop
  have hnn : ∀ᵐ a ∂(volume.restrict (Ioi (0 : ℝ))),
      (0 : ℝ) ≤ a ^ (-s) * Real.exp (-r ^ 2 / (8 * a)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ (fun a ha =>
      mul_nonneg (Real.rpow_nonneg (Set.mem_Ioi.1 ha).le _) (Real.exp_pos _).le)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable, h1,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _)]

/-- **Decay of the heat tail** (`PartIII-a:T15/5`; SP 3604-3606). -/
theorem heatTailBound : UnforcedLeray.Short.IIIa.HeatTailBound := by
  unfold HeatTailBound
  intro m
  have HT : HeatTailIterated := heatTailIterated
  obtain ⟨C0, hC0, hC0b⟩ := heatGBound m
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hs : 1 < (3 + (m : ℝ)) / 2 := by linarith
  have e0 : -(3 + (m : ℝ)) / 2 = -((3 + (m : ℝ)) / 2) := neg_div _ _
  refine ⟨C0 * (∫⁻ ρ in Ioi (0 : ℝ),
      ENNReal.ofReal (ρ ^ (-((3 + (m : ℝ)) / 2)) * Real.exp (-1 / (8 * ρ)))).toReal,
    mul_nonneg hC0 ENNReal.toReal_nonneg, ?_⟩
  intro t ht x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hsub : Ioi t ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ht
  rw [(HT t ht x hx).2 m]
  -- the dominating function, integrable on `(0,∞)` and hence on `(t,∞)`
  have hgint0 : IntegrableOn (fun a : ℝ => C0 * (a ^ (-((3 + (m : ℝ)) / 2)) *
      Real.exp (-‖x‖ ^ 2 / (8 * a)))) (Ioi (0 : ℝ)) :=
    Integrable.const_mul (hts_integrable_gauss hs hr) C0
  have hgint : IntegrableOn (fun a : ℝ => C0 * (a ^ (-((3 + (m : ℝ)) / 2)) *
      Real.exp (-‖x‖ ^ 2 / (8 * a)))) (Ioi t) :=
    IntegrableOn.mono_set hgint0 hsub
  -- pointwise domination on `(t,∞)`
  have hpt : ∀ᵐ a ∂(volume.restrict (Ioi t)),
      ‖iteratedFDeriv ℝ m (heatG a) x‖ ≤ C0 * (a ^ (-((3 + (m : ℝ)) / 2)) *
        Real.exp (-‖x‖ ^ 2 / (8 * a))) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => ?_)
    have ha0 : 0 < a := Set.mem_Ioi.1 (hsub ha)
    have hb := hC0b a ha0 x
    rw [e0] at hb
    exact hb.trans_eq (mul_assoc _ _ _)
  -- nonnegativity of the dominating function on `(0,∞)`
  have hgnn : ∀ᵐ a ∂(volume.restrict (Ioi (0 : ℝ))),
      (0 : ℝ) ≤ C0 * (a ^ (-((3 + (m : ℝ)) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a))) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => ?_)
    exact mul_nonneg hC0 (mul_nonneg (Real.rpow_nonneg (Set.mem_Ioi.1 ha).le _)
      (Real.exp_pos _).le)
  have h1 := norm_integral_le_of_norm_le hgint hpt
  have h2 : ∫ a in Ioi t, C0 * (a ^ (-((3 + (m : ℝ)) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a)))
      ≤ ∫ a in Ioi (0 : ℝ), C0 * (a ^ (-((3 + (m : ℝ)) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a))) :=
    setIntegral_mono_set hgint0 hgnn (LE.le.eventuallyLE hsub)
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [integral_const_mul, htb_integral_gauss hs hr,
    show (2 : ℝ) - 2 * ((3 + (m : ℝ)) / 2) = -1 - (m : ℝ) by ring]
  ring

end UnforcedLeray.Short.IIIa
