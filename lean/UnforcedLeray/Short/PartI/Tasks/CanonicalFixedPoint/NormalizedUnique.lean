import UnforcedLeray.Short.PartI.Sub.PartI_C06

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

theorem canonicalNormalizedUnique : CanonicalNormalizedUnique := by
  intro l b C g S hg hS y φ A r hl hKb hfi hgi hA hCM
  obtain ⟨K, hK⟩ := hKb
  -- the r-component: r θ = r_A θ for every θ ≥ b
  have hr_eq_part : ∀ θ, b ≤ θ → r θ = canonicalRA S y A θ := by
    intro θ hθ
    have hdec : ∀ s₀, θ ≤ s₀ →
        ‖S θ s₀ (r s₀)‖ ≤ |C| * K * Real.exp (-(g * (s₀ - θ))) := by
      intro s₀ hs₀
      have hb₀ : b ≤ s₀ := hθ.trans hs₀
      have h1 := hS.decay θ s₀ (r s₀) hθ hs₀ (hl s₀ hb₀)
      calc ‖S θ s₀ (r s₀)‖ ≤ C * Real.exp (-(g * (s₀ - θ))) * ‖r s₀‖ := h1
        _ ≤ |C| * Real.exp (-(g * (s₀ - θ))) * ‖r s₀‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_nonneg _)) (norm_nonneg _)
        _ ≤ |C| * Real.exp (-(g * (s₀ - θ))) * K :=
            mul_le_mul_of_nonneg_left (hK s₀ hb₀) (mul_nonneg (abs_nonneg C) (Real.exp_nonneg _))
        _ = |C| * K * Real.exp (-(g * (s₀ - θ))) := by ring
    have hexp : Tendsto (fun s₀ : ℝ => |C| * K * Real.exp (-(g * (s₀ - θ)))) atTop (𝓝 0) := by
      have hx : Tendsto (fun s : ℝ => g * (s - θ)) atTop atTop :=
        (Tendsto.const_mul_atTop hg
          (Filter.tendsto_atTop_add_const_right atTop (-θ) tendsto_id)).congr
          (fun s => by simp only [id_eq, sub_eq_add_neg])
      have h2 : Tendsto (fun s : ℝ => Real.exp (-(g * (s - θ)))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hx
      have h3 := h2.const_mul (|C| * K)
      rw [mul_zero] at h3
      exact h3
    have hz : Tendsto (fun s₀ => S θ s₀ (r s₀)) atTop (𝓝 0) :=
      squeeze_zero_norm' (eventually_atTop.2 ⟨θ, fun s₀ hs₀ => hdec s₀ hs₀⟩) hexp
    have hint : Tendsto (fun s₀ => ∫ s in θ..s₀, (A s / s) • S θ s y) atTop
        (𝓝 (canonicalRA S y A θ)) :=
      intervalIntegral_tendsto_integral_Ioi θ (hfi θ hθ) tendsto_id
    have hsum : Tendsto (fun s₀ => S θ s₀ (r s₀) + ∫ s in θ..s₀, (A s / s) • S θ s y) atTop
        (𝓝 (0 + canonicalRA S y A θ)) :=
      hz.add hint
    have hconst : Tendsto (fun s₀ => S θ s₀ (r s₀) + ∫ s in θ..s₀, (A s / s) • S θ s y) atTop
        (𝓝 (r θ)) :=
      tendsto_const_nhds.congr' (eventually_atTop.2 ⟨θ, fun s₀ hs₀ => (hCM θ s₀ hθ hs₀).1⟩)
    have h := tendsto_nhds_unique hconst hsum
    rw [zero_add] at h
    exact h
  -- the amplitude: A θ = 1 + ∫_θ^∞ φ(r s)/s ds
  have hA_eq : ∀ θ, b ≤ θ → A θ = 1 + ∫ s in Ioi θ, φ (r s) / s := by
    intro θ hθ
    have hlimA : Tendsto (fun s₀ => A s₀ + ∫ s in θ..s₀, φ (r s) / s) atTop
        (𝓝 (1 + ∫ s in Ioi θ, φ (r s) / s)) :=
      hA.add (intervalIntegral_tendsto_integral_Ioi θ (hgi θ hθ) tendsto_id)
    have hconstA : Tendsto (fun s₀ => A s₀ + ∫ s in θ..s₀, φ (r s) / s) atTop (𝓝 (A θ)) :=
      tendsto_const_nhds.congr' (eventually_atTop.2 ⟨θ, fun s₀ hs₀ => (hCM θ s₀ hθ hs₀).2⟩)
    exact tendsto_nhds_unique hconstA hlimA
  intro θ hθ
  refine ⟨hr_eq_part θ hθ, ?_⟩
  have hcongr : ∫ s in Ioi θ, φ (r s) / s = ∫ s in Ioi θ, φ (canonicalRA S y A s) / s := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    show φ (r s) / s = φ (canonicalRA S y A s) / s
    rw [hr_eq_part s (hθ.trans (le_of_lt (Set.mem_Ioi.mp hs)))]
  show A θ = 1 + ∫ s in Ioi θ, φ (canonicalRA S y A s) / s
  rw [← hcongr]
  exact hA_eq θ hθ

end UnforcedLeray.Short.PartI
