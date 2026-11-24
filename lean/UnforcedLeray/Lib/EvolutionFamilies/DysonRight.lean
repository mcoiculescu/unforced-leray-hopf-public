import UnforcedLeray.Lib.EvolutionFamilies.Fubini

/-!
# The right Duhamel identity of the Dyson evolution (INF08 T8.2 `dyson_right`)

`U(t,s)x = F(t,s)x + ∫_s^t U(t,r) A(r) F(r,s) x dr` for `U = dyson F A`
(`paper/main.tex`, lines 1597, 1617; blueprint B0104, B0244, B0313). Proof: the right side
`R(τ)` is continuous in `τ` and, by Fubini on the triangle (`integral_triangle_swap`) and the
left identity at `(r, τ)`, solves the left Duhamel equation; uniqueness
(`eq_zero_of_volterra`) gives `R(τ) = U(τ,s)x`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {a b : ℝ}
  (F : EvolutionFamily X a b) (A : BoundedPert X a b)

/-- **Right Duhamel identity** (INF08 T8.2 `dyson_right`; `paper/main.tex`, lines 1597, 1617):
`U(t,s)x = F(t,s)x + ∫_s^t U(t,r) A(r) F(r,s) x dr` for `U = dyson F A`. -/
theorem dyson_right {s t : ℝ} (h : a ≤ s ∧ s ≤ t ∧ t ≤ b) (x : X) :
    (dyson F A).U t s x = F.U t s x + ∫ r in s..t, (dyson F A).U t r (A.A r (F.U r s x)) := by
  obtain ⟨hs, hst, ht⟩ := h
  set U := dyson F A with hU
  set R : ℝ → X := fun τ => F.U τ s x + ∫ r in s..τ, U.U τ r (A.A r (F.U r s x)) with hR
  have hIc : ContinuousOn (fun τ => ∫ r in s..τ, U.U τ r (A.A r (F.U r s x))) (Icc s b) := by
    have h := U.continuousOn_integral_step A (y := fun p : ℝ × ℝ => F.U p.2 p.1 x) (F.U_cont x)
    exact h.comp (continuous_const.prodMk continuous_id).continuousOn
      fun τ hτ => ⟨hs, hτ.1, hτ.2⟩
  have hRc : ContinuousOn R (Icc s b) := (F.continuousOn_fst hs x).add hIc
  have hReq : ∀ τ ∈ Icc s b, R τ = F.U τ s x + ∫ q in s..τ, F.U τ q (A.A q (R q)) := by
    intro τ hτ
    have hsτ := hτ.1
    have hτb := hτ.2
    have hFc : ContinuousOn (fun q => F.U q s x) (Icc s τ) :=
      (F.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl hτb)
    have hi1 : IntervalIntegrable (fun q => F.U τ q (A.A q (F.U q s x))) volume s τ :=
      F.intervalIntegrable_integrand A hs hsτ hτb hFc
    have hi2 : IntervalIntegrable
        (fun q => F.U τ q (A.A q (∫ r in s..q, U.U q r (A.A r (F.U r s x))))) volume s τ :=
      F.intervalIntegrable_integrand A hs hsτ hτb (hIc.mono (Icc_subset_Icc le_rfl hτb))
    have hi3 : IntervalIntegrable (fun r => U.U τ r (A.A r (F.U r s x))) volume s τ :=
      U.intervalIntegrable_integrand A hs hsτ hτb hFc
    have h1 : ∫ q in s..τ, F.U τ q (A.A q (R q)) =
        (∫ q in s..τ, F.U τ q (A.A q (F.U q s x))) +
          ∫ q in s..τ, F.U τ q (A.A q (∫ r in s..q, U.U q r (A.A r (F.U r s x)))) := by
      rw [← intervalIntegral.integral_add hi1 hi2]
      refine intervalIntegral.integral_congr fun q _ => ?_
      simp only [hR, map_add]
    have h2 : ∫ q in s..τ, F.U τ q (A.A q (∫ r in s..q, U.U q r (A.A r (F.U r s x)))) =
        ∫ q in s..τ, ∫ r in s..q, F.U τ q (A.A q (U.U q r (A.A r (F.U r s x)))) := by
      refine intervalIntegral.integral_congr fun q hq => ?_
      rw [uIcc_of_le hsτ] at hq
      exact (((F.U τ q).comp (A.A q)).intervalIntegral_comp_comm
        (U.intervalIntegrable_integrand A hs hq.1 (hq.2.trans hτb)
          ((F.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl (hq.2.trans hτb))))).symm
    have h3 := integral_triangle_swap hsτ
      (G := fun q r => F.U τ q (A.A q (U.U q r (A.A r (F.U r s x)))))
      (K := F.M * A.C * (U.M * (A.C * (F.M * ‖x‖))))
      (F.aestronglyMeasurable_iterated U A A hs hτb (W := fun r => F.U r s x)
        (((F.continuousOn_fst hs x).mono
          (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτb))).aestronglyMeasurable
          measurableSet_Ioc))
      (fun q r hr hrq hq => (F.norm_iterated_le U A A hs hτb hr.le hrq.le hq _).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (F.norm_apply_le hs hr.le (hrq.le.trans (hq.trans hτb)) x) A.C_nonneg) U.M_nonneg)
          (mul_nonneg F.M_nonneg A.C_nonneg)))
    have h4 : ∫ r in s..τ, ∫ q in r..τ, F.U τ q (A.A q (U.U q r (A.A r (F.U r s x)))) =
        ∫ r in s..τ, (U.U τ r (A.A r (F.U r s x)) - F.U τ r (A.A r (F.U r s x))) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hsτ] at hr
      rw [hU, dyson_left F A ⟨hs.trans hr.1, hr.2, hτb⟩ (A.A r (F.U r s x))]
      abel
    rw [h1, h2, h3, h4, intervalIntegral.integral_sub hi3 hi1]
    simp only [hR]
    abel
  have hw := F.eq_zero_of_volterra A hs (w := fun τ => R τ - U.U τ s x)
    (hRc.sub (U.continuousOn_fst hs x)) (fun τ hτ => ?_) t ⟨hst, ht⟩
  · exact (sub_eq_zero.mp hw).symm
  · rw [hReq τ hτ, hU, dyson_left F A ⟨hs, hτ.1, hτ.2⟩ x, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub
        (F.intervalIntegrable_integrand A hs hτ.1 hτ.2 (hRc.mono (Icc_subset_Icc le_rfl hτ.2)))
        (F.intervalIntegrable_integrand A hs hτ.1 hτ.2
          (((dyson F A).continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl hτ.2)))]
    refine intervalIntegral.integral_congr fun q _ => ?_
    simp only [map_sub]

end UnforcedLeray.Evolution
