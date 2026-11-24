import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.AgeJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.PhaseJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.TransJet

/-!
# `ChartJetBound` (organizer task `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1/1/5`)

Source `the November 2 reference manuscript`,
lines 1208-1210: `Axi.chart R τ y = (Axi.age R y, (Axi.phase R τ y, Axi.trans R y))`.

The chart is the sum `L₁ ∘ age + L₂ ∘ phase + L₃ ∘ trans` of three continuous linear maps into
`ℝ × (ℝ × ℝ)`. Each `D^m` is bounded by the Leibniz-free composition bound
(`ContinuousLinearMap.norm_iteratedFDeriv_comp_left`) and the sum rule (`iteratedFDeriv_add_apply`).
The component jets come from `ageJet`, `phaseJet`, `transJet`; on `ϱ ≥ R` the age jet is absorbed
into `ϱ^{-m}` with the constant `(R²)⁻¹`, and `1 ≤ 1 + |y₃|/ϱ`. Finally `K = 1 + C₁ + C₂ + C₃`
(the constants for `m = 1, 2, 3`) satisfies `K ϱ^{-m}(1+t) ≤ (K(1+t)/ϱ)^m`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The first component `a ↦ (a, 0, 0)` of the chart. -/
def chartJetL1 : ℝ →L[ℝ] (ℝ × (ℝ × ℝ)) := ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)

/-- The second component `b ↦ (0, b, 0)` of the chart. -/
def chartJetL2 : ℝ →L[ℝ] (ℝ × (ℝ × ℝ)) :=
  (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)

/-- The third component `c ↦ (0, 0, c)` of the chart. -/
def chartJetL3 : ℝ →L[ℝ] (ℝ × (ℝ × ℝ)) :=
  (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)

theorem chartJet_decomp (R τ : ℝ) :
    Axi.chart R τ = (chartJetL1 ∘ Axi.age R + chartJetL2 ∘ Axi.phase R τ) + chartJetL3 ∘ Axi.trans R := by
  funext z
  simp [Axi.chart, chartJetL1, chartJetL2, chartJetL3]

theorem chartJetBound : ChartJetBound := by
  intro R hR
  -- the constants for each order `m ≥ 1`, valid on `ϱ ≥ R`
  have key : ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : UnforcedLeray.Space), R ≤ Axi.ϱ y →
      ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤
        C * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
    intro m hm
    obtain ⟨Ca, hCa0, hCa⟩ := ageJet R hR m hm
    obtain ⟨Cp, hCp0, hCp⟩ := phaseJet R hR m hm
    obtain ⟨Ct, hCt0, hCt⟩ := transJet R hR m
    have hL1 : 0 ≤ ‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg hCa0 (inv_nonneg.2 (sq_nonneg R)))
    have hL2 : 0 ≤ ‖chartJetL2‖ * Cp := mul_nonneg (norm_nonneg _) hCp0
    have hL3 : 0 ≤ ‖chartJetL3‖ * Ct := mul_nonneg (norm_nonneg _) hCt0
    refine ⟨‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) + ‖chartJetL2‖ * Cp + ‖chartJetL3‖ * Ct,
      add_nonneg (add_nonneg hL1 hL2) hL3, ?_⟩
    intro τ y hy
    have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR hy
    have hyax : y ∉ Axi.axis := by
      intro h
      rw [Axi.mem_axis_iff] at h
      linarith
    have hU : IsOpen (Axi.axisᶜ : Set UnforcedLeray.Space) := Axi.isOpen_compl_axis
    have hmem : (Axi.axisᶜ : Set UnforcedLeray.Space) ∈ nhds y := hU.mem_nhds hyax
    -- smoothness of the three chart components on `axisᶜ`
    have hAgeS : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Space => R ^ 2 / Axi.ϱ z ^ 2) Axi.axisᶜ :=
      contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
        (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
    have hLogS : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Space => Real.log (Axi.age R z)) Axi.axisᶜ :=
      ContDiffOn.log hAgeS (fun z hz => (Axi.age_pos hR.ne' hz).ne')
    have hPhaseS : ContDiffOn ℝ ∞
        (fun z : UnforcedLeray.Space => R * τ / 2 - (R / 2) * Real.log (Axi.age R z)) Axi.axisᶜ :=
      contDiffOn_const.sub (contDiffOn_const.mul hLogS)
    have hTransS : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Space => R * z 2 / Axi.ϱ z) Axi.axisᶜ :=
      ((show ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => R * z 2) by fun_prop).contDiffOn).div
        Axi.contDiffOn_ϱ (fun z hz => Axi.ϱ_ne_zero hz)
    have hAgeA : ContDiffAt ℝ ∞ (Axi.age R) y := hAgeS.contDiffAt hmem
    have hPhaseA : ContDiffAt ℝ ∞ (Axi.phase R τ) y := hPhaseS.contDiffAt hmem
    have hTransA : ContDiffAt ℝ ∞ (Axi.trans R) y := hTransS.contDiffAt hmem
    have hm' : (m : WithTop ℕ∞) ≤ ∞ := hjLe m
    have hA : ContDiffAt ℝ ∞ (chartJetL1 ∘ Axi.age R) y := chartJetL1.contDiff.comp_contDiffAt y hAgeA
    have hB : ContDiffAt ℝ ∞ (chartJetL2 ∘ Axi.phase R τ) y :=
      chartJetL2.contDiff.comp_contDiffAt y hPhaseA
    have hC : ContDiffAt ℝ ∞ (chartJetL3 ∘ Axi.trans R) y :=
      chartJetL3.contDiff.comp_contDiffAt y hTransA
    have hAB : ContDiffAt ℝ ∞ (chartJetL1 ∘ Axi.age R + chartJetL2 ∘ Axi.phase R τ) y := hA.add hB
    -- component bounds
    have hDA : ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ ≤
        ‖chartJetL1‖ * (Ca * Axi.ϱ y ^ (-(2 + (m : ℝ)))) :=
      le_trans (ContinuousLinearMap.norm_iteratedFDeriv_comp_left chartJetL1 hAgeA hm')
        (mul_le_mul_of_nonneg_left (hCa y hyax) (norm_nonneg _))
    have hDB : ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ ≤
        ‖chartJetL2‖ * (Cp * Axi.ϱ y ^ (-(m : ℝ))) :=
      le_trans (ContinuousLinearMap.norm_iteratedFDeriv_comp_left chartJetL2 hPhaseA hm')
        (mul_le_mul_of_nonneg_left (hCp τ y hyax) (norm_nonneg _))
    have hDC : ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ ≤
        ‖chartJetL3‖ * (Ct * Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
      le_trans (ContinuousLinearMap.norm_iteratedFDeriv_comp_left chartJetL3 hTransA hm')
        (mul_le_mul_of_nonneg_left (hCt y hyax) (norm_nonneg _))
    -- the age jet is absorbed into `ϱ^{-m}` on `ϱ ≥ R`
    have hq0 : 0 ≤ Axi.ϱ y ^ (-(m : ℝ)) := Real.rpow_nonneg hp.le _
    have hs0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
    have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
    have hage : Axi.ϱ y ^ (-(2 + (m : ℝ))) ≤ (R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)) := by
      have e : -(2 + (m : ℝ)) = -(m : ℝ) + -2 := by ring
      have h2 : Axi.ϱ y ^ (-2 : ℝ) = (Axi.ϱ y ^ 2)⁻¹ := by
        rw [Real.rpow_neg hp.le, Real.rpow_two]
      have hinv : (Axi.ϱ y ^ 2)⁻¹ ≤ (R ^ 2)⁻¹ :=
        inv_anti₀ (pow_pos hR 2) (by nlinarith [mul_nonneg (sub_nonneg.2 hy) (add_nonneg hR.le hp.le)])
      rw [e, Real.rpow_add hp, h2]
      calc Axi.ϱ y ^ (-(m : ℝ)) * (Axi.ϱ y ^ 2)⁻¹ = (Axi.ϱ y ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)) :=
            mul_comm _ _
        _ ≤ (R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)) := mul_le_mul_of_nonneg_right hinv hq0
    have eA : ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ ≤
        (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
          (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
      refine le_trans hDA ?_
      calc ‖chartJetL1‖ * (Ca * Axi.ϱ y ^ (-(2 + (m : ℝ))))
          ≤ ‖chartJetL1‖ * (Ca * ((R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hage hCa0) (norm_nonneg _)
        _ = (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
        _ ≤ (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
            (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hq0 hs1) hL1
    have eB : ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ ≤
        (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
      refine le_trans hDB ?_
      calc ‖chartJetL2‖ * (Cp * Axi.ϱ y ^ (-(m : ℝ)))
          = (‖chartJetL2‖ * Cp) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
        _ ≤ (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hq0 hs1) hL2
    have eC : ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ ≤
        (‖chartJetL3‖ * Ct) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
      refine le_trans hDC (le_of_eq ?_)
      ring
    -- assemble
    rw [chartJet_decomp R τ, iteratedFDeriv_add_apply (hAB.of_le hm') (hC.of_le hm'),
      iteratedFDeriv_add_apply (hA.of_le hm') (hB.of_le hm')]
    calc ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y +
            iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y +
          iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖
        ≤ ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y +
            iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ +
          ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ := norm_add_le _ _
      _ ≤ (‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ +
            ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖) +
          ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ :=
            add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
            (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) +
          (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y))) +
          (‖chartJetL3‖ * Ct) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
            add_le_add (add_le_add eA eB) eC
      _ = (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) + ‖chartJetL2‖ * Cp + ‖chartJetL3‖ * Ct) *
            (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by ring
  -- the three orders `1, 2, 3`
  obtain ⟨C1, hC10, hC1⟩ := key 1 le_rfl
  obtain ⟨C2, hC20, hC2⟩ := key 2 (by norm_num)
  obtain ⟨C3, hC30, hC3⟩ := key 3 (by norm_num)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + C1 + C2 + C3 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by linarith
  refine ⟨K, by linarith, fun τ y hy m hm1 hm3 => ?_⟩
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR hy
  have hs0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  have hq0 : 0 ≤ Axi.ϱ y ^ (-(m : ℝ)) := Real.rpow_nonneg hp.le _
  have hqs : 0 ≤ Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y) :=
    mul_nonneg hq0 (by linarith)
  have hfin : ∀ C : ℝ, C ≤ K →
      ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤ C * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) →
      ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤
        (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m := by
    intro C hCK hb
    have hq' : Axi.ϱ y ^ (-(m : ℝ)) = (Axi.ϱ y ^ m)⁻¹ := by
      rw [Real.rpow_neg hp.le, Real.rpow_natCast]
    have hKm : K ≤ K ^ m := le_self_pow₀ hK1 (by omega)
    have hsm : 1 + |y 2| / Axi.ϱ y ≤ (1 + |y 2| / Axi.ϱ y) ^ m := le_self_pow₀ hs1 (by omega)
    have hKnn : 0 ≤ K ^ m := pow_nonneg (by linarith) m
    have hinv : 0 ≤ (Axi.ϱ y ^ m)⁻¹ := inv_nonneg.2 (pow_nonneg hp.le m)
    calc ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖
        ≤ C * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := hb
      _ ≤ K * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
          mul_le_mul_of_nonneg_right hCK hqs
      _ = K * ((Axi.ϱ y ^ m)⁻¹ * (1 + |y 2| / Axi.ϱ y)) := by rw [hq']
      _ ≤ K ^ m * ((Axi.ϱ y ^ m)⁻¹ * (1 + |y 2| / Axi.ϱ y) ^ m) :=
          mul_le_mul hKm (mul_le_mul_of_nonneg_left hsm hinv) (mul_nonneg hinv (by linarith)) hKnn
      _ = (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m := by
          rw [div_pow, mul_pow]
          ring
  interval_cases m
  · exact hfin C1 (by linarith) (hC1 τ y hy)
  · exact hfin C2 (by linarith) (hC2 τ y hy)
  · exact hfin C3 (by linarith) (hC3 τ y hy)

end UnforcedLeray.Short.PartIIIb.Concrete
