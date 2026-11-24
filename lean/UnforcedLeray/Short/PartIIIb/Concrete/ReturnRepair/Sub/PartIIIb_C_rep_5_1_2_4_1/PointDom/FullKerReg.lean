import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.KerBounds
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.Weights

/-!
# `pdFullKerReg` (`PartIII-b:C/rep/5/1/2/4/1/2/11`; source 3604-3610, 4178-4186)

Regularity and crude bounds of `fullKer = χ_y xKer + (χ_y'/r)Ψ e_z` for receivers in
`{r₁ < ϱ y, ‖y‖ < Y}` and sources in `ϱ z ≤ ρ₀ < r₁`.  The `χ_y xKer` part is a product of a
cutoff (compact-region bounds) and the translated kernel (`PDKerBounds`); the stream part is the
outward primitive `primInt` of the scalar kernel `(xKer)₂` (`primInt_main`: `C²` with the sharp
bound `(r₁-ρ₀)² + (y₃ - λz₃)²`), composed with the ring map `y ↦ (ϱ y, 0, y₃)`; the `h`-derivative
passes under the integral (`primH_main`), and the limit `h ↓ 0` follows from the factor `1 - λ²`
in `xKer` (`xKer_small`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem pdFullKerReg : PDFullKerReg := by
  intro ν μ R χy hν hR hμ0 hμ1 hχ r₁ ρ₀ Y hρ₀ hρr
  obtain ⟨C, hC0, hC⟩ := pdKerBounds
  have hCPD : PDKB C := hC
  obtain ⟨C0, hC00, hsmall⟩ := xKer_small
  have hr₁ : 0 < r₁ := lt_of_le_of_lt hρ₀ hρr
  obtain ⟨Bch, hBch0, hBch⟩ := region_bound (ch_contDiffOn hχ ν R) hr₁ Y
  obtain ⟨Bcf, hBcf0, hBcf⟩ := region_bound (cf_contDiffOn hχ ν R) hr₁ Y
  obtain ⟨D, hD1, hspec⟩ := primY_spec hr₁ Y
  set δ := r₁ - ρ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hY0 : 0 ≤ Y → True := fun _ => trivial
  set κ := 1 / δ + 1 + Y / δ with hκ
  set c1 := 1 + δ⁻¹ + δ⁻¹ ^ 2 with hc1
  set cH := 2 + ν * δ⁻¹ ^ 2 + Y * δ⁻¹ with hcH
  set c₃ := (1 + 2 * Y ^ 2) / δ ^ 2 + 2 with hc₃
  set C₃ := (ρ₀ / δ + 1) * (3 + ν * (δ ^ 2)⁻¹ + Y / δ) with hC₃
  set Cp := primCp ρ₀ δ with hCp
  have hCp0 : 0 ≤ Cp := primCp_nonneg hρ₀ hδ0
  -- nonnegativity of Y: needed below; if Y ≤ 0 the region is empty
  by_cases hYpos : 0 ≤ Y
  swap
  · refine ⟨0, le_refl _, fun z M hz y hy hyY => ?_⟩
    exfalso; have := norm_nonneg y; linarith
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hcH0 : 0 ≤ cH := by rw [hcH]; positivity
  have hc30 : 0 ≤ c₃ := by rw [hc₃]; positivity
  have hC30 : 0 ≤ C₃ := by rw [hC₃]; positivity
  set pX := 4 * Bch * c1 * κ ^ 4 with hpX
  set pXh := cH * κ ^ 4 with hpXh
  set pS := 4 * Bcf * (2 * Cp * D ^ 2 * (c₃ / 2)) with hpS
  set pSh := Bcf * C₃ * (c₃ / 2) with hpSh
  have hpX0 : 0 ≤ pX := by rw [hpX]; positivity
  have hpXh0 : 0 ≤ pXh := by rw [hpXh]; positivity
  have hpS0 : 0 ≤ pS := by rw [hpS]; positivity
  have hpSh0 : 0 ≤ pSh := by rw [hpSh]; positivity
  set P := pX + pXh + pS + pSh with hP
  have hP0 : 0 ≤ P := by positivity
  refine ⟨C * P, mul_nonneg hC0 hP0, fun z M hz y hy hyY => ?_⟩
  have hcf : |deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y| ≤ Bcf := by
    have := hBcf y hy.le hyY.le 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  obtain ⟨t1, t2⟩ := tendsto_parts hC00 hsmall ν μ R hν hμ0 hμ1 hχ hρ₀ hρr M hz hy hcf
  refine ⟨by have := t1.add t2; rw [add_zero] at this; exact this, fun h hh => ?_⟩
  have hl0 := pdLam_pos h
  have hl1 := (pdLam_lt_one hh).le
  have hK0 : 0 ≤ C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M :=
    mul_nonneg (mul_nonneg hC0 (kb_coef_bounds μ h hμ0 hμ1 hh).1) (kb_tensor_nonneg M)
  set K := C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M with hK
  set A := ((1 + pdLam h * ‖z‖) ^ 4)⁻¹ with hA
  set B' := (1 + (pdLam h * z 2) ^ 2)⁻¹ with hB'
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B' := by rw [hB']; positivity
  have hsw : srcWeight μ h z = pdLam h ^ (2 * μ + 3) * (A + B') := rfl
  -- combinator
  have comb : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p ≤ P → q ≤ P →
      p * K * A + q * K * B' ≤ C * P * srcWeight μ h z * IIIa.tensorNorm M := by
    intro p q hp hq hpP hqP
    have h1 : p * K * A ≤ P * K * A := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpP hK0) hA0
    have h2 : q * K * B' ≤ P * K * B' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqP hK0) hB0
    calc p * K * A + q * K * B' ≤ P * K * A + P * K * B' := add_le_add h1 h2
      _ = _ := by rw [hsw, hK]; ring
  have hpPX : pX ≤ P := by rw [hP]; linarith
  have hpPXh : pXh ≤ P := by rw [hP]; linarith
  have hpPS : pS ≤ P := by rw [hP]; linarith
  have hpPSh : pSh ≤ P := by rw [hP]; linarith
  -- geometric weights
  have hwX := weightX hl0 hl1 hz hρr hy hyY
  have hwS := weightS (l := pdLam h) (z := z) hρr hy hyY
  -- the two parts
  obtain ⟨hX1, hX2⟩ := xPart1 C hC0 hCPD ν μ R hν hμ0 hμ1 hχ hρ₀ hρr hBch0 hBch M hz hh hy hyY
  obtain ⟨hS1, hS2⟩ := sPart1 C hC0 hCPD ν μ R hν hμ0 hμ1 hχ hρ₀ hρr hD1 hspec hBcf0 hBcf M hz hh hy hyY
  -- bounds for the n-th derivatives of each part, in the form p * K * A and q * K * B'
  have bX : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n
      (fun y' => χy (ν * age R y') • xKer ν μ h (y' - pdLam h • z) M) y‖ ≤ pX * K * A := by
    intro n hn
    refine (hX2 n hn).trans ?_
    have hKk : 0 ≤ K := hK0
    have e : (‖y - pdLam h • z‖ ^ 4)⁻¹ * c1 ≤ κ ^ 4 * A * c1 :=
      mul_le_mul_of_nonneg_right hwX (by rw [hc1]; positivity)
    calc 4 * Bch * (K * ((‖y - pdLam h • z‖ ^ 4)⁻¹ * c1)) ≤ 4 * Bch * (K * (κ ^ 4 * A * c1)) := by
          gcongr
      _ = pX * K * A := by rw [hpX]; ring
  have bS : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n
      (fun y' => (deriv χy (ν * age R y') * (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y' *
        sKer ν μ h (ϱ y') (y' 2) z M) • (coordinateVector 2 : Space)) y‖ ≤ pS * K * B' := by
    intro n hn
    refine (hS2 n hn).trans ?_
    have e : 1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - pdLam h * z 2) ^ 2)) ≤ (c₃ / 2) * B' := hwS
    have hKk : 0 ≤ K := hK0
    calc 4 * Bcf * (2 * (Cp * K * (1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - pdLam h * z 2) ^ 2)))) * D ^ 2)
        ≤ 4 * Bcf * (2 * (Cp * K * ((c₃ / 2) * B')) * D ^ 2) := by gcongr
      _ = pS * K * B' := by rw [hpS]; ring
  -- derivatives in h
  obtain ⟨d1, hd1, hd1b⟩ := xHder hC0 hCPD ν μ R hν hμ0 hμ1 hχ hρ₀ hρr M hz hh hy hyY
  obtain ⟨d2, hd2, hd2b⟩ := sHder hC0 hCPD ν μ R hν hμ0 hμ1 hρ₀ hρr M hz hh hy hyY hcf
  have bXh : ‖d1‖ ≤ pXh * K * A := by
    refine hd1b.trans ?_
    have e : (‖y - pdLam h • z‖ ^ 4)⁻¹ * cH ≤ κ ^ 4 * A * cH :=
      mul_le_mul_of_nonneg_right hwX hcH0
    calc K * ((‖y - pdLam h • z‖ ^ 4)⁻¹ * cH) ≤ K * (κ ^ 4 * A * cH) :=
          mul_le_mul_of_nonneg_left e hK0
      _ = pXh * K * A := by rw [hpXh]; ring
  have bSh : ‖d2‖ ≤ pSh * K * B' := by
    refine hd2b.trans ?_
    have e : 1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - pdLam h * z 2) ^ 2)) ≤ (c₃ / 2) * B' := hwS
    calc Bcf * (C₃ * K * (1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - pdLam h * z 2) ^ 2))))
        ≤ Bcf * (C₃ * K * ((c₃ / 2) * B')) := by gcongr
      _ = pSh * K * B' := by rw [hpSh]; ring
  have hfk : (fun y' => fullKer ν μ R χy h y' z M) =
      (fun y' => χy (ν * age R y') • xKer ν μ h (y' - pdLam h • z) M) +
      (fun y' => (deriv χy (ν * age R y') * (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y' *
        sKer ν μ h (ϱ y') (y' 2) z M) • (coordinateVector 2 : Space)) := rfl
  have hfkh : (fun h' => fullKer ν μ R χy h' y z M) =
      (fun h' => χy (ν * age R y) • xKer ν μ h' (y - pdLam h' • z) M) +
      (fun h' => (deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y *
        sKer ν μ h' (ϱ y) (y 2) z M) • (coordinateVector 2 : Space)) := rfl
  have hD12 : HasDerivAt (fun h' => fullKer ν μ R χy h' y z M) (d1 + d2) h := by
    rw [hfkh]; exact hd1.add hd2
  have hiter : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y' => fullKer ν μ R χy h y' z M) y‖ ≤
      C * P * srcWeight μ h z * IIIa.tensorNorm M := by
    intro n hn
    rw [hfk, iteratedFDeriv_add_apply (i := n) (hX1.of_le (by exact_mod_cast hn)) (hS1.of_le (by exact_mod_cast hn))]
    refine (norm_add_le _ _).trans ?_
    exact (add_le_add (bX n hn) (bS n hn)).trans (comb pX pS hpX0 hpS0 hpPX hpPS)
  refine ⟨?_, hD12.differentiableAt, ?_, ?_, ?_, ?_⟩
  · rw [hfk]; exact hX1.add hS1
  · have := hiter 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero] at this
  · rw [hD12.deriv]
    exact (norm_add_le _ _).trans ((add_le_add bXh bSh).trans (comb pXh pSh hpXh0 hpSh0 hpPXh hpPSh))
  · have := hiter 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this
  · exact hiter 2 le_rfl

end UnforcedLeray.Short.PartIIIb.Concrete

end
