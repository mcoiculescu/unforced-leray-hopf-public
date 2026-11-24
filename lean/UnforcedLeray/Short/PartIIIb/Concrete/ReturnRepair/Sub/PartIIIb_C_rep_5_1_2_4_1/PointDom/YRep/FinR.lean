import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.FinX
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.Rad
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.OutPrimRep

/-!
# Finiteness of the `ρ`-weighted majorant (`PDOutPrimRep` hypothesis)

Source `the November 2 reference manuscript` 4178-4186: across the radial gap,
`∫_r^∞ ρ |(ρ,0,y₃) - λz|^{-4} dρ ≤ C (1 + (λ z₃)²)^{-1}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_abs_z0 (z : Space) : |z 0| ≤ ϱ z := by
  have h := ϱ_sq z
  have h0 := ϱ_nonneg z
  exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (z 1)]) h0

lemma yr_norm_lower {z : Space} {l ρ₀ ρ y3 : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hz : ϱ z ≤ ρ₀)
    (hρ : ρ₀ ≤ ρ) :
    (ρ - ρ₀) ^ 2 + (y3 - l * z 2) ^ 2 ≤ ‖(!₂[ρ, 0, y3] : Space) - l • z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs,
    sq_abs]
  have h1 := yr_abs_z0 z
  have h2 : l * z 0 ≤ ρ₀ := by
    calc l * z 0 ≤ l * |z 0| := mul_le_mul_of_nonneg_left (le_abs_self _) hl0.le
      _ ≤ 1 * ϱ z := mul_le_mul hl1 h1 (abs_nonneg _) (by norm_num)
      _ ≤ ρ₀ := by linarith
  have e0 : (![ρ, 0, y3] : Fin 3 → ℝ) 0 = ρ := rfl
  have e2 : (![ρ, 0, y3] : Fin 3 → ℝ) 2 = y3 := rfl
  rw [e0, e2]
  have h3 : ρ - ρ₀ ≤ ρ - l * z 0 := by linarith
  have h5 : (0 : ℝ) ≤ ρ - ρ₀ := by linarith
  nlinarith [sq_nonneg ((![ρ, 0, y3] : Fin 3 → ℝ) 1 - l * z 1), mul_self_le_mul_self h5 h3]

lemma yr_inner (μ : ℝ) {ρ₀ δ Y : ℝ} (hδ : 0 < δ) (hρ0 : 0 ≤ ρ₀) {z : Space} (hz : ϱ z ≤ ρ₀)
    {h y3 r : ℝ} (hh : 0 < h) (hr : ρ₀ + δ ≤ r) (hy3 : |y3| < Y) :
    ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ * pdLam h ^ (2 * μ + 3) *
        (‖(!₂[ρ, 0, y3] : Space) - pdLam h • z‖ ^ 4)⁻¹) ≤
      ENNReal.ofReal ((1 + ρ₀ / δ) / 2 * ((1 + 2 * Y ^ 2) / δ ^ 2 + 2) * srcWeight μ h z) := by
  have hl0 : 0 < pdLam h := Real.exp_pos _
  have hl1 : pdLam h ≤ 1 := yr_pdLam_le_one hh
  set l := pdLam h with hl
  set hh' := y3 - l * z 2 with hhh
  have hla : 0 ≤ l ^ (2 * μ + 3) := Real.rpow_nonneg hl0.le _
  set C := l ^ (2 * μ + 3) * (1 + ρ₀ / δ) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hpt := yr_rad_lint (ρ₀ := ρ₀) (δ := δ) (r := r) (h := hh') (C := C) hδ hr hC0
    (fun ρ => ρ * l ^ (2 * μ + 3) * (‖(!₂[ρ, 0, y3] : Space) - l • z‖ ^ 4)⁻¹) (by
      intro ρ hρ
      have hρr : r < ρ := hρ
      have hs0 : δ ≤ ρ - ρ₀ := by linarith
      have hs0p : 0 < ρ - ρ₀ := by linarith
      have hlow := yr_norm_lower (y3 := y3) hl0 hl1 hz (by linarith : ρ₀ ≤ ρ)
      have hD : 0 < (ρ - ρ₀) ^ 2 + hh' ^ 2 := by positivity
      have h4 : ((ρ - ρ₀) ^ 2 + hh' ^ 2) ^ 2 ≤ ‖(!₂[ρ, 0, y3] : Space) - l • z‖ ^ 4 := by
        have : ‖(!₂[ρ, 0, y3] : Space) - l • z‖ ^ 4 = (‖(!₂[ρ, 0, y3] : Space) - l • z‖ ^ 2) ^ 2 := by
          ring
        rw [this]
        exact pow_le_pow_left₀ hD.le hlow 2
      have h5 : (‖(!₂[ρ, 0, y3] : Space) - l • z‖ ^ 4)⁻¹ ≤ (((ρ - ρ₀) ^ 2 + hh' ^ 2) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) h4
      have h6 : ρ ≤ (1 + ρ₀ / δ) * (ρ - ρ₀) := by
        have : ρ₀ ≤ ρ₀ / δ * (ρ - ρ₀) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
          nlinarith
        nlinarith
      calc ρ * l ^ (2 * μ + 3) * (‖(!₂[ρ, 0, y3] : Space) - l • z‖ ^ 4)⁻¹
          ≤ ((1 + ρ₀ / δ) * (ρ - ρ₀)) * l ^ (2 * μ + 3) * (((ρ - ρ₀) ^ 2 + hh' ^ 2) ^ 2)⁻¹ := by
            gcongr
        _ = C * (ρ - ρ₀) / (((ρ - ρ₀) ^ 2 + hh' ^ 2) ^ 2) := by
            rw [hC]; field_simp)
  refine hpt.trans (ENNReal.ofReal_le_ofReal ?_)
  -- compare with srcWeight
  have hc3 : 0 < (1 + 2 * Y ^ 2) / δ ^ 2 + 2 := by positivity
  have hA : 0 < δ ^ 2 + hh' ^ 2 := by positivity
  have hB : 0 < 1 + (l * z 2) ^ 2 := by positivity
  have hkey : (δ ^ 2 + hh' ^ 2)⁻¹ ≤ ((1 + 2 * Y ^ 2) / δ ^ 2 + 2) * (1 + (l * z 2) ^ 2)⁻¹ := by
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB]
    have hy2 : y3 ^ 2 ≤ Y ^ 2 := by
      have := abs_lt.1 hy3
      nlinarith [abs_nonneg y3, sq_abs y3]
    have hz2 : (l * z 2) ^ 2 ≤ 2 * Y ^ 2 + 2 * hh' ^ 2 := by
      have : l * z 2 = y3 - hh' := by rw [hhh]; ring
      rw [this]; nlinarith [sq_nonneg (y3 + hh')]
    have hid : (1 + 2 * Y ^ 2) / δ ^ 2 * δ ^ 2 = 1 + 2 * Y ^ 2 := by field_simp
    have hnn : 0 ≤ (1 + 2 * Y ^ 2) / δ ^ 2 := by positivity
    nlinarith [sq_nonneg hh', mul_nonneg hnn (sq_nonneg hh')]
  have hsw : l ^ (2 * μ + 3) * (1 + (l * z 2) ^ 2)⁻¹ ≤ srcWeight μ h z := by
    unfold srcWeight
    rw [← hl]
    have : 0 ≤ ((1 + l * ‖z‖) ^ 4)⁻¹ := by positivity
    nlinarith [mul_nonneg hla this]
  calc C / 2 / (δ ^ 2 + hh' ^ 2) = (1 + ρ₀ / δ) / 2 * l ^ (2 * μ + 3) * (δ ^ 2 + hh' ^ 2)⁻¹ := by
        rw [hC]; field_simp
    _ ≤ (1 + ρ₀ / δ) / 2 * l ^ (2 * μ + 3) *
          (((1 + 2 * Y ^ 2) / δ ^ 2 + 2) * (1 + (l * z 2) ^ 2)⁻¹) := by
        gcongr
    _ = (1 + ρ₀ / δ) / 2 * ((1 + 2 * Y ^ 2) / δ ^ 2 + 2) *
          (l ^ (2 * μ + 3) * (1 + (l * z 2) ^ 2)⁻¹) := by ring
    _ ≤ (1 + ρ₀ / δ) / 2 * ((1 + 2 * Y ^ 2) / δ ^ 2 + 2) * srcWeight μ h z := by
        gcongr

/-- **`PDOutPrimRep` finiteness hypothesis near the receiver.** -/
lemma yr_N3 (μ R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1)
    {ρ₀ r₁ Y τ ε : ℝ} (hρ0 : 0 ≤ ρ₀) (hρ : ρ₀ < r₁)
    (hsupp0 : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z ≤ ρ₀) (hε1 : ε ≤ 1)
    (hfin : ∫⁻ e : ℝ × Space, (if e.1 < τ + ε then ENNReal.ofReal (srcWeight μ (τ - e.1) e.2)
      else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤)
    (τ' : ℝ) (hτ' : |τ' - τ| < ε) (y3 r : ℝ) (hy3 : |y3| < Y) (hr : r₁ ≤ r) :
    ∫⁻ ρ in Ioi r, ∫⁻ e : ℝ × Space, (if e.1 < τ' then ENNReal.ofReal
        (ρ * pdLam (τ' - e.1) ^ (2 * μ + 3) *
          (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
      IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤ := by
  set δ := r₁ - ρ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set K := (1 + ρ₀ / δ) / 2 * ((1 + 2 * Y ^ 2) / δ ^ 2 + 2) * 512 with hK
  have hK0 : 0 ≤ K := by
    have hY : 0 ≤ Y := (abs_nonneg y3).trans hy3.le
    rw [hK]; positivity
  have hF0 := pdOR_F0_meas μ τ' R c y3 g hg
  rw [lintegral_lintegral_swap hF0.aemeasurable]
  have hle : ∀ e : ℝ × Space, ∫⁻ ρ in Ioi r, (if e.1 < τ' then ENNReal.ofReal
        (ρ * pdLam (τ' - e.1) ^ (2 * μ + 3) *
          (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
      IIIa.srcNorm (oldPhys R c g) e.1 e.2 ≤ ENNReal.ofReal K * ((if e.1 < τ + ε then
        ENNReal.ofReal (srcWeight μ (τ - e.1) e.2) else 0) *
          IIIa.srcNorm (oldPhys R c g) e.1 e.2) := by
    intro e
    by_cases h : e.1 < τ'
    · have hτe : e.1 < τ + ε := by
        have := (abs_lt.1 hτ').2; linarith
      rw [if_pos hτe]
      by_cases hM : oldPhys R c g e.1 e.2 = 0
      · rw [yr_srcNorm_zero _ _ _ hM]; simp
      · have hz := hsupp0 _ _ hM
        have hin := yr_inner μ hδ0 hρ0 hz (y3 := y3) (r := r) (sub_pos.2 h) (by rw [hδ]; linarith) hy3
        have hc := yr_srcWeight_cmp μ hμ0 hμ1 (τ - e.1) (τ' - e.1) e.2 (by
          have : τ' - e.1 - (τ - e.1) = τ' - τ := by ring
          rw [this]
          have := hτ'.le; linarith)
        have hsn : IIIa.srcNorm (oldPhys R c g) e.1 e.2 ≠ ⊤ := ENNReal.ofReal_ne_top
        have hcm : (fun ρ : ℝ => (if e.1 < τ' then ENNReal.ofReal
            (ρ * pdLam (τ' - e.1) ^ (2 * μ + 3) *
              (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
            IIIa.srcNorm (oldPhys R c g) e.1 e.2) = fun ρ => ENNReal.ofReal
            (ρ * pdLam (τ' - e.1) ^ (2 * μ + 3) *
              (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) *
            IIIa.srcNorm (oldPhys R c g) e.1 e.2 := by
          funext ρ; rw [if_pos h]
        rw [hcm, lintegral_mul_const' _ _ hsn]
        calc (∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ * pdLam (τ' - e.1) ^ (2 * μ + 3) *
              (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹)) *
              IIIa.srcNorm (oldPhys R c g) e.1 e.2
            ≤ ENNReal.ofReal ((1 + ρ₀ / δ) / 2 * ((1 + 2 * Y ^ 2) / δ ^ 2 + 2) *
                srcWeight μ (τ' - e.1) e.2) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 := by
              gcongr
          _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (srcWeight μ (τ - e.1) e.2) *
                IIIa.srcNorm (oldPhys R c g) e.1 e.2) := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hK0]
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
              have hK1 : 0 ≤ (1 + ρ₀ / δ) / 2 * ((1 + 2 * Y ^ 2) / δ ^ 2 + 2) := by
                have hY : 0 ≤ Y := (abs_nonneg y3).trans hy3.le
                positivity
              have := mul_le_mul_of_nonneg_left hc hK1
              rw [hK]
              linarith
    · simp [h]
  calc _ ≤ ∫⁻ e : ℝ × Space, ENNReal.ofReal K * ((if e.1 < τ + ε then
        ENNReal.ofReal (srcWeight μ (τ - e.1) e.2) else 0) *
          IIIa.srcNorm (oldPhys R c g) e.1 e.2) := lintegral_mono hle
    _ = ENNReal.ofReal K * ∫⁻ e : ℝ × Space, (if e.1 < τ + ε then
        ENNReal.ofReal (srcWeight μ (τ - e.1) e.2) else 0) *
          IIIa.srcNorm (oldPhys R c g) e.1 e.2 := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end UnforcedLeray.Short.PartIIIb.Concrete

end
