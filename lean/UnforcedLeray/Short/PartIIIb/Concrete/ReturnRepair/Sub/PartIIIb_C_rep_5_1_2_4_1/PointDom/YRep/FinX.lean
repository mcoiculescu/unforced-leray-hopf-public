import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.Cmp
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.FullMeas

/-!
# Finiteness of the order-four majorant near a young receiver (`PDX0Rep` hypothesis)

Source `the November 2 reference manuscript` 3604-3621, 4171.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_srcNorm_zero (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (σ : ℝ) (z : Space)
    (h : T σ z = 0) : IIIa.srcNorm T σ z = 0 := by
  simp [IIIa.srcNorm, IIIa.tensorNorm, h]

lemma yr_kerA_le {x z : Space} {h r₁ ρ₀ Y a : ℝ} (hh : 0 < h) (hz : ϱ z ≤ ρ₀) (hρ : ρ₀ < r₁)
    (hx : r₁ < ϱ x) (hxY : ‖x‖ < Y) :
    pdLam h ^ a * (‖x - pdLam h • z‖ ^ 4)⁻¹ ≤
      (1 / (r₁ - ρ₀) + 1 + Y / (r₁ - ρ₀)) ^ 4 *
        (pdLam h ^ a * (((1 + pdLam h * ‖z‖) ^ 4)⁻¹)) := by
  have hl0 : 0 < pdLam h := Real.exp_pos _
  have hl1 : pdLam h ≤ 1 := yr_pdLam_le_one hh
  set κ := 1 / (r₁ - ρ₀) + 1 + Y / (r₁ - ρ₀) with hκ
  have hlow := yr_gap_lower (z := z) hl0 hl1 hz hρ hx hxY
  rw [← hκ] at hlow
  have hδ : 0 < r₁ - ρ₀ := by linarith
  have hY : 0 ≤ Y := by linarith [norm_nonneg x]
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hA : 0 < 1 + pdLam h * ‖z‖ := by positivity
  have hn : 0 < ‖x - pdLam h • z‖ := by
    have := norm_sub_lam_ge (y := x) hl0 hl1 hz hx
    linarith
  have h1 : (1 + pdLam h * ‖z‖) / κ ≤ ‖x - pdLam h • z‖ := by
    rw [div_le_iff₀ hκ0]; linarith
  have h2 : ((1 + pdLam h * ‖z‖) / κ) ^ 4 ≤ ‖x - pdLam h • z‖ ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  have h3 : (‖x - pdLam h • z‖ ^ 4)⁻¹ ≤ κ ^ 4 * ((1 + pdLam h * ‖z‖) ^ 4)⁻¹ := by
    calc (‖x - pdLam h • z‖ ^ 4)⁻¹ ≤ (((1 + pdLam h * ‖z‖) / κ) ^ 4)⁻¹ :=
          inv_anti₀ (by positivity) h2
      _ = κ ^ 4 * ((1 + pdLam h * ‖z‖) ^ 4)⁻¹ := by rw [div_pow, inv_div]; ring
  have hp : 0 ≤ pdLam h ^ a := Real.rpow_nonneg hl0.le _
  calc pdLam h ^ a * (‖x - pdLam h • z‖ ^ 4)⁻¹ ≤ pdLam h ^ a * (κ ^ 4 * ((1 + pdLam h * ‖z‖) ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left h3 hp
    _ = κ ^ 4 * (pdLam h ^ a * ((1 + pdLam h * ‖z‖) ^ 4)⁻¹) := by ring

lemma yr_kerA_le_srcWeight {x z : Space} {h r₁ ρ₀ Y : ℝ} (μ : ℝ) (hh : 0 < h) (hz : ϱ z ≤ ρ₀)
    (hρ : ρ₀ < r₁) (hx : r₁ < ϱ x) (hxY : ‖x‖ < Y) :
    pdLam h ^ (2 * μ + 3) * (‖x - pdLam h • z‖ ^ 4)⁻¹ ≤
      (1 / (r₁ - ρ₀) + 1 + Y / (r₁ - ρ₀)) ^ 4 * srcWeight μ h z := by
  refine (yr_kerA_le hh hz hρ hx hxY).trans ?_
  have hκ : 0 ≤ (1 / (r₁ - ρ₀) + 1 + Y / (r₁ - ρ₀)) ^ 4 := by
    have hδ : 0 < r₁ - ρ₀ := by linarith
    have hY : 0 ≤ Y := by linarith [norm_nonneg x]
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hκ
  unfold srcWeight
  have hp : 0 ≤ pdLam h ^ (2 * μ + 3) := Real.rpow_nonneg (Real.exp_pos _).le _
  have h2 : 0 ≤ (1 + (pdLam h * z 2) ^ 2)⁻¹ := by positivity
  nlinarith

/-- **`PDX0Rep` finiteness hypothesis near the receiver.** -/
lemma yr_N2 (μ R c : ℝ) (g : Chart → Ten3) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1)
    {ρ₀ r₁ Y τ ε : ℝ} (hρ : ρ₀ < r₁) (hsupp0 : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z ≤ ρ₀)
    (hε1 : ε ≤ 1)
    (hfin : ∫⁻ e : ℝ × Space, (if e.1 < τ + ε then ENNReal.ofReal (srcWeight μ (τ - e.1) e.2)
      else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤)
    (τ' : ℝ) (hτ' : |τ' - τ| < ε) (x : Space) (hx : r₁ < ϱ x) (hxY : ‖x‖ < Y) :
    ∫⁻ e : ℝ × Space, (if e.1 < τ' then ENNReal.ofReal (pdLam (τ' - e.1) ^ (2 * μ + 3) *
        (‖x - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
      IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤ := by
  set K := (1 / (r₁ - ρ₀) + 1 + Y / (r₁ - ρ₀)) ^ 4 * 512 with hK
  have hle : ∀ e : ℝ × Space, (if e.1 < τ' then ENNReal.ofReal (pdLam (τ' - e.1) ^ (2 * μ + 3) *
        (‖x - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
      IIIa.srcNorm (oldPhys R c g) e.1 e.2 ≤ ENNReal.ofReal K * ((if e.1 < τ + ε then
        ENNReal.ofReal (srcWeight μ (τ - e.1) e.2) else 0) *
          IIIa.srcNorm (oldPhys R c g) e.1 e.2) := by
    intro e
    by_cases h : e.1 < τ'
    · have hτe : e.1 < τ + ε := by
        have := (abs_lt.1 hτ').2; linarith
      rw [if_pos h, if_pos hτe]
      by_cases hM : oldPhys R c g e.1 e.2 = 0
      · rw [yr_srcNorm_zero _ _ _ hM]; simp
      · have hz := hsupp0 _ _ hM
        have hk := yr_kerA_le_srcWeight (x := x) (z := e.2) μ (sub_pos.2 h) hz hρ hx hxY
        have hc := yr_srcWeight_cmp μ hμ0 hμ1 (τ - e.1) (τ' - e.1) e.2 (by
          have : τ' - e.1 - (τ - e.1) = τ' - τ := by ring
          rw [this]
          have := hτ'.le; linarith)
        have hK0 : 0 ≤ (1 / (r₁ - ρ₀) + 1 + Y / (r₁ - ρ₀)) ^ 4 := by
          have hδ : 0 < r₁ - ρ₀ := by linarith
          have hY : 0 ≤ Y := by linarith [norm_nonneg x]
          positivity
        have : pdLam (τ' - e.1) ^ (2 * μ + 3) * (‖x - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹ ≤
            K * srcWeight μ (τ - e.1) e.2 := by
          refine hk.trans ?_
          rw [hK, mul_assoc]
          exact mul_le_mul_of_nonneg_left (by
            have := hc
            -- srcWeight (τ'-e.1) ≤ 512 srcWeight (τ-e.1)
            exact this) hK0
        calc ENNReal.ofReal (pdLam (τ' - e.1) ^ (2 * μ + 3) * (‖x - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) *
              IIIa.srcNorm (oldPhys R c g) e.1 e.2
            ≤ ENNReal.ofReal (K * srcWeight μ (τ - e.1) e.2) *
              IIIa.srcNorm (oldPhys R c g) e.1 e.2 := by gcongr
          _ = _ := by
            rw [ENNReal.ofReal_mul (by rw [hK]; have := hK0; positivity), mul_assoc]
    · rw [if_neg h]; simp
  calc _ ≤ ∫⁻ e : ℝ × Space, ENNReal.ofReal K * ((if e.1 < τ + ε then
        ENNReal.ofReal (srcWeight μ (τ - e.1) e.2) else 0) *
          IIIa.srcNorm (oldPhys R c g) e.1 e.2) := lintegral_mono hle
    _ = ENNReal.ofReal K * ∫⁻ e : ℝ × Space, (if e.1 < τ + ε then
        ENNReal.ofReal (srcWeight μ (τ - e.1) e.2) else 0) *
          IIIa.srcNorm (oldPhys R c g) e.1 e.2 := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end UnforcedLeray.Short.PartIIIb.Concrete

end
