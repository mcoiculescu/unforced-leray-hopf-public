import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4

/-!
# `PartIII-b:C/rep/2/4/1` : the `ρ`-integral of the gap kernel (`OutMajRho`)

Source `the November 2 reference manuscript` 4181-4192, 3603-3610.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `∫_r^∞ (ρ-c)/((ρ-c)²+t²)² dρ = 1/(2((r-c)²+t²))` for `r > c`. -/
theorem tailInt (c t r : ℝ) (hr : c < r) :
    ∫⁻ ρ in Ioi r, ENNReal.ofReal ((ρ - c) / (((ρ - c) ^ 2 + t ^ 2) ^ 2)) =
      ENNReal.ofReal (1 / (2 * ((r - c) ^ 2 + t ^ 2))) := by
  have hpos : ∀ ρ, c < ρ → 0 < (ρ - c) ^ 2 + t ^ 2 := fun ρ hρ => by
    have : 0 < ρ - c := by linarith
    positivity
  set G : ℝ → ℝ := fun ρ => -(1 / 2) * ((ρ - c) ^ 2 + t ^ 2)⁻¹ with hG
  have hder : ∀ ρ ∈ Ioi r, HasDerivAt G ((ρ - c) / (((ρ - c) ^ 2 + t ^ 2) ^ 2)) ρ := by
    intro ρ hρ
    have hρc : c < ρ := lt_trans hr hρ
    have hne := (hpos ρ hρc).ne'
    have h1 : HasDerivAt (fun ρ => (ρ - c) ^ 2 + t ^ 2) (2 * (ρ - c)) ρ := by
      have := (((hasDerivAt_id ρ).sub_const c).pow 2).add_const (t ^ 2)
      simpa using this
    have h2 := (h1.inv hne).const_mul (-(1 / 2))
    refine HasDerivAt.congr_deriv h2 ?_
    field_simp
  have hnn : ∀ ρ ∈ Ioi r, 0 ≤ (ρ - c) / (((ρ - c) ^ 2 + t ^ 2) ^ 2) := by
    intro ρ hρ
    have : 0 < ρ - c := by have := hρ.out; linarith
    positivity
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun ρ : ℝ => (ρ - c) ^ 2 + t ^ 2) atTop atTop := by
      refine tendsto_atTop_add_const_right _ _ ?_
      exact (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    have := (tendsto_inv_atTop_zero.comp h1).const_mul (-(1 / 2) : ℝ)
    simpa [hG] using this
  have hcont : ContinuousWithinAt G (Ici r) r := by
    have : ContinuousAt G r := by
      have hne := (hpos r hr).ne'
      refine ContinuousAt.mul continuousAt_const (ContinuousAt.inv₀ ?_ hne)
      fun_prop
    exact this.continuousWithinAt
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hder hnn hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hnn hlim
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hnn)), hval]
  congr 1
  simp only [hG]
  have := (hpos r hr).ne'
  field_simp
  ring

/-- Pointwise bound of the gap kernel. -/
theorem sepKd_le (rOut rIn r z l : ℝ) (z' : Space) (hrO : 0 ≤ rOut) (hrr : rOut < rIn)
    (hr : rIn ≤ r) (hl0 : 0 < l) (hl1 : l < 1) (hz : ϱ z' ≤ rOut) (ρ : ℝ) (hρ : r < ρ) :
    IIIa.sepKd 0 (rIn - rOut) (!₂[ρ, 0, z] - l • z') ≤
      ENNReal.ofReal ((((ρ - rOut) ^ 2 + (z - l * z' 2) ^ 2) ^ 2)⁻¹) := by
  unfold IIIa.sepKd
  split_ifs with hD
  · set x : Space := !₂[ρ, 0, z] - l • z' with hx
    have hnorm : ‖x‖ ^ 2 = (ρ - l * z' 0) ^ 2 + (l * z' 1) ^ 2 + (z - l * z' 2) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_three, hx, Real.norm_eq_abs, sq_abs]
    have hu : 0 ≤ ρ - rOut := by linarith
    have hϱ0 : z' 0 ≤ ϱ z' := by
      unfold ϱ
      exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (z' 1)])
    have hϱ2 : ϱ z' ^ 2 = z' 0 ^ 2 + z' 1 ^ 2 := by
      unfold ϱ; rw [Real.sq_sqrt (by positivity)]
    have hϱnn : 0 ≤ ϱ z' := Real.sqrt_nonneg _
    have hρ0 : 0 ≤ ρ := by linarith
    have h1 : (ρ - l * ϱ z') ^ 2 ≤ (ρ - l * z' 0) ^ 2 + (l * z' 1) ^ 2 := by
      have : l * ϱ z' ^ 2 * l = l ^ 2 * (z' 0 ^ 2 + z' 1 ^ 2) := by rw [hϱ2]; ring
      nlinarith [mul_nonneg hρ0 hl0.le, mul_le_mul_of_nonneg_left hϱ0 (mul_nonneg hρ0 hl0.le)]
    have h2 : ρ - rOut ≤ ρ - l * ϱ z' := by nlinarith
    have h3 : (ρ - rOut) ^ 2 ≤ (ρ - l * ϱ z') ^ 2 := by
      apply pow_le_pow_left₀ hu h2
    have hw : (ρ - rOut) ^ 2 + (z - l * z' 2) ^ 2 ≤ ‖x‖ ^ 2 := by rw [hnorm]; linarith
    have hDpos : 0 < rIn - rOut := by linarith
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hDpos hD
    have hwpos : 0 < (ρ - rOut) ^ 2 + (z - l * z' 2) ^ 2 := by
      have : 0 < ρ - rOut := by linarith
      positivity
    refine ENNReal.ofReal_le_ofReal ?_
    have : ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)) = ((‖x‖ ^ 2) ^ 2)⁻¹ := by
      rw [show (-4 - ((0 : ℕ) : ℝ)) = -(4 : ℕ) by norm_num, Real.rpow_neg hxpos.le,
        Real.rpow_natCast]
      congr 1; ring
    rw [this]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hwpos.le hw 2)
  · exact bot_le

theorem outMajRho : OutMajRho := by
  intro rOut rIn hrO hrr r z l z' hr hl0 hl1 hz
  have hDpos : 0 < rIn - rOut := by linarith
  have hrIn : 0 < rIn := by linarith
  set D := rIn - rOut with hD
  set t := z - l * z' 2 with ht
  have hr0 : rOut < r := by linarith
  -- pointwise
  have hpt : ∀ ρ ∈ Ioi r, ENNReal.ofReal ρ * IIIa.sepKd 0 D (!₂[ρ, 0, z] - l • z') ≤
      ENNReal.ofReal (rIn / D) * ENNReal.ofReal ((ρ - rOut) / (((ρ - rOut) ^ 2 + t ^ 2) ^ 2)) := by
    intro ρ hρ
    have hρ' : r < ρ := hρ
    have hk := sepKd_le rOut rIn r z l z' hrO hrr hr hl0 hl1 hz ρ hρ'
    have hu : D ≤ ρ - rOut := by linarith
    have hρle : ρ ≤ rIn / D * (ρ - rOut) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hDpos]
      nlinarith [mul_le_mul_of_nonneg_left hu hrO]
    calc ENNReal.ofReal ρ * IIIa.sepKd 0 D (!₂[ρ, 0, z] - l • z')
        ≤ ENNReal.ofReal (rIn / D * (ρ - rOut)) *
            ENNReal.ofReal ((((ρ - rOut) ^ 2 + t ^ 2) ^ 2)⁻¹) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hρle) hk
      _ = _ := by
          rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) (by linarith)),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_eq_mul_inv]; ring
  calc ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * IIIa.sepKd 0 D (!₂[ρ, 0, z] - l • z')
      ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal (rIn / D) *
          ENNReal.ofReal ((ρ - rOut) / (((ρ - rOut) ^ 2 + t ^ 2) ^ 2)) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (rIn / D) * ENNReal.ofReal (1 / (2 * ((r - rOut) ^ 2 + t ^ 2))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, tailInt rOut t r hr0]
    _ ≤ vertKern rIn D t := by
        unfold vertKern
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hu : D ≤ r - rOut := by linarith
        have hsq : D ^ 2 ≤ (r - rOut) ^ 2 := pow_le_pow_left₀ hDpos.le hu 2
        have h1 : 0 < D ^ 2 + t ^ 2 := by positivity
        have h2 : 0 < (r - rOut) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 < rIn := hrIn
        nlinarith [mul_pos this hDpos, mul_nonneg (mul_pos this hDpos).le (sub_nonneg.2 hsq)]

end UnforcedLeray.Short.PartIIIb.Concrete
