import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3

/-!
# Heat-kernel parabolic scaling (`PartIII-b:IIIb-D2/3/1/1/2/3/1`)

Source `the November 2 reference manuscript`
3600-3610 (`K_t = δ G_t + D² ∫_t^∞ G_a`).  Definitions: `IIIa.heatG`, `IIIa.heatTail`
(`SeparatedKernels.lean:38-46`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Scaling of the heat kernel: `G_{tu}(x) = t^{-3/2} G_u(x/√t)` for `t, u > 0`. -/
theorem heatG_mul_scale_L1 (t u : ℝ) (ht : 0 < t) (hu : 0 < u) (x : Space) :
    IIIa.heatG (t * u) x = t ^ (-(3 / 2 : ℝ)) * IIIa.heatG u ((Real.sqrt t)⁻¹ • x) := by
  unfold IIIa.heatG
  have hsn : ‖(Real.sqrt t)⁻¹‖ = (Real.sqrt t)⁻¹ := by
    rw [norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
  have hs : ‖(Real.sqrt t)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / t := by
    rw [norm_smul, hsn, mul_pow, inv_pow, Real.sq_sqrt ht.le, div_eq_inv_mul]
  rw [hs]
  have hpos : 0 ≤ 4 * Real.pi * u := by positivity
  have hmul : 4 * Real.pi * (t * u) = t * (4 * Real.pi * u) := by ring
  rw [hmul, Real.mul_rpow ht.le hpos]
  have hexp : -‖x‖ ^ 2 / (4 * (t * u)) = -(‖x‖ ^ 2 / t) / (4 * u) := by
    field_simp
  rw [hexp, show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, mul_assoc]

/-- `t * t^{-3/2} = t^{-1/2}` for `t > 0`. -/
theorem mul_rpow_three_halves_L1 (t : ℝ) (ht : 0 < t) :
    t * t ^ (-(3 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
  nth_rewrite 1 [← Real.rpow_one t]
  rw [← Real.rpow_add ht]
  congr 1
  norm_num

/-- Scaling of the heat tail: `∫_t^∞ G_a(x) da = t^{-1/2} (∫_1^∞ G_a)(x/√t)`. -/
theorem heatTail_mul_scale_L1 (t : ℝ) (ht : 0 < t) (x : Space) :
    IIIa.heatTail t x = t ^ (-(1 / 2 : ℝ)) * IIIa.heatTail 1 ((Real.sqrt t)⁻¹ • x) := by
  unfold IIIa.heatTail
  have h1 := integral_comp_mul_left_Ioi' (fun a => IIIa.heatG a x) 1 ht
  simp only [mul_one] at h1
  have h2 : ∫ a in Ioi t, IIIa.heatG a x
      = t * ∫ u in Ioi (1 : ℝ), IIIa.heatG (t * u) x := by
    rw [← h1, smul_eq_mul]
  have h3 : ∫ u in Ioi (1 : ℝ), IIIa.heatG (t * u) x
      = ∫ u in Ioi (1 : ℝ), t ^ (-(3 / 2 : ℝ)) * IIIa.heatG u ((Real.sqrt t)⁻¹ • x) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hu' : (0 : ℝ) < u := by
      have : (1 : ℝ) < u := hu
      linarith
    exact heatG_mul_scale_L1 t u ht hu' x
  rw [h2, h3, integral_const_mul]
  rw [← mul_assoc, mul_rpow_three_halves_L1 t ht]

/-- Parabolic scaling of the heat kernel and of its tail. -/
theorem heatGTailScale_L1 : HeatGTailScale := by
  intro t ht x
  constructor
  · have h := heatG_mul_scale_L1 t 1 ht one_pos x
    rw [mul_one] at h
    exact h
  · exact heatTail_mul_scale_L1 t ht x

/-- **Target** `PartIII-b:IIIb-D2/3/1/1/2/3/1`: parabolic scaling of the heat kernel and its tail. -/
theorem heatGTailScale : HeatGTailScale := heatGTailScale_L1

end UnforcedLeray.Short.PartIIIb.Concrete
