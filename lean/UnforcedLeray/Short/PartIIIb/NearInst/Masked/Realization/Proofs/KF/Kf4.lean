import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub1

/-!
# `KF4`: homogeneity of the heat-Leray kernel (source 3604-3606)

`K_t(ρx) = ρ^{-3} K_{t/ρ²}(x)` for `ρ, t > 0`, from the heat kernel scaling
`G_t(ρx) = ρ^{-3} G_{t/ρ²}(x)`, the substitution `a = ρ² b` in `heatTail`, and the second-derivative
scaling `∂∂(f∘ρ) = ρ² (∂∂f)∘ρ`.  The derivative identity then follows by differentiating the
function identity along `ρ`.  No differentiability hypothesis is needed: the scalar and
composition rules used (`fderiv_comp_smul`, and `fderiv_const_mul` in both cases) hold for
non-differentiable maps as well.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.IIIa

/-- Pulling a real scalar out of a derivative, with no differentiability hypothesis. -/
theorem kf4_fderiv_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E → ℝ) (c : ℝ) (x : E) :
    fderiv ℝ (fun y => c * h y) x = c • fderiv ℝ h x := by
  by_cases hd : DifferentiableAt ℝ h x
  · exact fderiv_const_mul hd c
  · by_cases hc : c = 0
    · subst hc
      simp
    · have hnd : ¬ DifferentiableAt ℝ (fun y => c * h y) x := by
        intro h'
        apply hd
        have h'' := h'.const_mul c⁻¹
        simpa [inv_mul_cancel_left₀ hc] using h''
      rw [fderiv_zero_of_not_differentiableAt hnd,
        fderiv_zero_of_not_differentiableAt hd, smul_zero]

/-- Second derivatives under a dilation: `∂∂(f∘(c•)) = c² (∂∂f)∘(c•)`. -/
theorem kf4_part2_comp_smul (f : Space → ℝ) (c : ℝ) (i j : Fin 3) (x : Space) :
    part2 (fun y => f (c • y)) i j x = c ^ 2 * part2 f i j (c • x) := by
  unfold part2
  have h1 : (fun y => fderiv ℝ (fun y => f (c • y)) y (UnforcedLeray.coordinateVector j)) =
      fun y => c * fderiv ℝ (fun z => f z) (c • y) (UnforcedLeray.coordinateVector j) := by
    funext y
    rw [fderiv_comp_smul]
    simp [smul_eq_mul]
  rw [h1, kf4_fderiv_const_mul (fun y => fderiv ℝ (fun z => f z) (c • y)
    (UnforcedLeray.coordinateVector j)) c x]
  have h2 := fderiv_comp_smul (𝕜 := ℝ)
    (f := fun z => fderiv ℝ (fun w => f w) z (UnforcedLeray.coordinateVector j)) (x := x) c
  beta_reduce at h2
  rw [h2]
  simp [smul_eq_mul]
  ring

/-- Scalars out of `part2`. -/
theorem kf4_part2_const_mul (f : Space → ℝ) (c : ℝ) (i j : Fin 3) (x : Space) :
    part2 (fun y => c * f y) i j x = c * part2 f i j x := by
  unfold part2
  have h1 : (fun y => fderiv ℝ (fun y => c * f y) y (UnforcedLeray.coordinateVector j)) =
      fun y => c * fderiv ℝ f y (UnforcedLeray.coordinateVector j) := by
    funext y
    rw [kf4_fderiv_const_mul f c y]
    simp [smul_eq_mul]
  rw [h1, kf4_fderiv_const_mul (fun y => fderiv ℝ f y (UnforcedLeray.coordinateVector j)) c x]
  simp [smul_eq_mul]

/-- Heat kernel scaling `G_t(ρx) = ρ^{-3} G_{t/ρ²}(x)`. -/
theorem kf4_heatG_comp_smul (t ρ : ℝ) (ht : 0 < t) (hρ : 0 < ρ) (x : Space) :
    IIIa.heatG t (ρ • x) = (ρ ^ 3)⁻¹ * IIIa.heatG (t / ρ ^ 2) x := by
  unfold IIIa.heatG
  have hn : ‖ρ • x‖ ^ 2 = ρ ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg hρ.le]
    ring
  rw [hn]
  have hA : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hp : (ρ ^ 2) ^ (-3 / 2 : ℝ) = (ρ ^ 3)⁻¹ := by
    rw [show (ρ ^ 2 : ℝ) = ρ ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
      ← Real.rpow_mul hρ.le, show (((2 : ℕ) : ℝ)) * (-3 / 2) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hρ.le, Real.rpow_natCast]
  rw [show 4 * Real.pi * (t / ρ ^ 2) = (4 * Real.pi * t) / ρ ^ 2 by ring,
    Real.div_rpow hA.le (by positivity), hp]
  have he : -(ρ ^ 2 * ‖x‖ ^ 2) / (4 * t) = -‖x‖ ^ 2 / (4 * t / ρ ^ 2) := by
    field_simp
  rw [he]
  have hρ0 : ρ ≠ 0 := hρ.ne'
  field_simp

/-- Tail scaling `∫_t^∞ G_a(ρx) da = ρ^{-1} ∫_{t/ρ²}^∞ G_b(x) db`. -/
theorem kf4_heatTail_comp_smul (t ρ : ℝ) (ht : 0 < t) (hρ : 0 < ρ) (x : Space) :
    IIIa.heatTail t (ρ • x) = ρ⁻¹ * IIIa.heatTail (t / ρ ^ 2) x := by
  unfold IIIa.heatTail
  have hcongr : ∫ a in Ioi t, IIIa.heatG a (ρ • x) =
      ∫ a in Ioi t, (ρ ^ 3)⁻¹ * IIIa.heatG ((ρ ^ 2)⁻¹ * a) x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun a ha => ?_)
    have ha' : 0 < a := lt_trans ht ha
    rw [kf4_heatG_comp_smul a ρ ha' hρ x, div_eq_inv_mul]
  have hb : (0 : ℝ) < (ρ ^ 2)⁻¹ := by positivity
  have hsub := integral_comp_mul_left_Ioi (fun u => IIIa.heatG u x) t hb
  rw [hcongr, integral_const_mul, hsub, smul_eq_mul, inv_inv,
    show (ρ ^ 2)⁻¹ * t = t / ρ ^ 2 by ring]
  have hρ0 : ρ ≠ 0 := hρ.ne'
  field_simp

/-- The second derivative of the tail under the dilation. -/
theorem kf4_part2_heatTail_comp_smul (t ρ : ℝ) (ht : 0 < t) (hρ : 0 < ρ) (i j : Fin 3)
    (y : Space) :
    part2 (IIIa.heatTail t) i j (ρ • y) = (ρ ^ 3)⁻¹ * part2 (IIIa.heatTail (t / ρ ^ 2)) i j y := by
  have hA := kf4_part2_comp_smul (IIIa.heatTail t) ρ i j y
  have hfun : (fun z => IIIa.heatTail t (ρ • z)) =
      fun z => ρ⁻¹ * IIIa.heatTail (t / ρ ^ 2) z :=
    funext (kf4_heatTail_comp_smul t ρ ht hρ)
  rw [hfun, kf4_part2_const_mul] at hA
  have hρ0 : ρ ≠ 0 := hρ.ne'
  apply mul_left_cancel₀ (pow_ne_zero 2 hρ0)
  rw [← hA]
  field_simp

/-- The heat-Leray kernel scales as `K_t(ρx) = ρ^{-3} K_{t/ρ²}(x)`. -/
theorem kf4_heatLerayK_comp_smul (t ρ : ℝ) (ht : 0 < t) (hρ : 0 < ρ) (i j : Fin 3)
    (y : Space) :
    IIIa.heatLerayK t i j (ρ • y) = (ρ ^ 3)⁻¹ * IIIa.heatLerayK (t / ρ ^ 2) i j y := by
  unfold IIIa.heatLerayK
  rw [kf4_part2_heatTail_comp_smul t ρ ht hρ i j y]
  split_ifs
  · rw [kf4_heatG_comp_smul t ρ ht hρ y]
    ring
  · ring

theorem kf4 : KF4 := by
  unfold KF4
  intro ρ θ hρ hθ i j k x
  have hfun : (fun y => IIIa.heatLerayK θ i j (ρ • y)) =
      fun y => (ρ ^ 3)⁻¹ * IIIa.heatLerayK (θ / ρ ^ 2) i j y :=
    funext (kf4_heatLerayK_comp_smul θ ρ hθ hρ i j)
  have hA := fderiv_comp_smul (𝕜 := ℝ)
    (f := fun y => IIIa.heatLerayK θ i j y) (x := x) ρ
  beta_reduce at hA
  rw [hfun, kf4_fderiv_const_mul (fun y => IIIa.heatLerayK (θ / ρ ^ 2) i j y) (ρ ^ 3)⁻¹ x]
    at hA
  have hB := congrArg (fun L => L (UnforcedLeray.coordinateVector k)) hA
  simp only [smul_apply, smul_eq_mul] at hB
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have key : fderiv ℝ (fun y => IIIa.heatLerayK θ i j y) (ρ • x) (UnforcedLeray.coordinateVector k)
      = ρ⁻¹ * ((ρ ^ 3)⁻¹ * fderiv ℝ (fun y => IIIa.heatLerayK (θ / ρ ^ 2) i j y) x
        (UnforcedLeray.coordinateVector k)) := by
    rw [hB, ← mul_assoc, inv_mul_cancel₀ hρ0, one_mul]
  rw [key]
  field_simp
