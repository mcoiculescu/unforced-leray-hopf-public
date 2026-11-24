import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2

/-!
# Part III-a, task `PartIII-a:T21/c2/2/4`: `FmrIsoRadial`

Source of record: `the November 2 reference manuscript` lines 2952-2953.
The central Gaussian velocity `isoVelocity ν σ` is a perpendicular gradient of a radial stream,
so it is orthogonal to the gradient of the radial weight `p = (1 + |x|²/a)^m`; and
`|∂_j p| ≤ (m/√a) p` because `2|x_j|√a ≤ a + |x|²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa

/-- Differentiability of the dilated weight (base `≥ 1`). -/
theorem fmrIso_movWeight_differentiable (m a : ℝ) (ha : 0 < a) :
    Differentiable ℝ (movWeight m a) := by
  intro x
  unfold movWeight
  have hb : (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ≠ 0 := by
    have : 0 ≤ (x.1 ^ 2 + x.2 ^ 2) / a := div_nonneg (by positivity) ha.le
    linarith
  have h1 : DifferentiableAt ℝ (fun y : B0579.Plane => 1 + (y.1 ^ 2 + y.2 ^ 2) / a) x := by
    fun_prop
  exact (h1.rpow_const (Or.inl hb))

/-- Partial derivative of the dilated weight in the `q` direction. -/
theorem fmrIso_pd0 (m a : ℝ) (ha : 0 < a) (x : B0579.Plane) :
    B0579.pd 0 (movWeight m a) x =
      m * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 1) * (2 * x.1 / a) := by
  obtain ⟨q, η⟩ := x
  have h1 := B0579.hasDerivAt_fst (fmrIso_movWeight_differentiable m a ha) q η
  have hb : (1 + (q ^ 2 + η ^ 2) / a) ≠ 0 := by
    have : 0 ≤ (q ^ 2 + η ^ 2) / a := div_nonneg (by positivity) ha.le
    linarith
  have h2 : HasDerivAt (fun t => movWeight m a (t, η))
      (m * (1 + (q ^ 2 + η ^ 2) / a) ^ (m - 1) * (2 * q / a)) q := by
    unfold movWeight
    have hh : HasDerivAt (fun t : ℝ => 1 + (t ^ 2 + η ^ 2) / a) (2 * q / a) q := by
      have := (((hasDerivAt_pow 2 q).add_const (η ^ 2)).div_const a).const_add 1
      exact this.congr_deriv (by norm_num)
    have := hh.rpow_const (p := m) (Or.inl hb)
    convert this using 1
    ring
  exact h1.unique h2

/-- Partial derivative of the dilated weight in the `η` direction. -/
theorem fmrIso_pd1 (m a : ℝ) (ha : 0 < a) (x : B0579.Plane) :
    B0579.pd 1 (movWeight m a) x =
      m * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 1) * (2 * x.2 / a) := by
  obtain ⟨q, η⟩ := x
  have h1 := B0579.hasDerivAt_snd (fmrIso_movWeight_differentiable m a ha) q η
  have hb : (1 + (q ^ 2 + η ^ 2) / a) ≠ 0 := by
    have : 0 ≤ (q ^ 2 + η ^ 2) / a := div_nonneg (by positivity) ha.le
    linarith
  have h2 : HasDerivAt (fun t => movWeight m a (q, t))
      (m * (1 + (q ^ 2 + η ^ 2) / a) ^ (m - 1) * (2 * η / a)) η := by
    unfold movWeight
    have hh : HasDerivAt (fun t : ℝ => 1 + (q ^ 2 + t ^ 2) / a) (2 * η / a) η := by
      have := (((hasDerivAt_pow 2 η).const_add (q ^ 2)).div_const a).const_add 1
      exact this.congr_deriv (by norm_num)
    have := hh.rpow_const (p := m) (Or.inl hb)
    convert this using 1
    ring
  exact h1.unique h2

theorem fmrIsoRadial : FmrIsoRadial := by
  intro m hm ν σ ha x
  set a := clockA ν σ with ha_def
  have hA : a = UnforcedLeray.B0113.heatWidth ν σ := rfl
  have hv : UnforcedLeray.B0146.isoVelocity ν σ x =
      UnforcedLeray.B0113.vExp a x := by
    rw [UnforcedLeray.B0146.isoVelocity_eq, hA]
  have hw : 0 < 1 + (x.1 ^ 2 + x.2 ^ 2) / a := by
    have : 0 ≤ (x.1 ^ 2 + x.2 ^ 2) / a := div_nonneg (by positivity) ha.le
    linarith
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hss : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  rw [fmrIso_pd0 m a ha x, fmrIso_pd1 m a ha x]
  set W := (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 1) with hW
  set w := 1 + (x.1 ^ 2 + x.2 ^ 2) / a with hwdef
  have hWnn : 0 ≤ W := Real.rpow_nonneg hw.le _
  have hpow : movWeight m a x = W * w := by
    unfold movWeight
    rw [hW, ← Real.rpow_add_one hw.ne']
    congr 1
    ring
  have hmW : 0 ≤ m * W := mul_nonneg hm hWnn
  refine ⟨?_, ?_, ?_⟩
  · rw [hv]
    unfold UnforcedLeray.B0113.vExp
    simp only
    ring
  · rw [hpow]
    have key : 2 * |x.1| / a ≤ w / Real.sqrt a := by
      rw [div_le_div_iff₀ ha hs]
      have hwa : w * a = a + (x.1 ^ 2 + x.2 ^ 2) := by
        rw [hwdef]
        field_simp
      rw [hwa]
      nlinarith [sq_nonneg (Real.sqrt a - |x.1|), sq_abs x.1, sq_nonneg x.2, hss]
    rw [show m * W * (2 * x.1 / a) = m * W * (2 * x.1 / a) from rfl]
    have habs : |m * W * (2 * x.1 / a)| = m * W * (2 * |x.1| / a) := by
      rw [abs_mul, abs_of_nonneg hmW, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_pos ha]
    rw [habs]
    have h3 : m * W * (2 * |x.1| / a) ≤ m * W * (w / Real.sqrt a) :=
      mul_le_mul_of_nonneg_left key hmW
    calc m * W * (2 * |x.1| / a) ≤ m * W * (w / Real.sqrt a) := h3
      _ = m / Real.sqrt a * (W * w) := by ring
  · rw [hpow]
    have key : 2 * |x.2| / a ≤ w / Real.sqrt a := by
      rw [div_le_div_iff₀ ha hs]
      have hwa : w * a = a + (x.1 ^ 2 + x.2 ^ 2) := by
        rw [hwdef]
        field_simp
      rw [hwa]
      nlinarith [sq_nonneg (Real.sqrt a - |x.2|), sq_abs x.2, sq_nonneg x.1, hss]
    have habs : |m * W * (2 * x.2 / a)| = m * W * (2 * |x.2| / a) := by
      rw [abs_mul, abs_of_nonneg hmW, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_pos ha]
    rw [habs]
    have h3 : m * W * (2 * |x.2| / a) ≤ m * W * (w / Real.sqrt a) :=
      mul_le_mul_of_nonneg_left key hmW
    calc m * W * (2 * |x.2| / a) ≤ m * W * (w / Real.sqrt a) := h3
      _ = m / Real.sqrt a * (W * w) := by ring

end UnforcedLeray.Short.IIIa
