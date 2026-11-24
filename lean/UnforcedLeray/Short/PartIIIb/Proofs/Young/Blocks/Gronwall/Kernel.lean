import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Gronwall.Ode

/-!
# Exponential-kernel primitives for the block Gronwall step (source 4396-4406)

For a function `X` continuous on `[t, T]` the kernel primitive
`J(u) = ∫_t^u exp(-g(u-r)) X(r) dr` is continuous, has derivative `X(x) - g J(x)`,
and satisfies `g ∫_t^s J = ∫_t^s X - J(s)`.  These are the facts used to bound the
complement integral `∫ ρ` without a Fubini argument.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.BlockGronwallAux

/-- Continuity of the primitive `u ↦ ∫_t^u f` on `[t, T]`. -/
theorem primitive_continuousOn {t T : ℝ} {f : ℝ → ℝ} (hT : t ≤ T)
    (hf : ContinuousOn f (Icc t T)) :
    ContinuousOn (fun u => ∫ r in t..u, f r) (Icc t T) := by
  have hfT : IntervalIntegrable f volume t T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact hf
  have := intervalIntegral.continuousOn_primitive_interval' hfT (Set.left_mem_uIcc)
  rw [Set.uIcc_of_le hT] at this
  exact this

/-- Derivative of the primitive `u ↦ ∫_t^u f` at interior points. -/
theorem primitive_hasDerivAt {t T : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc t T)) {x : ℝ}
    (hx : x ∈ Ioo t T) :
    HasDerivAt (fun u => ∫ r in t..u, f r) (f x) x := by
  have hxI : x ∈ Icc t T := Ioo_subset_Icc_self hx
  have hfc : ContinuousAt f x := hf.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hfm : StronglyMeasurableAtFilter f (nhds x) volume :=
    (hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_of_cont hf hxI) hfm hfc

/-- Factorisation `∫_t^s e^{-g(s-r)} X(r) dr = e^{-gs} ∫_t^s e^{gr} X(r) dr`. -/
theorem kernel_factor {g t : ℝ} {X : ℝ → ℝ} (s : ℝ) :
    (∫ r in t..s, Real.exp (-g * (s - r)) * X r) =
      Real.exp (-g * s) * ∫ r in t..s, Real.exp (g * r) * X r := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [show -g * (s - r) = -g * s + g * r by ring, Real.exp_add]
  ring

/-- Continuity of the kernel primitive `J(u) = ∫_t^u e^{-g(u-r)} X(r) dr` on `[t, T]`. -/
theorem kernel_continuousOn {g t T : ℝ} {X : ℝ → ℝ} (hT : t ≤ T)
    (hX : ContinuousOn X (Icc t T)) :
    ContinuousOn (fun u => ∫ r in t..u, Real.exp (-g * (u - r)) * X r) (Icc t T) := by
  have hf : ContinuousOn (fun r => Real.exp (g * r) * X r) (Icc t T) :=
    (Continuous.continuousOn (by fun_prop : Continuous (fun r : ℝ => Real.exp (g * r)))).mul hX
  have hc1 : ContinuousOn (fun u : ℝ => Real.exp (-g * u)) (Icc t T) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (-g * u))).continuousOn
  have hfun : (fun u => ∫ r in t..u, Real.exp (-g * (u - r)) * X r) =
      fun u => Real.exp (-g * u) * ∫ r in t..u, Real.exp (g * r) * X r :=
    funext kernel_factor
  rw [hfun]
  exact hc1.mul (primitive_continuousOn hT hf)

/-- Derivative of the kernel primitive at interior points: `J'(x) = X(x) - g J(x)`. -/
theorem kernel_hasDerivAt {g t T : ℝ} {X : ℝ → ℝ} (hX : ContinuousOn X (Icc t T)) {x : ℝ}
    (hx : x ∈ Ioo t T) :
    HasDerivAt (fun u => ∫ r in t..u, Real.exp (-g * (u - r)) * X r)
      (X x - g * ∫ r in t..x, Real.exp (-g * (x - r)) * X r) x := by
  have hf : ContinuousOn (fun r => Real.exp (g * r) * X r) (Icc t T) :=
    (Continuous.continuousOn (by fun_prop : Continuous (fun r : ℝ => Real.exp (g * r)))).mul hX
  have hP := primitive_hasDerivAt hf hx
  have he : HasDerivAt (fun u => Real.exp (-g * u)) (Real.exp (-g * x) * (-g * 1)) x :=
    ((hasDerivAt_id' x).const_mul (-g)).exp
  have hprod := he.mul hP
  have hE : Real.exp (-g * x) * Real.exp (g * x) = 1 := by
    rw [← Real.exp_add, show -g * x + g * x = 0 by ring, Real.exp_zero]
  have hfun : (fun u => ∫ r in t..u, Real.exp (-g * (u - r)) * X r) =
      fun u => Real.exp (-g * u) * ∫ r in t..u, Real.exp (g * r) * X r :=
    funext kernel_factor
  rw [hfun, kernel_factor x]
  exact hprod.congr_deriv (by beta_reduce; linear_combination (X x) * hE)

/-- Nonnegativity of the kernel primitive when `X ≥ 0` on `[t, s]`. -/
theorem kernel_nonneg {g t s : ℝ} {X : ℝ → ℝ} (hts : t ≤ s) (hX : ∀ r ∈ Icc t s, 0 ≤ X r) :
    0 ≤ ∫ r in t..s, Real.exp (-g * (s - r)) * X r := by
  apply intervalIntegral.integral_nonneg hts
  intro r hr
  exact mul_nonneg (Real.exp_pos _).le (hX r hr)

/-- Integral identity `g ∫_t^s J = ∫_t^s X - J(s)` for `J(u) = ∫_t^u e^{-g(u-r)} X(r) dr`. -/
theorem kernel_integral_identity {g t T : ℝ} {X : ℝ → ℝ} (hT : t ≤ T)
    (hX : ContinuousOn X (Icc t T)) {s : ℝ} (hs : s ∈ Icc t T) :
    g * ∫ u in t..s, (∫ r in t..u, Real.exp (-g * (u - r)) * X r) =
      (∫ r in t..s, X r) - ∫ r in t..s, Real.exp (-g * (s - r)) * X r := by
  have hts : t ≤ s := hs.1
  have hsub : Icc t s ⊆ Icc t T := Icc_subset_Icc le_rfl hs.2
  have hXs : ContinuousOn X (Icc t s) := hX.mono hsub
  have hderiv : ∀ x ∈ Ioo t s, HasDerivWithinAt
      (fun u => (∫ r in t..u, X r) - ∫ r in t..u, Real.exp (-g * (u - r)) * X r)
      (g * ∫ r in t..x, Real.exp (-g * (x - r)) * X r) (Ioi x) x := by
    intro x hx
    have hxT : x ∈ Ioo t T := ⟨hx.1, lt_of_lt_of_le hx.2 hs.2⟩
    have h1 := primitive_hasDerivAt hX hxT
    have h2 := kernel_hasDerivAt (g := g) hX hxT
    have h3 := h1.sub h2
    have h4 := h3.hasDerivWithinAt (s := Ioi x)
    exact h4.congr_deriv (by ring)
  have hcont : ContinuousOn
      (fun u => (∫ r in t..u, X r) - ∫ r in t..u, Real.exp (-g * (u - r)) * X r) (Icc t s) :=
    (primitive_continuousOn hts hXs).sub (kernel_continuousOn hts hXs)
  have hint : IntervalIntegrable
      (fun u => g * ∫ r in t..u, Real.exp (-g * (u - r)) * X r) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hts]
    exact continuousOn_const.mul (kernel_continuousOn hts hXs)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hts hcont hderiv hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [intervalIntegral.integral_same, sub_self, sub_zero] at hFTC
  linarith

end UnforcedLeray.Short.PartIIIb.BlockGronwallAux
