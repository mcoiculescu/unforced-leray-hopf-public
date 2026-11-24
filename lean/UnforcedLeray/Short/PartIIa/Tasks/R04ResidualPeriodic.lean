import UnforcedLeray.Short.PartIIa.StatementsRing

/-!


Target: `ringResidual_periodic` (`Short/PartII-a/Tasks/R04ResidualPeriodic.lean`).

Source: `the November 2 reference manuscript`, lines 1215-1217 (period `2c/R`
of `U_R`) and 1316-1318 (period of `F_R`).

Route. The target carries no smoothness hypothesis, so the chart identity `ringResidual_eq_chart`
of R03 (which needs `ContDiffAt` of `ψ`, `p` at the chart point) does not apply. We argue
directly from the discrete self-similarity of the lift. Put `λ = e^{c/R}`. The dilation
`(r, z, t) ↦ (λr, λz, λ²t)` multiplies `u_r`, `u_z` by `λ⁻¹` and `p_raw` by `λ⁻²`
(`B0190.liftUr_dss`, `liftUz_dss`, `rawPressure_dss`). Each physical derivative adds one factor
`λ⁻¹` (chain rule for a dilation), so every term of the cylindrical residual scales by `λ⁻³`.
The similarity shift `τ ↦ τ + 2c/R` sends `t ↦ λ²t` and `y ↦ λ e^{τ/2} y`, and the factors
`e^{3τ/2}` and `λ³` cancel.

The derivative lemmas below make no differentiability assumption. Mathlib's `deriv` is `0` at
non-differentiable points, and `deriv_comp_mul_left` and `deriv_const_mul_field` hold without
hypotheses, so the scaling identities hold on the axis and off it alike.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-! ### Scaling of the physical derivatives under the dilation `(r, z, t) ↦ (λr, λz, λ²t)` -/

/-- The radial derivative of a function of degree `a` under the dilation carries one more
power: `∂_r F(λr, λz, λ²t) = λ^{-(a+1)} ∂_r F(r, z, t)`. -/
theorem r04_physR_dil {l : ℝ} (hl : 0 < l) (a : ℕ) (F : ℝ → ℝ → ℝ → ℝ)
    (hF : ∀ r z s : ℝ, 0 < s → F (l * r) (l * z) (l ^ 2 * s) = (l ^ a)⁻¹ * F r z s)
    (r z s : ℝ) (hs : 0 < s) :
    UnforcedLeray.B0187.physR F (l * r) (l * z) (l ^ 2 * s) =
      (l ^ (a + 1))⁻¹ * UnforcedLeray.B0187.physR F r z s := by
  have hfun : (fun w => F w (l * z) (l ^ 2 * s)) = fun w => (l ^ a)⁻¹ * F (l⁻¹ * w) z s := by
    funext w
    have h := hF (l⁻¹ * w) z s hs
    rwa [mul_inv_cancel_left₀ hl.ne'] at h
  have hd : deriv (fun w => F (l⁻¹ * w) z s) (l * r) = l⁻¹ * deriv (fun v => F v z s) r := by
    have h := deriv_comp_mul_left (l⁻¹) (fun v => F v z s) (l * r)
    simp only [smul_eq_mul, inv_mul_cancel_left₀ hl.ne'] at h
    exact h
  unfold UnforcedLeray.B0187.physR
  rw [hfun, deriv_const_mul_field, hd, pow_succ, mul_inv]
  ring

/-- The axial derivative of a function of degree `a` under the dilation carries one more power. -/
theorem r04_physZ_dil {l : ℝ} (hl : 0 < l) (a : ℕ) (F : ℝ → ℝ → ℝ → ℝ)
    (hF : ∀ r z s : ℝ, 0 < s → F (l * r) (l * z) (l ^ 2 * s) = (l ^ a)⁻¹ * F r z s)
    (r z s : ℝ) (hs : 0 < s) :
    UnforcedLeray.B0187.physZ F (l * r) (l * z) (l ^ 2 * s) =
      (l ^ (a + 1))⁻¹ * UnforcedLeray.B0187.physZ F r z s := by
  have hfun : (fun y => F (l * r) y (l ^ 2 * s)) = fun y => (l ^ a)⁻¹ * F r (l⁻¹ * y) s := by
    funext y
    have h := hF r (l⁻¹ * y) s hs
    rwa [mul_inv_cancel_left₀ hl.ne'] at h
  have hd : deriv (fun y => F r (l⁻¹ * y) s) (l * z) = l⁻¹ * deriv (fun v => F r v s) z := by
    have h := deriv_comp_mul_left (l⁻¹) (fun v => F r v s) (l * z)
    simp only [smul_eq_mul, inv_mul_cancel_left₀ hl.ne'] at h
    exact h
  unfold UnforcedLeray.B0187.physZ
  rw [hfun, deriv_const_mul_field, hd, pow_succ, mul_inv]
  ring

/-- The time derivative of a function of degree `a` under the dilation carries two more powers
(`t ↦ λ²t`). The identity hypothesis is used only for `s > 0`, which is an open condition, so an
eventual equality of the time profiles suffices. -/
theorem r04_physT_dil {l : ℝ} (hl : 0 < l) (a : ℕ) (F : ℝ → ℝ → ℝ → ℝ)
    (hF : ∀ r z s : ℝ, 0 < s → F (l * r) (l * z) (l ^ 2 * s) = (l ^ a)⁻¹ * F r z s)
    (r z s : ℝ) (hs : 0 < s) :
    UnforcedLeray.B0187.physT F (l * r) (l * z) (l ^ 2 * s) =
      (l ^ (a + 2))⁻¹ * UnforcedLeray.B0187.physT F r z s := by
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.ne'
  have hev : (fun μ => F (l * r) (l * z) μ) =ᶠ[𝓝 (l ^ 2 * s)]
      (fun μ => (l ^ a)⁻¹ * F r z ((l ^ 2)⁻¹ * μ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (mul_pos (pow_pos hl 2) hs))]
      with μ hμ
    have h := hF r z ((l ^ 2)⁻¹ * μ) (mul_pos (inv_pos.mpr (pow_pos hl 2)) (Set.mem_Ioi.mp hμ))
    rwa [mul_inv_cancel_left₀ hl2] at h
  have hd : deriv (fun μ => F r z ((l ^ 2)⁻¹ * μ)) (l ^ 2 * s) =
      (l ^ 2)⁻¹ * deriv (fun v => F r z v) s := by
    have h := deriv_comp_mul_left ((l ^ 2)⁻¹) (fun v => F r z v) (l ^ 2 * s)
    simp only [smul_eq_mul, inv_mul_cancel_left₀ hl2] at h
    exact h
  unfold UnforcedLeray.B0187.physT
  rw [hev.deriv_eq, deriv_const_mul_field, hd, pow_add]
  ring

/-! ### The cylindrical residual scales like `λ⁻³` -/

/-- **Dilation of the cylindrical residual.** If the radial velocity `u_r`, axial velocity `u_z`
and pressure `p` have degrees `1`, `1`, `2` under `(r, z, t) ↦ (λr, λz, λ²t)`, then both
components of the cylindrical Navier-Stokes residual have degree `3`. -/
theorem r04_cyl_dil (ν : ℝ) {l : ℝ} (hl : 0 < l) (ur uz pr : ℝ → ℝ → ℝ → ℝ)
    (hur : ∀ r z s : ℝ, 0 < s → ur (l * r) (l * z) (l ^ 2 * s) = (l ^ 1)⁻¹ * ur r z s)
    (huz : ∀ r z s : ℝ, 0 < s → uz (l * r) (l * z) (l ^ 2 * s) = (l ^ 1)⁻¹ * uz r z s)
    (hpr : ∀ r z s : ℝ, 0 < s → pr (l * r) (l * z) (l ^ 2 * s) = (l ^ 2)⁻¹ * pr r z s)
    (r z s : ℝ) (hs : 0 < s) :
    UnforcedLeray.B0187.cylRadialResidual ν ur uz pr (l * r) (l * z) (l ^ 2 * s) =
        (l ^ 3)⁻¹ * UnforcedLeray.B0187.cylRadialResidual ν ur uz pr r z s ∧
      UnforcedLeray.B0187.cylAxialResidual ν ur uz pr (l * r) (l * z) (l ^ 2 * s) =
        (l ^ 3)⁻¹ * UnforcedLeray.B0187.cylAxialResidual ν ur uz pr r z s := by
  -- degrees of the first and second derivatives of the components
  have hR_ur : UnforcedLeray.B0187.physR ur (l * r) (l * z) (l ^ 2 * s) =
      (l ^ 2)⁻¹ * UnforcedLeray.B0187.physR ur r z s :=
    r04_physR_dil hl 1 ur hur r z s hs
  have hZ_ur : UnforcedLeray.B0187.physZ ur (l * r) (l * z) (l ^ 2 * s) =
      (l ^ 2)⁻¹ * UnforcedLeray.B0187.physZ ur r z s :=
    r04_physZ_dil hl 1 ur hur r z s hs
  have hR_uz : UnforcedLeray.B0187.physR uz (l * r) (l * z) (l ^ 2 * s) =
      (l ^ 2)⁻¹ * UnforcedLeray.B0187.physR uz r z s :=
    r04_physR_dil hl 1 uz huz r z s hs
  have hZ_uz : UnforcedLeray.B0187.physZ uz (l * r) (l * z) (l ^ 2 * s) =
      (l ^ 2)⁻¹ * UnforcedLeray.B0187.physZ uz r z s :=
    r04_physZ_dil hl 1 uz huz r z s hs
  have hR_pr : UnforcedLeray.B0187.physR pr (l * r) (l * z) (l ^ 2 * s) =
      (l ^ 3)⁻¹ * UnforcedLeray.B0187.physR pr r z s :=
    r04_physR_dil hl 2 pr hpr r z s hs
  have hZ_pr : UnforcedLeray.B0187.physZ pr (l * r) (l * z) (l ^ 2 * s) =
      (l ^ 3)⁻¹ * UnforcedLeray.B0187.physZ pr r z s :=
    r04_physZ_dil hl 2 pr hpr r z s hs
  have hT_ur : UnforcedLeray.B0187.physT ur (l * r) (l * z) (l ^ 2 * s) =
      (l ^ 3)⁻¹ * UnforcedLeray.B0187.physT ur r z s :=
    r04_physT_dil hl 1 ur hur r z s hs
  have hT_uz : UnforcedLeray.B0187.physT uz (l * r) (l * z) (l ^ 2 * s) =
      (l ^ 3)⁻¹ * UnforcedLeray.B0187.physT uz r z s :=
    r04_physT_dil hl 1 uz huz r z s hs
  have hRR_ur : UnforcedLeray.B0187.physR (UnforcedLeray.B0187.physR ur) (l * r) (l * z)
        (l ^ 2 * s) =
      (l ^ 3)⁻¹ * UnforcedLeray.B0187.physR (UnforcedLeray.B0187.physR ur) r z s :=
    r04_physR_dil hl 2 (UnforcedLeray.B0187.physR ur)
      (fun r' z' s' hs' => r04_physR_dil hl 1 ur hur r' z' s' hs') r z s hs
  have hZZ_ur : UnforcedLeray.B0187.physZ (UnforcedLeray.B0187.physZ ur) (l * r) (l * z)
        (l ^ 2 * s) =
      (l ^ 3)⁻¹ * UnforcedLeray.B0187.physZ (UnforcedLeray.B0187.physZ ur) r z s :=
    r04_physZ_dil hl 2 (UnforcedLeray.B0187.physZ ur)
      (fun r' z' s' hs' => r04_physZ_dil hl 1 ur hur r' z' s' hs') r z s hs
  have hRR_uz : UnforcedLeray.B0187.physR (UnforcedLeray.B0187.physR uz) (l * r) (l * z)
        (l ^ 2 * s) =
      (l ^ 3)⁻¹ * UnforcedLeray.B0187.physR (UnforcedLeray.B0187.physR uz) r z s :=
    r04_physR_dil hl 2 (UnforcedLeray.B0187.physR uz)
      (fun r' z' s' hs' => r04_physR_dil hl 1 uz huz r' z' s' hs') r z s hs
  have hZZ_uz : UnforcedLeray.B0187.physZ (UnforcedLeray.B0187.physZ uz) (l * r) (l * z)
        (l ^ 2 * s) =
      (l ^ 3)⁻¹ * UnforcedLeray.B0187.physZ (UnforcedLeray.B0187.physZ uz) r z s :=
    r04_physZ_dil hl 2 (UnforcedLeray.B0187.physZ uz)
      (fun r' z' s' hs' => r04_physZ_dil hl 1 uz huz r' z' s' hs') r z s hs
  have hu := hur r z s hs
  have hw := huz r z s hs
  constructor
  · unfold UnforcedLeray.B0187.cylRadialResidual UnforcedLeray.B0187.radialVectorLaplacian
    simp only [hT_ur, hu, hR_ur, hw, hZ_ur, hRR_ur, hZZ_ur, hR_pr]
    ring
  · unfold UnforcedLeray.B0187.cylAxialResidual UnforcedLeray.B0187.axialVectorLaplacian
    simp only [hT_uz, hu, hR_uz, hw, hZ_uz, hRR_uz, hZZ_uz, hZ_pr]
    ring

/-! ### The vector residual and the unit radial vector -/

/-- The radial unit vector is invariant under positive dilations: `e_r(λy) = e_r(y)`. -/
theorem r04_eR_dil {l : ℝ} (hl : 0 < l) (y : Space) : Axi.eR (l • y) = Axi.eR y := by
  have hhor : Axi.hor (l • y) = l • Axi.hor y := by
    rw [Axi.hor_eq, Axi.hor_eq, UnforcedLeray.B0190.apply_two_dilate, smul_sub, smul_smul]
  unfold Axi.eR
  rw [UnforcedLeray.B0190.ϱ_dilate hl y, hhor, smul_smul]
  by_cases hy : Axi.ϱ y = 0
  · simp [hy]
  · have hy' : Axi.ϱ y ≠ 0 := hy
    have hl' : l ≠ 0 := hl.ne'
    congr 1
    field_simp

/-- **Dilation of the physical residual field.** For `λ > 0` and the DSS lift of a periodic
stream and pressure, the vector residual at `(λ²t, λx)` is `λ^{-3}` times the residual at
`(t, x)`. -/
theorem r04_phys_dil (R ν : ℝ) (ψ p : ProfilePoint → ℝ) {l : ℝ} (hl : 0 < l)
    (hur : ∀ r z s : ℝ, 0 < s →
      liftUr R ψ (l * r) (l * z) (l ^ 2 * s) = (l ^ 1)⁻¹ * liftUr R ψ r z s)
    (huz : ∀ r z s : ℝ, 0 < s →
      liftUz R ψ (l * r) (l * z) (l ^ 2 * s) = (l ^ 1)⁻¹ * liftUz R ψ r z s)
    (hpr : ∀ r z s : ℝ, 0 < s →
      rawPressure R p (l * r) (l * z) (l ^ 2 * s) = (l ^ 2)⁻¹ * rawPressure R p r z s)
    (t : ℝ) (x : Space) (ht : 0 < t) :
    physResidualField R ν ψ p (l ^ 2 * t) (l • x) =
      (l ^ 3)⁻¹ • physResidualField R ν ψ p t x := by
  obtain ⟨hC1, hC2⟩ := r04_cyl_dil ν hl (liftUr R ψ) (liftUz R ψ) (rawPressure R p) hur huz hpr
    (Axi.ϱ x) (x 2) t ht
  unfold physResidualField
  rw [UnforcedLeray.B0190.ϱ_dilate hl x, UnforcedLeray.B0190.apply_two_dilate l x,
    r04_eR_dil hl x, hC1, hC2, smul_add, smul_smul, smul_smul]

/-! ### The target: `2c/R`-periodicity of the similarity residual -/

/-- **Task `PartII-a:R04`.** The similarity residual `F_R(τ, y)` of the exact periodic train is
periodic in `τ` with period `2c/R`, for every `y`. -/
theorem ringResidual_periodic (R nu c : Real) (hR : 2 <= R) (psi p : ProfilePoint -> Real)
    (hpsi : QPeriodicOn c psi) (hp : QPeriodicOn c p) (tau : Real) :
    ringResidual R nu psi p (tau + 2*c/R) = ringResidual R nu psi p tau := by
  have hR0 : R ≠ 0 := by
    have hpos : (0 : ℝ) < R := by linarith
    exact hpos.ne'
  have hl : 0 < Real.exp (c / R) := Real.exp_pos _
  have hl0 : Real.exp (c / R) ≠ 0 := hl.ne'
  have hur : ∀ r z s : ℝ, 0 < s →
      liftUr R psi (Real.exp (c / R) * r) (Real.exp (c / R) * z) (Real.exp (c / R) ^ 2 * s) =
        (Real.exp (c / R) ^ 1)⁻¹ * liftUr R psi r z s := by
    intro r z s hs
    rw [pow_one]
    exact liftUr_dss hR0 hpsi r z hs
  have huz : ∀ r z s : ℝ, 0 < s →
      liftUz R psi (Real.exp (c / R) * r) (Real.exp (c / R) * z) (Real.exp (c / R) ^ 2 * s) =
        (Real.exp (c / R) ^ 1)⁻¹ * liftUz R psi r z s := by
    intro r z s hs
    rw [pow_one]
    exact liftUz_dss hR0 hpsi r z hs
  have hpr : ∀ r z s : ℝ, 0 < s →
      rawPressure R p (Real.exp (c / R) * r) (Real.exp (c / R) * z)
          (Real.exp (c / R) ^ 2 * s) =
        (Real.exp (c / R) ^ 2)⁻¹ * rawPressure R p r z s :=
    fun r z s hs => rawPressure_dss hR0 hp r z hs
  funext y
  unfold ringResidual
  have h1 : Real.exp (tau + 2 * c / R) = Real.exp (c / R) ^ 2 * Real.exp tau := by
    rw [show tau + 2 * c / R = tau + (c / R + c / R) by ring, Real.exp_add, Real.exp_add]
    ring
  have h2 : Real.exp ((tau + 2 * c / R) / 2) = Real.exp (c / R) * Real.exp (tau / 2) := by
    rw [show (tau + 2 * c / R) / 2 = c / R + tau / 2 by ring, Real.exp_add]
  have hkey := r04_phys_dil R nu psi p hl hur huz hpr (Real.exp tau)
    (Real.exp (tau / 2) • y) (Real.exp_pos tau)
  have hfac : (Real.exp (c / R) * Real.exp (tau / 2)) ^ 3 * (Real.exp (c / R) ^ 3)⁻¹ =
      Real.exp (tau / 2) ^ 3 := by
    rw [mul_pow, mul_comm (Real.exp (c / R) ^ 3) (Real.exp (tau / 2) ^ 3), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 3 hl0), mul_one]
  rw [h1, h2, mul_smul, hkey, smul_smul, hfac]

end UnforcedLeray.Short.PartIIa
