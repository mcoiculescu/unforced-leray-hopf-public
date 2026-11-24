import UnforcedLeray.Short.PartI.Sub.C09

/-!
# Helper for `polarReduction`: the polar chain rule for the planar Laplacian

For a smooth `φ : ℝ × ℝ → ℂ` and `pol r θ = (r cos θ, r sin θ)`, the one-variable derivatives of
`(r, θ) ↦ φ (pol r θ)` satisfy, for `r ≠ 0`,

`∂_r² + r⁻¹ ∂_r + r⁻² ∂_θ² = Δφ (pol r θ)`  (`polar_laplacian`).

The Cartesian Laplacian is `iterDirDeriv [ev 0, ev 0] φ + iterDirDeriv [ev 1, ev 1] φ`
(`WeakLapOn`, `C09.lean`).  The proof uses the chain rule, the symmetry of second derivatives and
the invariance of the trace of a symmetric bilinear form under the rotation `(c, s) ↦ (-s, c)`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.PolarRed

open UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob

/-- The polar parametrization `(r, θ) ↦ (r cos θ, r sin θ)`. -/
def pol (r θ : ℝ) : ℝ × ℝ := (r * Real.cos θ, r * Real.sin θ)

theorem hasDerivAt_pol_r (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => pol s θ) (Real.cos θ, Real.sin θ) r := by
  have h1 : HasDerivAt (fun s : ℝ => s * Real.cos θ) (Real.cos θ) r := by
    simpa using (hasDerivAt_id r).mul_const (Real.cos θ)
  have h2 : HasDerivAt (fun s : ℝ => s * Real.sin θ) (Real.sin θ) r := by
    simpa using (hasDerivAt_id r).mul_const (Real.sin θ)
  exact h1.prodMk h2

theorem hasDerivAt_pol_θ (r θ : ℝ) :
    HasDerivAt (fun σ : ℝ => pol r σ) (-r * Real.sin θ, r * Real.cos θ) θ := by
  have h1 : HasDerivAt (fun σ : ℝ => r * Real.cos σ) (-r * Real.sin θ) θ := by
    simpa using (Real.hasDerivAt_cos θ).const_mul r
  have h2 : HasDerivAt (fun σ : ℝ => r * Real.sin σ) (r * Real.cos θ) θ := by
    simpa using (Real.hasDerivAt_sin θ).const_mul r
  exact h1.prodMk h2

/-- The derivative of `pol r ·` in `θ`, as a function of `θ`. -/
theorem hasDerivAt_w (r θ : ℝ) :
    HasDerivAt (fun τ : ℝ => (-r * Real.sin τ, r * Real.cos τ))
      (-r * Real.cos θ, -r * Real.sin θ) θ := by
  have h1 : HasDerivAt (fun τ : ℝ => -r * Real.sin τ) (-r * Real.cos θ) θ := by
    simpa using (Real.hasDerivAt_sin θ).const_mul (-r)
  have h2 : HasDerivAt (fun τ : ℝ => r * Real.cos τ) (-r * Real.sin θ) θ := by
    simpa using (Real.hasDerivAt_cos θ).const_mul r
  exact h1.prodMk h2

theorem fderiv_fderiv_symm {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (x v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ φ) x v w = fderiv ℝ (fderiv ℝ φ) x w v :=
  (hφ.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

theorem hasFDerivAt_fderiv {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (x : ℝ × ℝ) :
    HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x :=
  ((ContDiff.fderiv_right (m := ∞) hφ (by simp)).differentiable (by simp)).differentiableAt.hasFDerivAt

/-- Derivative along the polar radius of `s ↦ φ (pol s θ)`. -/
theorem hasDerivAt_phi_r {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (s θ : ℝ) :
    HasDerivAt (fun t : ℝ => φ (pol t θ)) (fderiv ℝ φ (pol s θ) (Real.cos θ, Real.sin θ)) s :=
  (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_pol_r s θ)

/-- Derivative along the polar angle of `σ ↦ φ (pol r σ)`. -/
theorem hasDerivAt_phi_θ {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (r θ : ℝ) :
    HasDerivAt (fun σ : ℝ => φ (pol r σ)) (fderiv ℝ φ (pol r θ) (-r * Real.sin θ, r * Real.cos θ)) θ :=
  (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_pol_θ r θ)

/-- Derivative in `s` of the directional derivative `s ↦ Dφ(pol s θ) u` for fixed `u`. -/
theorem hasDerivAt_fderiv_apply {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (r θ : ℝ) (u : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ φ (pol s θ) u)
      (fderiv ℝ (fderiv ℝ φ) (pol r θ) (Real.cos θ, Real.sin θ) u) r := by
  have h := (hasFDerivAt_fderiv hφ (pol r θ)).comp_hasDerivAt r (hasDerivAt_pol_r r θ)
  have h2 := h.clm_apply (hasDerivAt_const r u)
  simpa using h2

/-- Derivative in `θ` of `τ ↦ Dφ(pol r τ) (w τ)`. -/
theorem hasDerivAt_fderiv_w {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (r θ : ℝ) :
    HasDerivAt (fun τ : ℝ => fderiv ℝ φ (pol r τ) (-r * Real.sin τ, r * Real.cos τ))
      (fderiv ℝ (fderiv ℝ φ) (pol r θ) (-r * Real.sin θ, r * Real.cos θ)
          (-r * Real.sin θ, r * Real.cos θ) +
        fderiv ℝ φ (pol r θ) (-r * Real.cos θ, -r * Real.sin θ)) θ := by
  have h := (hasFDerivAt_fderiv hφ (pol r θ)).comp_hasDerivAt θ (hasDerivAt_pol_θ r θ)
  exact h.clm_apply (hasDerivAt_w r θ)

/-- The bilinear form `H` of a symmetric second derivative, expanded in the basis `ev 0, ev 1`. -/
theorem bilin_pair (H : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℂ) (hs : ∀ v w, H v w = H w v)
    (a b : ℝ) :
    H (a, b) (a, b) = (a : ℂ) ^ 2 * H (ev 0) (ev 0) +
      (2 * (a : ℂ) * (b : ℂ)) * H (ev 0) (ev 1) + (b : ℂ) ^ 2 * H (ev 1) (ev 1) := by
  have e : ((a, b) : ℝ × ℝ) = a • ev 0 + b • ev 1 := by
    ext <;> simp [ev, UnforcedLeray.B0094.e1, UnforcedLeray.B0094.e2]
  rw [e]
  simp only [map_add, map_smul, add_apply, smul_apply,
    Complex.real_smul, hs (ev 1) (ev 0)]
  ring

/-- `Dφ` applied to a constant vector, differentiated along `x`: `∂_v (∂_w φ) = ∂²φ (v, w)`. -/
theorem fderiv_apply_const {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (x w v : ℝ × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ φ y w) x v = fderiv ℝ (fderiv ℝ φ) x v w := by
  have h : HasFDerivAt (fun y => fderiv ℝ φ y w) ((fderiv ℝ (fderiv ℝ φ) x).flip w) x := by
    simpa using (hasFDerivAt_fderiv hφ x).clm_apply (hasFDerivAt_const w x)
  rw [h.fderiv, ContinuousLinearMap.flip_apply]

/-- Pointwise polar form of the planar Laplacian of a smooth function, for `r ≠ 0`. -/
theorem polar_laplacian {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    deriv (fun s => deriv (fun t => φ (pol t θ)) s) r +
        deriv (fun t => φ (pol t θ)) r / (r : ℂ) +
        deriv (fun τ => deriv (fun σ => φ (pol r σ)) τ) θ / (r : ℂ) ^ 2 =
      iterDirDeriv [ev 0, ev 0] φ (pol r θ) + iterDirDeriv [ev 1, ev 1] φ (pol r θ) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have hfun_r : (fun s' : ℝ => deriv (fun t => φ (pol t θ)) s') =
      fun s' => fderiv ℝ φ (pol s' θ) (Real.cos θ, Real.sin θ) := by
    funext s'
    exact (hasDerivAt_phi_r hφ s' θ).deriv
  have hd_rr : deriv (fun s' => deriv (fun t => φ (pol t θ)) s') r =
      fderiv ℝ (fderiv ℝ φ) (pol r θ) (Real.cos θ, Real.sin θ) (Real.cos θ, Real.sin θ) := by
    rw [hfun_r]
    exact (hasDerivAt_fderiv_apply hφ r θ _).deriv
  have hd_r : deriv (fun t => φ (pol t θ)) r = fderiv ℝ φ (pol r θ) (Real.cos θ, Real.sin θ) :=
    (hasDerivAt_phi_r hφ r θ).deriv
  have hfun_θ : (fun τ : ℝ => deriv (fun σ => φ (pol r σ)) τ) =
      fun τ => fderiv ℝ φ (pol r τ) (-r * Real.sin τ, r * Real.cos τ) := by
    funext τ
    exact (hasDerivAt_phi_θ hφ r τ).deriv
  have hd_θθ : deriv (fun τ => deriv (fun σ => φ (pol r σ)) τ) θ =
      fderiv ℝ (fderiv ℝ φ) (pol r θ) (-r * Real.sin θ, r * Real.cos θ)
          (-r * Real.sin θ, r * Real.cos θ) +
        fderiv ℝ φ (pol r θ) (-r * Real.cos θ, -r * Real.sin θ) := by
    rw [hfun_θ]
    exact (hasDerivAt_fderiv_w hφ r θ).deriv
  have hw' : fderiv ℝ φ (pol r θ) (-r * Real.cos θ, -r * Real.sin θ) =
      -(r : ℂ) * fderiv ℝ φ (pol r θ) (Real.cos θ, Real.sin θ) := by
    have e : ((-r * Real.cos θ, -r * Real.sin θ) : ℝ × ℝ) = (-r) • (Real.cos θ, Real.sin θ) := by
      ext <;> simp
    rw [e, map_smul, Complex.real_smul]
    push_cast
    ring
  have hR0 : iterDirDeriv [ev 0, ev 0] φ (pol r θ) =
      fderiv ℝ (fderiv ℝ φ) (pol r θ) (ev 0) (ev 0) :=
    fderiv_apply_const hφ _ _ _
  have hR1 : iterDirDeriv [ev 1, ev 1] φ (pol r θ) =
      fderiv ℝ (fderiv ℝ φ) (pol r θ) (ev 1) (ev 1) :=
    fderiv_apply_const hφ _ _ _
  rw [hd_rr, hd_r, hd_θθ, hw', hR0, hR1,
    bilin_pair (fderiv ℝ (fderiv ℝ φ) (pol r θ)) (fun v w => fderiv_fderiv_symm hφ (pol r θ) v w)
      (Real.cos θ) (Real.sin θ),
    bilin_pair (fderiv ℝ (fderiv ℝ φ) (pol r θ)) (fun v w => fderiv_fderiv_symm hφ (pol r θ) v w)
      (-r * Real.sin θ) (r * Real.cos θ)]
  generalize fderiv ℝ (fderiv ℝ φ) (pol r θ) (ev 0) (ev 0) = A
  generalize fderiv ℝ (fderiv ℝ φ) (pol r θ) (ev 0) (ev 1) = B
  generalize fderiv ℝ (fderiv ℝ φ) (pol r θ) (ev 1) (ev 1) = C
  generalize fderiv ℝ φ (pol r θ) (Real.cos θ, Real.sin θ) = X
  have hsum : (Real.cos θ : ℂ) ^ 2 * A + 2 * (Real.cos θ : ℂ) * (Real.sin θ : ℂ) * B +
      (Real.sin θ : ℂ) ^ 2 * C + X / (r : ℂ) +
      (((-r * Real.sin θ : ℝ) : ℂ) ^ 2 * A + 2 * ((-r * Real.sin θ : ℝ) : ℂ) *
        ((r * Real.cos θ : ℝ) : ℂ) * B + ((r * Real.cos θ : ℝ) : ℂ) ^ 2 * C + -(r : ℂ) * X) /
        (r : ℂ) ^ 2 =
      ((Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2) * (A + C) := by
    push_cast
    field_simp
    ring
  linear_combination hsum + (A + C) * hcs

end UnforcedLeray.Short.PartI.PolarRed
