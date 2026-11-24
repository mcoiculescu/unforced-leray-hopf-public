import UnforcedLeray.Short.PartIIb.Sub.T12_1_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.SmoothPrimEta

/-!
# Part II-b, leaf `PartII-b:T12/1/5/6` (`CylFluxConst`): constant flux of a cylinder solenoidal test

Source of record: `the November 2 reference manuscript` lines 1727-1731 (the radial
component of the zero frequency is solenoidal, so its flux is constant). The target is
`CylFluxConst` of `Sub/T12_1_5.lean`.

Proof. Choose `M > 0` with `M > L0`, `M > L1` (support radii of `Ψ₀`, `Ψ₁`). Put
`P(q, η) = ∫_{-M}^{η} Ψ₀(q, s) ds` (`smoothPrimEta`). Then `T(q) = P(q, M)` has derivative
`∫_{-M}^{M} ∂_qΨ₀(q, s) ds`. By `div_free` the integrand is `-∂_ηΨ₁(q, s)`, and the fundamental
theorem of calculus with `Ψ₁(q, ±M) = 0` makes the derivative vanish. So `T` is constant
(`is_const_of_deriv_eq_zero`), and `∫ Ψ₀(q, ·) = T(q)` because `Ψ₀(q, ·)` vanishes outside `(-M, M]`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- **Leaf `PartII-b:T12/1/5/6`** (constant flux): for a cylinder solenoidal test `Ψ`, the flux
`∫ Ψ₀(q, s) ds` does not depend on `q`. -/
theorem cylFluxConst : CylFluxConst := by
  unfold CylFluxConst
  intro c Ψ hΨ q
  have h0 := hΨ.comp 0
  have h1 := hΨ.comp 1
  obtain ⟨L0, hL0⟩ := h0.bounded
  obtain ⟨L1, hL1⟩ := h1.bounded
  obtain ⟨M, hM0, hML0, hML1⟩ : ∃ M : ℝ, 0 < M ∧ L0 < M ∧ L1 < M :=
    ⟨|L0| + |L1| + 1, by positivity, by linarith [le_abs_self L0, abs_nonneg L1],
      by linarith [le_abs_self L1, abs_nonneg L0]⟩
  have hg : ContDiff ℝ ∞ (fun y : ℝ × ℝ => Ψ y 0) := h0.smooth
  have hh1 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => Ψ y 1) := h1.smooth
  have hvan : ∀ z : ℝ × ℝ, M < |z.2| → (fun y : ℝ × ℝ => Ψ y 0) z = 0 :=
    fun z hz => hL0 z (lt_trans hML0 hz)
  obtain ⟨hsmooth, _, hP3⟩ := smoothPrimEta (fun y : ℝ × ℝ => Ψ y 0) M hg hvan
  have hPd : Differentiable ℝ (fun y : ℝ × ℝ => ∫ s in (-M)..y.2, Ψ (y.1, s) 0) :=
    hsmooth.differentiable (by simp)
  -- derivative of the flux function `q ↦ ∫_{-M}^{M} Ψ₀(q, s) ds`
  have hGd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ∫ s in (-M)..M, Ψ (x, s) 0)
      (∫ s in (-M)..M, fderiv ℝ (fun y : ℝ × ℝ => Ψ y 0) (x, s) (1, 0)) x := by
    intro x
    have hc : HasDerivAt (fun t : ℝ => ((t, M) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x M)
    have hA := (hPd (x, M)).hasFDerivAt.comp_hasDerivAt x hc
    have h2 : fderiv ℝ (fun y : ℝ × ℝ => ∫ s in (-M)..y.2, Ψ (y.1, s) 0) (x, M) (1, 0)
        = ∫ s in (-M)..M, fderiv ℝ (fun y : ℝ × ℝ => Ψ y 0) (x, s) (1, 0) := hP3 (x, M)
    rw [h2] at hA
    exact hA
  -- the integral of the `q`-derivative vanishes
  have hzero : ∀ x : ℝ, ∫ s in (-M)..M, fderiv ℝ (fun y : ℝ × ℝ => Ψ y 0) (x, s) (1, 0) = 0 := by
    intro x
    have hk : ∀ s : ℝ, fderiv ℝ (fun y : ℝ × ℝ => Ψ y 0) (x, s) (1, 0)
        = -(fderiv ℝ (fun y : ℝ × ℝ => Ψ y 1) (x, s) (0, 1)) := by
      intro s
      have := hΨ.div_free (x, s)
      linarith
    have hint : ∫ s in (-M)..M, fderiv ℝ (fun y : ℝ × ℝ => Ψ y 0) (x, s) (1, 0)
        = -∫ s in (-M)..M, fderiv ℝ (fun y : ℝ × ℝ => Ψ y 1) (x, s) (0, 1) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr (fun s _ => hk s)
    have hcont : Continuous (fun s : ℝ => fderiv ℝ (fun y : ℝ × ℝ => Ψ y 1) (x, s) (0, 1)) := by
      have hfd : Continuous (fderiv ℝ (fun y : ℝ × ℝ => Ψ y 1)) :=
        hh1.continuous_fderiv (by simp)
      exact (hfd.comp (by fun_prop : Continuous fun s : ℝ => ((x, s) : ℝ × ℝ))).clm_apply
        continuous_const
    have hftc : ∫ s in (-M)..M, fderiv ℝ (fun y : ℝ × ℝ => Ψ y 1) (x, s) (0, 1)
        = Ψ (x, M) 1 - Ψ (x, -M) 1 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s : ℝ => Ψ (x, s) 1)
        (fun s _ => ?_) (hcont.intervalIntegrable _ _)
      have hc' : HasDerivAt (fun t : ℝ => ((x, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) s :=
        (hasDerivAt_const s x).prodMk (hasDerivAt_id s)
      exact (hh1.differentiable (by simp) (x, s)).hasFDerivAt.comp_hasDerivAt s hc'
    have hb1 : Ψ (x, M) 1 = 0 :=
      hL1 (x, M) (by show L1 < |M|; rw [abs_of_pos hM0]; exact hML1)
    have hbm1 : Ψ (x, -M) 1 = 0 :=
      hL1 (x, -M) (by show L1 < |-M|; rw [abs_neg, abs_of_pos hM0]; exact hML1)
    rw [hint, hftc, hb1, hbm1]
    simp
  have hconst : ∀ x : ℝ, deriv (fun x : ℝ => ∫ s in (-M)..M, Ψ (x, s) 0) x = 0 := by
    intro x
    rw [(hGd x).deriv, hzero x]
  have hdiff : Differentiable ℝ (fun x : ℝ => ∫ s in (-M)..M, Ψ (x, s) 0) :=
    fun x => (hGd x).differentiableAt
  have hcst := is_const_of_deriv_eq_zero hdiff hconst
  -- the flux over `ℝ` equals the flux over `(-M, M]`
  have hsupp : ∀ p : ℝ, ∫ s, Ψ (p, s) 0 = ∫ s in (-M)..M, Ψ (p, s) 0 := by
    intro p
    rw [intervalIntegral.integral_of_le (show -M ≤ M by linarith)]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have hs' : L0 < |s| := by
      by_cases hsM : -M < s
      · have hsM2 : M < s := by
          by_contra hc
          exact hs (Set.mem_Ioc.mpr ⟨hsM, not_lt.mp hc⟩)
        rw [abs_of_pos (by linarith)]
        linarith
      · have hsM3 : s ≤ -M := not_lt.mp hsM
        rw [abs_of_nonpos (by linarith)]
        linarith
    exact hL0 (p, s) hs'
  rw [hsupp q, hsupp 0]
  exact hcst q 0

end UnforcedLeray.Short.IIb
