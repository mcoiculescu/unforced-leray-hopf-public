import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3_2_2

/-!
# `PhaseTestSplit` (task `PartIII-b:C/near/pins/3/2/2/2`)

Source `the November 2 reference manuscript` 4139-4146 (test transport, `x = ε y`).

For a complex phase test `φ` and a continuous real-linear functional `ℓ : ℂ → ℝ` (`re` or `im`),
the function `(x, τ) ↦ ℓ (φ (τ, ε⁻¹ x))` is a real physical test of period `2εc`.  Its spatial
gradient is `ε⁻¹ ℓ(∂_i φ(τ, ε⁻¹ x))` (chain rule with the linear map `(x, τ) ↦ (τ, ε⁻¹ x)`),
which gives `∂_i φ (τ, ε⁻¹ x) = ε (∇ₓφ₁ + i ∇ₓφ₂)_i`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Chain rule for `x`-gradients of `z ↦ ℓ (φ (z.2, ε⁻¹ • z.1))`. -/
theorem gradX_scale_comp (φ : ℝ × Space → ℂ) (hφ : Differentiable ℝ φ) (ε : ℝ) (hε : 0 < ε)
    (ℓ : ℂ →L[ℝ] ℝ) (i : Fin 3) (y : Space × ℝ) :
    UnforcedLeray.B0226.gradX (fun z : Space × ℝ => ℓ (φ (z.2, ε⁻¹ • z.1))) y i =
      ε⁻¹ * ℓ (dy i φ (y.2, ε⁻¹ • y.1)) := by
  set L : Space × ℝ →L[ℝ] ℝ × Space :=
    (ContinuousLinearMap.snd ℝ Space ℝ).prod (ε⁻¹ • ContinuousLinearMap.fst ℝ Space ℝ) with hLdef
  have hLd : HasFDerivAt (fun z : Space × ℝ => (z.2, ε⁻¹ • z.1)) L y := L.hasFDerivAt
  have hφd : HasFDerivAt φ (fderiv ℝ φ (y.2, ε⁻¹ • y.1)) (y.2, ε⁻¹ • y.1) :=
    (hφ _).hasFDerivAt
  have hcomp : HasFDerivAt (fun z : Space × ℝ => ℓ (φ (z.2, ε⁻¹ • z.1)))
      (ℓ.comp ((fderiv ℝ φ (y.2, ε⁻¹ • y.1)).comp L)) y :=
    ℓ.hasFDerivAt.comp y (hφd.comp y hLd)
  have hcoord : (UnforcedLeray.B0226.gradX (fun z : Space × ℝ => ℓ (φ (z.2, ε⁻¹ • z.1))) y) i
      = ⟪EuclideanSpace.single i (1 : ℝ),
          UnforcedLeray.B0226.gradX (fun z : Space × ℝ => ℓ (φ (z.2, ε⁻¹ • z.1))) y⟫_ℝ := by
    simp [PiLp.inner_apply]
  rw [hcoord, real_inner_comm, UnforcedLeray.B0226.inner_gradX, hcomp.fderiv]
  have hL0 : L (EuclideanSpace.single i (1 : ℝ), (0 : ℝ)) =
      ((0 : ℝ), ε⁻¹ • EuclideanSpace.single i (1 : ℝ)) := by
    simp [L]
  have hsm : ((0 : ℝ), ε⁻¹ • EuclideanSpace.single i (1 : ℝ)) =
      ε⁻¹ • ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
    simp
  have hdy : dy i φ (y.2, ε⁻¹ • y.1) =
      fderiv ℝ φ (y.2, ε⁻¹ • y.1) (0, EuclideanSpace.single i (1 : ℝ)) := rfl
  simp only [ContinuousLinearMap.comp_apply]
  rw [hL0, hsm, map_smul, map_smul, hdy, smul_eq_mul]

/-- **Test transport** (dilation `x = ε y`; source 4139-4146). -/
theorem phaseTestSplit : PhaseTestSplit := by
  intro p φ hφ
  have hε : 0 < p.ε := p.ε_pos
  have hdiff : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hL : ContDiff ℝ ∞ (fun z : Space × ℝ => (z.2, p.ε⁻¹ • z.1)) :=
    contDiff_snd.prodMk (contDiff_fst.const_smul _)
  obtain ⟨R0, hR0⟩ := hφ.bounded_support
  have mk : ∀ ℓ : ℂ →L[ℝ] ℝ,
      UnforcedLeray.B0226.IsPhysTest (2 * p.ε * p.c) (fun z : Space × ℝ => ℓ (φ (z.2, p.ε⁻¹ • z.1))) := by
    intro ℓ
    refine ⟨?_, ?_, ?_⟩
    · exact ℓ.contDiff.comp (hφ.smooth.comp hL)
    · intro x τ
      show ℓ (φ (τ + 2 * p.ε * p.c, p.ε⁻¹ • x)) = ℓ (φ (τ, p.ε⁻¹ • x))
      rw [hφ.periodic]
    · refine ⟨p.ε * R0, fun z hz => ?_⟩
      by_contra hlt
      push Not at hlt
      apply hz
      show ℓ (φ (z.2, p.ε⁻¹ • z.1)) = 0
      have h1 : R0 < ‖p.ε⁻¹ • z.1‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]
        have := mul_lt_mul_of_pos_left hlt (inv_pos.2 hε)
        rwa [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] at this
      rw [hR0 z.2 _ h1, map_zero]
  have hg : ∀ (q : ℝ × Space) (j : Fin 3), gradT φ q j = dy j φ q := by
    intro q j
    simp [gradT, dy, Pi.single_apply, Finset.sum_apply]
  refine ⟨⟨fun z : Space × ℝ => Complex.reCLM (φ (z.2, p.ε⁻¹ • z.1)), mk Complex.reCLM⟩,
    ⟨fun z : Space × ℝ => Complex.imCLM (φ (z.2, p.ε⁻¹ • z.1)), mk Complex.imCLM⟩,
    fun y i => ?_⟩
  rw [hg]
  show dy i φ (y.2, p.ε⁻¹ • y.1) = (p.ε : ℂ) * ((((UnforcedLeray.B0226.gradX
      (fun z : Space × ℝ => Complex.reCLM (φ (z.2, p.ε⁻¹ • z.1))) y) i : ℝ) : ℂ) +
      Complex.I * (((UnforcedLeray.B0226.gradX
      (fun z : Space × ℝ => Complex.imCLM (φ (z.2, p.ε⁻¹ • z.1))) y) i : ℝ) : ℂ))
  rw [gradX_scale_comp φ hdiff p.ε hε Complex.reCLM i y,
    gradX_scale_comp φ hdiff p.ε hε Complex.imCLM i y]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply]
  push_cast
  conv_lhs => rw [← Complex.re_add_im (dy i φ (y.2, p.ε⁻¹ • y.1))]
  have hε' : (p.ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  field_simp

end UnforcedLeray.Short.PartIIIb.NearInst
