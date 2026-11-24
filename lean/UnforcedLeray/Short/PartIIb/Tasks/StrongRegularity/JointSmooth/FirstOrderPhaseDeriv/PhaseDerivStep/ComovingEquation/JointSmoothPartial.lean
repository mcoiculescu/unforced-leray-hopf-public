import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_comoving

/-!
# `PartII-b:S3/1/1/2/1/3` (`JointSmoothComovingPartial`, SP 2559-2562)

A jointly smooth phase field `F` has the classical comoving derivative
`comovingPartial F = ∂_τ F - ½ (y·∇) F` on every spatial jet: chain rule along the comoving ray
`t ↦ (τ + t, e^{-t/2} y)`, Schwarz commutation (`phasePartial_dirSpatialJet`), and the all-order
radial-drift commutator (`dirSpatialJet_spatialRadialDrift`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

open UnforcedLeray UnforcedLeray.Short.IIb

theorem jointSmoothComovingPartial_proof : UnforcedLeray.Short.IIb.JointSmoothComovingPartial := by
  intro F hF ws τ y
  have hF' : ContDiff ℝ ∞ (PhaseDerivStepSub.uncurriedField F) := hF
  have hG : ContDiff ℝ ∞
      (PhaseDerivStepSub.uncurriedField (fun τ' => dirSpatialJet (F τ') ws)) :=
    PhaseDerivStepSub.contDiff_joint_dirSpatialJet hF' ws
  have hslice : ∀ τ' : ℝ, ContDiff ℝ ∞ (F τ') :=
    fun τ' => PhaseDerivStepSub.contDiff_slice_of_joint hF' τ'
  set G := PhaseDerivStepSub.uncurriedField (fun τ' => dirSpatialJet (F τ') ws) with hGdef
  have hGd : HasFDerivAt G (fderiv ℝ G (τ, y)) (τ, y) :=
    (hG.differentiable (by simp) (τ, y)).hasFDerivAt
  -- the comoving ray
  have hc : HasDerivAt (fun t : ℝ => ((τ + t, Real.exp (-t / 2) • y) : ℝ × Space))
      ((1 : ℝ), (-(1 / 2 : ℝ)) • y) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using (hasDerivAt_id (0 : ℝ)).const_add τ
    · have h1 : HasDerivAt (fun t : ℝ => -t / 2) (-(1 / 2 : ℝ)) 0 := by
        exact ((hasDerivAt_id (0 : ℝ)).neg.div_const 2).congr_deriv (by norm_num)
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2))
          (Real.exp (-(0 : ℝ) / 2) * (-(1 / 2 : ℝ))) 0 :=
        (Real.hasDerivAt_exp _).comp 0 h1
      simpa using h2.smul_const y
  have hGd0 : HasFDerivAt G (fderiv ℝ G (τ, y)) ((τ + 0, Real.exp (-(0 : ℝ) / 2) • y) : ℝ × Space) := by
    simpa using hGd
  have hcomp := hGd0.comp_hasDerivAt (0 : ℝ) hc
  -- splitting the derivative direction
  have hsplit : ((1 : ℝ), (-(1 / 2 : ℝ)) • y) =
      ((1 : ℝ), (0 : Space)) + (-(1 / 2 : ℝ)) • ((0 : ℝ), y) := by
    ext <;> simp
  have h1 : fderiv ℝ G (τ, y) ((1 : ℝ), (0 : Space)) =
      dirSpatialJet (PhaseDerivStepSub.phasePartial F τ) ws y := by
    rw [← PhaseDerivStepSub.phasePartial_dirSpatialJet hF' ws τ y]
    rfl
  have h2 : fderiv ℝ G (τ, y) ((0 : ℝ), y) =
      spatialRadialDrift (dirSpatialJet (F τ) ws) y :=
    (PhaseDerivStepSub.dirSpatialJet_singleton_eq_joint_fderiv hG y τ y).symm
  -- commutators on the spatial jet of the comoving partial
  have hPh : ContDiff ℝ ∞ (PhaseDerivStepSub.phasePartial F τ) :=
    PhaseDerivStepSub.contDiff_slice_phasePartial hF' τ
  have hR : ContDiff ℝ ∞ (spatialRadialDrift (F τ)) :=
    HigherPhaseSub.contDiff_infty_spatialRadialDrift (hslice τ)
  have hRs : ContDiff ℝ ∞ ((1 / 2 : ℝ) • spatialRadialDrift (F τ)) := by
    show ContDiff ℝ ∞ (fun y => (1 / 2 : ℝ) • spatialRadialDrift (F τ) y)
    exact hR.const_smul _
  have h3 : dirSpatialJet (comovingPartial F τ) ws =
      dirSpatialJet (PhaseDerivStepSub.phasePartial F τ) ws -
        (1 / 2 : ℝ) • dirSpatialJet (spatialRadialDrift (F τ)) ws := by
    show dirSpatialJet (PhaseDerivStepSub.phasePartial F τ - (1 / 2 : ℝ) • spatialRadialDrift (F τ)) ws
      = _
    rw [HigherPhaseSub.dirSpatialJet_sub hPh hRs ws,
      HigherPhaseSub.dirSpatialJet_smul _ hR ws]
  have h4 : dirSpatialJet (spatialRadialDrift (F τ)) ws =
      spatialRadialDrift (dirSpatialJet (F τ) ws) + (ws.length : ℝ) • dirSpatialJet (F τ) ws :=
    PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift (hslice τ) ws
  have h5 : dirSpatialJet (comovingPartial F τ) ws y =
      dirSpatialJet (PhaseDerivStepSub.phasePartial F τ) ws y -
        (1 / 2 : ℝ) • (spatialRadialDrift (dirSpatialJet (F τ) ws) y +
          (ws.length : ℝ) • dirSpatialJet (F τ) ws y) := by
    rw [h3, h4]
    simp [Pi.sub_apply, Pi.smul_apply, Pi.add_apply]
  -- assemble
  have hval : fderiv ℝ G (τ, y) ((1 : ℝ), (-(1 / 2 : ℝ)) • y) =
      dirSpatialJet (comovingPartial F τ) ws y +
        ((ws.length : ℝ) / 2) • dirSpatialJet (F τ) ws y := by
    rw [hsplit, map_add, map_smul, h1, h2, h5]
    module
  rw [hval] at hcomp
  exact hcomp
