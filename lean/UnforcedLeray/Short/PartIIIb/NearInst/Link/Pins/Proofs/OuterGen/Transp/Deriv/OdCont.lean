import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

/-!
# `OD_Cont` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/6`)

Strong continuity of `s ↦ outerTransp h s Ψ` on `[0, ∞)` for `h ≥ 0`.  Mirror of
`B0223.Sop_continuousOn` (`Units/B0223/Semigroup.lean:155`): the factors are the dilation
`dilN (e^{s/2})⁻¹` (`tendsto_dilN_at`), the heat factor `heatC (h(e^s-1))` (`heatC_continuousOn`
composed with `s ↦ h(e^s-1) ≥ 0`, `heatTime_nonneg`), the phase translation `transC (-s)`
(`continuous_transC`, composed with `s ↦ -s`), and the scalar `e^{-s/4}`.  Each uniformly bounded
family is handled by `tendsto_clm_apply`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odCont : OD_Cont := by
  intro P _ h hh Ψ t0 ht0
  -- dilation factor `s ↦ dilN (e^{s/2})⁻¹ Ψ`
  have ha : Tendsto (fun t : ℝ => (Real.exp (t / 2))⁻¹) (𝓝[Ici 0] t0)
      (𝓝 (Real.exp (t0 / 2))⁻¹) :=
    ((Continuous.inv₀ (Real.continuous_exp.comp (continuous_id.div_const 2))
      (fun t => (Real.exp_pos _).ne')).tendsto t0).mono_left nhdsWithin_le_nhds
  have hD := UnforcedLeray.B0223.tendsto_dilN_at (E := UnforcedLeray.B0223.SpaceC)
    (inv_pos.mpr (Real.exp_pos (t0 / 2))) ha
    (Eventually.of_forall fun t => inv_pos.mpr (Real.exp_pos _)) Ψ
  -- heat factor `s ↦ heatC (h(e^s-1))`, applied to the fixed vector `dilN (e^{t0/2})⁻¹ Ψ`
  have hθc : ContinuousWithinAt (fun t : ℝ => h * (Real.exp t - 1)) (Ici 0) t0 :=
    (continuous_const.mul (Real.continuous_exp.sub continuous_const)).continuousWithinAt
  have hmaps : MapsTo (fun t : ℝ => h * (Real.exp t - 1)) (Ici 0) (Ici 0) :=
    fun t ht => UnforcedLeray.B0223.heatTime_nonneg hh ht
  have hAv1 : Tendsto (fun t : ℝ =>
      UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) (h * (Real.exp t - 1))
        (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (t0 / 2))⁻¹ Ψ))
      (𝓝[Ici 0] t0)
      (𝓝 (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) (h * (Real.exp t0 - 1))
        (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (t0 / 2))⁻¹ Ψ))) :=
    ContinuousWithinAt.comp (f := fun t : ℝ => h * (Real.exp t - 1))
      (g := fun θ : ℝ => UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) θ
        (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
          (Real.exp (t0 / 2))⁻¹ Ψ))
      ((UnforcedLeray.B0223.heatC_continuousOn (E := UnforcedLeray.B0223.SpaceC)
        (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
          (Real.exp (t0 / 2))⁻¹ Ψ)) _ (hmaps ht0))
      hθc hmaps
  have hw := UnforcedLeray.B0223.tendsto_clm_apply
    (fun t : ℝ => UnforcedLeray.B0223.norm_heatC_le (E := UnforcedLeray.B0223.SpaceC)
      (P := P) (h * (Real.exp t - 1))) hAv1 hD
  -- transposed translation `s ↦ transC (-s)` applied to the heat-dilation vector
  have hc : Continuous fun t : ℝ =>
      UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-t)
        (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) (h * (Real.exp t0 - 1))
          (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
            (Real.exp (t0 / 2))⁻¹ Ψ)) :=
    (UnforcedLeray.B0223.continuous_transC (E := UnforcedLeray.B0223.SpaceC) _).comp
      continuous_neg
  have hAv2 : Tendsto (fun t : ℝ =>
      (LinearIsometry.toContinuousLinearMap
        (UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-t)))
        (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) (h * (Real.exp t0 - 1))
          (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
            (Real.exp (t0 / 2))⁻¹ Ψ)))
      (𝓝[Ici 0] t0)
      (𝓝 ((LinearIsometry.toContinuousLinearMap
        (UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-t0)))
        (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) (h * (Real.exp t0 - 1))
          (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
            (Real.exp (t0 / 2))⁻¹ Ψ)))) := by
    simp only [LinearIsometry.coe_toContinuousLinearMap]
    exact (hc.tendsto t0).mono_left nhdsWithin_le_nhds
  have hT := UnforcedLeray.B0223.tendsto_clm_apply
    (fun t : ℝ => LinearIsometry.norm_toContinuousLinearMap_le
      (UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-t))) hAv2 hw
  simp only [LinearIsometry.coe_toContinuousLinearMap] at hT
  -- scalar factor `e^{-s/4}`
  have hcs : Tendsto (fun t : ℝ => ((Real.exp (-t / 4) : ℝ) : ℂ)) (𝓝[Ici 0] t0)
      (𝓝 ((Real.exp (-t0 / 4) : ℝ) : ℂ)) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_neg.div_const 4))).tendsto t0).mono_left nhdsWithin_le_nhds
  exact hcs.smul hT

end UnforcedLeray.Short.PartIIIb.NearInst
