import UnforcedLeray.Lib.HeatCylinder.CellBridge

/-!
# Exact normalization of periodic `L²` classes

For one measurable periodic representative, the centered and normalized-cell quotient norms
differ by exactly `√c`. This is the norm transport needed when taking the smooth periodic core to
the closure of the actual normalized-cell heat operators.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)

/-- The exact centered/normalized `L²` norm conversion for a single periodic representative. -/
theorem norm_centered_toLp_eq_sqrt_period_mul_normalized {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {c : ℝ} (hc : 0 < c) {f : Plane → E} (hfmeas : Measurable f)
    (hfper : UnforcedLeray.B0284.IsQPeriodic c f)
    (hfc : MemLp f 2 (UnforcedLeray.Cyl.cellμ c))
    (hfn : MemLp f 2 (UnforcedLeray.B0284.cellMeasure c)) :
    ‖hfc.toLp f‖ = Real.sqrt c * ‖hfn.toLp f‖ := by
  have hscale := UnforcedLeray.HeatCylinder.eLpNorm_sq_cyl_eq_cellMeasure hc hfmeas hfper
  have hsq := congrArg ENNReal.toReal hscale
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt hc), ENNReal.toReal_pow] at hsq
  have hsq' : (eLpNorm (hfc.toLp f : Plane → E) 2
        (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2 =
      c * (eLpNorm (hfn.toLp f : Plane → E) 2
        (UnforcedLeray.B0284.cellMeasure c)).toReal ^ 2 := by
    rw [eLpNorm_congr_ae hfc.coeFn_toLp, eLpNorm_congr_ae hfn.coeFn_toLp]
    exact hsq
  have hnormsq : ‖hfc.toLp f‖ ^ 2 = c * ‖hfn.toLp f‖ ^ 2 := by
    simpa [Lp.norm_def] using hsq'
  have hsqrt : (Real.sqrt c * ‖hfn.toLp f‖) ^ 2 =
      (‖hfc.toLp f‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hc)]
    nlinarith
  have hleft : 0 ≤ Real.sqrt c * ‖hfn.toLp f‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hright : 0 ≤ ‖hfc.toLp f‖ := norm_nonneg _
  exact ((sq_eq_sq₀ hleft hright).mp hsqrt).symm

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_centered_toLp_eq_sqrt_period_mul_normalized
