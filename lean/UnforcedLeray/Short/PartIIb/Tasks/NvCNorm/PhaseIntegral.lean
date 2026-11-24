import UnforcedLeray.Short.PartIIb.Sub.T07
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.Pointwise
import UnforcedLeray.Lib.AxisymmetricB.Lift

/-!


Source of record: `the November 2 reference manuscript`, lines 1902-1906
(the complex lift `N_v b = N_v(Re b) + i N_v(Im b)` and its norm factor `(πR²)^{1/r}`).
The target is the Prop `NvCPhaseIntegral` of `Short/PartII-b/Sub/T07.lean`.

Proof: the complex copy of `Axi.lintegral_Nv_rpow` (`Lib/AxisymmetricB/Lift.lean`, lines 143-163).
With `G p := ofReal (p.1^(q/2)) * ‖b p‖ₑ^q`, the pointwise identity `nvCPointwise` (T07/3)
replaces `Axi.enorm_Nv_rpow` inside the inner integral, then the ring-chart phase average
`Axi.phaseAvg_ringChart`, the age-measure formula `Axi.lintegral_ageμ` and the density identity
`Axi.ofReal_density_mul` finish the computation exactly as in the template.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- SP 1902-1906, step 4: the complex copy of `Axi.lintegral_Nv_rpow` for a measurable,
everywhere `c`-periodic complex profile `b`, with `P = 2c/R` and `q > 0`:
`P⁻¹ ∫_{(0,P]} ∫_{ℝ³} ‖N_v b‖ₑ^q dy dτ = πR² ∫ ‖b‖ₑ^q dageμ c (q/2 − 5/2)`. -/
theorem nvCPhaseIntegral : UnforcedLeray.Short.IIb.NvCPhaseIntegral := by
  unfold UnforcedLeray.Short.IIb.NvCPhaseIntegral
  intro R c P q hR hc hP hq b hb hper
  have hpw : UnforcedLeray.Short.IIb.NvCPointwise := nvCPointwise
  unfold UnforcedLeray.Short.IIb.NvCPointwise at hpw
  set G : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 ^ (q / 2)) * ‖b p‖ₑ ^ q with hG
  have hGm : Measurable G :=
    ((Axi.measurable_ofReal_rpow _).comp measurable_fst).mul (hb.enorm.pow_const q)
  have hGper : ∀ s ξ η, G (s, (ξ + c, η)) = G (s, (ξ, η)) := fun s ξ η => by
    simp only [hG, hper]
  have hin : ∀ τ : ℝ, ∫⁻ y : Space, ‖NvC R b (τ, y)‖ₑ ^ q =
      ∫⁻ y : Space, G (Axi.age R y, (Axi.phase R τ y, Axi.trans R y)) := by
    intro τ
    refine lintegral_congr_ae ?_
    filter_upwards [Axi.ae_not_mem_axis] with y hy
    rw [hpw R b τ y hy q hq.le]
    rfl
  rw [setLIntegral_congr_fun measurableSet_Ioc (fun τ _ => hin τ),
    Axi.phaseAvg_ringChart hR hc hP G hGm hGper,
    Axi.lintegral_ageμ hc _ (hb.enorm.pow_const q)]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ))
    fun p hp => ?_
  exact Axi.ofReal_density_mul hc hp.1 _ _

end UnforcedLeray.Short.IIb
