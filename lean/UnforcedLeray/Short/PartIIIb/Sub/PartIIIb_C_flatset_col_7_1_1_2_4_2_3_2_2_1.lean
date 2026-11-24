import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec

/-!
# `pepsC0FubiniSol` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2/2/1`)

Source `the November 2 reference manuscript` 1650-1656, 1676.

Strategy: the `L²(measureH c)` inner product of two `MeridC`-valued fields is the integral of the
pointwise pairing `Σ conj(f_i) g_i`; `cgrad` is real-valued, so the conjugation drops.  The
`measureH` integral is an iterated integral over `s^(-3/2) ds × (strip)` (complex version of
`B0224.integral_measureH_eq_iter`, proved the same way), and the weight is constant in `x`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Complex-valued iterated formula for `measureH` integrals (the `ℂ` analogue of
`B0224.integral_measureH_eq_iter`). -/
theorem hj2_integral_measureH_complex {c : ℝ}
    {φ : UnforcedLeray.B0220.Profile → ℂ}
    (hφ : Integrable φ (UnforcedLeray.B0220.measureH c)) :
    ∫ p, φ p ∂UnforcedLeray.B0220.measureH c =
      ∫ s in Ioi (0 : ℝ), ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ x in UnforcedLeray.B0224.strip c, φ (s, x) := by
  have hlt : ∀ᵐ p ∂UnforcedLeray.B0220.cellMeasure c, UnforcedLeray.B0220.weightH p < ∞ :=
    Eventually.of_forall fun p => ENNReal.ofReal_lt_top
  have hint : Integrable (fun p => (UnforcedLeray.B0220.weightH p).toReal • φ p)
      (UnforcedLeray.B0220.cellMeasure c) :=
    (integrable_withDensity_iff_integrable_smul' UnforcedLeray.B0220.measurable_weightH hlt).1 hφ
  rw [UnforcedLeray.B0220.measureH,
    integral_withDensity_eq_integral_toReal_smul UnforcedLeray.B0220.measurable_weightH hlt]
  rw [UnforcedLeray.B0224.cellMeasure_eq_prod'] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : (0 : ℝ) < s := hs
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))).toReal • φ (s, x)
    = ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * φ (s, x)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hs'.le _), Complex.real_smul]

theorem pepsC0FubiniSol : PepsC0FubiniSol := by
  intro c _hc Φt hg Ψ hmem
  set μ := UnforcedLeray.B0220.measureH c with hμ
  set F : UnforcedLeray.B0220.Profile → ℂ := fun p =>
    ∑ i : Fin 2, UnforcedLeray.Short.PartIIa.cgrad 0 Φt.1 p i * Ψ p i with hF
  have hae : (fun a => inner ℂ (hg.toLp _ a) (hmem.toLp _ a)) =ᵐ[μ] F := by
    filter_upwards [hg.coeFn_toLp, hmem.coeFn_toLp] with a h1 h2
    simp only [h1, h2, hF]
    simp [PiLp.inner_apply, UnforcedLeray.Short.PartIIa.cgrad, toMC, Fin.sum_univ_two]
    ring
  have hint : Integrable F μ :=
    (L2.integrable_inner (hg.toLp _) (hmem.toLp _)).congr hae
  rw [L2.inner_def, integral_congr_ae hae]
  exact hj2_integral_measureH_complex hint

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
