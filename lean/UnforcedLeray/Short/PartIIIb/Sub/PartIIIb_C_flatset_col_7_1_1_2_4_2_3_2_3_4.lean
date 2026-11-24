import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec
import UnforcedLeray.Units.B0224.FiberHeat

/-!
# `pepsC0FubiniOrth` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2/3/4`)

Source `the November 2 reference manuscript` 1650-1656, 1676.
Fubini for the `H`-pairing of `f' - Ψ` (an `L²(measureH c)` class) with `b`: the pairing is the
`H`-integral of the pointwise pairing, which by `withDensity` and the product structure of
`cellMeasure c` is the iterated integral `∫_{s>0} s^(-3/2) ∫_strip ⟨Φ - Ψ, b⟩ ds`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem pepsC0FubiniOrth : PepsC0FubiniOrth := by
  intro c hc f' Φ Ψ hH hmem b
  obtain ⟨hΦm, hΨm, -, -, hf, -⟩ := hH
  -- the difference `f' - Ψ` is `toMC (Φ - Ψ)` almost everywhere
  have hg_ae : ⇑(f' - hmem.toLp (fun p => toMC (Ψ p)))
      =ᵐ[UnforcedLeray.B0220.measureH c] fun p => toMC (Φ p) - toMC (Ψ p) := by
    filter_upwards [Lp.coeFn_sub f' (hmem.toLp (fun p => toMC (Ψ p))), hf,
      MemLp.coeFn_toLp hmem] with p h1 h2 h3
    simp only [h1, Pi.sub_apply, h2, h3]
  have hint : Integrable (fun p => inner ℂ ((f' - hmem.toLp (fun p => toMC (Ψ p))) p) (b p))
      (UnforcedLeray.B0220.measureH c) :=
    L2.integrable_inner (𝕜 := ℂ) (f' - hmem.toLp (fun p => toMC (Ψ p))) b
  have hH_int : Integrable (fun p => ∑ i : Fin 2, (starRingEnd ℂ) (Φ p i - Ψ p i) *
      (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i)
      (UnforcedLeray.B0220.measureH c) := by
    refine hint.congr ?_
    filter_upwards [hg_ae] with p hp
    rw [hp]
    simp [PiLp.inner_apply, Fin.sum_univ_two, toMC, map_sub] <;> ring
  have hcong : ∫ p, inner ℂ ((f' - hmem.toLp (fun p => toMC (Ψ p))) p) (b p)
      ∂(UnforcedLeray.B0220.measureH c)
      = ∫ p, ∑ i : Fin 2, (starRingEnd ℂ) (Φ p i - Ψ p i) *
          (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i
        ∂(UnforcedLeray.B0220.measureH c) := by
    refine integral_congr_ae ?_
    filter_upwards [hg_ae] with p hp
    rw [hp]
    simp [PiLp.inner_apply, Fin.sum_univ_two, toMC, map_sub] <;> ring
  rw [L2.inner_def, hcong]
  have hlt : ∀ᵐ p ∂UnforcedLeray.B0220.cellMeasure c, UnforcedLeray.B0220.weightH p < ∞ :=
    Eventually.of_forall fun p => ENNReal.ofReal_lt_top
  have hint2 : Integrable (fun p => (UnforcedLeray.B0220.weightH p).toReal • ∑ i : Fin 2,
      (starRingEnd ℂ) (Φ p i - Ψ p i) *
        (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i)
      (UnforcedLeray.B0220.cellMeasure c) :=
    (integrable_withDensity_iff_integrable_smul' UnforcedLeray.B0220.measurable_weightH hlt).1
      hH_int
  refine (integral_withDensity_eq_integral_toReal_smul UnforcedLeray.B0220.measurable_weightH
    hlt _).trans ?_
  rw [UnforcedLeray.B0224.cellMeasure_eq_prod' c] at hint2 ⊢
  rw [integral_prod _ hint2]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : (0 : ℝ) < s := hs
  have hr : ∀ x : ℝ × ℝ, (UnforcedLeray.B0220.weightH (s, x)).toReal = s ^ (-(3 / 2 : ℝ)) :=
    fun x => ENNReal.toReal_ofReal (Real.rpow_nonneg hs0.le _)
  simp only [hr, Complex.real_smul]
  rw [integral_const_mul]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
