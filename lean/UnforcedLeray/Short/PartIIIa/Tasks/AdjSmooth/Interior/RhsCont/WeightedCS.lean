import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.LocalizedSourceBounds

/-!
# `PartIII-a:T21/2/7/2/1/1/3/1`: weighted Cauchy-Schwarz on the cell (`WeightedCS`)

Source: `the November 2 reference manuscript` lines 3052-3058.
`∫_cell |f||B| ≤ ‖f‖_{X_{-m}} ‖B‖_{X_m}`: pass to the unweighted cell by
`eLpNorm_cellMeasure(_cx)`, then Hölder with exponents `2, 2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- Hölder with exponents `2, 2` for `eLpNorm` on a measure space. -/
theorem wcs_holder2 {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [MeasurableSpace F]
    [BorelSpace F] {μ : Measure α} (f : α → E) (g : α → F)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf.aemeasurable.enorm hg.aemeasurable.enorm

theorem weightedCS : UnforcedLeray.Short.IIIa.WeightedCS := by
  unfold UnforcedLeray.Short.IIIa.WeightedCS UnforcedLeray.Short.IIIa.xNorm
  intro c m f B hf hB
  have hf' : AEStronglyMeasurable f (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    hf.mono_ac (UnforcedLeray.B0579.ac_cellMeasure c (-m))
  have hB' : AEStronglyMeasurable B (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    hB.mono_ac (UnforcedLeray.B0579.ac_cellMeasure c m)
  have hw : Continuous fun x : ℝ × ℝ => ((UnforcedLeray.B0579.jb x ^ ((-m) / 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (UnforcedLeray.B0579.continuous_jb_rpow _)
  have hw' : Continuous fun x : ℝ × ℝ => UnforcedLeray.B0579.jb x ^ (m / 2) :=
    UnforcedLeray.B0579.continuous_jb_rpow _
  have hH := wcs_holder2 (μ := volume.restrict (UnforcedLeray.B0579.cell c))
    (fun x => ((UnforcedLeray.B0579.jb x ^ ((-m) / 2) : ℝ) : ℂ) * f x)
    (fun x => UnforcedLeray.B0579.jb x ^ (m / 2) * B x)
    (hw.aestronglyMeasurable.mul hf') (hw'.aestronglyMeasurable.mul hB')
  rw [UnforcedLeray.Short.IIIa.eLpNorm_cellMeasure_cx, UnforcedLeray.B0579.eLpNorm_cellMeasure]
  refine le_trans (le_of_eq ?_) hH
  refine lintegral_congr fun x => ?_
  have ha : 0 ≤ UnforcedLeray.B0579.jb x ^ ((-m) / 2) :=
    Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le _
  have hb : 0 ≤ UnforcedLeray.B0579.jb x ^ (m / 2) :=
    Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le _
  have hj : UnforcedLeray.B0579.jb x ^ ((-m) / 2) * UnforcedLeray.B0579.jb x ^ (m / 2) = 1 := by
    have h0 : (-m) / 2 + m / 2 = 0 := by ring
    rw [← Real.rpow_add (UnforcedLeray.B0579.jb_pos x), h0, Real.rpow_zero]
  have hab : ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) *
      ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ (m / 2)) = 1 := by
    rw [← ENNReal.ofReal_mul ha, hj, ENNReal.ofReal_one]
  have hc : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := fun r => by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]
  have e1 : ‖((UnforcedLeray.B0579.jb x ^ ((-m) / 2) : ℝ) : ℂ) * f x‖ₑ =
      ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) * ‖f x‖ₑ := by
    rw [enorm_mul, hc, Real.enorm_of_nonneg ha]
  have e2 : ‖UnforcedLeray.B0579.jb x ^ (m / 2) * B x‖ₑ =
      ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ (m / 2)) * ‖B x‖ₑ := by
    rw [enorm_mul, Real.enorm_of_nonneg hb]
  rw [e1, e2]
  calc ‖f x‖ₑ * ‖B x‖ₑ
      = (ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) *
          ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ (m / 2))) * (‖f x‖ₑ * ‖B x‖ₑ) := by
        rw [hab, one_mul]
    _ = _ := by ring
