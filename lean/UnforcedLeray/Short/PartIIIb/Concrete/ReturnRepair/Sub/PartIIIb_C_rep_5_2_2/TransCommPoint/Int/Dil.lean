import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.SepX0Dom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_3
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Kernel

/-!
# Pointwise Cauchy-Schwarz bound for the dilation integral, uniform in the phase

Source `the November 2 reference manuscript` 3624-3647 (`sep:young` with
`p = b = 2`, Hölder in `z` instead of Young in `y`) and 3838-3845 (periodic dilation sum).

For `g` jointly measurable and `P`-periodic with finite `L²_τL²` moment, at **every** phase `τ`
and **every** receiver `y`,
`sepDom a j D g τ y ≤ C_j D^{-5/2-j} · M`, with `M` independent of `τ, y, D`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `L²` norm of the gap kernel is finite. -/
theorem tcd_kerL2_ne_top (j : ℕ) : ∫⁻ x : Space, IIIa.sepKd j 1 x ^ (2 : ℝ) ≠ ⊤ :=
  IIIa.lintegral_sepKd_rpow_one_ne_top j 2 (by norm_num)

theorem tcd_rpow_half {l : ℝ} (hl : 0 < l) : ((l ^ 3)⁻¹) ^ (1 / 2 : ℝ) = l ^ (-(3 / 2 : ℝ)) := by
  have h1 : (l ^ 3)⁻¹ = l ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hl.le]
    congr 1
    exact (Real.rpow_natCast l 3).symm
  rw [h1, ← Real.rpow_mul hl.le]
  congr 1
  ring

/-- Hölder in `z` and dilation. -/
theorem tcd_inner_le (j : ℕ) (D : ℝ) (hD : 0 < D) (y : Space) (l : ℝ) (hl : 0 < l)
    (g' : Space → ℝ≥0∞) (hg : Measurable g') :
    ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g' z ≤
      ENNReal.ofReal (l ^ (-(3 / 2 : ℝ))) *
        ((ENNReal.ofReal (D ^ (3 - (4 + (j : ℝ)) * 2)) *
            ∫⁻ x : Space, IIIa.sepKd j 1 x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * lqNorm 2 g') := by
  have hKm : Measurable fun z : Space => IIIa.sepKd j D (y - l • z) :=
    (IIIa.sepKd_measurable j D).comp (measurable_const.sub (measurable_const_smul l))
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Space)
    (Real.HolderConjugate.two_two) (f := fun z => IIIa.sepKd j D (y - l • z)) (g := g')
    hKm.aemeasurable hg.aemeasurable
  refine h.trans ?_
  have e1 := IIIa.lintegral_sepKd_dilate j D 2 y l hl (by norm_num)
  have e2 := IIIa.lintegral_sepKd_rpow j D 2 hD (by norm_num)
  rw [e1, e2, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 (pow_nonneg hl.le _)) (by norm_num),
    tcd_rpow_half hl, mul_assoc]
  unfold lqNorm
  norm_num

/-- The dilation integral at one point, in terms of the phase profile
`G(s) = ‖g(s)‖_{L²_z}`. -/
theorem tcd_sepDom_le (a : ℝ) (j : ℕ) (D : ℝ) (hD : 0 < D) (g : ℝ → Space → ℝ≥0∞)
    (hgm : Measurable (Function.uncurry g)) (τ : ℝ) (y : Space) :
    IIIa.sepDom a j D g τ y ≤
      (ENNReal.ofReal (D ^ (3 - (4 + (j : ℝ)) * 2)) *
          ∫⁻ x : Space, IIIa.sepKd j 1 x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a - 3 / 2)) *
          lqNorm 2 (g (τ + 2 * Real.log l)) := by
  set K : ℝ≥0∞ := (ENNReal.ofReal (D ^ (3 - (4 + (j : ℝ)) * 2)) *
          ∫⁻ x : Space, IIIa.sepKd j 1 x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) with hK
  have hKne : K ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (tcd_kerL2_ne_top j))
  unfold IIIa.sepDom
  rw [← lintegral_const_mul' _ _ hKne]
  refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
  have hgl : Measurable (g (τ + 2 * Real.log l)) :=
    hgm.comp (measurable_const.prodMk measurable_id)
  have h1 := tcd_inner_le j D hD y l hl.1 _ hgl
  have h2 : ENNReal.ofReal (l ^ a) * ENNReal.ofReal (l ^ (-(3 / 2 : ℝ))) =
      ENNReal.ofReal (l ^ (a - 3 / 2)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _), ← Real.rpow_add hl.1]
    congr 2
  calc ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z
      ≤ ENNReal.ofReal (l ^ a) * (ENNReal.ofReal (l ^ (-(3 / 2 : ℝ))) *
          (K * lqNorm 2 (g (τ + 2 * Real.log l)))) := mul_le_mul' le_rfl h1
    _ = K * (ENNReal.ofReal (l ^ (a - 3 / 2)) * lqNorm 2 (g (τ + 2 * Real.log l))) := by
        rw [← h2]; ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
