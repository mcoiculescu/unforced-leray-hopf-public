import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_2_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/2/1/3`: the Gaussian in `η` is `L²` over the cell

Source `the November 2 reference manuscript`, lines 261-288.

The cell is `Ioc 0 c ×ˢ univ`, so `cellMeasure c = c⁻¹ • volume.restrict (cell c)` restricts to
`(volume.restrict (Ioc 0 c)).prod volume`.  The square of `e^{-η²/32}` is `e^{-η²/16}`, which is
integrable in `η` and constant in the finite `q`-interval.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace GaussCellL2Aux

open UnforcedLeray

/-- `e^{-η²/16}` is integrable on one cell `(0, c] × ℝ`. -/
theorem integrable_gauss_cell (c : ℝ) :
    Integrable (fun z : Cyl.Plane => Real.exp (-(1 / 16 : ℝ) * z.2 ^ 2))
      (volume.restrict (B0284.cell c)) := by
  have hg : Integrable (fun η : ℝ => Real.exp (-(1 / 16 : ℝ) * η ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hf : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 c) volume :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hm : ((volume : Measure ℝ).restrict (Ioc 0 c)).prod (volume : Measure ℝ)
      = (volume : Measure (ℝ × ℝ)).restrict (B0284.cell c) := by
    have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Ioc 0 c) univ
    rw [Measure.restrict_univ] at this
    exact this
  have hprod := hf.mul_prod hg
  rw [← hm]
  exact hprod.congr (ae_of_all _ fun z => by simp)

theorem gaussCellL2_aux (c : ℝ) :
    eLpNorm (fun z : Cyl.Plane => Real.exp (-(z.2 ^ 2) / 32)) 2 (B0284.cellMeasure c) < ⊤ := by
  have hmeas : AEStronglyMeasurable (fun z : Cyl.Plane => Real.exp (-(z.2 ^ 2) / 32))
      (B0284.cellMeasure c) :=
    (Continuous.aestronglyMeasurable (by fun_prop))
  have hint : Integrable (fun z : Cyl.Plane => ‖Real.exp (-(z.2 ^ 2) / 32)‖ ^ 2)
      (B0284.cellMeasure c) := by
    have h1 : Integrable (fun z : Cyl.Plane => Real.exp (-(1 / 16 : ℝ) * z.2 ^ 2))
        (B0284.cellMeasure c) := by
      unfold B0284.cellMeasure
      exact (integrable_gauss_cell c).smul_measure_nnreal
    refine h1.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  exact ((memLp_two_iff_integrable_sq_norm hmeas).2 hint).eLpNorm_lt_top

end GaussCellL2Aux

/-- **Leaf G (Gaussian in `η` is `L²` over the cell; source lines 261-288).** -/
theorem gaussCellL2 : UnforcedLeray.Short.PartI.GaussCellL2 := by
  unfold UnforcedLeray.Short.PartI.GaussCellL2
  intro c _hc
  exact GaussCellL2Aux.gaussCellL2_aux c
