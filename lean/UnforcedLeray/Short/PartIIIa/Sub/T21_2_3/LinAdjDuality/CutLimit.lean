import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# Removing the transverse cutoff (`LadCutLimit`, SP 3074-3075)

Dominated convergence for `R → ∞` in `∫_{C_c} F χ_R G`, with `χ_R = ladCut R` (`0 ≤ χ_R ≤ 1`,
`χ_R = 1` on `η² ≤ R²`), and `FG ∈ L¹(C_c)` by weighted Cauchy-Schwarz (`integrableOn_mul_neg`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutLimitAux

lemma nonneg (R : ℝ) (x : ℝ × ℝ) : 0 ≤ ladCut R x := Real.smoothTransition.nonneg _

lemma le_one (R : ℝ) (x : ℝ × ℝ) : ladCut R x ≤ 1 := Real.smoothTransition.le_one _

lemma continuous_cut (R : ℝ) : Continuous (ladCut R) := by
  unfold ladCut
  exact Real.smoothTransition.continuous.comp
    (continuous_const.sub ((continuous_snd.pow 2).div_const _))

lemma eq_one {R : ℝ} {x : ℝ × ℝ} (hR : |x.2| + 1 ≤ R) : ladCut R x = 1 := by
  have hR0 : 0 < R := by linarith [abs_nonneg x.2]
  have hx2 : x.2 ^ 2 ≤ R ^ 2 := by
    have h1 : |x.2| ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
    rwa [sq_abs] at h1
  have hdiv : x.2 ^ 2 / R ^ 2 ≤ 1 := (div_le_one (pow_pos hR0 2)).2 hx2
  unfold ladCut
  exact Real.smoothTransition.one_of_one_le (by linarith)

/-- The complex-valued weighted product is integrable on the cell, from the real-valued
Cauchy-Schwarz `integrableOn_mul_neg` (`X c m` against `X c (-m)`). -/
lemma integrable_real {c m : ℝ} {f g : ℝ × ℝ → ℝ} (hf : MemLp f 2 (B0579.cellMeasure c m))
    (hg : MemLp g 2 (B0579.cellMeasure c (-m))) :
    Integrable (fun x => f x * g x) (volume.restrict (B0579.cell c)) := by
  have h := B0579.integrableOn_mul_neg c m (hf.toLp f) (hg.toLp g)
  have e1 : (⇑(hf.toLp f)) =ᵐ[volume.restrict (B0579.cell c)] f :=
    (B0579.ac_cellMeasure c m).ae_le hf.coeFn_toLp
  have e2 : (⇑(hg.toLp g)) =ᵐ[volume.restrict (B0579.cell c)] g :=
    (B0579.ac_cellMeasure c (-m)).ae_le hg.coeFn_toLp
  exact Integrable.congr h (e1.mul e2)

lemma integrable_complex {c m : ℝ} {F G : ℝ × ℝ → ℂ} (hF : MemLp F 2 (B0579.cellMeasure c m))
    (hG : MemLp G 2 (B0579.cellMeasure c (-m))) :
    Integrable (fun x => F x * G x) (volume.restrict (B0579.cell c)) := by
  have hn : Integrable (fun x => ‖F x‖ * ‖G x‖) (volume.restrict (B0579.cell c)) :=
    integrable_real hF.norm hG.norm
  refine Integrable.mono' hn ?_ (ae_of_all _ fun x => ?_)
  · exact (hF.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m)).mul
      (hG.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c (-m)))
  · exact (norm_mul _ _).le

end CutLimitAux

/-- **Removing the cutoff** (SP 3074-3075): `∫_{C_c} F χ_R G → ∫_{C_c} F G` as `R → ∞`. -/
theorem ladCutLimit : LadCutLimit := by
  intro c m F G hF hG
  have hint := CutLimitAux.integrable_complex hF hG
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x * G x‖)
    (F := fun (R : ℝ) (x : ℝ × ℝ) => F x * ((ladCut R x : ℂ) * G x)) (f := fun x => F x * G x)
    ?_ ?_ hint.norm ?_
  · refine Eventually.of_forall fun R => ?_
    have hFm := hF.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m)
    have hGm := hG.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c (-m))
    have hLm : AEStronglyMeasurable (fun x : ℝ × ℝ => (ladCut R x : ℂ)) (volume.restrict (B0579.cell c)) :=
      (Complex.continuous_ofReal.comp (CutLimitAux.continuous_cut R)).aestronglyMeasurable
    exact hFm.mul (hLm.mul hGm)
  · refine Eventually.of_forall fun R => ae_of_all _ fun x => ?_
    have e : F x * ((ladCut R x : ℂ) * G x) = (ladCut R x : ℂ) * (F x * G x) := by ring
    show ‖F x * ((ladCut R x : ℂ) * G x)‖ ≤ ‖F x * G x‖
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (CutLimitAux.nonneg R x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (CutLimitAux.le_one R x)
  · refine ae_of_all _ fun x => ?_
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (|x.2| + 1)] with R hR
    rw [CutLimitAux.eq_one hR]
    simp

end UnforcedLeray.Short.IIIa
