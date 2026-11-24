import UnforcedLeray.Units.B0579
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.LocalizedSourceBounds

/-!
# Integrability of `X_{m,c}` functions on the centred cell (`m > 1`)

Helper for `VelLipZeroCirc`, `VelLipBSSub`, `VelLipBSBound`: `∫_cell |f| < ∞` for `f ∈ X_{m,c}`
with `m > 1`, because `⟨x⟩^{-m}` is integrable on the cell (dominated by `(1+η²)^{-m}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace CellIntAux

/-- `jb^{-m}` is integrable on the centred cell for `m > 1/2`. -/
lemma integrable_jb_neg {c m : ℝ} (hm : 1 < m) :
    Integrable (fun x : ℝ × ℝ => B0579.jb x ^ (-m)) (volume.restrict (B0579.cell c)) := by
  have hI1 : Integrable (fun y : ℝ => (1 + y ^ 2) ^ (-m)) volume := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * m)
      (by simp; linarith)
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  have hI0 : Integrable (Set.indicator (Ico (-(c / 2)) (c / 2)) (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Ico).2
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  have hP : Integrable (fun z : ℝ × ℝ =>
      (Ico (-(c / 2)) (c / 2)).indicator (fun _ : ℝ => (1 : ℝ)) z.1 * (1 + z.2 ^ 2) ^ (-m)) volume := by
    rw [Measure.volume_eq_prod]
    exact hI0.mul_prod hI1
  refine Integrable.mono' (hP.restrict (s := B0579.cell c))
    ((B0579.continuous_jb_rpow (-m)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
  have hx1 : x.1 ∈ Ico (-(c / 2)) (c / 2) := hx.1
  rw [Set.indicator_of_mem hx1, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _)]
  have hle : 1 + x.2 ^ 2 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)

end CellIntAux

/-- **Integrability on the cell**: for `m > 1`, `f ∈ X_{m,c}` is integrable on the centred cell. -/
lemma integrableOn_cell_of_X {c m : ℝ} (hm : 1 < m) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c m)) : IntegrableOn f (B0579.cell c) := by
  have hG : MemLp (fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * f x) 2
      (volume.restrict (B0579.cell c)) := by
    refine ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow (m / 2))).aestronglyMeasurable.mul
        (hf.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m))
    · rw [← eLpNorm_cellMeasure_cx]
      exact hf.eLpNorm_lt_top
  have hH : MemLp (fun x => ((B0579.jb x ^ (-(m / 2)) : ℝ) : ℂ)) 2 (volume.restrict (B0579.cell c)) := by
    refine (memLp_two_iff_integrable_sq_norm ?_).2 ?_
    · exact (Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow (-(m / 2)))).aestronglyMeasurable
    · refine (CellIntAux.integrable_jb_neg hm).congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _),
        ← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos x).le]
      congr 1
      push_cast
      ring
  have key := hH.integrable_mul hG
  show Integrable f (volume.restrict (B0579.cell c))
  refine key.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (B0579.jb_pos x),
    show -(m / 2) + m / 2 = (0 : ℝ) by ring, Real.rpow_zero, Complex.ofReal_one, one_mul]

end UnforcedLeray.Short.IIIa
