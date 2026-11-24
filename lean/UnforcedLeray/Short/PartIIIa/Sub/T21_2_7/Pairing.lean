import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The pointwise density identity behind the transfer from `cellMeasure c (-m)` to Lebesgue
measure on the cell: `⟨x⟩^{-2m} · (w · ⟨x⟩^{m} χ) = w χ`. -/
theorem pr_density_key (m : ℝ) (χ : ℝ × ℝ → ℝ) (w : ℂ) (x : ℝ × ℝ) :
    ((B0579.density (-m) x : NNReal) • (w * ((B0579.mulFun m χ x : ℝ) : ℂ))) =
      w * (χ x : ℂ) := by
  have hp : ((B0579.jb x ^ (-m) : ℝ) : ℂ) * ((B0579.jb x ^ m : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (B0579.jb_pos x)]
    simp
  simp only [NNReal.smul_def, Complex.real_smul, B0579.coe_density, B0579.mulFun]
  push_cast
  linear_combination (w * (χ x : ℂ)) * hp

/-- **The test pairing on `X_{-m,c}`** (SP 2823-2826): a cylinder test `χ` gives an integrable
pairing `w ↦ ∫_{C_c} w χ` on `X_{-m,c}`, a continuous linear functional. -/
theorem adjPairing : AdjPairing := by
  intro c m hc χ hχ
  -- `⟨x⟩^m χ` lies in `L²(cellMeasure c (-m))`, with the norm of `χ` in `X_{m,c}`.
  have hnorm : eLpNorm (B0579.mulFun m χ) 2 (B0579.cellMeasure c (-m)) =
      eLpNorm χ 2 (B0579.cellMeasure c m) := by
    have h2 : (m - -m) / 2 = m := by ring
    have := B0579.eLpNorm_mulFun c m (-m) χ
    rw [h2] at this
    exact this
  have hmeas : Continuous (B0579.mulFun m χ) :=
    (B0579.continuous_jb_rpow m).mul hχ.continuous
  have hAm : MemLp (B0579.mulFun m χ) 2 (B0579.cellMeasure c (-m)) :=
    ⟨hmeas.aestronglyMeasurable, by rw [hnorm]; exact (hχ.memLp m).2⟩
  have hAC : MemLp (fun x => ((B0579.mulFun m χ x : ℝ) : ℂ)) 2 (B0579.cellMeasure c (-m)) :=
    hAm.ofReal
  refine ⟨fun w => ?_, ?_⟩
  · -- integrability on the cell, by the density transfer
    have hint := (Lp.memLp w).integrable_mul hAC
    have hint' := (integrable_withDensity_iff_integrable_smul
      (B0579.measurable_density (-m))).1 hint
    exact Integrable.congr hint' (Eventually.of_forall fun x => pr_density_key m χ (w x) x)
  · refine ⟨innerSL ℂ (hAC.toLp (fun x => ((B0579.mulFun m χ x : ℝ) : ℂ))), fun w => ?_⟩
    rw [innerSL_apply_apply, L2.inner_def]
    calc ∫ x, inner ℂ (hAC.toLp (fun x => ((B0579.mulFun m χ x : ℝ) : ℂ)) x) (w x)
            ∂(B0579.cellMeasure c (-m))
        = ∫ x, w x * ((B0579.mulFun m χ x : ℝ) : ℂ) ∂(B0579.cellMeasure c (-m)) := by
          refine integral_congr_ae ?_
          filter_upwards [hAC.coeFn_toLp] with x hx
          rw [hx]
          simp [RCLike.inner_apply]
      _ = ∫ x in B0579.cell c, w x * (χ x : ℂ) := by
          have h := integral_withDensity_eq_integral_smul (μ := volume.restrict (B0579.cell c))
            (B0579.measurable_density (-m))
            (fun x => w x * ((B0579.mulFun m χ x : ℝ) : ℂ))
          refine h.trans ?_
          exact integral_congr_ae (Eventually.of_forall fun x => pr_density_key m χ (w x) x)

end UnforcedLeray.Short.IIIa
