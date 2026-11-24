import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.XNorm

/-!
# `PartIII-a:T21/2/7/2/2/1/1`: the uniform weighted `L²` bound `AdjSupL2`

Source: `the November 2 reference manuscript` (SP) line 3060. The weak adjoint
`r ↦ φ r` is strongly continuous in `X_{-m,c}` on `[t, s]` (`IsAdjointWeak.strongCont`), so
`r ↦ ‖φ r‖_{X_{-m,c}}` is continuous on the compact `[t, s]` (`xNorm_continuousWithinAt_of_strongCont`),
hence bounded; the lintegral of `‖·‖ₑ^2` is the square of `xNorm`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The squared lintegral is the square of the `X` norm (`eLpNorm` with `p = 2`). -/
theorem lintegral_enorm_rpow_two_eq_xNorm_sq (c m : ℝ) (f : ℝ × ℝ → ℂ) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c m) = xNorm c m f ^ 2 := by
  unfold xNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [show ((2 : ℝ≥0∞)).toReal = 2 by norm_num, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **Leaf `PartIII-a:T21/2/7/2/2/1/1`** (SP 3060): the weighted `L²` norm of the weak adjoint is
uniformly bounded on `[t, s]`. -/
theorem adjSupL2 (m : ℝ) (hm : 8 < m) : AdjSupL2 m := by
  intro ν tr t s G φ hctx
  obtain ⟨_hν, _hν1, _hb, _ht, _hts, _hG, hW, _hC⟩ := hctx
  have hcont : ∀ r ∈ Icc t s,
      ContinuousWithinAt (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m) (φ r')) (Icc t s) r :=
    fun r hr => xNorm_continuousWithinAt_of_strongCont (fun r' hr' => hW.memX r' hr')
      (fun r' hr' => hW.strongCont r' hr') r hr
  have hG : ContinuousOn (fun r' => (xNorm (ν ^ (-2 : ℝ)) (-m) (φ r')).toReal) (Icc t s) := by
    intro r hr
    have hF : xNorm (ν ^ (-2 : ℝ)) (-m) (φ r) ≠ ⊤ := (hW.memX r hr).2.ne
    have hT : ContinuousAt ENNReal.toReal (xNorm (ν ^ (-2 : ℝ)) (-m) (φ r)) :=
      ENNReal.continuousAt_toReal hF
    exact ContinuousAt.comp_continuousWithinAt (f := fun r' => xNorm (ν ^ (-2 : ℝ)) (-m) (φ r'))
      (x := r) hT (hcont r hr)
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hG).bddAbove
  refine ⟨M ^ 2, fun ρ hρ => ?_⟩
  have hF : xNorm (ν ^ (-2 : ℝ)) (-m) (φ ρ) ≠ ⊤ := (hW.memX ρ hρ).2.ne
  have ha : (xNorm (ν ^ (-2 : ℝ)) (-m) (φ ρ)).toReal ≤ M :=
    hM (Set.mem_image_of_mem _ hρ)
  have ha0 : 0 ≤ (xNorm (ν ^ (-2 : ℝ)) (-m) (φ ρ)).toReal := ENNReal.toReal_nonneg
  have hsq := lintegral_enorm_rpow_two_eq_xNorm_sq (ν ^ (-2 : ℝ)) (-m) (φ ρ)
  rw [hsq]
  have hX : xNorm (ν ^ (-2 : ℝ)) (-m) (φ ρ) = ENNReal.ofReal
      ((xNorm (ν ^ (-2 : ℝ)) (-m) (φ ρ)).toReal) := (ENNReal.ofReal_toReal hF).symm
  rw [hX, ← ENNReal.ofReal_pow ha0]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [ha, ha0]

end UnforcedLeray.Short.IIIa
